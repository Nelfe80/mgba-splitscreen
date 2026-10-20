/* Optional v0.5 online transport.
 *
 * The host remains authoritative: it owns the mGBA/WASM session and guests send
 * only input messages. The transport uses PeerJS, which is WebRTC DataChannels
 * under the hood — payloads go peer-to-peer, only the tiny signaling handshake
 * touches a broker. It is intentionally opt-in and does not affect local play
 * when PeerJS is blocked.
 *
 * Video: each guest receives ONLY its own seat's screen, JPEG-encoded on the
 * host (~10-20KB/frame vs ~300KB raw RGBA for a 2P broadcast). Raw RGBA is kept
 * available for future local-network use, but JPEG is the default because a
 * reliable DataChannel backed up by megabytes-per-second of raw frames stalls
 * to a few fps and the backlog grows unboundedly (observed: guests minutes
 * behind at 3-4 fps). A 30 fps cap keeps latency at a fraction of a second.
 *
 * v3 raw-frame transport (2026-10-19): video frames move on a DEDICATED,
 * UNRELIABLE, UNORDERED WebRTC DataChannel ({ordered:false, maxRetransmits:0})
 * while input/auth/other control messages stay on the original reliable
 * channel. Unreliable transport means a lost packet is never retransmitted:
 * the next frame is already newer, so the guest renders the freshest picture
 * with zero catch-up latency. Both sides drop stale frames aggressively:
 * the host skips an encode entirely while the channel backlog isn't
 * draining, and the guest discards any frame older than the newest decoded
 * sequence number. Framing is a 16-byte binary header (magic, wrap-safe
 * sequence number, dimensions, quality tier) followed by raw JPEG bytes.
 * Encoding moved off the fast path's toDataURL/base64 detour: frames are
 * JPEG-encoded to a Blob asynchronously (OffscreenCanvas where available)
 * and transferred as a single ArrayBuffer, and the guest decodes with
 * createImageBitmap instead of Blob-URL Image elements.
 *
 * Audio: chunks are COALESCED, never dropped. The host batches ~30ms of PCM
 * into one send (instead of 60 tiny sends/s), and guests keep a bounded backlog
 * that discards the OLDEST audio when they fall behind, so a slow device hears
 * slightly compressed recent audio rather than increasingly stale garbage.
 */
(() => {
  const state = {
    role: 'idle',
    peer: null,
    host: null,
    connections: [],
    invites: new Map(), // player number -> { token, expires, consumed }
    session: null,
    assignedPlayer: 0,
    callbacks: {},
    // Video: per-seat JPEG encoders, one per guest (seat -> { canvas, ctx }).
    // Encoding is capped at VIDEO_FPS per guest and skipped entirely if the
    // previous JPEG is still in flight, so a slow link never builds a backlog.
    videoEncoders: new Map(),
    videoLastSent: 0,
    frameBusy: false,
    frameSeq: 0,          // monotonically increasing video frame sequence number
    videoDropped: 0,      // host-side frames skipped while a channel was backed up
    // Audio coalescing: the pump produces ~60 chunks/s of a few KB each; we
    // batch ~30ms worth into one message instead of dropping under load.
    audioPending: null,
    audioLastSent: 0,
    audioBusy: false,
    audioRate: 0,
    // Guest-side video health (decoded frames; windowed fps for the probe).
    videoFrames: 0,
    videoBytes: 0,
    videoFps: 0,
    videoWindowStart: 0,
    videoFramesDropped: 0,
  };

  // ~2 GBA screens' worth of raw RGBA for reference; per-seat JPEGs run 10-20KB.
  const FRAME_BYTES = 240 * 160 * 4;
  const VIDEO_FPS = 30;          // guests are phones on Wi-Fi; 30 looks fluid
  const VIDEO_MIN_INTERVAL = 1000 / VIDEO_FPS;
  const AUDIO_BATCH_MS = 30;     // coalesce window before one send
  const AUDIO_MAX_PENDING = 16384; // ~250ms of stereo s16 at 32kHz; then coalesce tail-drop;

  // ---- Raw-frame video DataChannel (v3) ----
  // Wire format: 16-byte header + raw JPEG bytes.
  //   0..3   u32 LE magic 'FRA1' (0x46524131)
  //   4..7   u32 LE sequence number (wraps; guest compares mod 2^32)
  //   8..9   u16 LE frame width
  //   10..11 u16 LE frame height
  //   12     u8 quality tier (index into VIDEO_QUALITY_STEPS)
  //   13..15 reserved (zero)
  const FRAME_MAGIC = 0x46524131; // 'FRA1'
  const FRAME_HEADER = 16;
  const VIDEO_CHANNEL_LABEL = 'mgs-video';
  // Quality ladder: drop JPEG quality (smaller messages) when the guest's
  // link shows congestion, climb back when the channel is empty.
  const VIDEO_QUALITY_STEPS = [0.55, 0.45, 0.35];
  // While more than ~64KB (≈6-8 frames at Wi-Fi rates) sits unbuffeted in the
  // SCTP send buffer, do not even START an encode: sending newer frames into
  // a backed-up unreliable channel just makes the receiver drop the older
  // ones anyway.
  const VIDEO_BACKLOG_LIMIT = 64 * 1024;
  const VIDEO_CALM_FRAMES = 12;  // consecutive empty-buffer sends before recovering quality

  function query(name) {
    try { return new URLSearchParams(window.location.search).get(name); } catch (_) { return null; }
  }

  function fragment(name) {
    try {
      const raw = window.location.hash.startsWith('#') ? window.location.hash.slice(1) : window.location.hash;
      return new URLSearchParams(raw).get(name);
    } catch (_) { return null; }
  }

  function randomToken(size = 32) {
    const bytes = new Uint8Array(size);
    crypto.getRandomValues(bytes);
    return [...bytes].map((b) => b.toString(16).padStart(2, '0')).join('');
  }

  function report(text) {
    state.callbacks.status?.(text);
  }

  function peerConstructor() {
    if (typeof window.Peer === 'function') return window.Peer;
    throw new Error('PeerJS did not load; check the network or Content-Security-Policy');
  }

  function send(conn, message) {
    try {
      if (conn && conn.open) conn.send(message);
    } catch (err) {
      console.warn('Online transport send failed:', err);
    }
  }

  function removeConnection(conn) {
    state.connections = state.connections.filter((item) => item !== conn);
    state.videoEncoders.delete(conn.__player);
    // Close the guest's video channel so the association tears down cleanly.
    if (conn.__video) { try { conn.__video.close(); } catch (_) {} conn.__video = null; }
    conn.__videoReady = false;
  }

  // ---- Per-seat JPEG video encoding ----
  // main.js hands us raw RGBA for one player (or a seat->pixels provider). We
  // push it into a per-guest offscreen canvas and JPEG-encode it: 240x160 at
  // 0.55 quality is ~8-15KB, which a DataChannel moves in a few milliseconds.
  // Encoding serializes per guest: while one encode runs we keep only the
  // newest frame — we always want the freshest picture, never a stale queue.
  // The encode is async (Blob-based, no main-thread base64 round trip) and
  // runs on OffscreenCanvas when the browser has it.
  function encoderFor(seat) {
    let enc = state.videoEncoders.get(seat);
    if (!enc) {
      let canvas = null;
      let ctx = null;
      if (typeof OffscreenCanvas !== 'undefined') {
        canvas = new OffscreenCanvas(240, 160);
        ctx = canvas.getContext('2d', { alpha: false, desynchronized: true });
      } else {
        canvas = document.createElement('canvas');
        canvas.width = 240;
        canvas.height = 160;
        ctx = canvas.getContext('2d');
      }
      enc = {
        canvas, ctx,
        busy: false,
        pending: null,
        qualityIdx: 0,    // current rung on VIDEO_QUALITY_STEPS
        calm: 0,          // consecutive empty-buffer sends (quality recovery)
      };
      state.videoEncoders.set(seat, enc);
    }
    return enc;
  }

  // Async toBlob both avoiding (a) the toDataURL base64 string + atob byte
  // loop and (b) the network round trip of passing through an ImageBitmap.
  function canvasToBlob(canvas, type, quality) {
    if (canvas.convertToBlob) return canvas.convertToBlob({ type, quality });
    return new Promise((resolve, reject) => canvas.toBlob(
      (blob) => blob ? resolve(blob) : reject(new Error('canvas.toBlob returned null')),
      type, quality));
  }

  // GBA is 240x160 RGBA (FRAME_BYTES); GB/GBC cores produce 160x144. Anything
  // else: derive a height at 240 wide rather than crash the encoder.
  function frameDims(len) {
    if (len >= FRAME_BYTES) return { w: 240, h: 160 };
    if (len === 160 * 144 * 4) return { w: 160, h: 144 };
    return { w: 240, h: Math.max(1, Math.round(len / 4 / 240)) };
  }

  function packFrame(seq, dims, qualityIdx, jpegBytes) {
    const out = new Uint8Array(FRAME_HEADER + jpegBytes.byteLength);
    const view = new DataView(out.buffer);
    view.setUint32(0, FRAME_MAGIC, true);
    view.setUint32(4, seq >>> 0, true);
    view.setUint16(8, dims.w, true);
    view.setUint16(10, dims.h, true);
    view.setUint8(12, qualityIdx);
    out.set(jpegBytes instanceof Uint8Array ? jpegBytes : new Uint8Array(jpegBytes), FRAME_HEADER);
    return out.buffer;
  }

  function adaptiveQuality(enc, dc) {
    // Recover quality only after many back-to-back empty-buffer sends; a
    // single fast send is not evidence the link has slack again.
    const backlogged = dc ? dc.bufferedAmount : 0;
    if (backlogged === 0) {
      enc.calm++;
      if (enc.calm > VIDEO_CALM_FRAMES && enc.qualityIdx > 0) {
        enc.qualityIdx--;
        enc.calm = 0;
      }
    } else {
      enc.calm = 0;
    }
  }

  function hostTransport(conn) {
    // Dedicated unreliable channel once the guest confirmed it; otherwise the
    // reliable control channel (protocol-1 guests, channel never opened).
    const dc = conn.__video;
    if (dc && conn.__videoReady && dc.readyState === 'open') return { dc, seq: true };
    return { conn, seq: false };
  }

  async function encodeAndSendFrame(conn, seat, bytes) {
    const enc = encoderFor(seat);
    if (enc.busy) {
      // An encode is running; keep only the newest frame and return.
      enc.pending = bytes;
      return;
    }
    enc.busy = true;
    try {
      const dims = frameDims(bytes.length);
      if (enc.canvas.width !== dims.w || enc.canvas.height !== dims.h) {
        enc.canvas.width = dims.w;
        enc.canvas.height = dims.h;
      }
      const imgData = enc.ctx.createImageData(dims.w, dims.h);
      imgData.data.set(bytes.length > dims.w * dims.h * 4 ? bytes.subarray(0, dims.w * dims.h * 4) : bytes);
      enc.ctx.putImageData(imgData, 0, 0);
      const jpeg = await canvasToBlob(enc.canvas, 'image/jpeg', VIDEO_QUALITY_STEPS[enc.qualityIdx]);
      const jpegBuf = await jpeg.arrayBuffer();
      const t = hostTransport(conn);
      if (t.dc) {
        // Drop-in-latest-frame on the SENDER: a full backlog means the guest
        // would discard our frame for a newer one that follows anyway. Skip
        // the send (and this frame) so the next frame starts fresh.
        if (t.dc.bufferedAmount > VIDEO_BACKLOG_LIMIT) {
          state.videoDropped++;
          enc.pending = null; // the next arriving frame will encode fresh
          return;
        }
        adaptiveQuality(enc, t.dc);
        t.dc.send(packFrame(++state.frameSeq, dims, enc.qualityIdx, jpegBuf));
      } else {
        // Legacy reliable path: PeerJS exposes its own underlying channel.
        // The same backlog guard applies (reliable channels can buffer
        // unboundedly and this was the "minutes behind" failure mode).
        const under = conn.dataChannel?.bufferedAmount;
        if (typeof under === 'number' && under > VIDEO_BACKLOG_LIMIT) {
          state.videoDropped++;
          enc.pending = null;
          return;
        }
        send(conn, { type: 'frame', seat, jpg: true, seq: ++state.frameSeq, data: jpegBuf });
      }
    } catch (err) {
      console.warn('Online video encode failed:', err);
    } finally {
      enc.busy = false;
      if (enc.pending) {
        const next = enc.pending;
        enc.pending = null;
        encodeAndSendFrame(conn, seat, next);
      }
    }
  }

  function guestCount() {
    return state.callbacks.playerCount?.() || 2;
  }

  function inviteDescriptors() {
    return [...state.invites.entries()].map(([player, invite]) => ({
      player,
      expires: invite.expires,
      consumed: invite.consumed,
      url: invite.consumed ? null : buildInvite(player),
    }));
  }

  function publishInvites() {
    state.callbacks.invites?.(inviteDescriptors());
  }

  function hostMessage(conn, message) {
    if (!message || typeof message !== 'object') return;
    if (message.type === 'hello') {
      const player = Number(message.player);
      const invite = state.invites.get(player);
      const expired = !invite || Date.now() >= invite.expires;
      // Each guest slot has its own high-entropy, time-limited capability.
      // Consuming P2's URL does not consume P3 or P4's URL.
      if (expired || invite.consumed || message.token !== invite.token) {
        send(conn, { type: 'error', message: expired ? 'This player invite has expired' : 'This player invite is no longer valid' });
        conn.close();
        return;
      }
      if (state.connections.some((item) => item.__player === player)) {
        send(conn, { type: 'error', message: `Player ${player + 1} is already connected` });
        conn.close();
        return;
      }
      invite.consumed = true;
      invite.token = null;
      conn.__player = player;
      state.connections.push(conn);
      publishInvites();
      state.callbacks.inviteUsed?.(player);
      send(conn, {
        type: 'welcome',
        session: state.session,
        player,
        players: guestCount(),
      });
      report(`Online host: Player ${player + 1} joined (${state.connections.length} guest${state.connections.length === 1 ? '' : 's'})`);
      // The authenticated connection is live: start the separate video
      // peer negotiation (offer flows to the guest over this channel).
      setupVideoPeer(conn);
      return;
    }
    if (message.type === 'video-answer') {
      hostVideoAnswer(conn, message.sdp);
      return;
    }
    if (message.type === 'video-ice') {
      hostVideoIce(conn, message.data);
      return;
    }
    if (message.type === 'input' && Number.isInteger(conn.__player)) {
      if (Number.isInteger(message.keys) && state.callbacks.input) {
        state.callbacks.input(conn.__player, message.keys >>> 0);
      }
    }
  }

  // ---- Host video broadcast: per-seat, JPEG, rate-capped ----
  // Called from main.js once per emulated frame. `source` is either a seat
  // provider ((seat) => Uint8Array RGBA, the wasm path — zero copies) or a raw
  // RGBA buffer; a buffer LONGER than one frame is the legacy concatenated
  // all-players layout (desktop socket path) and is sliced per connection.
  // Rate limit: encode at most VIDEO_FPS per guest no matter how fast the
  // emulator runs, and skip entirely while the previous encode round is
  // pending, so a slow link NEVER builds a backlog — that backlog was the
  // "minutes behind at 3-4 fps" bug (300KB raw frames × 60/s saturated the
  // reliable DataChannel and queued indefinitely).
  function broadcastFrame(source, seat) {
    if (state.role !== 'host' || !state.connections.length || state.frameBusy) return;
    state.frameBusy = true;
    const now = performance.now();
    if (now - state.videoLastSent < VIDEO_MIN_INTERVAL) {
      queueMicrotask(() => { state.frameBusy = false; });
      return;
    }
    state.videoLastSent = now;
    for (const conn of state.connections) {
      const guestSeat = conn.__player;
      if (!Number.isInteger(guestSeat)) continue;
      let bytes = null;
      if (typeof source === 'function') {
        bytes = source(guestSeat);
      } else {
        const buf = source instanceof Uint8Array ? source : new Uint8Array(source);
        if (!Number.isInteger(seat)) {
          const off = guestSeat * FRAME_BYTES;
          if (buf.length < off + 4) continue;
          bytes = buf.subarray(off);
        } else {
          bytes = buf;
        }
      }
      if (!bytes || !bytes.length) continue;
      encodeAndSendFrame(conn, guestSeat, bytes);
    }
    queueMicrotask(() => { state.frameBusy = false; });
  }

  // v3: the dedicated UNRELIABLE, UNORDERED DataChannel for raw video frames
  // lives on its OWN RTCPeerConnection, negotiated through the reliable
  // control channel (hello/welcome/input/audio stay on PeerJS untouched).
  // Inside PeerJS's managed connection we must NOT add channels: adding one
  // to an established connection renegotiates the association PeerJS relies
  // on, and both A/B attempts (host-created post-open, guest-created
  // pre-offer) wedged one direction of the control channel in turn. With the
  // separate peer connection there is no renegotiation of anything PeerJS
  // manages: control and video fail independently. Unordered + zero
  // retransmits is the point: a lost or stale packet is never retransmitted,
  // so the guest always renders the freshest frame, and the host skips
  // sends while the backlog is high instead of queueing. The video peer is
  // best-effort: if its negotiation fails the host keeps sending per-seat
  // frames over the reliable channel (protocol-1-compatible fallback).
  const VIDEO_ICE = [{ urls: 'stun:stun.l.google.com:19302' }];

  function setupVideoPeer(conn) {
    try {
      if (conn.__video) return;
      const pc = new RTCPeerConnection({ iceServers: VIDEO_ICE });
      const dc = pc.createDataChannel(VIDEO_CHANNEL_LABEL, { ordered: false, maxRetransmits: 0 });
      dc.binaryType = 'arraybuffer';
      conn.__videoPc = pc;
      conn.__video = dc;
      conn.__videoIcePending = [];
      dc.onopen = () => { conn.__videoReady = true; };
      dc.onclose = () => { if (conn.__video === dc) conn.__video = null; };
      pc.onicecandidate = (event) => {
        if (event.candidate) send(conn, { type: 'video-ice', data: JSON.stringify(event.candidate) });
      };
      pc.onconnectionstatechange = () => {
        if (pc.connectionState === 'failed' && conn.__video === dc) conn.__video = null;
      };
      pc.createOffer()
        .then((offer) => pc.setLocalDescription(offer))
        .then(() => send(conn, { type: 'video-offer', sdp: pc.localDescription.sdp }))
        .catch((err) => console.warn('Online host video negotiation failed:', err));
    } catch (err) {
      console.warn('Online host video peer unavailable:', err);
    }
  }

  function hostVideoAnswer(conn, sdp) {
    const pc = conn.__videoPc;
    if (!pc || !sdp) return;
    pc.setRemoteDescription({ type: 'answer', sdp })
      .then(() => {
        for (const cand of conn.__videoIcePending.splice(0)) {
          pc.addIceCandidate(cand).catch((err) => console.warn('Late video ICE rejected:', err));
        }
      })
      .catch((err) => console.warn('Online host video answer failed:', err));
  }

  function hostVideoIce(conn, raw) {
    try {
      const cand = JSON.parse(raw);
      const pc = conn.__videoPc;
      if (!pc) return;
      if (!pc.remoteDescription) {
        conn.__videoIcePending.push(cand);
        return;
      }
      pc.addIceCandidate(cand).catch((err) => console.warn('Video ICE rejected:', err));
    } catch (_) { /* malformed trickle; the channel can still come up */ }
  }

  function setupHostConnection(conn) {
    conn.on('open', () => report('Online host: guest connected; authenticating…'));
    conn.on('data', (message) => hostMessage(conn, message));
    conn.on('close', () => {
      removeConnection(conn);
      report(`Online host: ${state.connections.length} guest${state.connections.length === 1 ? '' : 's'} connected`);
    });
    conn.on('error', () => removeConnection(conn));
  }

  function guestMessage(message) {
    if (!message || typeof message !== 'object') return;
    if (message.type === 'welcome') {
      state.assignedPlayer = message.player;
      // Guests render exactly ONE screen (their own seat). The host's `players`
      // count describes its local grid; `seat` tells the guest which slice of
      // the old concatenated format it used to receive — with per-seat JPEG
      // frames the guest just plays what arrives.
      state.callbacks.playerCount?.(1);
      state.callbacks.guestSeat?.(message.player);
      report(`Online guest: connected as Player ${message.player + 1}`);
    } else if (message.type === 'frame' && message.data) {
      // Legacy fallback path (channel not confirmed; protocol-1 semantics):
      // the reliable channel's frames decode the same way, tagged with the
      // sequence the host attached (ordering is guaranteed there, so a
      // seq-less protocol-1 host simply never stale-drops).
      const bytes = message.data instanceof ArrayBuffer
        ? new Uint8Array(message.data)
        : new Uint8Array(message.data.buffer || message.data);
      decodeGuestVideoLegacy(bytes, Number(message.seq));
    } else if (message.type === 'audio' && message.data) {
      // Tagged audio chunk (u32 LE rate + interleaved stereo s16), same format
      // the desktop WebSocket streams. Guests play it through the same
      // resampler the local browser path uses.
      const bytes = message.data instanceof ArrayBuffer
        ? new Uint8Array(message.data)
        : new Uint8Array(message.data.buffer || message.data);
      state.callbacks.audio?.(bytes);
    } else if (message.type === 'video-offer') {
      setupGuestVideoPeer(message.sdp);
    } else if (message.type === 'video-ice') {
      guestVideoIce(message.data);
    } else if (message.type === 'error') {
      report(`Online guest: ${message.message || 'host rejected the connection'}`);
    }
  }

  // The guest's own RTCPeerConnection for the dedicated video channel —
  // separate from PeerJS's managed peer connection on purpose (see the
  // comment on setupVideoPeer for why).
  let guestVideoPc = null;
  let guestVideoIcePending = [];

  function setupGuestVideoPeer(sdp) {
    try {
      if (!sdp) return;
      if (guestVideoPc) { try { guestVideoPc.close(); } catch (_) {} guestVideoPc = null; }
      const pc = new RTCPeerConnection({ iceServers: VIDEO_ICE });
      guestVideoPc = pc;
      pc.ondatachannel = (event) => {
        if (event.channel && event.channel.label === VIDEO_CHANNEL_LABEL) guestVideoChannel(event.channel);
      };
      pc.onicecandidate = (event) => {
        if (event.candidate) send(state.host, { type: 'video-ice', data: JSON.stringify(event.candidate) });
      };
      guestVideoIcePending = [];
      pc.setRemoteDescription({ type: 'offer', sdp })
        .then(() => {
          for (const cand of guestVideoIcePending.splice(0)) {
            pc.addIceCandidate(cand).catch((err) => console.warn('Late video ICE rejected:', err));
          }
          return pc.createAnswer();
        })
        .then((answer) => pc.setLocalDescription(answer))
        .then(() => send(state.host, { type: 'video-answer', sdp: pc.localDescription.sdp }))
        .catch((err) => console.warn('Online guest video negotiation failed:', err));
    } catch (err) {
      console.warn('Online guest video peer unavailable:', err);
    }
  }

  function guestVideoIce(raw) {
    try {
      const cand = JSON.parse(raw);
      if (!guestVideoPc) { guestVideoIcePending.push(cand); return; }
      if (!guestVideoPc.remoteDescription) { guestVideoIcePending.push(cand); return; }
      guestVideoPc.addIceCandidate(cand).catch(() => {});
    } catch (_) { /* malformed trickle; the channel can still come up */ }
  }

  // v3 guest video: frames arrive on the dedicated unreliable data channel as
  // raw binary (16-byte header + JPEG). Unreliable/unordered transport means
  // EVERY packet's delay is unrecoverable by design — the freshest frame is
  // always right behind a stale one — so the decoder keeps only ONE pending
  // slot and overwrites it with any newer sequence number that arrives. A
  // frame is decoded strictly in newest-first order; anything out of order or
  // older than the last DELIVERED frame is dropped without work.
  const guestDecoder = {
    busy: false,
    pending: null,           // { seq, w, h, payload } still undecoded
    deliveredSeq: 0,         // newest blitted frame; never dropped older than this
  };

  // True unless seq is "older" than ref on the 2^32 wraparound ring.
  function seqIsNewer(seq, ref) {
    const d = (seq - ref) >>> 0;
    return d !== 0 && d < 0x80000000;
  }

  function imageDecode(job) {
    return new Promise((resolve, reject) => {
      const url = URL.createObjectURL(new Blob([job.payload], { type: 'image/jpeg' }));
      const img = new Image();
      img.onload = () => { URL.revokeObjectURL(url); resolve(img); };
      img.onerror = () => { URL.revokeObjectURL(url); reject(new Error('Image decode failed')); };
      img.src = url;
    });
  }

  function guestVideoChannel(channel) {
    channel.binaryType = 'arraybuffer';
    channel.onmessage = (event) => {
      const data = event.data;
      if (data instanceof ArrayBuffer) {
        guestVideoMessage(new Uint8Array(data));
      } else if (ArrayBuffer.isView(data)) {
        guestVideoMessage(new Uint8Array(data.buffer, data.byteOffset, data.byteLength));
      }
    };
  }

  function guestVideoMessage(bytes) {
    if (bytes.length < FRAME_HEADER) return;
    const view = new DataView(bytes.buffer, bytes.byteOffset, FRAME_HEADER);
    if (view.getUint32(0, true) !== FRAME_MAGIC) return;
    const seq = view.getUint32(4, true);
    const w = view.getUint16(8, true);
    const h = view.getUint16(10, true);
    const payload = bytes.subarray(FRAME_HEADER);
    if (payload.length === 0) return;
    guestVideoJob({ seq, w, h, payload });
  }

  // Legacy reliable-path frames become the same decoded job, tagged with the
  // sequence carried in the message (absent for protocol-1 hosts -> never
  // stale-drop, ordering is already guaranteed on the reliable channel).
  function decodeGuestVideoLegacy(jpegBytes, seq) {
    if (!jpegBytes.length) return;
    const dims = frameDims(jpegBytes.length);
    guestVideoJob({
      seq: Number.isInteger(seq) ? seq >>> 0 : 0,
      w: dims.w, h: dims.h,
      payload: jpegBytes,
    });
  }

  function guestVideoJob(job) {
    // Drop-old-frames: an unordered channel can deliver a stale frame after
    // a fresh one. The seq != 0 guard makes protocol-1 (seq-less) frames
    // alwaysDecode; deliveredSeq == 0 means no frame decoded yet.
    if (job.seq !== 0 && guestDecoder.deliveredSeq !== 0 &&
        !seqIsNewer(job.seq, guestDecoder.deliveredSeq)) {
      state.videoFramesDropped++;
      return;
    }
    // A decode may be in flight; keep ONLY the newest pending frame.
    if (guestDecoder.pending &&
        !seqIsNewer(job.seq, guestDecoder.pending.seq)) {
      state.videoFramesDropped++;
      return;
    }
    guestDecoder.pending = job;
    if (!guestDecoder.busy) decodeGuestVideo();
  }

  async function decodeGuestVideo() {
    if (guestDecoder.busy) return;
    guestDecoder.busy = true;
    try {
      let job = guestDecoder.pending;
      while (job) {
        guestDecoder.pending = null;
        // decodeBitmap is createImageBitmap where available (async, GPU-
        // friendly, no DOM image element); older browsers fall back to the
        // object-URL Image path this used to use exclusively.
        const bmp = await (typeof createImageBitmap === 'function'
          ? createImageBitmap(new Blob([job.payload], { type: 'image/jpeg' }))
          : imageDecode(job));
        guestDecoder.deliveredSeq = job.seq || guestDecoder.deliveredSeq;
        // Windowed fps for the videoStats() probe: cheap and self-resetting.
        const now = performance.now();
        if (!state.videoWindowStart || now - state.videoWindowStart >= 1000) {
          state.videoWindowStart = now;
          state.videoFps = 0;
        }
        state.videoFrames++;
        state.videoBytes += job.payload.length;
        state.videoFps++;
        state.callbacks.frame?.({ jpeg: bmp, width: job.w, height: job.h });
        // The receiver holds the newest bitmap only: if a newer frame landed
        // while this decode ran, discard our bitmap and decode ahead.
        const next = guestDecoder.pending;
        if (next) { bmp.close?.(); job = next; continue; }
        job = null;
        // Bitmap stays alive for main.js's next rAF blit (it closes it after
        // drawing — ImageBitmaps hold GPU memory).
        break;
      }
    } catch (err) {
      console.warn('Online guest video decode failed:', err);
    } finally {
      guestDecoder.busy = false;
      if (guestDecoder.pending) decodeGuestVideo();
    }
  }

  function setupGuestConnection(conn) {
    state.host = conn;
    conn.on('open', () => {
      send(conn, {
        type: 'hello',
        token: fragment('token') || query('token'),
        player: Number(fragment('player') || query('player')),
        protocol: 2,
      });
      report('Online guest: connecting to host…');
    });
    conn.on('data', guestMessage);
    conn.on('close', () => report('Online guest: host disconnected'));
    conn.on('error', (err) => report(`Online guest: ${err.message || 'connection failed'}`));
  }

  function buildInvite(player) {
    const invite = state.invites.get(player);
    if (!invite || invite.consumed) return null;
    const url = new URL(window.location.href);
    url.search = '';
    url.hash = '';
    url.searchParams.set('online', 'join');
    url.searchParams.set('peer', state.peer.id);
    url.searchParams.set('player', String(player));
    url.searchParams.set('players', String(guestCount()));
    const rom = query('rom');
    if (rom) url.searchParams.set('rom', rom);
    // Keep bearer data in the fragment: browsers do not send it in referrers.
    url.hash = new URLSearchParams({
      session: state.session,
      token: invite.token,
      expires: String(invite.expires),
      player: String(player),
    }).toString();
    return url.href;
  }

  function createInvites() {
    state.invites = new Map();
    const expires = Date.now() + 10 * 60 * 1000;
    for (let player = 1; player < guestCount(); player++) {
      state.invites.set(player, { token: randomToken(), expires, consumed: false });
    }
  }

  async function startHost() {
    const needsFresh = state.role === 'host' && [...state.invites.values()].every((invite) =>
      invite.consumed || Date.now() >= invite.expires);
    if (state.role === 'host' && needsFresh) {
      state.session = randomToken(8);
      createInvites();
      publishInvites();
      report('Online host: issued fresh invites for all guest slots');
      return buildInvite(1);
    }
    if (state.role !== 'idle') return buildInvite(1);
    try {
      const Peer = peerConstructor();
      state.role = 'host';
      state.session = randomToken(8);
      createInvites();
      state.peer = new Peer();
      await new Promise((resolve, reject) => {
        const timer = setTimeout(() => reject(new Error('PeerJS broker timeout')), 10000);
        state.peer.on('open', () => { clearTimeout(timer); resolve(); });
        state.peer.on('error', (err) => { clearTimeout(timer); reject(err); });
      });
      state.peer.on('connection', setupHostConnection);
      publishInvites();
      report('Online host ready — one invite is available for each guest slot');
      return buildInvite(1);
    } catch (err) {
      state.role = 'idle';
      state.invites.clear();
      report(`Online unavailable: ${err.message || err}`);
      return null;
    }
  }

  async function startGuest() {
    if (state.role !== 'idle') return;
    const peerId = query('peer');
    const token = fragment('token') || query('token');
    const player = Number(fragment('player') || query('player'));
    const expires = Number(query('expires') || fragment('expires') || 0);
    const session = fragment('session') || query('session');
    if (!peerId || !token || !session || !Number.isInteger(player) || player < 1 || !expires || Date.now() >= expires) {
      report('Online invite is missing, expired, or invalid');
      return;
    }
    try {
      const Peer = peerConstructor();
      state.role = 'guest';
      state.peer = new Peer();
      await new Promise((resolve, reject) => {
        const timer = setTimeout(() => reject(new Error('PeerJS broker timeout')), 10000);
        state.peer.on('open', () => { clearTimeout(timer); resolve(); });
        state.peer.on('error', (err) => { clearTimeout(timer); reject(err); });
      });
      const conn = state.peer.connect(peerId, { reliable: true });
      state.host = conn;
      // setupGuestConnection owns the hello + control wiring; its open
      // handler reads the same URL values validated above, so no second
      // hello here (two hellos would trip the host's already-connected
      // rejection and close the connection). Reuse the SAME connection —
      // connecting twice would open a parallel session and split the wire.
      setupGuestConnection(conn);
    } catch (err) {
      state.role = 'idle';
      report(`Online unavailable: ${err.message || err}`);
    }
  }

  function sendInput(player, keys) {
    if (state.role !== 'guest') return false;
    send(state.host, { type: 'input', player, keys: keys >>> 0, t: performance.now() });
    return true;
  }

  // Host -> guest audio: coalesce, never drop. The pump delivers ~60 tagged
  // chunks/s (u32 LE rate + interleaved stereo s16). Small chunks are batched
  // into ~30ms sends: per-message overhead drops, and latency is bounded to
  // one batch window. The previous behavior DROPPED whole chunks whenever a
  // send was in flight — periodic sample gaps the guest hears as crackle.
  // The merge strips every per-chunk rate header and emits ONE tagged payload:
  // concatenating raw chunks would deliver header bytes as audio samples.
  function broadcastAudio(bytes) {
    if (state.role !== 'host' || !state.connections.length) return;
    const chunk = bytes instanceof Uint8Array ? bytes : new Uint8Array(bytes);
    if (chunk.length < 5) return;
    const rate = new DataView(chunk.buffer, chunk.byteOffset, chunk.byteLength).getUint32(0, true);
    const samples = chunk.subarray(4);
    // Rate change (SOUNDBIAS switch): flush the old-rate batch first so the
    // guest's resampler never sees mixed-rate samples in one payload.
    if (state.audioPending && state.audioPending.length && rate !== state.audioRate) flushAudio();
    state.audioRate = rate;
    if (!state.audioPending) state.audioPending = [];
    state.audioPending.push(samples);
    let pending = 0;
    for (const c of state.audioPending) pending += c.length;
    // Overflow guard: if sends stall longer than the window allows, coalesce
    // away the OLDEST samples (head drop) rather than grow unbounded.
    while (pending > AUDIO_MAX_PENDING && state.audioPending.length > 1) {
      const dropped = state.audioPending.shift();
      pending -= dropped.length;
    }
    const now = performance.now();
    if (now - state.audioLastSent < AUDIO_BATCH_MS || state.audioBusy) return;
    flushAudio();
  }

  function flushAudio() {
    if (!state.audioPending || !state.audioPending.length || state.audioBusy) return;
    state.audioLastSent = performance.now();
    state.audioBusy = true;
    let total = 4;
    for (const c of state.audioPending) total += c.length;
    const merged = new Uint8Array(total);
    new DataView(merged.buffer).setUint32(0, state.audioRate, true);
    let off = 4;
    for (const c of state.audioPending) { merged.set(c, off); off += c.length; }
    state.audioPending = [];
    for (const conn of state.connections) send(conn, { type: 'audio', data: merged.buffer });
    queueMicrotask(() => { state.audioBusy = false; });
  }

  function init(callbacks) {
    state.callbacks = callbacks || {};
    if (query('online') === 'join') startGuest();
  }

  window.mgbaOnline = {
    init,
    startHost,
    sendInput,
    broadcastFrame,
    broadcastAudio,
    isGuest: () => state.role === 'guest',
    isHost: () => state.role === 'host',
    // Read-only introspection for the crash reporter's session details.
    assignedPlayer: () => state.assignedPlayer,
    guestCount: () => state.connections.length,
    invite: () => buildInvite(1),
    // Guest AV health probe (crash reporter / manual debugging).
    videoStats: () => ({
      frames: state.videoFrames,
      bytes: state.videoBytes,
      fps: state.videoFps,
      dropped: state.videoFramesDropped,
    }),
    // Host probe: how each connected guest's video is transported
    // (true = dedicated unreliable v3 channel confirmed; false = legacy
    // reliable control-channel frames).
    videoChannels: () => state.connections.map((conn) => ({
      unreliable: !!(conn.__video && conn.__videoReady),
    })),
  };
})();
