/* Touchscreen controls overlay (GBA-style pad for phones and tablets).
 *
 * Why: a guest opening a magic link on their phone has no keyboard or
 * gamepad — without this they can watch but never play. The overlay is a
 * transparent layer with a D-pad, A/B, L/R shoulders, START/SELECT, and a
 * small pause button; it feeds the SAME per-player key-mask pipeline the
 * keyboard and gamepads use (main.js merges `mgbaTouch.maskFor(p)` into
 * sendKeys), so host/local play and guest input forwarding both work
 * unchanged.
 *
 * Multi-touch: every pointer is tracked independently (press A while holding
 * a direction), and the D-pad supports sliding between directions without
 * lifting the thumb — the natural way people play GBA games.
 *
 * Visibility modes (persisted): 'auto' (default) shows on the first real
 * touch and when a magic-link guest connects; 'on'/'off' force it. Desktops
 * never see it in auto mode.
 */
(() => {
  // Must match GBA_BUTTONS in main.js (mGBA's key mask layout).
  const BUTTON_BITS = {
    A: 1 << 0, B: 1 << 1, SELECT: 1 << 2, START: 1 << 3,
    RIGHT: 1 << 4, LEFT: 1 << 5, UP: 1 << 6, DOWN: 1 << 7,
    R: 1 << 8, L: 1 << 9,
  };

  const MODE_KEY = 'mgba-splitscreen_touch_v1';
  /* Custom layouts: per-ROM (or 'default') map of data-btn ->
   * { x, y, s } — x/y are percentage coordinates of the pad area (0-100,
   * centered on the button), s is a scale factor applied on top of the CSS
   * size. Edit mode (the pencil chip) lets a thumb drag buttons anywhere and
   * tap them to cycle 0.75x / 1x / 1.4x / 2x. Reason: different games want
   * different pads — e.g. Mario Kart Super Circuit is mostly LEFT/RIGHT, so
   * enlarging those two helps enormously without touching other games. */
  const LAYOUT_KEY = 'mgba-splitscreen_touch_layout_v1';
  const SIZE_STEPS = [0.75, 1, 1.4, 2];
  const MAX_PLAYERS = 4;

  const state = {
    root: null,
    note: null,
    picker: null,
    callbacks: {},
    masks: new Array(MAX_PLAYERS).fill(0),
    activePlayer: 0,
    playerCount: 2,
    pointers: new Map(), // pointerId -> button name currently held
    mode: 'auto',        // 'auto' | 'on' | 'off'
    touchSeen: false,    // a real touch input happened at least once
    guestSeat: null,     // set when the magic-link guest is welcomed
    forced: false,       // controller-only guest: pad always on
    awaitingGuest: false, // ?online=join seen but welcome not yet received
    editMode: false,     // layout editor active
    edits: {},           // currently applied layout map (per-ROM profile)
    romName: 'default',  // profile key; set by main.js when a ROM loads
    dragPid: null,       // pointerId captured during a drag
    dragBtn: null,
    dragMoved: false,
  };

  function loadMode() {
    try {
      const raw = localStorage.getItem(MODE_KEY);
      if (raw === 'on' || raw === 'off' || raw === 'auto') state.mode = raw;
    } catch (_) {}
  }

  function saveMode() {
    try { localStorage.setItem(MODE_KEY, state.mode); } catch (_) {}
  }

  function query(name) {
    try { return new URLSearchParams(window.location.search).get(name); } catch (_) { return null; }
  }

  function shouldShow() {
    if (state.forced) return true;
    if (state.mode === 'on') return true;
    if (state.mode === 'off') return false;
    return state.touchSeen || state.guestSeat !== null
      || (state.awaitingGuest && state.touchSeen);
  }

  function updateVisibility() {
    if (!state.root) return;
    state.root.hidden = !shouldShow();
  }

  function updatePicker() {
    if (!state.picker) return;
    if (state.guestSeat !== null) {
      // Guests drive exactly one seat; the picker is meaningless to them.
      state.picker.hidden = true;
      if (state.note) state.note.textContent = `You are Player ${state.guestSeat + 1}`;
      return;
    }
    state.picker.hidden = state.playerCount <= 1;
    state.picker.querySelectorAll('button').forEach((btn) => {
      const p = parseInt(btn.dataset.player, 10);
      btn.classList.toggle('active', p === state.activePlayer);
      btn.style.display = p < state.playerCount ? '' : 'none';
    });
    if (state.note) state.note.textContent = '';
  }

  function sendMask() {
    // Route through main.js's union sender so keyboard/gamepad masks survive.
    state.callbacks.onInput?.(state.activePlayer);
  }

  function pressedVisual(btn, on) {
    const el = state.root && state.root.querySelector(`[data-btn="${btn}"]`);
    if (el) el.classList.toggle('pressed', on);
  }

  function press(btn) {
    const bit = BUTTON_BITS[btn];
    if (!bit || (state.masks[state.activePlayer] & bit)) return;
    // Guests must not inject input before the host assigns their seat —
    // seat 0 is Player 1 on the host, and an unassigned guest is nobody.
    if (state.awaitingGuest && state.guestSeat === null) return;
    state.masks[state.activePlayer] |= bit;
    pressedVisual(btn, true);
    try { navigator.vibrate && navigator.vibrate(8); } catch (_) {}
    sendMask();
  }

  function release(btn) {
    const bit = BUTTON_BITS[btn];
    if (!bit || !(state.masks[state.activePlayer] & bit)) { pressedVisual(btn, false); return; }
    state.masks[state.activePlayer] &= ~bit;
    pressedVisual(btn, false);
    sendMask();
  }

  function buttonAt(x, y) {
    const el = document.elementFromPoint(x, y);
    return el && el.closest ? el.closest('[data-btn]') : null;
  }

  // ---- Layout editor: drag to place, tap to cycle size, per-ROM persisted ----
  function layoutPath() {
    try { return JSON.parse(localStorage.getItem(LAYOUT_KEY) || '{}'); } catch (_) { return {}; }
  }

  function saveLayout(all) {
    try { localStorage.setItem(LAYOUT_KEY, JSON.stringify(all)); } catch (_) {}
  }

  function applyLayout() {
    if (!state.root) return;
    for (const el of state.root.querySelectorAll('.touch-btn')) {
      const name = el.dataset.btn;
      const conf = name ? state.edits[name] : null;
      if (conf) {
        el.classList.add('touch-custom');
        el.style.left = conf.x + '%';
        el.style.top = conf.y + '%';
        el.style.transform = `translate(-50%, -50%) scale(${conf.s || 1})`;
      } else {
        el.classList.remove('touch-custom');
        el.style.left = el.style.top = el.style.transform = '';
      }
    }
  }

  function toggleEditMode() {
    if (!state.root) return;
    state.editMode = !state.editMode;
    state.root.classList.toggle('editing', state.editMode);
    const chip = document.getElementById('touch-edit');
    if (chip) {
      chip.setAttribute('aria-pressed', String(state.editMode));
      chip.classList.toggle('active', state.editMode);
    }
    if (state.editMode) {
      state.edits = layoutPath()[state.romName] || {};
      applyLayout();
      state.callbacks.onStatus?.(`Touch layout editing (for ${state.romName}); drag a button, tap to resize, or tap Done`);
    } else {
      applyLayout();
      state.callbacks.onStatus?.('Touch layout editing done');
    }
  }

  function clampPct(v) { return Math.max(4, Math.min(96, v)); }

  function editPointerDown(e, el) {
    state.dragPid = e.pointerId;
    state.dragBtn = el.dataset.btn;
    state.dragMoved = false;
    try { state.root.setPointerCapture(e.pointerId); } catch (_) {}
  }

  function editPointerMove(e) {
    if (e.pointerId !== state.dragPid || !state.dragBtn) return;
    e.preventDefault();
    const rect = state.root.getBoundingClientRect();
    const conf = state.edits[state.dragBtn] || (state.edits[state.dragBtn] = { x: 50, y: 50, s: 1 });
    conf.x = clampPct(((e.clientX - rect.left) / rect.width) * 100);
    conf.y = clampPct(((e.clientY - rect.top) / rect.height) * 100);
    state.dragMoved = true;
    applyOne(state.dragBtn);
  }

  function editPointerUp(e) {
    if (e.pointerId !== state.dragPid) return;
    const btn = state.dragBtn;
    state.dragPid = null;
    if (!btn) return;
    if (!state.dragMoved) {
      // A tap (no drag) cycles the button's size.
      const conf = state.edits[btn] || (state.edits[btn] = { x: 50, y: 50, s: 1 });
      const cur = SIZE_STEPS.indexOf(conf.s || 1);
      conf.s = SIZE_STEPS[(cur + 1 + SIZE_STEPS.length) % SIZE_STEPS.length] ?? SIZE_STEPS[0];
      applyOne(btn);
    }
    try {
      const all = layoutPath();
      all[state.romName] = state.edits;
      saveLayout(all);
    } catch (_) {}
    state.dragBtn = null;
  }

  function applyOne(name) {
    const el = state.root.querySelector(`[data-btn="${name}"]`);
    const conf = state.edits[name];
    if (!el || !conf) return;
    el.classList.add('touch-custom');
    el.style.left = conf.x + '%';
    el.style.top = conf.y + '%';
    el.style.transform = `translate(-50%, -50%) scale(${conf.s || 1})`;
  }

  function onPointerDown(e) {
    if (!state.root || state.root.hidden) return;
    if (state.editMode) {
      const target = e.target.closest ? e.target.closest('[data-btn]') : null;
      if (target) {
        e.preventDefault();
        editPointerDown(e, target);
      }
      return; // no gameplay input while editing
    }
    const target = e.target.closest ? e.target.closest('[data-btn]') : null;
    if (!target) return;
    e.preventDefault();
    try { state.root.setPointerCapture(e.pointerId); } catch (_) {}
    state.pointers.set(e.pointerId, target.dataset.btn);
    press(target.dataset.btn);
  }

  function onPointerMove(e) {
    if (state.editMode) { editPointerMove(e); return; }
    if (!state.pointers.has(e.pointerId)) return;
    e.preventDefault();
    const hit = buttonAt(e.clientX, e.clientY);
    const btn = hit ? hit.dataset.btn : null;
    const current = state.pointers.get(e.pointerId);
    if (btn === current) return;
    // Slide support: release the old button, press the new one under the
    // finger (D-pad rolls between directions; lifting off releases all).
    if (current) release(current);
    if (btn) press(btn);
    state.pointers.set(e.pointerId, btn);
  }

  function onPointerUp(e) {
    if (state.editMode) { editPointerUp(e); return; }
    if (!state.pointers.has(e.pointerId)) return;
    e.preventDefault();
    const btn = state.pointers.get(e.pointerId);
    state.pointers.delete(e.pointerId);
    if (btn) release(btn);
  }

  function bindEvents() {
    state.root.addEventListener('pointerdown', onPointerDown);
    state.root.addEventListener('pointermove', onPointerMove);
    state.root.addEventListener('pointerup', onPointerUp);
    state.root.addEventListener('pointercancel', onPointerUp);
    // A long-press must never open the text-selection/callout UI mid-game.
    state.root.addEventListener('contextmenu', (e) => e.preventDefault());
    // Pause button (tiny, top-center): same hotkey path as the menubar.
    const pauseBtn = state.root.querySelector('[data-action="pause"]');
    if (pauseBtn) {
      pauseBtn.addEventListener('pointerdown', (e) => e.preventDefault());
      pauseBtn.addEventListener('click', () => state.callbacks.onPause?.());
    }
    const editBtn = document.getElementById('touch-edit');
    if (editBtn) {
      editBtn.addEventListener('pointerdown', (e) => e.preventDefault());
      editBtn.addEventListener('click', toggleEditMode);
    }
    if (state.picker) {
      state.picker.addEventListener('click', (e) => {
        const btn = e.target.closest('button[data-player]');
        if (!btn) return;
        const p = parseInt(btn.dataset.player, 10);
        if (p >= 0 && p < state.playerCount && p !== state.activePlayer) {
          // Don't let a held button stick on the old player.
          for (const [id, b] of state.pointers) { if (b) release(b); }
          state.masks.fill(0);
          state.activePlayer = p;
          updatePicker();
          sendMask();
        }
      });
    }
    // Auto-show on the first REAL touch (desktop mice never trigger this).
    window.addEventListener('pointerdown', (e) => {
      if (e.pointerType === 'touch' || e.pointerType === 'pen') {
        if (!state.touchSeen) {
          state.touchSeen = true;
          updateVisibility();
        }
      }
    }, { capture: true, passive: true });
  }

  function setModeLabel() {
    const btn = document.getElementById('toggle-touch');
    if (btn) {
      const label = state.mode === 'auto' ? 'Auto' : state.mode === 'on' ? 'On' : 'Off';
      btn.textContent = `Touch Controls: ${label}`;
      btn.classList.toggle('active', state.mode !== 'off');
    }
  }

  window.mgbaTouch = {
    init(callbacks) {
      state.callbacks = callbacks || {};
      state.root = document.getElementById('touch-controls');
      state.note = document.getElementById('touch-note');
      state.picker = document.getElementById('touch-player-picker');
      if (!state.root) return;
      loadMode();
      state.awaitingGuest = query('online') === 'join';
      // Build the P1-P4 picker once (local play only; guests never see it).
      if (state.picker && !state.picker.children.length) {
        for (let p = 0; p < MAX_PLAYERS; p++) {
          const b = document.createElement('button');
          b.type = 'button';
          b.dataset.player = String(p);
          b.textContent = `P${p + 1}`;
          state.picker.appendChild(b);
        }
      }
      try { state.edits = layoutPath()[state.romName] || {}; } catch (_) { state.edits = {}; }
      applyLayout();
      bindEvents();
      setModeLabel();
      updatePicker();
      updateVisibility();
    },
    // main.js calls this when the player count changes (screens rebuilt).
    setPlayerCount(count) {
      const n = Math.max(1, Math.min(MAX_PLAYERS, count | 0));
      if (n === state.playerCount) return;
      state.playerCount = n;
      state.masks.fill(0);
      // Never clamp an assigned guest down to the local count: guests build a
      // 1-screen view but drive a seat the host picked (0..3). Only local
      // players follow the local grid size.
      if (state.guestSeat === null) {
        state.activePlayer = Math.min(state.activePlayer, n - 1);
      }
      updatePicker();
    },
    // main.js calls this when an online session role resolves:
    // seat = 0-based guest slot, or null for hosts/local play.
    setGuest(seat) {
      state.guestSeat = (Number.isInteger(seat) && seat >= 0) ? seat : null;
      if (state.guestSeat !== null) {
        state.activePlayer = state.guestSeat;
        state.masks.fill(0);
      }
      updatePicker();
      updateVisibility(); // magic-link arrival (or host fallback) re-evaluates
    },
    // Controller-only guests (phone-as-gamepad) always show the pad: that is
    // the whole point of their session. Does not change the persisted mode.
    forceOn() {
      state.forced = true;
      updateVisibility();
    },
    cycleMode() {
      state.mode = state.mode === 'auto' ? 'on' : state.mode === 'on' ? 'off' : 'auto';
      saveMode();
      setModeLabel();
      updateVisibility();
      state.callbacks.onStatus?.(
        state.mode === 'auto' ? 'Touch controls: auto (shows on touch devices and guests)'
          : state.mode === 'on' ? 'Touch controls: always shown'
          : 'Touch controls: hidden');
    },
    // main.js calls this once a ROM is running so per-game layouts switch
    // automatically (e.g. bigger LEFT/RIGHT for Mario Kart Super Circuit).
    setRom(name) {
      const next = name || 'default';
      if (state.romName === next) return;
      state.romName = next;
      try { state.edits = layoutPath()[next] || {}; } catch (_) { state.edits = {}; }
      if (state.editMode) toggleEditMode(); // leave edit mode on a game switch
      applyLayout();
    },
    maskFor(player) {
      return state.masks[player] || 0;
    },
    releaseAll() {
      state.masks.fill(0);
      state.pointers.clear();
      if (!state.root) return;
      state.root.querySelectorAll('.touch-btn.pressed').forEach((el) => el.classList.remove('pressed'));
    },
  };
})();
