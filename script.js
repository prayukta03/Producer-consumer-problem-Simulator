'use strict';
/* =====================================================================
   AIRPORT BAGGAGE FLOW — Producer–Consumer Operating Systems simulator

   PART 1  Simulation engine  (pure logic, no DOM, one source of truth)
   PART 2  User interface     (renders ONLY from the engine state)

   Mapping to the OS concepts
   - Producer  = check-in & security      (inserts bags into the buffer)
   - Buffer    = baggage conveyor         (bounded buffer, FIFO)
   - Consumer  = sorting & loading        (removes bags, sorts them)
   - Mutex     = lock on the critical section "remove a bag from the buffer"
   - Semaphores: empty = free slots, full = filled slots
   - Race      = with synchronization OFF, two consumers read the same
                 bag at the same time, so the bag is corrupted and lost.
   ===================================================================== */

/* ---------------------------------------------------------------------
   PART 1 — ENGINE
   --------------------------------------------------------------------- */

const TICK_MS = 50;            // simulated time advanced per engine step
const ACCESS_MS = 600;         // critical section: taking a bag off the conveyor
const PRODUCE_MS = 700;        // time to tag and scan a bag at check-in
const HOLD_MS = 400;           // consumer shows "COMPLETED" for a moment
const CONFLICT_MS = 1600;      // how long a race conflict stays visible
const WAKE_MIN = 100;          // reaction time of a consumer that was waiting
const WAKE_MAX = 1500;
const IDLE_REACT_MAX = 300;    // reaction time of an idle consumer
const HISTORY_MAX = 8;
const LOG_MAX = 120;
const RUSH_MS = 20000;         // length of a Flight Rush (simulated time)
const RUSH_FACTOR = 3;         // check-in rate multiplier during a rush

const FLIGHTS = [
  { code: 'AI-201', dest: 'DELHI',     gate: 'A12' },
  { code: '6E-512', dest: 'MUMBAI',    gate: 'B07' },
  { code: 'UK-833', dest: 'BENGALURU', gate: 'C03' },
  { code: 'SG-114', dest: 'KOLKATA',   gate: 'A05' },
  { code: 'AI-657', dest: 'HYDERABAD', gate: 'B11' }
];

const prodInterval = s => Math.round(6000 / s);   // ms between bags at speed s
const consTime = s => Math.round(12000 / s);      // ms to sort a bag at speed s
const speedLabel = v => (v <= 2 ? 'Slow' : v <= 5 ? 'Medium' : v <= 8 ? 'Fast' : 'Very Fast');
const pretty = s => String(s).replace(/_/g, ' ');

function mulberry32(a) {
  return function () {
    a |= 0; a = (a + 0x6D2B79F5) | 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

function clockString() {
  const d = new Date();
  const p = n => String(n).padStart(2, '0');
  return p(d.getHours()) + ':' + p(d.getMinutes()) + ':' + p(d.getSeconds());
}

function createSim(userCfg, hooks) {
  const cfg = Object.assign({
    capacity: 6, producerSpeed: 4, consumerSpeed: 4, consumers: 3, sync: true,
    seed: (Date.now() ^ 0x5bd1e995) >>> 0
  }, userCfg || {});
  hooks = hooks || {};

  const rngP = mulberry32(cfg.seed);                          // producer randomness
  const rngC = mulberry32((cfg.seed ^ 0x9e3779b9) >>> 0);     // consumer randomness
  const rc = (a, b) => a + rngC() * (b - a);
  let logId = 0, bagCounter = 100, acc = 0;
  const fx = ev => { if (hooks.fx) hooks.fx(ev); };

  /* ---- the single source of truth ---- */
  const simulationState = {
    status: 'IDLE', statusSince: 0, started: false, paused: false, time: 0,
    syncEnabled: !!cfg.sync,

    buffer: [],
    bufferCapacity: cfg.capacity,
    bufferState: 'EMPTY',

    producer: {
      status: 'IDLE', produced: 0, waitCount: 0, auto: true,
      speed: cfg.producerSpeed, bag: null, doneAt: 0, lastAt: 0, manual: false
    },

    autoConsume: true,
    consumerSpeed: cfg.consumerSpeed,
    consumers: [],

    mutex: { locked: false, owner: null, queue: [], lastReleaseAt: -1e9, acquisitions: 0 },

    statistics: {
      processed: 0, consumerWaits: 0, raceConditions: 0, totalProcessingTime: 0,
      lost: 0, bufferFullEvents: 0, bufferEmptyEvents: 0, maxBuffer: 0, mutexWaits: 0
    },

    scenario: { active: false, name: null },
    rush: { active: false, endsAt: 0, count: 0 },
    raceDemo: null,
    lastRace: null,
    loaded: {},
    history: [],
    log: []
  };
  const S = simulationState;
  FLIGHTS.forEach(f => { S.loaded[f.code] = 0; });
  for (let i = 1; i <= cfg.consumers; i++) {
    S.consumers.push({
      id: i, name: 'Consumer ' + i, status: 'IDLE', phase: null,
      phaseStart: 0, phaseEnd: 0, bag: null, processed: 0, waitCount: 0,
      totalTime: 0, procDur: 0, waitSince: 0, wakeAt: null, until: 0,
      manual: false, held: false
    });
  }

  const cap = () => S.bufferCapacity;
  const consumerById = id => S.consumers.find(c => c.id === id);
  const interval = () => prodInterval(S.producer.speed) / (S.rush.active ? RUSH_FACTOR : 1);

  function emit(text, cat) {
    S.log.push({ id: ++logId, clock: clockString(), text: text, cat: cat || 'normal' });
    if (S.log.length > LOG_MAX) S.log.shift();
  }

  /* ---------------- bags ---------------- */
  function makeBag() {
    const f = FLIGHTS[Math.floor(rngP() * FLIGHTS.length)];
    const n = ++bagCounter;
    return {
      id: 'BAG-' + n, n: n, flight: f.code, dest: f.dest, gate: f.gate,
      status: 'CREATED', reservedBy: null, peekedBy: [], conflictUntil: 0
    };
  }

  function insertBag(bag) {
    bag.status = 'WAITING';
    S.buffer.push(bag);
    S.producer.produced++;
    if (S.buffer.length > S.statistics.maxBuffer) S.statistics.maxBuffer = S.buffer.length;
    emit(bag.id + ' entered buffer', 'normal');
    fx({ type: 'enter', bag: bag.id });
  }

  /* ---------------- producer ---------------- */
  function startProduce() {
    const P = S.producer;
    const bag = makeBag();
    P.bag = bag;
    if (S.buffer.length >= cap()) {
      P.status = 'WAITING_BUFFER_FULL';
      P.waitCount++;
      emit('Producer waiting — buffer full (' + bag.id + ' on hold)', 'wait');
    } else {
      P.status = 'PRODUCING';
      P.doneAt = S.time + PRODUCE_MS;
      emit(bag.id + ' produced (' + bag.flight + ' → ' + bag.dest + ')', 'normal');
    }
  }

  function producerStep() {
    const P = S.producer;
    if (P.status === 'PRODUCING') {
      if (S.time >= P.doneAt) {
        if (S.buffer.length < cap()) {
          insertBag(P.bag); P.bag = null; P.status = 'IDLE'; P.lastAt = S.time;
        } else {
          P.status = 'WAITING_BUFFER_FULL'; P.waitCount++;
          emit('Producer waiting — buffer full (' + P.bag.id + ' on hold)', 'wait');
        }
      }
    } else if (P.status === 'WAITING_BUFFER_FULL') {
      if (S.buffer.length < cap()) {
        emit('Producer resumed — a slot is free', 'normal');
        insertBag(P.bag); P.bag = null; P.status = 'IDLE'; P.lastAt = S.time;
      }
    } else {
      const due = P.auto && (S.time - P.lastAt >= interval());
      if (P.manual || due) { P.manual = false; startProduce(); }
    }
  }

  /* ---------------- consumers ---------------- */
  function findAvailable() {
    for (const b of S.buffer) {
      if (b.status === 'CONFLICT') continue;
      if (S.syncEnabled && b.reservedBy != null) continue;   // already claimed via semaphore "full"
      return b;
    }
    return null;
  }

  function lockMutex(c) {
    S.mutex.locked = true; S.mutex.owner = c.id; S.mutex.acquisitions++;
    c.status = 'PROCESSING'; c.phase = 'REMOVING';
    c.phaseStart = S.time; c.phaseEnd = S.time + ACCESS_MS;
    emit('Consumer-' + c.id + ' acquired mutex', 'sync');
  }

  function releaseMutex(c) {
    S.mutex.locked = false; S.mutex.owner = null; S.mutex.lastReleaseAt = S.time;
    emit('Consumer-' + c.id + ' released mutex', 'sync');
    const nextId = S.mutex.queue.shift();
    if (nextId != null) lockMutex(consumerById(nextId));
  }

  function conflict(bag, ids) {
    bag.status = 'CONFLICT';
    bag.conflictUntil = S.time + CONFLICT_MS;
    ids.forEach(id => {
      const c = consumerById(id);
      c.status = 'RACE_CONFLICT'; c.phase = null; c.bag = bag;
      c.until = S.time + CONFLICT_MS; c.manual = false; c.wakeAt = null;
    });
    S.statistics.raceConditions++;
    S.lastRace = { bag: bag.id, ids: ids.slice(), at: S.time };
    emit('⚠ RACE CONDITION — Consumer-' + ids[0] + ' and Consumer-' + ids[1] +
         ' accessed ' + bag.id + ' simultaneously', 'error');
    fx({ type: 'conflict', bag: bag.id, ids: ids.slice() });
  }

  function beginAccess(c, bag) {
    c.bag = bag;
    if (S.syncEnabled) {
      bag.reservedBy = c.id;                       // wait(full): claim one filled slot
      emit('Consumer-' + c.id + ' requests mutex for ' + bag.id, 'sync');
      if (!S.mutex.locked) {
        lockMutex(c);
      } else {
        S.mutex.queue.push(c.id);
        c.status = 'WAITING_FOR_MUTEX'; c.waitSince = S.time; c.phase = null;
        S.statistics.mutexWaits++;
        emit('Consumer-' + c.id + ' waiting for mutex (held by Consumer-' + S.mutex.owner + ')', 'sync');
      }
    } else {
      if (bag.peekedBy.length) {                   // somebody is already reading this bag
        conflict(bag, bag.peekedBy.concat(c.id));
        return;
      }
      bag.peekedBy.push(c.id);
      c.status = 'PROCESSING'; c.phase = 'REMOVING';
      c.phaseStart = S.time; c.phaseEnd = S.time + ACCESS_MS;
      emit('Consumer-' + c.id + ' reading ' + bag.id + ' (no mutex)', 'normal');
    }
  }

  function tryAcquire(c) {
    if (c.held) return;
    const waiting = c.status === 'WAITING_BUFFER_EMPTY';
    if (!(waiting || c.manual || S.autoConsume)) return;
    const bag = findAvailable();
    if (!bag) {
      if (!waiting) {
        c.status = 'WAITING_BUFFER_EMPTY'; c.waitSince = S.time; c.waitCount++;
        S.statistics.consumerWaits++;
        emit('Consumer-' + c.id + ' waiting — buffer empty', 'wait');
      }
      c.wakeAt = null;
      return;
    }
    if (c.wakeAt == null) {
      c.wakeAt = S.time + (c.manual ? 0 : waiting ? rc(WAKE_MIN, WAKE_MAX) : rc(0, IDLE_REACT_MAX));
    }
    if (S.time < c.wakeAt) return;
    c.wakeAt = null; c.manual = false;
    beginAccess(c, bag);
  }

  function commitRemoval(c) {
    const bag = c.bag;
    const idx = S.buffer.indexOf(bag);
    if (idx < 0) {                                  // defensive: never expected
      if (S.mutex.owner === c.id) releaseMutex(c);
      c.status = 'IDLE'; c.phase = null; c.bag = null;
      return;
    }
    S.buffer.splice(idx, 1);
    bag.status = 'PROCESSING'; bag.reservedBy = null; bag.peekedBy = [];
    fx({ type: 'take', bag: bag.id, consumer: c.id });
    const dur = Math.round(consTime(S.consumerSpeed) * (0.8 + rc(0, 0.4)));
    c.procDur = dur; c.phase = 'SORTING'; c.phaseStart = S.time; c.phaseEnd = S.time + dur;
    emit('Consumer-' + c.id + ' processing ' + bag.id, 'normal');
    if (S.mutex.owner === c.id) releaseMutex(c);
  }

  function finishSorting(c) {
    const bag = c.bag;
    bag.status = 'SORTED';
    S.statistics.processed++;
    S.statistics.totalProcessingTime += c.procDur;
    c.processed++; c.totalTime += c.procDur;
    c.status = 'COMPLETED'; c.phase = null; c.until = S.time + HOLD_MS;
    emit(bag.id + ' sorted successfully', 'normal');
  }

  function stepConsumer(c) {
    switch (c.status) {
      case 'COMPLETED':
        if (S.time >= c.until) {
          const bag = c.bag;
          bag.status = 'LOADED';
          S.loaded[bag.flight]++;
          emit(bag.id + ' loaded onto ' + bag.flight + ' (' + bag.dest + ')', 'normal');
          fx({ type: 'load', bag: bag.id, consumer: c.id });
          c.status = 'IDLE'; c.bag = null;
        }
        break;
      case 'RACE_CONFLICT':
        if (S.time >= c.until) { c.status = 'IDLE'; c.bag = null; c.wakeAt = null; }
        break;
      case 'WAITING_FOR_MUTEX':
        break;                                       // woken up by releaseMutex()
      case 'PROCESSING':
        if (S.time >= c.phaseEnd) {
          if (c.phase === 'REMOVING') commitRemoval(c); else finishSorting(c);
        }
        break;
      default:                                       // IDLE or WAITING_BUFFER_EMPTY
        tryAcquire(c);
    }
  }

  function consumersStep() {
    // bags corrupted by a race are thrown away once the conflict display ends
    for (let i = S.buffer.length - 1; i >= 0; i--) {
      const b = S.buffer[i];
      if (b.status === 'CONFLICT' && S.time >= b.conflictUntil) {
        S.buffer.splice(i, 1);
        S.statistics.lost++;
        emit(b.id + ' corrupted by the race condition — discarded', 'error');
      }
    }
    const key = c => (c.status === 'WAITING_BUFFER_EMPTY' ? c.waitSince : 1e12 + c.id);
    S.consumers.slice().sort((a, b) => key(a) - key(b)).forEach(stepConsumer);
  }

  /* deterministic "Simulate race condition" experiment */
  function raceDemoStep() {
    if (!S.raceDemo) return;
    const c1 = S.consumers[0], c2 = S.consumers[1];
    const free = c => c.status === 'IDLE' || c.status === 'WAITING_BUFFER_EMPTY';
    if (!(free(c1) && free(c2))) return;
    S.raceDemo = null; c1.held = false; c2.held = false;
    const need = S.syncEnabled ? 2 : 1;
    const avail = S.buffer.filter(b => b.status !== 'CONFLICT' && b.reservedBy == null && !b.peekedBy.length);
    while (avail.length < need && S.buffer.length < cap()) {
      const b = makeBag(); insertBag(b); avail.push(b);
    }
    if (avail.length < need) { emit('Race test cancelled — no free bag available', 'error'); return; }
    emit('Race test: Consumer-1 and Consumer-2 reach for ' +
         (S.syncEnabled ? avail[0].id + ' and ' + avail[1].id : avail[0].id) + ' at the same instant', 'scenario');
    beginAccess(c1, avail[0]);
    beginAccess(c2, S.syncEnabled ? avail[1] : avail[0]);
  }

  function rushStep() {
    if (S.rush.active && S.time >= S.rush.endsAt) {
      S.rush.active = false;
      emit('Flight rush ended — arrival rate back to normal', 'scenario');
    }
  }

  /* ---------------- derived states ---------------- */
  function deriveBufferState() {
    const n = S.buffer.length, c = cap();
    const st = n === 0 ? 'EMPTY' : n >= c ? 'FULL' : (n / c >= 0.5 ? 'PARTIALLY_FULL' : 'AVAILABLE');
    if (st !== S.bufferState) {
      S.bufferState = st;
      if (st === 'FULL') { S.statistics.bufferFullEvents++; emit('Buffer FULL', 'wait'); }
      else if (st === 'EMPTY' && S.started) { S.statistics.bufferEmptyEvents++; emit('Buffer EMPTY', 'wait'); }
    }
  }

  function computeStatus() {
    if (!S.started) return 'IDLE';
    if (S.paused) return 'PAUSED';
    if (S.consumers.some(c => c.status === 'RACE_CONFLICT')) return 'RACE_CONDITION';
    if (S.bufferState === 'FULL') return 'BUFFER_FULL';
    if (S.syncEnabled && (S.mutex.locked || S.mutex.queue.length)) return 'SYNCHRONIZED';
    if (S.bufferState === 'EMPTY') return 'BUFFER_EMPTY';
    if (S.producer.status === 'PRODUCING') return 'PRODUCING';
    if (S.consumers.some(c => c.status === 'PROCESSING')) return 'CONSUMING';
    return 'BUFFER_AVAILABLE';
  }

  function refreshStatus() {
    const next = computeStatus();
    if (next !== S.status) { S.status = next; S.statusSince = S.time; }
    if (!S.started) return;
    const last = S.history[S.history.length - 1];
    const stable = S.status === 'PAUSED' || (S.time - S.statusSince >= 300);
    if (stable && (!last || last.label !== S.status)) {
      S.history.push({ label: S.status, t: S.time });
      if (S.history.length > HISTORY_MAX) S.history.shift();
    }
  }

  function update() {
    S.time += TICK_MS;
    producerStep();
    consumersStep();
    raceDemoStep();
    rushStep();
    deriveBufferState();
    refreshStatus();
  }

  /* ---------------- public API ---------------- */
  const api = {
    state: S,
    cfg: cfg,

    start() {
      if (S.started) return;
      S.started = true; S.paused = false;
      S.producer.lastAt = S.time - interval() + 600;   // first bag after ~0.6 s
      S.history.push({ label: 'RUNNING', t: S.time });
      emit('Simulation started', 'normal');
      refreshStatus();
    },
    pause() { if (S.started && !S.paused) { S.paused = true; refreshStatus(); } },
    resume() { if (S.started && S.paused) { S.paused = false; S.statusSince = S.time; refreshStatus(); } },

    advance(dtMs) {
      if (!S.started || S.paused) return;
      acc += dtMs;
      while (acc >= TICK_MS) { acc -= TICK_MS; update(); }
    },

    addBaggage() {
      const P = S.producer;
      if (S.paused) return { ok: false, msg: 'Simulation is paused. Press Start to resume.' };
      if (P.status === 'PRODUCING') return { ok: false, msg: 'Producer is busy checking in a bag.' };
      if (P.status === 'WAITING_BUFFER_FULL') return { ok: false, msg: 'Producer is already waiting: the buffer is full.' };
      P.manual = true;
      return { ok: true, full: S.buffer.length >= cap() };
    },

    consume(id) {
      const c = consumerById(id);
      if (!c) return { ok: false, msg: 'Unknown consumer.' };
      if (S.paused) return { ok: false, msg: 'Simulation is paused. Press Start to resume.' };
      if (c.status !== 'IDLE') return { ok: false, msg: c.name + ' is busy (' + pretty(c.status) + ').' };
      c.manual = true;
      return { ok: true, empty: findAvailable() === null };
    },

    simulateRace() {
      if (S.consumers.length < 2) return { ok: false, msg: 'The race test needs at least 2 consumers.' };
      if (S.paused) return { ok: false, msg: 'Simulation is paused. Press Start to resume.' };
      if (S.raceDemo) return { ok: false, msg: 'Race test is already armed.' };
      S.raceDemo = { since: S.time };
      S.consumers[0].held = true; S.consumers[1].held = true;
      emit('Race test armed — Consumer-1 and Consumer-2 will reach for the same bag', 'scenario');
      return { ok: true };
    },

    setSync(on) {
      on = !!on;
      if (on === S.syncEnabled) return;
      S.syncEnabled = on;
      for (const c of S.consumers) {
        const accessing = c.status === 'WAITING_FOR_MUTEX' || (c.status === 'PROCESSING' && c.phase === 'REMOVING');
        if (accessing) {
          emit('Consumer-' + c.id + ' access aborted (synchronization mode changed)', 'sync');
          c.status = 'IDLE'; c.phase = null; c.bag = null; c.wakeAt = null;
        }
      }
      S.mutex.locked = false; S.mutex.owner = null; S.mutex.queue = [];
      for (const b of S.buffer) { if (b.status !== 'CONFLICT') { b.reservedBy = null; b.peekedBy = []; } }
      emit(on ? 'Synchronization ENABLED — mutex protects the buffer'
              : 'Synchronization DISABLED — buffer access is unprotected', 'sync');
      refreshStatus();
    },

    setProducerAuto(v) { S.producer.auto = !!v; },
    setAutoConsume(v) { S.autoConsume = !!v; },
    setProducerSpeed(v) { S.producer.speed = v; },
    setConsumerSpeed(v) { S.consumerSpeed = v; },

    startRush() {
      S.rush.active = true; S.rush.endsAt = S.time + RUSH_MS; S.rush.count++;
      emit('🚨 FLIGHT RUSH ACTIVE — high baggage arrival rate detected', 'scenario');
    },
    stopRush() {
      if (!S.rush.active) return;
      S.rush.active = false;
      emit('Flight rush stopped by operator', 'scenario');
    },

    note(text, cat) { emit(text, cat); },

    snapshot() {
      const st = S.statistics;
      return {
        produced: S.producer.produced,
        processed: st.processed,
        lost: st.lost,
        races: st.raceConditions,
        producerWaits: S.producer.waitCount,
        consumerWaits: st.consumerWaits,
        fullEvents: st.bufferFullEvents,
        maxBuffer: st.maxBuffer,
        inBuffer: S.buffer.length,
        mutexWaits: st.mutexWaits,
        avgProc: st.processed ? st.totalProcessingTime / st.processed / 1000 : 0,
        consumers: S.consumers.length,
        capacity: cap()
      };
    }
  };
  emit('System ready — press START', 'normal');
  return api;
}

/* ---------- headless run, prediction and classification (Scenario Lab) ---------- */

function runHeadless(cfg, seconds) {
  const sim = createSim(cfg, {});
  sim.start();
  sim.advance(seconds * 1000);
  return sim.snapshot();
}

function levelProducerWait(snap) {
  const r = snap.producerWaits / Math.max(1, snap.producerWaits + snap.produced);
  return r >= 0.25 ? 'HIGH' : r >= 0.08 ? 'MEDIUM' : 'LOW';
}
function levelConsumerWait(snap) {
  const r = snap.consumerWaits / Math.max(1, snap.processed + snap.lost + snap.consumers);
  return r >= 0.5 ? 'HIGH' : r >= 0.2 ? 'MEDIUM' : 'LOW';
}

function predict(cfg) {
  const lambda = 1000 / (prodInterval(cfg.producerSpeed) + PRODUCE_MS);        // bags/s in (gap + check-in time)
  const cycle = ACCESS_MS + consTime(cfg.consumerSpeed) + HOLD_MS + IDLE_REACT_MAX / 2;
  let mu = cfg.consumers * 1000 / cycle;                                       // bags/s out
  if (cfg.sync) mu = Math.min(mu, 1000 / ACCESS_MS);
  const rho = lambda / mu;
  const maybeLow = cfg.capacity <= 3 ? 0.6 : cfg.capacity <= 6 ? 0.8 : 0.9;
  let full, pw, cw, line;
  if (rho > 1.1) {
    full = 'YES'; pw = 'HIGH'; cw = 'LOW';
    line = 'Producer speed is higher than consumer capacity. The buffer is likely to become full.';
  } else if (rho >= maybeLow) {
    full = 'MAYBE'; pw = rho >= 0.95 ? 'MEDIUM' : 'LOW'; cw = 'MEDIUM';
    line = 'Producer and consumers are closely matched. The buffer may fill up now and then.';
  } else if (rho < 0.7) {
    full = 'NO'; pw = 'LOW'; cw = 'HIGH';
    line = 'Producer is slower than consumer capacity. Consumers will often wait for baggage.';
  } else {
    full = 'NO'; pw = 'LOW'; cw = 'MEDIUM';
    line = 'Consumers are faster than the Producer. The buffer should stay mostly low.';
  }
  let race, raceLine;
  if (cfg.consumers < 2) { race = 'NONE'; raceLine = 'Only one consumer: a race condition is not possible.'; }
  else if (cfg.sync) { race = 'NONE'; raceLine = 'Mutex is ON: conflicting access to a bag is prevented.'; }
  else { race = 'LIKELY'; raceLine = 'Synchronization is OFF with ' + cfg.consumers + ' consumers: a race condition is likely.'; }
  return { lambda: lambda, mu: mu, rho: rho, full: full, producerWait: pw, consumerWait: cw, race: race, lines: [line, raceLine] };
}

if (typeof module !== 'undefined' && module.exports) {
  module.exports = { createSim, runHeadless, predict, levelProducerWait, levelConsumerWait, prodInterval, consTime };
}

/* ---------------------------------------------------------------------
   PART 2 — USER INTERFACE
   --------------------------------------------------------------------- */
if (typeof document !== 'undefined') {
(function UI() {

  const $ = id => document.getElementById(id);
  const REDUCED = !!(window.matchMedia && window.matchMedia('(prefers-reduced-motion: reduce)').matches);
  const EXP_SECONDS = 60;

  const DEFAULT_CFG = { capacity: 6, producerSpeed: 4, consumerSpeed: 4, consumers: 3, sync: true };
  const PRESETS = {
    normal: { icon: '🟢', name: 'Normal Airport', desc: 'Balanced producer and consumers.',
              expect: 'Buffer stays low; consumers often wait for the next bag.',
              cfg: { capacity: 6, producerSpeed: 4, consumerSpeed: 4, consumers: 3, sync: true } },
    rush:   { icon: '🚨', name: 'Flight Rush', desc: 'Producer much faster than consumers.',
              expect: 'Buffer fills quickly → Producer waits.',
              cfg: { capacity: 6, producerSpeed: 10, consumerSpeed: 2, consumers: 3, sync: true } },
    slow:   { icon: '🐢', name: 'Slow Sorting', desc: 'Consumers become slower.',
              expect: 'Buffer gradually fills.',
              cfg: { capacity: 6, producerSpeed: 4, consumerSpeed: 2, consumers: 3, sync: true } },
    empty:  { icon: '🏜', name: 'Empty Airport', desc: 'Producer is slow.',
              expect: 'Consumers frequently wait.',
              cfg: { capacity: 6, producerSpeed: 2, consumerSpeed: 4, consumers: 3, sync: true } },
    race:   { icon: '⚠', name: 'Race Test', desc: 'Synchronization OFF.',
              expect: 'Race condition occurs.',
              cfg: { capacity: 6, producerSpeed: 4, consumerSpeed: 7, consumers: 3, sync: false } },
    safe:   { icon: '🔐', name: 'Safe Mode', desc: 'Synchronization ON.',
              expect: 'Mutex prevents conflicting access.',
              cfg: { capacity: 6, producerSpeed: 4, consumerSpeed: 7, consumers: 3, sync: true } }
  };

  const STATUS_META = {
    IDLE:            { icon: '⚪', label: 'IDLE',           cls: 'idle' },
    RUNNING:         { icon: '🟢', label: 'RUNNING',        cls: 'ok' },
    PRODUCING:       { icon: '🟢', label: 'PRODUCING',      cls: 'ok' },
    CONSUMING:       { icon: '🟢', label: 'CONSUMING',      cls: 'ok' },
    BUFFER_AVAILABLE:{ icon: '🟢', label: 'BUFFER AVAILABLE', cls: 'ok' },
    BUFFER_EMPTY:    { icon: '🟡', label: 'BUFFER EMPTY',   cls: 'warn' },
    BUFFER_FULL:     { icon: '🔴', label: 'BUFFER FULL',    cls: 'danger' },
    RACE_CONDITION:  { icon: '🔴', label: 'RACE CONDITION', cls: 'danger' },
    SYNCHRONIZED:    { icon: '🔵', label: 'SYNCHRONIZED',   cls: 'info' },
    PAUSED:          { icon: '⏸', label: 'PAUSED',         cls: 'idle' }
  };
  const CAPTIONS = {
    IDLE: 'Press START to open the check-in counters.',
    RUNNING: 'The system is running.',
    PRODUCING: 'The Producer is checking in a bag.',
    CONSUMING: 'A Consumer is sorting a bag.',
    BUFFER_AVAILABLE: 'There are bags on the conveyor and free slots left.',
    BUFFER_EMPTY: 'The conveyor is empty. Consumers wait for the Producer.',
    BUFFER_FULL: 'The conveyor is full. The Producer waits for a free slot.',
    RACE_CONDITION: 'Two Consumers touched the same bag without a lock.',
    SYNCHRONIZED: 'The mutex lets one Consumer at a time into the critical section.',
    PAUSED: 'Simulation paused. Press START to resume.'
  };
  const CHIP = {
    IDLE: 'idle', PRODUCING: 'ok', WAITING_BUFFER_FULL: 'danger',
    WAITING_BUFFER_EMPTY: 'warn', WAITING_FOR_MUTEX: 'info',
    PROCESSING: 'ok', COMPLETED: 'ok', RACE_CONFLICT: 'danger'
  };
  const BUFFER_CHIP = { EMPTY: 'warn', AVAILABLE: 'ok', PARTIALLY_FULL: 'info', FULL: 'danger' };

  /* ---- tiny DOM helpers that only touch the DOM when something changed ---- */
  const setText = (el, t) => { if (el && el.textContent !== t) el.textContent = t; };
  const setHTML = (el, h) => { if (el && el._h !== h) { el._h = h; el.innerHTML = h; } };
  const setCls = (el, c) => { if (el && el._c !== c) { el._c = c; el.className = c; } };
  const setHidden = (el, h) => { if (el && el.hidden !== h) el.hidden = h; };
  const setWidth = (el, pct) => { const v = pct.toFixed(0) + '%'; if (el._w !== v) { el._w = v; el.style.width = v; } };

  /* ---- UI state (everything simulation-related lives in sim.state) ---- */
  let sim = null;
  let speedMult = 1;
  let timer = null, lastTs = 0;
  let exp = null;                       // running / finished experiment
  let lastLogId = 0;
  let beltSig = '';
  let fxQueue = [];
  let toastTimer = null;
  let activePreset = null;
  const R = { c: {} };                  // cached consumer elements
  const E = {};                         // cached static elements

  /* =============== simulation lifecycle =============== */
  function newSim(cfg) {
    stopLoop();
    exp = null;
    sim = createSim(cfg, { fx: onFx });
    lastLogId = 0; beltSig = ''; fxQueue = [];
    E.logBox.innerHTML = '';
    E.fx.innerHTML = '';
    E.raceSvg.innerHTML = ''; E.raceSvg._on = false;
    buildConsumers();
    syncControlsFromState();
    render();
  }

  function running() { return sim.state.started && !sim.state.paused; }

  function startLoop() {
    if (timer) return;
    lastTs = performance.now();
    timer = setInterval(tick, 50);
  }
  function stopLoop() {
    if (timer) { clearInterval(timer); timer = null; }
  }
  function tick() {
    const now = performance.now();
    const dt = Math.min(now - lastTs, 250);
    lastTs = now;
    sim.advance(dt * speedMult);
    checkExperiment();
    render();
  }

  function doStart() {
    if (!sim.state.started) sim.start(); else if (sim.state.paused) sim.resume();
    startLoop();
    render();
  }
  function doPause() {
    if (!running()) return;
    sim.pause();
    stopLoop();
    render();
  }
  function resetAll() {
    speedMult = 1;
    activePreset = null;
    setLabFromCfg(DEFAULT_CFG);
    clearLabResults();
    newSim(DEFAULT_CFG);
    updateSpeedUI();
    showPrediction(predict(DEFAULT_CFG), 'preview', 'Current lab settings');
    renderPresetButtons();
    toast('System reset. All state, statistics and logs were cleared.');
  }

  /* start automatically for manual actions; refuse when paused */
  function ensureRunning() {
    if (!sim.state.started) { doStart(); return true; }
    if (sim.state.paused) { toast('Simulation is paused. Press Start to resume.'); return false; }
    return true;
  }

  function setSpeed(v) {
    speedMult = v;
    updateSpeedUI();
  }
  function updateSpeedUI() {
    setText(E.hdrSpeed, speedMult + '×');
    document.querySelectorAll('.seg-btn').forEach(b => {
      b.setAttribute('aria-pressed', String(parseFloat(b.dataset.speed) === speedMult));
    });
  }

  /* =============== building dynamic markup =============== */
  function buildConsumers() {
    const S = sim.state;
    let sg = '<div class="sg-row"><dt>Producer</dt><dd id="sgProducer"></dd></div>' +
             '<div class="sg-row"><dt>Buffer</dt><dd id="sgBuffer"></dd></div>';
    let pc = '', cp = '';
    S.consumers.forEach(c => {
      sg += '<div class="sg-row"><dt>Consumer ' + c.id + '</dt><dd id="sgC' + c.id + '"></dd></div>';
      pc += '<div class="pc" id="pc' + c.id + '">' +
              '<div class="pc-top"><b>🔍 CONSUMER ' + c.id + '</b><span class="chip idle" data-r="status">IDLE</span></div>' +
              '<div class="pc-scan"><div class="scan-line"></div><div class="pc-bag" data-r="bag"></div></div>' +
              '<div class="bar"><i data-r="bar"></i></div>' +
              '<div class="pc-detail" data-r="detail"></div>' +
            '</div>';
      cp += '<div class="cp" id="cp' + c.id + '">' +
              '<div class="cp-head"><b>🔍 CONSUMER ' + c.id + '</b><span class="chip idle" data-r="status">IDLE</span></div>' +
              '<p class="cp-sub">Baggage Sorting Process</p>' +
              '<dl class="cp-kv">' +
                '<div><dt>Current bag</dt><dd data-r="bag">—</dd></div>' +
                '<div><dt>Processed</dt><dd data-r="processed">0</dd></div>' +
                '<div><dt>Processing time</dt><dd data-r="time">—</dd></div>' +
                '<div><dt>Waits</dt><dd data-r="waits">0</dd></div>' +
              '</dl>' +
              '<button class="btn sm block" type="button" data-act="consume" data-id="' + c.id + '">Process Baggage</button>' +
            '</div>';
    });
    sg += '<div class="sg-row"><dt>Mutex</dt><dd id="sgMutex"></dd></div>';
    E.stateGrid.innerHTML = sg;
    E.pipeConsumers.innerHTML = pc;
    E.cPanelList.innerHTML = cp;
    R.c = {};
    S.consumers.forEach(c => {
      const a = $('pc' + c.id), b = $('cp' + c.id);
      R.c[c.id] = {
        pc: a, pcStatus: a.querySelector('[data-r=status]'), pcBag: a.querySelector('[data-r=bag]'),
        pcBar: a.querySelector('[data-r=bar]'), pcDetail: a.querySelector('[data-r=detail]'),
        cp: b, cpStatus: b.querySelector('[data-r=status]'), cpBag: b.querySelector('[data-r=bag]'),
        cpProcessed: b.querySelector('[data-r=processed]'), cpTime: b.querySelector('[data-r=time]'),
        cpWaits: b.querySelector('[data-r=waits]'), cpBtn: b.querySelector('button'),
        sg: $('sgC' + c.id)
      };
    });
    E.sgProducer = $('sgProducer'); E.sgBuffer = $('sgBuffer'); E.sgMutex = $('sgMutex');
  }

  function bagHTML(b, mini) {
    const res = (b.reservedBy != null && b.status === 'WAITING')
      ? '<span class="bag-res" title="Claimed by Consumer ' + b.reservedBy + '">C' + b.reservedBy + '</span>' : '';
    return '<div class="bag s-' + b.status.toLowerCase() + (mini ? ' mini' : '') + '" data-bag="' + b.id + '">' +
             '<div class="bag-top"><span class="bag-ico" aria-hidden="true">🧳</span><b>' + b.id + '</b>' + res + '</div>' +
             '<div class="bag-fl">' + b.flight + '</div>' +
             '<div class="bag-dest">' + b.dest + '</div>' +
             '<div class="bag-st"><i></i>' + b.status + '</div>' +
           '</div>';
  }

  /* =============== RENDER (state → DOM) =============== */
  function render() {
    const S = sim.state;
    renderHeaderAndState(S);
    renderPipeline(S);
    renderPanels(S);
    renderSync(S);
    renderStats(S);
    renderLog(S);
    renderHistory(S);
    renderWhy(S);
    renderExperimentProgress(S);
    renderRunButtons(S);
    document.body.classList.toggle('is-paused', !running());
    processFx();
    renderRaceLines(S);
  }

  function mutexText(S) {
    if (!S.syncEnabled) return 'DISABLED (sync OFF)';
    return S.mutex.locked ? 'LOCKED by Consumer ' + S.mutex.owner : 'UNLOCKED';
  }

  function consumerSummary(S, c) {
    if (c.status === 'PROCESSING' && c.bag) return 'PROCESSING ' + c.bag.id;
    if (c.status === 'WAITING_BUFFER_EMPTY') return 'WAITING (buffer empty)';
    if (c.status === 'WAITING_FOR_MUTEX') return 'WAITING FOR MUTEX';
    if (c.status === 'RACE_CONFLICT') return 'RACE CONFLICT' + (c.bag ? ' on ' + c.bag.id : '');
    if (c.status === 'COMPLETED' && c.bag) return 'COMPLETED ' + c.bag.id;
    return pretty(c.status);
  }

  function renderHeaderAndState(S) {
    const meta = STATUS_META[S.status] || STATUS_META.IDLE;
    // header badge
    setCls(E.hdrStatus, 'status-badge ' + meta.cls);
    setText(E.hdrStatus.querySelector('b'), S.status === 'IDLE' ? 'SYSTEM READY' : meta.label);
    // state pill
    setCls(E.statePill, 'state-pill ' + meta.cls);
    setText(E.stateIcon, meta.icon);
    setText(E.stateLabel, meta.label);
    setText(E.stateCaption, CAPTIONS[S.status]);

    // rows
    const P = S.producer;
    const pCls = { IDLE: 'idle', PRODUCING: 'ok', WAITING_BUFFER_FULL: 'danger' }[P.status];
    setText(E.sgProducer, pretty(P.status));
    setCls(E.sgProducer, 'v ' + pCls);
    setText(E.sgBuffer, S.buffer.length + ' / ' + S.bufferCapacity + ' — ' + pretty(S.bufferState));
    setCls(E.sgBuffer, 'v ' + BUFFER_CHIP[S.bufferState]);
    S.consumers.forEach(c => {
      const el = R.c[c.id].sg;
      setText(el, consumerSummary(S, c));
      setCls(el, 'v ' + CHIP[c.status]);
    });
    setText(E.sgMutex, mutexText(S));
    setCls(E.sgMutex, 'v ' + (!S.syncEnabled ? 'idle' : S.mutex.locked ? 'info' : 'ok'));

    // banners
    let b = '';
    if (S.rush.active) {
      const left = Math.max(0, Math.ceil((S.rush.endsAt - S.time) / 1000));
      b += '<div class="banner danger"><b>🚨 FLIGHT RUSH ACTIVE</b><span>High baggage arrival rate detected (' + left + ' s left).</span></div>';
    }
    if (exp && !exp.done) {
      b += '<div class="banner scenario"><b>🧪 Experiment running</b><span>' + exp.name + '</span></div>';
    }
    if (S.raceDemo) {
      b += '<div class="banner warn"><b>⚠ Race test armed</b><span>Waiting until Consumer 1 and Consumer 2 are free.</span></div>';
    }
    setHTML(E.bannerArea, b);
  }

  /* ---------- pipeline ---------- */
  function renderPipeline(S) {
    const P = S.producer;

    // producer station
    setText(E.pStatusChip, pretty(P.status));
    setCls(E.pStatusChip, 'chip ' + ({ IDLE: 'idle', PRODUCING: 'ok', WAITING_BUFFER_FULL: 'danger' }[P.status]));
    setHTML(E.pBagSlot, P.bag ? bagHTML(P.bag) : '<span class="slot-note">Counter open</span>');
    setCls(E.pScan, 'scanbar' + (P.status === 'PRODUCING' ? ' on' : ''));
    const people = S.rush.active ? 7 : (P.status === 'PRODUCING' ? 3 : 2);
    setText(E.pQueue, '🧍'.repeat(people));
    setText(E.pNote, P.status === 'WAITING_BUFFER_FULL'
      ? 'Holding ' + (P.bag ? P.bag.id : 'bag') + ': conveyor full'
      : P.status === 'PRODUCING' ? 'Tagging & scanning ' + P.bag.id : (S.rush.active ? 'Heavy queue' : 'Ready'));
    setCls(E.stProducer, 'station st-producer' + (P.status === 'WAITING_BUFFER_FULL' ? ' blocked' : ''));

    // buffer station
    setText(E.bCount, S.buffer.length + ' / ' + S.bufferCapacity);
    setCls(E.bCount, 'count-chip ' + BUFFER_CHIP[S.bufferState]);
    renderBelt(S);
    const conflictNow = S.consumers.some(c => c.status === 'RACE_CONFLICT');
    setCls(E.beltWrap, 'belt-wrap' +
      (S.started && S.syncEnabled && S.mutex.locked ? ' locked' : '') +
      (S.started && !S.syncEnabled ? ' unprotected' : '') +
      (conflictNow ? ' conflict' : ''));
    if (S.started && S.syncEnabled && S.mutex.locked) {
      setText(E.lockBadge, '🔒 MUTEX LOCKED · Consumer ' + S.mutex.owner);
      setCls(E.lockBadge, 'lock-badge'); setHidden(E.lockBadge, false);
    } else if (S.started && !S.syncEnabled) {
      setText(E.lockBadge, '⚠ NO MUTEX · unprotected access');
      setCls(E.lockBadge, 'lock-badge off'); setHidden(E.lockBadge, false);
    } else if (S.started && S.syncEnabled) {
      setText(E.lockBadge, '🔓 MUTEX FREE');
      setCls(E.lockBadge, 'lock-badge free'); setHidden(E.lockBadge, false);
    } else {
      setHidden(E.lockBadge, true);
    }

    let alertTxt = '', alertCls = '';
    if (S.started && S.bufferState === 'FULL') { alertTxt = '🔴 BUFFER FULL — Producer is waiting for free space.'; alertCls = 'danger'; }
    else if (S.started && S.bufferState === 'EMPTY') { alertTxt = '🟡 BUFFER EMPTY — Consumers are waiting for baggage.'; alertCls = 'warn'; }
    setText(E.bufAlert, alertTxt);
    setCls(E.bufAlert, 'alert ' + alertCls);
    setHidden(E.bufAlert, !alertTxt);

    renderConsumersPipeline(S);

    // aircraft
    const total = Object.values(S.loaded).reduce((a, b) => a + b, 0);
    setText(E.loadedTotal, String(total));
    let chips = '';
    FLIGHTS.forEach(f => {
      const n = S.loaded[f.code];
      const status = n === 0 ? 'Check-in open' : n < 6 ? 'Loading' : 'Boarding soon';
      chips += '<div class="fchip' + (n > 0 ? ' hot' : '') + '"><b>✈ ' + f.code + '</b><span>' + f.dest + ' · Gate ' + f.gate +
               '</span><em>' + status + ' · ' + n + (n === 1 ? ' bag' : ' bags') + '</em></div>';
    });
    setHTML(E.flightChips, chips);
  }

  function renderBelt(S) {
    const sig = S.bufferCapacity + '|' + S.buffer.map(b => b.id + ':' + b.status + ':' + (b.reservedBy || '')).join(',');
    if (sig === beltSig) return;
    beltSig = sig;

    const prev = {};
    if (!REDUCED) {
      E.belt.querySelectorAll('.bag[data-bag]').forEach(el => { prev[el.dataset.bag] = el.getBoundingClientRect(); });
    }
    // slot 0 is the head of the queue and is drawn at the exit end of the belt
    let html = '';
    for (let i = 0; i < S.bufferCapacity; i++) {
      const b = S.buffer[i];
      html += '<div class="slot' + (b ? ' filled' : '') + '" role="listitem" aria-label="Slot ' + (i + 1) + ': ' + (b ? b.id : 'empty') + '">' +
                (b ? bagHTML(b) : '<span class="slot-empty">empty</span>') +
                '<span class="slot-no">' + (i + 1) + '</span></div>';
    }
    E.belt.innerHTML = html;

    if (REDUCED) return;
    const from = E.pBagSlot.getBoundingClientRect();
    const ms = Math.max(160, 520 / speedMult);
    E.belt.querySelectorAll('.bag[data-bag]').forEach(el => {
      const r = el.getBoundingClientRect();
      const p = prev[el.dataset.bag];
      if (p) {
        const dx = p.left - r.left, dy = p.top - r.top;
        if (Math.abs(dx) > 1 || Math.abs(dy) > 1) {
          el.animate([{ transform: 'translate(' + dx + 'px,' + dy + 'px)' }, { transform: 'none' }], { duration: ms * 0.7, easing: 'ease-out' });
        }
      } else if (from.width > 0) {
        const dx = from.left + from.width / 2 - (r.left + r.width / 2);
        const dy = from.top + from.height / 2 - (r.top + r.height / 2);
        el.animate([{ transform: 'translate(' + dx + 'px,' + dy + 'px) scale(.7)', opacity: 0.2 }, { transform: 'none', opacity: 1 }],
                   { duration: ms, easing: 'ease-out' });
      }
    });
  }

  function renderConsumersPipeline(S) {
    S.consumers.forEach(c => {
      const r = R.c[c.id];
      const st = c.status;
      setText(r.pcStatus, pretty(st));
      setCls(r.pcStatus, 'chip ' + CHIP[st]);
      setCls(r.pc, 'pc s-' + st.toLowerCase() + (st === 'PROCESSING' ? ' ph-' + String(c.phase).toLowerCase() : ''));

      let bag = '<span class="pc-empty">no bag</span>', detail = 'Idle: ready for baggage', prog = 0, barCls = '';
      const b = c.bag;
      if (st === 'WAITING_BUFFER_EMPTY') detail = 'Buffer empty: waiting for the Producer';
      else if (st === 'WAITING_FOR_MUTEX') {
        bag = '<span class="pc-ghost">🔒 ' + b.id + ' claimed</span>';
        detail = 'Waiting for mutex (owner: Consumer ' + S.mutex.owner + ')';
      } else if (st === 'PROCESSING' && c.phase === 'REMOVING') {
        bag = '<span class="pc-ghost">→ taking ' + b.id + '</span>';
        detail = S.syncEnabled ? 'Critical section: holds the mutex' : 'Reading shared buffer: NO lock!';
        prog = (S.time - c.phaseStart) / (c.phaseEnd - c.phaseStart);
        barCls = S.syncEnabled ? 'crit' : 'risk';
      } else if (st === 'PROCESSING') {
        bag = bagHTML(b, true);
        detail = 'Scanning & sorting → ' + b.flight + ' ' + b.dest;
        prog = (S.time - c.phaseStart) / (c.phaseEnd - c.phaseStart);
      } else if (st === 'COMPLETED') {
        bag = bagHTML(b, true);
        detail = b.id + ' sorted ✓ sending to aircraft';
        prog = 1;
      } else if (st === 'RACE_CONFLICT') {
        bag = '<span class="pc-ghost bad">⚠ ' + b.id + ' conflict</span>';
        detail = 'RACE CONDITION: bag corrupted';
        prog = 1; barCls = 'risk';
      }
      setHTML(r.pcBag, bag);
      setText(r.pcDetail, detail);
      setCls(r.pcBar.parentNode, 'bar ' + barCls);
      setWidth(r.pcBar, Math.max(0, Math.min(1, prog)) * 100);
    });
  }

  /* ---------- producer / buffer / consumer panels ---------- */
  function renderPanels(S) {
    const P = S.producer;
    setText(E.ppStatus, pretty(P.status));
    setText(E.ppProduced, String(P.produced));
    setText(E.ppSpeed, speedLabel(P.speed));
    setText(E.ppWaiting, String(P.waitCount));
    const full = S.started && S.bufferState === 'FULL';
    setHidden(E.ppAlert, !full);
    setText(E.ppAlert.querySelector('span'),
      P.status === 'WAITING_BUFFER_FULL' ? 'Producer is waiting for available space.' : 'No free slot: the next bag will have to wait.');
    const blocked = S.bufferState === 'FULL' || P.status === 'WAITING_BUFFER_FULL';
    setText(E.btnAdd, blocked ? '⛔ Buffer full: producer blocked' : '➕ Add Baggage');
    setCls(E.btnAdd, 'btn primary block' + (blocked ? ' blocked' : ''));
    E.btnAdd.setAttribute('aria-disabled', String(blocked));

    // buffer panel
    const n = S.buffer.length, cap = S.bufferCapacity;
    setText(E.bpUsed, String(n));
    setText(E.bpCap, String(cap));
    setText(E.bpOcc, String(n));
    setText(E.bpFree, String(cap - n));
    let m = '';
    for (let i = 0; i < cap; i++) {
      const b = S.buffer[i];
      m += '<i class="' + (b ? (b.status === 'CONFLICT' ? 'bad' : 'on') : '') + '"></i>';
    }
    setHTML(E.bpMeter, m);
    setText(E.bpState, pretty(S.bufferState));
    setCls(E.bpState, 'chip ' + BUFFER_CHIP[S.bufferState]);
    const msgs = {
      EMPTY: ['warn', 'BUFFER EMPTY', 'Consumers are waiting for baggage.'],
      AVAILABLE: ['ok', 'SPACE AVAILABLE', 'Producer can add baggage freely.'],
      PARTIALLY_FULL: ['info', 'PARTIALLY FULL', 'Still room, but the conveyor is filling up.'],
      FULL: ['danger', 'BUFFER FULL', 'Producer is waiting for free space.']
    }[S.bufferState];
    setCls(E.bpAlert, 'alert ' + msgs[0]);
    setHTML(E.bpAlert, '<b>' + msgs[1] + '</b><span>' + msgs[2] + '</span>');

    // consumer panel
    S.consumers.forEach(c => {
      const r = R.c[c.id];
      setText(r.cpStatus, pretty(c.status));
      setCls(r.cpStatus, 'chip ' + CHIP[c.status]);
      setText(r.cpBag, c.bag ? c.bag.id : '—');
      setText(r.cpProcessed, String(c.processed));
      setText(r.cpTime, c.processed ? (c.totalTime / c.processed / 1000).toFixed(1) + ' s' :
                        (c.status === 'PROCESSING' && c.phase === 'SORTING' ? (c.procDur / 1000).toFixed(1) + ' s' : '—'));
      setText(r.cpWaits, String(c.waitCount));
      r.cpBtn.disabled = c.status !== 'IDLE';
    });
  }

  /* ---------- synchronization monitor ---------- */
  function renderSync(S) {
    const on = S.syncEnabled;
    const locked = on && S.mutex.locked;
    setText(E.mxIcon, !on ? '⚠' : locked ? '🔒' : '🔓');
    setText(E.mxState, !on ? 'DISABLED' : locked ? 'LOCKED' : 'UNLOCKED');
    setCls(E.mxLockBox, 'mx-lock ' + (!on ? 'off' : locked ? 'locked' : 'free'));
    setText(E.mxVal, !on ? 'DISABLED' : locked ? 'LOCKED' : 'UNLOCKED');
    setText(E.mxOwner, locked ? 'Consumer ' + S.mutex.owner : '—');
    setText(E.mxWaiting, String(S.mutex.queue.length));
    setText(E.semEmpty, String(S.bufferCapacity - S.buffer.length));
    setText(E.semFull, String(S.buffer.length));

    const steps = E.mxSteps.querySelectorAll('li');
    const justReleased = on && !locked && (S.time - S.mutex.lastReleaseAt) < 900 && S.mutex.lastReleaseAt >= 0;
    const act = [
      on && S.mutex.queue.length > 0,
      locked,
      locked,
      justReleased
    ];
    steps.forEach((li, i) => setCls(li, act[i] ? 'active' : ''));
    setText(E.mxNote, on
      ? 'Semaphores: empty = free slots, full = filled slots. The mutex guards the removal of a bag, so only one Consumer is in the critical section.'
      : '⚠ No mutex: two Consumers can read the same bag at the same time. That is a race condition and the bag is corrupted.');
    setSyncButtons(on);
  }

  function setSyncButtons(on) {
    const lbl = 'Synchronization: ' + (on ? 'ON' : 'OFF');
    setText(E.btnSync, '🔒 ' + lbl);
    setCls(E.btnSync, 'btn toggle' + (on ? ' on' : ''));
    E.btnSync.setAttribute('aria-pressed', String(on));
    setText(E.btnSync2, lbl);
    setCls(E.btnSync2, 'btn toggle' + (on ? ' on' : ''));
    E.btnSync2.setAttribute('aria-pressed', String(on));
  }

  /* ---------- statistics ---------- */
  function renderStats(S) {
    const st = S.statistics;
    setText(E.mProduced, String(S.producer.produced));
    setText(E.mProcessed, String(st.processed));
    setText(E.mUsage, S.buffer.length + ' / ' + S.bufferCapacity);
    setText(E.mPWaits, String(S.producer.waitCount));
    setText(E.mCWaits, String(st.consumerWaits));
    setText(E.mRaces, String(st.raceConditions));
    setText(E.mLost, String(st.lost));
    setText(E.mAvg, st.processed ? (st.totalProcessingTime / st.processed / 1000).toFixed(1) + ' sec' : '—');
  }

  /* ---------- log + history ---------- */
  function renderLog(S) {
    const entries = S.log;
    if (!entries.length) return;
    const newest = entries[entries.length - 1].id;
    if (newest === lastLogId) return;
    const box = E.logBox;
    const atBottom = box.scrollHeight - box.scrollTop - box.clientHeight < 40;
    const frag = document.createDocumentFragment();
    entries.forEach(e => {
      if (e.id <= lastLogId) return;
      const row = document.createElement('div');
      row.className = 'log-row ' + e.cat;
      const t = document.createElement('time'); t.textContent = e.clock;
      const d = document.createElement('i'); d.className = 'd ' + e.cat;
      const s = document.createElement('span'); s.textContent = e.text;
      row.appendChild(t); row.appendChild(d); row.appendChild(s);
      frag.appendChild(row);
    });
    box.appendChild(frag);
    lastLogId = newest;
    while (box.children.length > LOG_MAX_DOM) box.removeChild(box.firstChild);
    if (atBottom) box.scrollTop = box.scrollHeight;
  }
  const LOG_MAX_DOM = 100;

  function renderHistory(S) {
    if (!S.history.length) { setHTML(E.historyList, '<li class="empty">No states yet. Press Start.</li>'); return; }
    let h = '';
    S.history.forEach((x, i) => {
      const meta = STATUS_META[x.label] || STATUS_META.IDLE;
      const now = i === S.history.length - 1;
      h += '<li class="' + meta.cls + (now ? ' now' : '') + '"><span aria-hidden="true">' + meta.icon + '</span>' + meta.label +
           (now ? '<em>now</em>' : '') + '</li>';
    });
    setHTML(E.historyList, h);
  }

  /* ---------- "What's happening?" ---------- */
  function renderWhy(S) {
    let t, term;
    switch (S.status) {
      case 'IDLE':
        t = 'Press START. The Producer (check-in) puts baggage on the conveyor, and the Consumers (sorting) take it off and load it onto aircraft.';
        term = 'Producer–Consumer: two groups of processes share one bounded buffer.'; break;
      case 'PAUSED':
        t = 'The simulation is paused. Nothing changes until you press START again.';
        term = 'All timers are stopped, so the state you see is exactly the state of the system.'; break;
      case 'RACE_CONDITION':
        t = 'Two Consumers are trying to access the same shared resource simultaneously. Without synchronization, this can cause inconsistent results.';
        term = 'Race condition: the result depends on the timing of unsynchronized access. Turn Synchronization ON to prevent it.'; break;
      case 'BUFFER_FULL':
        t = 'The buffer has reached its maximum capacity. The Producer must wait until a Consumer removes a baggage item.';
        term = 'The Producer blocks on the semaphore "empty" (empty = 0).'; break;
      case 'BUFFER_EMPTY':
        t = 'There are no baggage items available. Consumers must wait for the Producer.';
        term = 'Consumers block on the semaphore "full" (full = 0).'; break;
      case 'SYNCHRONIZED':
        t = 'The mutex allows only one Consumer to enter the critical section at a time.';
        term = 'Critical section = removing a bag from the shared buffer. Other Consumers show WAITING FOR MUTEX.'; break;
      case 'PRODUCING':
        t = 'The Producer is tagging and scanning a bag. It goes onto the conveyor as soon as a slot is free.';
        term = 'Producer: wait(empty), insert bag, signal(full).'; break;
      case 'CONSUMING':
        t = 'A Consumer is scanning and sorting a bag while the Producer keeps checking in new bags.';
        term = 'Sorting happens outside the critical section, so other Consumers are not blocked.'; break;
      default:
        t = 'The buffer has free slots and bags waiting. Producer and Consumers work at the same time.';
        term = 'Bounded buffer: empty slots + filled slots = capacity.';
    }
    if (S.started && !S.syncEnabled && S.status !== 'RACE_CONDITION' && S.status !== 'PAUSED') {
      term += ' Synchronization is OFF: two Consumers may grab the same bag.';
    }
    setText(E.whyText, t);
    setText(E.whyTerm, term);
  }

  function renderRunButtons(S) {
    const run = running();
    E.btnStart.disabled = run;
    setText(E.btnStart, S.started && S.paused ? '▶ Resume' : '▶ Start');
    E.btnPause.disabled = !run;
    const rush = S.rush.active;
    setText(E.btnRush, rush ? '🚨 Stop Flight Rush' : '🚨 Simulate Flight Rush');
    setText(E.btnLabRush, rush ? '🚨 Stop Flight Rush' : '🚨 Flight Rush');
    setText(E.btnRace, S.raceDemo ? '⚠ Race test armed…' : '⚠ Simulate Race Condition');
    E.tgProducer.setAttribute('aria-checked', String(S.producer.auto));
    E.tgConsumer.setAttribute('aria-checked', String(S.autoConsume));
  }

  function syncControlsFromState() {
    const S = sim.state;
    E.sliderProd.value = S.producer.speed;
    E.sliderCons.value = S.consumerSpeed;
    setText(E.sliderProdVal, speedLabel(S.producer.speed));
    setText(E.sliderConsVal, speedLabel(S.consumerSpeed));
    setSyncButtons(S.syncEnabled);
  }

  /* =============== animation hooks =============== */
  function relRect(el) {
    const r = el.getBoundingClientRect(), p = E.pipeline.getBoundingClientRect();
    return { left: r.left - p.left, top: r.top - p.top, width: r.width, height: r.height };
  }

  function onFx(ev) {
    if (REDUCED || !sim) return;
    try {
      if (ev.type === 'take') {
        const el = E.belt.querySelector('[data-bag="' + ev.bag + '"]');
        if (el) ev.from = relRect(el);
      } else if (ev.type === 'load') {
        const r = R.c[ev.consumer];
        const el = r && r.pcBag.querySelector('.bag');
        if (el) ev.from = relRect(el);
      }
    } catch (e) { /* animation is cosmetic only */ }
    if (fxQueue.length < 20) fxQueue.push(ev);
  }

  function flyer(html, from, to, ms) {
    if (!from || !to || from.width < 2 || E.fx.children.length > 8) return;
    const el = document.createElement('div');
    el.className = 'flyer';
    el.innerHTML = html;
    el.style.left = from.left + 'px';
    el.style.top = from.top + 'px';
    el.style.width = from.width + 'px';
    E.fx.appendChild(el);
    const dx = (to.left + to.width / 2) - (from.left + from.width / 2);
    const dy = (to.top + to.height / 2) - (from.top + from.height / 2);
    const a = el.animate([
      { transform: 'translate(0,0) scale(1)', opacity: 1 },
      { transform: 'translate(' + dx + 'px,' + dy + 'px) scale(.55)', opacity: 0.15 }
    ], { duration: ms, easing: 'ease-in-out' });
    const done = () => { if (el.parentNode) el.parentNode.removeChild(el); };
    a.onfinish = done; a.oncancel = done;
  }

  function processFx() {
    if (!fxQueue.length) return;
    const queue = fxQueue; fxQueue = [];
    if (REDUCED) return;
    const ms = Math.max(200, 650 / speedMult);
    queue.forEach(ev => {
      try {
        if (ev.type === 'take' && ev.from) {
          const r = R.c[ev.consumer];
          const target = r && r.pcBag;
          if (target) {
            const bagEl = target.querySelector('.bag');
            if (bagEl) bagEl.animate([{ opacity: 0 }, { opacity: 0, offset: 0.8 }, { opacity: 1 }], { duration: ms });
            flyer(bagHTML({ id: ev.bag, flight: '', dest: '', status: 'PROCESSING' }, true).replace('<div class="bag-fl"></div><div class="bag-dest"></div>', ''),
                  ev.from, relRect(target), ms);
          }
        } else if (ev.type === 'load' && ev.from) {
          flyer('<div class="bag mini s-loaded"><div class="bag-top"><span class="bag-ico">🧳</span><b>' + ev.bag + '</b></div><div class="bag-st"><i></i>LOADED</div></div>',
                ev.from, relRect(E.planeIcon), ms * 1.2);
          E.planeIcon.animate([{ transform: 'scale(1)' }, { transform: 'scale(1.18)' }, { transform: 'scale(1)' }], { duration: 380, delay: ms });
        }
      } catch (e) { /* cosmetic */ }
    });
  }

  /* two consumer paths converge on the contested bag */
  function renderRaceLines(S) {
    const svg = E.raceSvg;
    const active = S.consumers.filter(c => c.status === 'RACE_CONFLICT' && c.bag);
    if (!active.length || REDUCED) {
      if (svg._on) { svg.innerHTML = ''; svg._on = false; }
      return;
    }
    const bagEl = E.belt.querySelector('[data-bag="' + active[0].bag.id + '"]');
    if (!bagEl) { if (svg._on) { svg.innerHTML = ''; svg._on = false; } return; }
    const p = E.pipeline.getBoundingClientRect();
    svg.setAttribute('viewBox', '0 0 ' + p.width + ' ' + p.height);
    const b = relRect(bagEl);
    const bx = b.left + b.width / 2, by = b.top + b.height / 2;
    let h = '';
    active.forEach(c => {
      const r = relRect(R.c[c.id].pc);
      h += '<line class="race-line" x1="' + r.left + '" y1="' + (r.top + r.height / 2) + '" x2="' + bx + '" y2="' + by + '"/>';
    });
    h += '<circle class="race-ring" cx="' + bx + '" cy="' + by + '" r="34"/>';
    svg.innerHTML = h;
    svg._on = true;
  }

  /* =============== toast =============== */
  function toast(msg) {
    E.toast.textContent = msg;
    E.toast.classList.add('show');
    clearTimeout(toastTimer);
    toastTimer = setTimeout(() => E.toast.classList.remove('show'), 3200);
  }

  /* =============== Scenario Lab =============== */
  function labCfg() {
    return {
      capacity: parseInt(E.labCap.value, 10),
      producerSpeed: parseInt(E.labProd.value, 10),
      consumerSpeed: parseInt(E.labCons.value, 10),
      consumers: parseInt(E.labN.value, 10),
      sync: E.labSync.value === 'on'
    };
  }
  function setLabFromCfg(c) {
    E.labCap.value = String(c.capacity);
    E.labProd.value = String(c.producerSpeed);
    E.labCons.value = String(c.consumerSpeed);
    E.labN.value = String(c.consumers);
    E.labSync.value = c.sync ? 'on' : 'off';
  }

  function cfgSummary(c) {
    return 'capacity ' + c.capacity + ', producer ' + speedLabel(c.producerSpeed) + ', consumers ' + c.consumers +
           ' × ' + speedLabel(c.consumerSpeed) + ', sync ' + (c.sync ? 'ON' : 'OFF');
  }

  function showPrediction(pred, mode, title) {
    const tag = mode === 'preview' ? 'Preview' : mode === 'running' ? 'Running' : 'Completed';
    setHTML(E.predBox,
      '<div class="lab-card-head"><h3>SYSTEM PREDICTION</h3><span class="tag ' + mode + '">' + tag + '</span></div>' +
      '<p class="pred-title">' + title + '</p>' +
      pred.lines.map(l => '<p class="pred-line">' + l + '</p>').join('') +
      '<p class="pred-rates">Producer rate ≈ <b>' + pred.lambda.toFixed(2) + '</b> bags/s · Consumer capacity ≈ <b>' + pred.mu.toFixed(2) + '</b> bags/s</p>');
  }

  function clearLabResults() {
    E.resultBox.hidden = true; E.resultBox.innerHTML = ''; E.resultBox._h = '';
    E.compareBox.hidden = true; E.compareBox.innerHTML = ''; E.compareBox._h = '';
  }

  function runExperiment(cfg, name, expectText) {
    clearLabResults();
    const pred = predict(cfg);
    newSim(cfg);
    sim.state.scenario = { active: true, name: name };
    sim.note('Scenario: ' + name + ' (' + cfgSummary(cfg) + ')', 'scenario');
    exp = { name: name, cfg: cfg, pred: pred, done: false, duration: EXP_SECONDS * 1000 };
    showPrediction(pred, 'running', name + (expectText ? ' · Expected: ' + expectText : ''));
    speedMult = 4;
    updateSpeedUI();
    doStart();
    toast('Experiment "' + name + '" running for ' + EXP_SECONDS + ' simulated seconds at 4×.');
  }

  function checkExperiment() {
    if (exp && !exp.done && sim.state.time >= exp.duration) finishExperiment();
  }

  function finishExperiment() {
    exp.done = true;
    const S = sim.state;
    S.scenario.active = false;
    sim.note('Experiment "' + exp.name + '" complete', 'scenario');
    const snap = sim.snapshot();
    sim.pause();
    stopLoop();
    showPrediction(exp.pred, 'done', exp.name);
    showResult(exp, snap);
    render();
    E.resultBox.scrollIntoView({ block: 'nearest', behavior: REDUCED ? 'auto' : 'smooth' });
    toast('Experiment complete. See the result table in the Scenario Lab.');
  }

  function verdict(ok) { return ok === true ? '<span class="vd ok">✓</span>' : ok === 'near' ? '<span class="vd near">≈</span>' : ok === 'na' ? '<span class="vd na">~</span>' : '<span class="vd bad">✗</span>'; }
  const LV = { LOW: 0, MEDIUM: 1, HIGH: 2 };
  function levelMatch(p, a) { const d = Math.abs(LV[p] - LV[a]); return d === 0 ? true : d === 1 ? 'near' : false; }

  function showResult(ex, snap) {
    const p = ex.pred;
    const pwA = levelProducerWait(snap), cwA = levelConsumerWait(snap);
    const fullA = snap.fullEvents > 0;
    const fullOk = p.full === 'MAYBE' ? 'na' : (p.full === 'YES') === fullA;
    const raceOk = p.race === 'NONE' ? snap.races === 0 : snap.races > 0;
    const rows = [
      ['Buffer reaches FULL', p.full, fullA ? 'YES (' + snap.fullEvents + '×)' : 'NO', fullOk],
      ['Producer wait', p.producerWait, snap.producerWaits + ' (' + pwA + ')', levelMatch(p.producerWait, pwA)],
      ['Consumer wait', p.consumerWait, snap.consumerWaits + ' (' + cwA + ')', levelMatch(p.consumerWait, cwA)],
      ['Race conditions', p.race, String(snap.races), raceOk]
    ];
    let h = '<div class="lab-card-head"><h3>EXPERIMENT RESULT</h3><span class="tag done">' + EXP_SECONDS + ' s simulated</span></div>' +
            '<p class="pred-title">' + ex.name + ' · ' + cfgSummary(ex.cfg) + '</p>' +
            '<div class="table-wrap"><table class="res"><thead><tr><th scope="col"></th><th scope="col">PREDICTED</th><th scope="col">ACTUAL</th><th scope="col"><span class="sr-only">Match</span></th></tr></thead><tbody>';
    rows.forEach(r => { h += '<tr><th scope="row">' + r[0] + '</th><td>' + r[1] + '</td><td>' + r[2] + '</td><td>' + verdict(r[3]) + '</td></tr>'; });
    h += '</tbody></table></div>' +
         '<dl class="res-sum">' +
         '<div><dt>Bags produced</dt><dd>' + snap.produced + '</dd></div>' +
         '<div><dt>Bags processed</dt><dd>' + snap.processed + '</dd></div>' +
         '<div><dt>Lost to races</dt><dd>' + snap.lost + '</dd></div>' +
         '<div><dt>Max buffer used</dt><dd>' + snap.maxBuffer + ' / ' + snap.capacity + '</dd></div>' +
         '<div><dt>Avg processing</dt><dd>' + (snap.processed ? snap.avgProc.toFixed(1) + ' s' : '—') + '</dd></div>' +
         '</dl>' +
         '<p class="hint">✓ prediction matched · ≈ one level off · ~ either outcome was plausible · ✗ prediction missed. Figures come from this simulation run, not from random numbers.</p>';
    E.resultBox.hidden = false;
    setHTML(E.resultBox, h);
  }

  function renderExperimentProgress(S) {
    const show = !!(exp && !exp.done);
    setHidden(E.expWrap, !show);
    if (!show) return;
    const secs = Math.min(EXP_SECONDS, Math.floor(S.time / 1000));
    setText(E.expText, '🧪 ' + exp.name + ': ' + secs + ' / ' + EXP_SECONDS + ' s');
    setWidth(E.expBar, Math.min(100, S.time / exp.duration * 100));
  }

  /* ---------- compare mode ---------- */
  function runCompare() {
    const base = labCfg();
    const mode = E.cmpMode.value;
    let A, B, nameA, nameB, title;
    if (mode === 'sync') {
      A = Object.assign({}, base, { sync: false }); B = Object.assign({}, base, { sync: true });
      nameA = 'No Synchronization'; nameB = 'Mutex Enabled'; title = 'Synchronization OFF vs ON';
    } else if (mode === 'consumers') {
      const a = base.consumers >= 4 ? 3 : base.consumers, b = a + 1;
      A = Object.assign({}, base, { consumers: a }); B = Object.assign({}, base, { consumers: b });
      nameA = a + (a === 1 ? ' consumer' : ' consumers'); nameB = b + ' consumers'; title = 'Fewer vs more consumers';
    } else {
      const a = Math.max(2, Math.round(base.capacity / 2)), b = Math.min(10, base.capacity * 2);
      A = Object.assign({}, base, { capacity: a }); B = Object.assign({}, base, { capacity: b });
      nameA = 'Buffer of ' + a; nameB = 'Buffer of ' + b; title = 'Small vs large buffer';
    }
    const seed = (Date.now() & 0x7fffffff) >>> 0;           // same workload for both systems
    A.seed = seed; B.seed = seed;
    const ra = runHeadless(A, EXP_SECONDS), rb = runHeadless(B, EXP_SECONDS);

    const metrics = [
      ['Bags produced', 'produced', 'high'],
      ['Bags processed', 'processed', 'high'],
      ['Bags lost to races', 'lost', 'low'],
      ['Race conditions', 'races', 'low'],
      ['Producer waits', 'producerWaits', 'low'],
      ['Consumer waits', 'consumerWaits', 'low'],
      ['Max buffer used', 'maxBuffer', null],
      ['Avg processing time', 'avgProc', null]
    ];
    const fmt = (k, v) => k === 'avgProc' ? (v ? v.toFixed(1) + ' s' : '—') : String(v);
    let rows = '';
    metrics.forEach(m => {
      const a = ra[m[1]], b = rb[m[1]];
      let ca = '', cb = '';
      if (m[2] && a !== b) {
        const aBetter = m[2] === 'high' ? a > b : a < b;
        if (aBetter) ca = ' class="best"'; else cb = ' class="best"';
      }
      rows += '<tr><th scope="row">' + m[0] + '</th><td' + ca + '>' + fmt(m[1], a) + '</td><td' + cb + '>' + fmt(m[1], b) + '</td></tr>';
    });

    const lines = [];
    const dProc = rb.processed - ra.processed;
    if (dProc !== 0) lines.push('System ' + (dProc > 0 ? 'B' : 'A') + ' processed ' + Math.abs(dProc) + ' more bag' + (Math.abs(dProc) === 1 ? '' : 's') + '.');
    else lines.push('Both systems processed the same number of bags.');
    if (ra.races !== rb.races) lines.push('Race conditions: ' + ra.races + ' in System A vs ' + rb.races + ' in System B.');
    if (ra.producerWaits !== rb.producerWaits) lines.push('Producer waits: ' + ra.producerWaits + ' in A vs ' + rb.producerWaits + ' in B.');
    if (mode === 'sync') lines.push('Synchronization trades a little waiting (mutex queue: ' + rb.mutexWaits + ' waits) for correct results.');

    const h = '<div class="lab-card-head"><h3>⚔ COMPARE SYSTEMS</h3><span class="tag done">' + EXP_SECONDS + ' s each</span></div>' +
      '<p class="pred-title">' + title + ' · same workload · ' + cfgSummary(base) + '</p>' +
      '<div class="table-wrap"><table class="res cmp"><thead><tr><th scope="col"></th>' +
      '<th scope="col">SYSTEM A<small>' + nameA + '</small></th><th scope="col">SYSTEM B<small>' + nameB + '</small></th></tr></thead><tbody>' + rows + '</tbody></table></div>' +
      '<p class="pred-line"><b>What changed?</b> ' + lines.join(' ') + '</p>' +
      '<p class="hint">Both systems were really simulated with the same random seed. Highlighted cells are the better value.</p>';
    E.compareBox.hidden = false;
    setHTML(E.compareBox, h);
    sim.note('Compare Systems: ' + title + ' → A processed ' + ra.processed + ', B processed ' + rb.processed, 'scenario');
    E.compareBox.scrollIntoView({ block: 'nearest', behavior: REDUCED ? 'auto' : 'smooth' });
  }

  function renderPresetButtons() {
    let h = '';
    Object.keys(PRESETS).forEach(k => {
      const p = PRESETS[k];
      h += '<button type="button" class="preset" data-preset="' + k + '" aria-pressed="' + (activePreset === k) + '">' +
             '<span class="preset-name">' + p.icon + ' ' + p.name + '</span>' +
             '<span class="preset-desc">' + p.desc + '</span>' +
             '<span class="preset-exp">' + p.expect + '</span></button>';
    });
    setHTML(E.presetGrid, h);
  }

  function applyPreset(key) {
    const p = PRESETS[key];
    activePreset = key;
    setLabFromCfg(p.cfg);
    renderPresetButtons();
    runExperiment(Object.assign({}, p.cfg), p.name, p.expect);
  }

  function labPreview() {
    activePreset = null;
    renderPresetButtons();
    if (exp && !exp.done) return;
    showPrediction(predict(labCfg()), 'preview', 'Current lab settings: ' + cfgSummary(labCfg()));
  }

  /* =============== wiring =============== */
  function toggleRush() {
    if (!ensureRunning()) return;
    const S = sim.state;
    if (S.rush.active) { sim.stopRush(); toast('Flight rush stopped.'); }
    else { sim.startRush(); toast('Flight rush: check-in rate ×3 for 20 simulated seconds.'); }
    render();
  }

  function setSyncFromUI(on) {
    sim.setSync(on);
    render();
    toast(on ? 'Synchronization ON: the mutex protects the buffer.' : 'Synchronization OFF: race conditions can now occur.');
  }

  function init() {
    [
      'logBox', 'hdrStatus', 'hdrSpeed', 'hdrReset', 'stateGrid', 'statePill', 'stateIcon', 'stateLabel', 'stateCaption',
      'bannerArea', 'btnStart', 'btnPause', 'btnReset', 'btnSync', 'btnRace', 'btnRush', 'btnViva', 'pipeline',
      'stProducer', 'pQueue', 'pScan', 'pBagSlot', 'pStatusChip', 'pNote', 'bCount', 'beltWrap', 'belt', 'lockBadge',
      'bufAlert', 'pipeConsumers', 'loadedTotal', 'flightChips', 'planeIcon', 'raceSvg', 'ppStatus', 'ppProduced',
      'ppSpeed', 'ppWaiting', 'ppAlert', 'btnAdd', 'tgProducer', 'sliderProd', 'sliderProdVal', 'bpUsed', 'bpCap',
      'bpMeter', 'bpOcc', 'bpFree', 'bpState', 'bpAlert', 'tgConsumer', 'sliderCons', 'sliderConsVal', 'cPanelList',
      'btnSync2', 'mxLockBox', 'mxIcon', 'mxState', 'mxVal', 'mxOwner', 'mxWaiting', 'semEmpty', 'semFull', 'mxSteps',
      'mxNote', 'mProduced', 'mProcessed', 'mUsage', 'mPWaits', 'mCWaits', 'mRaces', 'mLost', 'mAvg', 'labCap',
      'labProd', 'labCons', 'labN', 'labSync', 'btnRun', 'btnLabRush', 'presetGrid', 'cmpMode', 'btnCompare', 'predBox',
      'resultBox', 'compareBox', 'historyList', 'whyText', 'whyTerm', 'vivaDialog', 'btnVivaClose', 'toast'
    ].forEach(id => { E[id] = $(id); });
    E.fx = $('fxLayer');
    E.expWrap = $('expProgressWrap'); E.expText = $('expProgressText'); E.expBar = $('expProgressBar');

    // capacity options 2..10
    let opts = '';
    for (let i = 2; i <= 10; i++) opts += '<option value="' + i + '"' + (i === DEFAULT_CFG.capacity ? ' selected' : '') + '>' + i + '</option>';
    E.labCap.innerHTML = opts;
    setLabFromCfg(DEFAULT_CFG);
    renderPresetButtons();

    // control bar
    E.btnStart.addEventListener('click', doStart);
    E.btnPause.addEventListener('click', doPause);
    E.btnReset.addEventListener('click', resetAll);
    E.hdrReset.addEventListener('click', resetAll);
    document.querySelectorAll('.seg-btn').forEach(b => b.addEventListener('click', () => setSpeed(parseFloat(b.dataset.speed))));
    E.hdrSpeed.addEventListener('click', () => {
      const order = [0.5, 1, 2, 4];
      setSpeed(order[(order.indexOf(speedMult) + 1) % order.length]);
    });
    E.btnSync.addEventListener('click', () => setSyncFromUI(!sim.state.syncEnabled));
    E.btnSync2.addEventListener('click', () => setSyncFromUI(!sim.state.syncEnabled));
    E.btnRace.addEventListener('click', () => {
      if (!ensureRunning()) return;
      const r = sim.simulateRace();
      toast(r.ok ? 'Race test armed: both consumers will reach for the same bag.' : r.msg);
      render();
    });
    E.btnRush.addEventListener('click', toggleRush);
    E.btnLabRush.addEventListener('click', toggleRush);
    E.btnViva.addEventListener('click', () => {
      if (typeof E.vivaDialog.showModal === 'function') { if (!E.vivaDialog.open) E.vivaDialog.showModal(); }
      else E.vivaDialog.setAttribute('open', '');
    });
    E.btnVivaClose.addEventListener('click', () => {
      if (typeof E.vivaDialog.close === 'function') E.vivaDialog.close(); else E.vivaDialog.removeAttribute('open');
    });
    E.vivaDialog.addEventListener('click', ev => { if (ev.target === E.vivaDialog && E.vivaDialog.close) E.vivaDialog.close(); });

    // producer
    E.btnAdd.addEventListener('click', () => {
      if (!ensureRunning()) return;
      const r = sim.addBaggage();
      if (!r.ok) toast(r.msg);
      else if (r.full) toast('Buffer is full: the Producer must wait for a free slot.');
      render();
    });
    E.tgProducer.addEventListener('click', () => {
      sim.setProducerAuto(!sim.state.producer.auto);
      toast('Auto Produce ' + (sim.state.producer.auto ? 'ON' : 'OFF'));
      render();
    });
    E.sliderProd.addEventListener('input', () => {
      const v = parseInt(E.sliderProd.value, 10);
      sim.setProducerSpeed(v); setText(E.sliderProdVal, speedLabel(v)); render();
    });

    // consumers
    E.tgConsumer.addEventListener('click', () => {
      sim.setAutoConsume(!sim.state.autoConsume);
      toast('Auto Consume ' + (sim.state.autoConsume ? 'ON' : 'OFF'));
      render();
    });
    E.sliderCons.addEventListener('input', () => {
      const v = parseInt(E.sliderCons.value, 10);
      sim.setConsumerSpeed(v); setText(E.sliderConsVal, speedLabel(v)); render();
    });
    E.cPanelList.addEventListener('click', ev => {
      const btn = ev.target.closest('button[data-act="consume"]');
      if (!btn) return;
      if (!ensureRunning()) return;
      const r = sim.consume(parseInt(btn.dataset.id, 10));
      if (!r.ok) toast(r.msg);
      else if (r.empty) toast('Buffer is empty: this consumer will wait for the Producer.');
      render();
    });

    // scenario lab
    ['labCap', 'labProd', 'labCons', 'labN', 'labSync'].forEach(id => E[id].addEventListener('change', labPreview));
    E.btnRun.addEventListener('click', () => { activePreset = null; renderPresetButtons(); runExperiment(labCfg(), 'Custom experiment', ''); });
    E.btnCompare.addEventListener('click', runCompare);
    E.presetGrid.addEventListener('click', ev => {
      const b = ev.target.closest('button[data-preset]');
      if (b) applyPreset(b.dataset.preset);
    });

    // keyboard: Space pauses/resumes unless a control has focus
    document.addEventListener('keydown', ev => {
      if (ev.key !== ' ' || ev.target !== document.body) return;
      ev.preventDefault();
      if (running()) doPause(); else doStart();
    });

    newSim(DEFAULT_CFG);
    updateSpeedUI();
    showPrediction(predict(DEFAULT_CFG), 'preview', 'Current lab settings: ' + cfgSummary(DEFAULT_CFG));
  }

  init();
})();
}
