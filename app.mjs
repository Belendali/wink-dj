// Wink Wink — wink-controlled rhythm game. Greybox v1.
const $ = (id) => document.getElementById(id);
const video = $('cam'), canvas = $('scene'), ctx = canvas.getContext('2d');
const W = 390; let H = 693, DPR = 1;
const BPM = 80, BEAT = 60 / BPM, SONG = 15, LEAD = 2.0;
const PERFECT = 0.28, GOOD = 0.6; // generous: a wink is slower than a tap
const BOOTH_W = W * 1.12, BOOTH_S = BOOTH_W / 900; // booth image is 900 px wide; platters at (238,677) and (662,677), table bottom at 830
const BOOTH_TOP = () => H * 0.67 - 575 * BOOTH_S; // table top at 63% so the platters (the interaction) sit inside TikTok's core zone (y ≤ 533/694)
const LANE_X = [(W - BOOTH_W) / 2 + 238 * BOOTH_S, (W - BOOTH_W) / 2 + 662 * BOOTH_S]; let HIT_Y = 0.88; // judge line: a whole character at the hit moment stays inside the visual zone (y ≤ 545/694)

let mode = 'idle'; // idle | setup | countdown | playing | result
let practice = false, bothMode = false;
let notes = [], effects = [], startAt = 0, songTime = 0;
let stats = { perfect: 0, good: 0, miss: 0, combo: 0, maxCombo: 0, score: 0 };
let landmarker = null, stream = null, lastVideoTime = -1;
let eye = { L: false, R: false, both: false, pendingAt: 0, armed: true };
let blinkStats = { both: 0, single: 0 }; // auto fallback: only double blinks → both-eyes mode
let faceBest = null, faceWorst = null, confetti = [], confettiAt = 0, pile = [], resultAt = 0, showcase = [], showIdx = 0, showAt = 0, crowdFinal = 'good';
let audioCtx = null, schedulerId = 0, nextBeat = 0, beatIndex = 0;

// ---------- people (one walk image + reaction images per character) ----------
const PEOPLE = Array.from({ length: 10 }, (_, i) => { const n = String(i + 1).padStart(2, '0'); return { wait: `assets/people/p${n}-wait.png`, good: `assets/people/p${n}-good.png`, bad: `assets/people/p${n}-bad.png` }; });
const BOOTH = 'assets/booth/booth.png', HAND = ['assets/booth/hand-left.png', 'assets/booth/hand-right.png'];
const NOTE = ['assets/stickers/note-pink.png', 'assets/stickers/note-cyan.png', 'assets/stickers/note-record.png'];
const STICKER = { glasses: 'assets/stickers/sunglasses.png', chain: 'assets/stickers/chain.png', frustrated: 'assets/stickers/frustrated.png' };
const IMG = {};
function loadImg(src) { if (IMG[src]) return IMG[src]; const i = new Image(); i.src = src; IMG[src] = i; return i; }
PEOPLE.forEach((p) => Object.values(p).forEach(loadImg)); loadImg(BOOTH); HAND.forEach(loadImg); NOTE.forEach(loadImg); Object.values(STICKER).forEach(loadImg);
function img(src, x, y, w, opts = {}) { const i = loadImg(src); if (!ready(src)) return false; const h = w * i.naturalHeight / i.naturalWidth; ctx.save(); ctx.translate(x, y); ctx.rotate(opts.rot || 0); ctx.globalAlpha = opts.alpha ?? 1; ctx.drawImage(i, -w / 2, -h * (opts.ay ?? 0.5), w, h); ctx.restore(); return true; }
const ready = (src) => { const i = IMG[src]; return i && i.complete && i.naturalWidth > 0; };
const PERSON_H = 150;
function sprite(src, x, baseY, opts = {}) {
  const img = loadImg(src); if (!ready(src)) return false;
  const h = PERSON_H * (opts.scale || 1), w = h * img.naturalWidth / img.naturalHeight;
  ctx.save(); ctx.translate(x, baseY); ctx.rotate(opts.rot || 0); ctx.globalAlpha = opts.alpha ?? 1;
  ctx.drawImage(img, -w / 2, -h, w, h); ctx.restore(); return true;
}

// ---------- sizing ----------
function resize() {
  const r = $('phone').getBoundingClientRect();
  DPR = Math.min(2, window.devicePixelRatio || 1);
  H = Math.round(W * r.height / r.width); HIT_Y = (BOOTH_TOP() + 677 * BOOTH_S) / H; // platter centres
  $('phone').style.setProperty('--band-top', ((BOOTH_TOP() + 800 * BOOTH_S) / H * 100).toFixed(1) + '%');
  canvas.width = W * DPR; canvas.height = H * DPR;
  ctx.setTransform(DPR, 0, 0, DPR, 0, 0);
}
window.addEventListener('resize', resize); resize();

// ---------- audio (synthesized) ----------
function ensureAudio() { if (!audioCtx) audioCtx = new (window.AudioContext || window.webkitAudioContext)(); if (audioCtx.state === 'suspended') audioCtx.resume(); }
function tone(freq, t, dur, type = 'sine', gain = 0.2, slide = 0) {
  const o = audioCtx.createOscillator(), g = audioCtx.createGain();
  o.type = type; o.frequency.setValueAtTime(freq, t); if (slide) o.frequency.exponentialRampToValueAtTime(slide, t + dur);
  g.gain.setValueAtTime(gain, t); g.gain.exponentialRampToValueAtTime(0.001, t + dur);
  o.connect(g).connect(audioCtx.destination); o.start(t); o.stop(t + dur + 0.02);
}
let noiseBuf = null;
function noise(t, dur, gain = 0.08) {
  if (!noiseBuf) { noiseBuf = audioCtx.createBuffer(1, audioCtx.sampleRate, audioCtx.sampleRate); const d = noiseBuf.getChannelData(0); for (let i = 0; i < d.length; i++) d[i] = Math.random() * 2 - 1; }
  const s = audioCtx.createBufferSource(), g = audioCtx.createGain(), f = audioCtx.createBiquadFilter();
  f.type = 'highpass'; f.frequency.value = 6000; s.buffer = noiseBuf; g.gain.setValueAtTime(gain, t); g.gain.exponentialRampToValueAtTime(0.001, t + dur);
  s.connect(f).connect(g).connect(audioCtx.destination); s.start(t); s.stop(t + dur + 0.01);
}
const BASS = [55, 0, 55, 82, 0, 55, 73, 98];          // per 8th note, two beats
const CHORDS = [[262, 330, 392], [294, 349, 440], [330, 392, 494], [294, 349, 440]];
const MELODY = [523, 0, 659, 784, 0, 659, 587, 0, 523, 659, 0, 784, 880, 0, 784, 659, 587, 0, 523, 0, 659, 0, 523, 0, 587, 659, 0, 587, 523, 0, 0, 0];
function scheduleBeats() {
  const now = audioCtx.currentTime, step = BEAT / 4; // 16th notes
  while (nextBeat < now + 0.25) {
    const i = beatIndex, beat = Math.floor(i / 4), sub = ((i % 4) + 4) % 4, eighth = Math.floor(i / 2);
    if (i < 0) { if (sub === 0) tone(150, nextBeat, 0.16, 'sine', 0.5, 40); noise(nextBeat, 0.04, 0.05); nextBeat += step; beatIndex++; continue; } // count-in: kick + hats only
    if (sub === 0) tone(150, nextBeat, 0.16, 'sine', 0.7, 40);                        // kick on every beat
    if (sub === 0 && beat % 2 === 1) { noise(nextBeat, 0.14, 0.26); tone(180, nextBeat, 0.08, 'triangle', 0.22); } // snare on 2 and 4
    noise(nextBeat, sub % 2 ? 0.03 : 0.05, sub === 2 ? 0.13 : 0.07);                 // 16th hats, open on the offbeat
    if (sub % 2 === 0) { const bnote = BASS[eighth % 8]; if (bnote) tone(bnote, nextBeat, step * 1.6, 'square', 0.11); }
    if (sub === 2 && beat % 2 === 0) CHORDS[Math.floor(beat / 2) % 4].forEach((f) => tone(f, nextBeat, 0.12, 'sawtooth', 0.025)); // offbeat stab
    if (sub % 2 === 0) { const m = MELODY[eighth % 32]; if (m) tone(m, nextBeat, 0.22, 'triangle', 0.05); }
    nextBeat += step; beatIndex++;
  }
  schedulerId = setTimeout(scheduleBeats, 60);
}
// hits are musical: every hit plays the next step of a riff, so a streak becomes a melody
const RIFF = [523, 659, 784, 880, 784, 659, 1047, 880, 784, 659, 587, 523];
function hitSound(lane, big) {
  if (!audioCtx) return; const t = audioCtx.currentTime, f = RIFF[riff++ % RIFF.length];
  if (lane === 2) { [f, f * 1.25, f * 1.5].forEach((x, i) => tone(x, t + i * 0.03, 0.5, 'sawtooth', 0.09)); tone(f / 4, t, 0.6, 'square', 0.12); } // the drop: a chord + sub
  else { tone(f * (lane ? 1 : 0.5), t, big ? 0.45 : 0.28, lane ? 'triangle' : 'square', big ? 0.22 : 0.16); tone(f * (lane ? 2 : 1), t + 0.02, 0.2, 'sine', 0.08); }
  if (big) [f * 2, f * 3].forEach((x, i) => tone(x, t + 0.12 + i * 0.05, 0.25, 'sine', 0.06));
  cheer(big);
}
function cheer(big = false) { // a short noisy "whoo" from the crowd
  const t = audioCtx.currentTime, dur = big ? 0.6 : 0.35;
  if (!noiseBuf) noise(t, 0.01, 0);
  const n = audioCtx.createBufferSource(); n.buffer = noiseBuf; const f = audioCtx.createBiquadFilter(); f.type = 'bandpass'; f.frequency.setValueAtTime(600, t); f.frequency.exponentialRampToValueAtTime(big ? 2200 : 1400, t + dur); f.Q.value = 1.4;
  const g = audioCtx.createGain(); g.gain.setValueAtTime(0.0001, t); g.gain.exponentialRampToValueAtTime(big ? 0.3 : 0.16, t + 0.06); g.gain.exponentialRampToValueAtTime(0.0001, t + dur);
  n.connect(f).connect(g).connect(audioCtx.destination); n.start(t); n.stop(t + dur + 0.02);
}
function roar() { // end-of-round crowd cheer: a long rising whoo with a few voices and a whistle
  if (!audioCtx) return; const t = audioCtx.currentTime;
  if (!noiseBuf) noise(t, 0.01, 0);
  for (let v = 0; v < 3; v++) { const n = audioCtx.createBufferSource(); n.buffer = noiseBuf; const f = audioCtx.createBiquadFilter(); f.type = 'bandpass'; f.frequency.setValueAtTime(500 + v * 200, t); f.frequency.exponentialRampToValueAtTime(2200 + v * 400, t + 1.2); f.Q.value = 1.1; const g = audioCtx.createGain(); g.gain.setValueAtTime(0.0001, t + v * 0.08); g.gain.exponentialRampToValueAtTime(0.28, t + 0.25 + v * 0.08); g.gain.setValueAtTime(0.28, t + 0.9); g.gain.exponentialRampToValueAtTime(0.0001, t + 1.6); n.connect(f).connect(g).connect(audioCtx.destination); n.start(t); n.stop(t + 1.7); }
  [523, 659, 784, 1047, 1319].forEach((fr, i) => tone(fr, t + 0.1 + i * 0.09, 0.5, 'triangle', 0.1));
  tone(2200, t + 0.5, 0.35, 'sine', 0.08, 3200); tone(3200, t + 0.85, 0.3, 'sine', 0.06, 2400); // whistle
}
function scratch() { // miss: a record scratch and a low boo
  if (!audioCtx) return; const t = audioCtx.currentTime; riff = Math.max(0, riff - 2);
  if (!noiseBuf) noise(t, 0.01, 0);
  const n = audioCtx.createBufferSource(); n.buffer = noiseBuf; n.playbackRate.setValueAtTime(1.6, t); n.playbackRate.exponentialRampToValueAtTime(0.25, t + 0.3);
  const f = audioCtx.createBiquadFilter(); f.type = 'bandpass'; f.frequency.setValueAtTime(3000, t); f.frequency.exponentialRampToValueAtTime(300, t + 0.3); f.Q.value = 2;
  const g = audioCtx.createGain(); g.gain.setValueAtTime(0.3, t); g.gain.exponentialRampToValueAtTime(0.001, t + 0.32); n.connect(f).connect(g).connect(audioCtx.destination); n.start(t); n.stop(t + 0.35);
  [110, 92].forEach((fr, i) => tone(fr, t + 0.1 + i * 0.05, 0.5, 'sawtooth', 0.07, fr * 0.8));
}
function sfx(kind) {
  if (!audioCtx) return; const t = audioCtx.currentTime;
  if (kind === 'perfect' || kind === 'good' || kind === 'miss') return; // handled by hitSound / scratch
  if (kind === 'count') tone(660, t, 0.1, 'square', 0.12);
  if (kind === 'land') { tone(120, t, 0.08, 'sine', 0.2, 60); noise(t, 0.04, 0.05); }
  if (kind === 'go') tone(990, t, 0.3, 'square', 0.14);
  if (kind === 'win') [523, 659, 784, 1047].forEach((f, i) => tone(f, t + i * 0.12, 0.4, 'triangle', 0.16));
}

// ---------- chart ----------
function makeChart() {
  const list = []; let seed = Math.floor(Math.random() * 233280); const rnd = () => (seed = (seed * 9301 + 49297) % 233280) / 233280; // fresh pattern every round
  const beats = Math.floor(SONG / BEAT);
  let lane = 0, lastDouble = -9;
  for (let b = 4; b < beats - 1; b++) {
    const t = b * BEAT;
    if (b < 14 && b % 2) continue;                                                     // first half: one pedestrian every two beats, time to enjoy the swoon
    if (b % 8 === 6) { list.push({ t, lane: 2 }); continue; }                          // a couple every 8 beats: both eyes
    if (b >= 16 && b - lastDouble > 4 && rnd() < 0.25) { lastDouble = b; list.push({ t, lane }); lane = 1 - lane; list.push({ t: t + BEAT / 2, lane }); lane = 1 - lane; continue; }
    if (rnd() < 0.65) lane = 1 - lane;
    list.push({ t, lane });
  }
  // casting: a shuffled deck of all ten, dealt without replacement, reshuffled when empty (no one repeats until everyone has walked by)
  let deck = [];
  const deal = (avoid) => { if (!deck.length) { deck = PEOPLE.map((_, i) => i); for (let i = deck.length - 1; i > 0; i--) { const j = Math.floor(rnd() * (i + 1)); [deck[i], deck[j]] = [deck[j], deck[i]]; } if (deck[deck.length - 1] === avoid && deck.length > 1) [deck[0], deck[deck.length - 1]] = [deck[deck.length - 1], deck[0]]; } return deck.pop(); };
  let prev = -1;
  return list.map((n, i) => { const who = deal(prev); const who2 = n.lane === 2 ? deal(who) : who; prev = who2; return { ...n, id: i, hit: null, who, who2 }; });
}

// ---------- flow ----------
function show(id, on = true) { $(id).classList.toggle('hidden', !on); }
function setMode(m) { mode = m; $('phone').classList.toggle('setup', m === 'setup'); $('phone').classList.toggle('howto', m === 'howto'); show('startPanel', m === 'idle'); show('setupPanel', m === 'setup'); show('hud', ['playing', 'countdown', 'setup', 'howto'].includes(m)); show('resultPanel', m === 'result'); show('countdown', m === 'countdown'); show('howto', m === 'howto'); }

$('play').onclick = () => { ensureAudio(); practice = false; $('phone').classList.remove('practice'); startSetup(); };
$('practice').onclick = () => { ensureAudio(); practice = true; $('phone').classList.add('practice'); bothMode = false; stopCamera(); beginCountdown(); };
$('startRound').onclick = () => beginCountdown();
$('bothMode').onclick = () => { bothMode = true; beginCountdown(); };
$('replay').onclick = () => showHowto();
$('home').onclick = () => { clearTimeout(beginCountdown.t); clearTimeout(endRound.t); stopCamera(); setMode('idle'); };

async function startSetup() {
  setMode('setup'); show('calib', false); show('startRound', false); show('bothMode', false);
  $('setupKicker').textContent = 'CAMERA'; $('setupTitle').textContent = 'Loading the face tracker…'; $('setupText').textContent = 'One second.';
  try {
    await Promise.all([loadLandmarker(), startCamera()]);
  } catch (e) {
    $('setupTitle').textContent = 'Camera blocked'; $('setupText').textContent = 'Allow the camera in your browser, then reload. Or try tap practice.'; return;
  }
  $('setupTitle').textContent = 'Looking for your face…'; $('setupText').textContent = 'Hold the phone at arm\'s length.';
  bothMode = false; blinkStats = { both: 0, single: 0 };
  const started = performance.now();
  const wait = setInterval(() => { if (mode !== 'setup') { clearInterval(wait); return; } if (performance.now() - faceAt < 300 || performance.now() - started > 8000) { clearInterval(wait); showHowto(); } }, 100);
}
async function loadLandmarker() {
  if (landmarker) return;
  const { FilesetResolver, FaceLandmarker } = await import('./vendor/vision_bundle.mjs');
  const fileset = await FilesetResolver.forVisionTasks('./vendor/wasm');
  landmarker = await FaceLandmarker.createFromOptions(fileset, { baseOptions: { modelAssetPath: './vendor/face_landmarker.task' }, runningMode: 'VIDEO', numFaces: 1, outputFaceBlendshapes: true });
}
async function startCamera() {
  if (stream) return;
  stream = await navigator.mediaDevices.getUserMedia({ video: { facingMode: 'user', width: { ideal: 720 }, height: { ideal: 1280 } }, audio: false });
  video.srcObject = stream; await video.play();
}
function stopCamera() { if (stream) { stream.getTracks().forEach((t) => t.stop()); stream = null; video.srcObject = null; } }

function showHowto() {
  ensureAudio(); setMode('howto'); clearTimeout(beginCountdown.t);
  $('howtoCta').textContent = practice ? 'Starting…' : 'Blink to start';
  if (practice) beginCountdown.t = setTimeout(startCountdown, 2000);   // no camera: just wait
  // camera: the first detected blink starts the round, which also proves tracking is live
}
function beginCountdown() { showHowto(); }
function startCountdown() {
  notes = makeChart(); effects = []; faceBest = faceWorst = null; confetti = []; blinkStats = { both: 0, single: 0 }; pickCrowd();
  stats = { perfect: 0, good: 0, miss: 0, combo: 0, maxCombo: 0, score: 0 }; updateHud();
  setMode('countdown');
  // three-beat count-in on the actual groove: the round starts on beat four
  startAt = audioCtx.currentTime + 3 * BEAT + 0.05; nextBeat = startAt - 3 * BEAT; beatIndex = -12; clearTimeout(schedulerId); scheduleBeats();
  let n = 3; $('countdown').textContent = n; sfx('count');
  const iv = setInterval(() => { n--; if (n > 0) { $('countdown').textContent = n; sfx('count'); } else { clearInterval(iv); $('countdown').textContent = ''; sfx('go'); startRound(); } }, BEAT * 1000);
}
function startRound() { if (DEBUG) dlog('round start'); setMode('playing'); }
function pickCrowd() { // five different people, fresh each round
  const ids = PEOPLE.map((_, i) => i); for (let i = ids.length - 1; i > 0; i--) { const j = Math.floor(Math.random() * (i + 1)); [ids[i], ids[j]] = [ids[j], ids[i]]; }
  crowd = ids.slice(0, 5).map((who) => ({ who, state: 'wait', until: 0, bob: Math.random() * TAU }));
  if (!crowd.length) return;
}
function crowdReact(state, dur) { const t = songTime; for (const c of crowd) { c.state = state; c.until = t + dur + Math.random() * 0.25; } }
function startNow() { // camera flow: the first wink is the start button, no countdown
  notes = makeChart(); effects = []; confetti = []; blinkStats = { both: 0, single: 0 }; pickCrowd();
  stats = { perfect: 0, good: 0, miss: 0, combo: 0, maxCombo: 0, score: 0 }; updateHud();
  ensureAudio(); startAt = audioCtx.currentTime + 0.05; nextBeat = startAt; beatIndex = 0; clearTimeout(schedulerId); scheduleBeats(); sfx('go');
  startRound();
}
function endRound() {
  clearTimeout(schedulerId); setMode('result'); sfx('win');
  const total = notes.length, hits = stats.perfect + stats.good, pct = total ? Math.round(hits / total * 100) : 0;
  $('rPct').textContent = pct + '%'; $('rLine').textContent = hits + ' of ' + total + ' beats landed';
  $('resultTitle').textContent = pct >= 90 ? 'The club is yours.' : pct >= 70 ? 'Crowd is moving.' : pct >= 40 ? 'Warming up.' : 'They want the aux back.';
  showcase = []; crowdFinal = pct >= 50 ? 'good' : 'bad'; if (crowdFinal === 'good') roar(); else scratch();
  show('rbtns', false); clearTimeout(endRound.t); endRound.t = setTimeout(() => show('rbtns'), 5000);
  resultAt = performance.now();
  confetti = crowdFinal !== 'good' ? [] : Array.from({ length: 90 }, () => ({ x: Math.random() * W, y: -Math.random() * H, vx: (Math.random() - .5) * 40, vy: 80 + Math.random() * 120, r: 4 + Math.random() * 5, c: ['#ff5c8a', '#ffb3c8', '#b58cff', '#ffe052', '#fff7fb'][Math.floor(Math.random() * 5)], a: Math.random() * TAU }));
  confettiAt = resultAt;
}

// ---------- input ----------
const DETECT_LAG = 0.04; // small camera + model latency, seconds
function fire(lane, at = songTime) {
  if (mode !== 'playing') return;
  const t = at, t2 = songTime; // closure start vs confirmation: judge by whichever is closer to the note
  let best = null, bestD = GOOD * 1.5 + 1e-9;
  for (const n of notes) {
    if (n.hit) continue;
    const win = n.id < 2 ? GOOD * 1.5 : GOOD; // warm-up: the first two are forgiving
    if (!bothMode && !(n.lane === lane || (n.lane === 2 && lane === 2))) continue;
    if (!bothMode && n.lane === 2 && lane !== 2) continue;
    const d = Math.min(Math.abs(n.t - t), Math.abs(n.t - t2)); if (d <= win && d < bestD) { bestD = d; best = n; }
  }
  let lenient = false;
  if (!best) { // second pass: a wink read as "both" (or the other way round) still counts, capped at Good
    for (const n of notes) { if (n.hit) continue; const win = n.id < 2 ? GOOD * 1.5 : GOOD; const d = Math.min(Math.abs(n.t - t), Math.abs(n.t - t2)); if (d <= win && d < bestD) { bestD = d; best = n; lenient = true; } }
  }
  if (!best) { if (DEBUG) dlog('no note in window'); return; }
  const grade = !lenient && bestD <= PERFECT ? 'perfect' : 'good';
  best.hit = grade; best.hitAt = songTime;
  if (DEBUG) dlog(`hit ${grade} note#${best.id} d=${(t - best.t).toFixed(3)}`);
  stats[grade]++; stats.combo++; stats.maxCombo = Math.max(stats.maxCombo, stats.combo); stats.score += grade === 'perfect' ? 100 : 60;
  effects.push({ kind: grade, lane: best.lane, at: t });
  judge(grade === 'perfect' ? 'PERFECT' : 'GOOD'); sfx(grade); shootHearts(best.lane, grade === 'perfect' ? 8 : 4, true);
  crowdReact('good', grade === 'perfect' ? 1.3 : 0.9); hitSound(best.lane, grade === 'perfect'); flash = grade === 'perfect' ? 1 : 0.6; if (best.lane === 2) hand = [0, 0]; else hand[best.lane] = 0;
  if (grade === 'perfect' && (!faceBest || Math.random() < 0.4)) faceBest = grabFace();
  updateHud();
}
function missNote(n) { if (DEBUG) dlog(`miss note#${n.id} at ${songTime.toFixed(2)}`); crowdReact('bad', 1.1); scratch(); n.hit = 'miss'; stats.miss++; stats.combo = 0; effects.push({ kind: 'miss', lane: n.lane, at: songTime }); judge('MISS'); sfx('miss'); if (!faceWorst || Math.random() < 0.5) faceWorst = grabFace(); updateHud(); }
let judgeTimer = 0;
function judge(text) { const j = $('judge'); j.textContent = text; j.classList.add('show'); clearTimeout(judgeTimer); judgeTimer = setTimeout(() => j.classList.remove('show'), 350); }
function updateHud() { $('score').textContent = stats.score; $('combo').textContent = stats.combo; }

// eye state machine. Wink = one eye clearly more closed than the other; both = both closed together.
// Scores are smoothed a little; thresholds are relative so people with "lazy" winks still register.
let smL = 0, smR = 0, faceAt = 0;
let eyePos = { L: null, R: null }; // canvas coords of the player's eyes
let face = null; // chin / top / left / right, canvas coords
let hearts = [];
let pulse = [0, 0]; // seconds since the last wink on each lane
let crowd = []; // five audience members: { who, state, until }
let hand = [0, 0]; // seconds since each hand slammed
let flash = 0; // hit flash, decays
let riff = 0; // position in the hit melody
function handleEyes(rawL, rawR) {
  faceAt = performance.now();
  smL += (rawL - smL) * 0.5; smR += (rawR - smR) * 0.5;
  const l = smL, r = smR;
  const both = l > 0.38 && r > 0.38 && Math.abs(l - r) < 0.3;
  const L = !both && l > 0.3 && l - r > 0.18;
  const R = !both && r > 0.3 && r - l > 0.18;
  $('eyeL').classList.toggle('on', L || both); $('eyeR').classList.toggle('on', R || both);
  const now = performance.now();
  const closed = L || R || both;
  if (!closed) { eye.armed = true; eye.pendingAt = 0; eye.L = eye.R = false; eye.both = false; return; }
  if (!eye.armed) return;
  if (!eye.pendingAt) eye.pendingAt = now;
  eye.L = eye.L || L; eye.R = eye.R || R; eye.both = eye.both || both;
  if (now - eye.pendingAt >= 70) {
    eye.armed = false;
    const isBoth = eye.both || (eye.L && eye.R);
    if (mode === 'howto' && !practice) { startNow(); }
    else if (mode === 'playing') { if (isBoth) blinkStats.both++; else blinkStats.single++; if (!bothMode && blinkStats.both >= 4 && blinkStats.single === 0) { bothMode = true; judge('BOTH EYES MODE'); } const lane = bothMode ? 2 : isBoth ? 2 : eye.L ? 0 : 1; shootHearts(lane, 3); fire(lane); }
    eye.L = eye.R = false; eye.both = false;
  }
}
// tap practice: left third = left eye, right third = right eye, middle = both
$('phone').addEventListener('pointerdown', (e) => {
  if (!practice || mode !== 'playing') return;
  const r = $('phone').getBoundingClientRect(), x = (e.clientX - r.left) / r.width;
  const lane = x < 0.38 ? 0 : x > 0.62 ? 1 : 2;
  $('eyeL').classList.toggle('on', lane !== 1); $('eyeR').classList.toggle('on', lane !== 0);
  setTimeout(() => { $('eyeL').classList.remove('on'); $('eyeR').classList.remove('on'); }, 120);
  if (lane === 2) { pulse = [0, 0]; hand = [0, 0]; } else { pulse[lane] = 0; hand[lane] = 0; }
  fire(lane);
});

// ---------- face capture ----------
function grabFace() {
  if (!stream || video.readyState < 2) return null;
  const c = document.createElement('canvas'); c.width = 160; c.height = 200; const g = c.getContext('2d');
  const vw = video.videoWidth, vh = video.videoHeight, cw = vw * 0.5, ch = cw * 1.25, sx = (vw - cw) / 2, sy = Math.max(0, vh * 0.42 - ch / 2);
  g.translate(160, 0); g.scale(-1, 1); g.drawImage(video, sx, sy, cw, ch, 0, 0, 160, 200); return c;
}
function paintFace(target, src) {
  const g = target.getContext('2d'); g.clearRect(0, 0, 160, 200);
  if (src) g.drawImage(src, 0, 0); else { g.fillStyle = '#f3e8ff'; g.fillRect(0, 0, 160, 200); g.font = '64px system-ui'; g.textAlign = 'center'; g.fillText(practice ? '😉' : '🫥', 80, 120); }
}

// ---------- hearts from the eyes ----------
function shootHearts(lane, count, big = false) {
  const hy = H * HIT_Y;
  const srcs = lane === 2 ? [['L', 0], ['R', 1]] : [[lane === 0 ? 'L' : 'R', lane]];
  for (const [side, l] of srcs) {
    const from = eyePos[side] || { x: LANE_X[l], y: H * 0.3 };
    for (let i = 0; i < count; i++) hearts.push({ x: from.x + (Math.random() - .5) * 16, y: from.y, tx: LANE_X[l] + (Math.random() - .5) * 40, ty: hy - 40 + (Math.random() - .5) * 30, t: 0, dur: 0.45 + Math.random() * 0.25, size: (big ? 18 : 12) + Math.random() * 8, wob: Math.random() * TAU });
  }
}
function drawHearts(dt) {
  ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
  for (const h of hearts) {
    h.t += dt; const k = Math.min(1, h.t / h.dur), e = 1 - Math.pow(1 - k, 2);
    const x = h.x + (h.tx - h.x) * e + Math.sin(h.wob + k * 6) * 10, y = h.y + (h.ty - h.y) * e - Math.sin(k * Math.PI) * 60;
    ctx.globalAlpha = k < 0.85 ? 1 : 1 - (k - 0.85) / 0.15; ctx.font = (h.size * (0.6 + 0.4 * k)) + 'px system-ui'; ctx.fillText(['🎵', '🎶'][h.wob > 3 ? 1 : 0], x, y);
  }
  ctx.globalAlpha = 1; hearts = hearts.filter((h) => h.t < h.dur);
  // a little sparkle on the eye that is closed right now
  if (mode === 'playing' || mode === 'setup') for (const side of ['L', 'R']) { const on = $('eye' + side).classList.contains('on'), p = eyePos[side]; if (on && p) { ctx.font = '22px system-ui'; ctx.fillText('✨', p.x + (side === 'L' ? -18 : 18), p.y - 14); } }
}

// ---------- render ----------
const TAU = Math.PI * 2; let lastDraw = 0;
const SHOW_ZONES = new URLSearchParams(location.search).has('zones');
const DEBUG = new URLSearchParams(location.search).has('debug');
const dlines = [];
function dlog(m) { dlines.push(m); if (dlines.length > 14) dlines.shift(); }
function nearest(at) { let b = null, d = 9; for (const n of notes) { if (n.hit) continue; const x = Math.abs(n.t - at); if (x < d) { d = x; b = n; } } return b ? `#${b.id}(${['L','R','both'][b.lane]}) ${(b.t - at).toFixed(2)}` : 'none'; }
function drawDebug() { ctx.save(); ctx.font = '11px ui-monospace, monospace'; ctx.textAlign = 'left'; ctx.fillStyle = 'rgba(0,0,0,.55)'; ctx.fillRect(4, H * 0.3, W - 8, 14 * dlines.length + 8); ctx.fillStyle = '#9dff9d'; dlines.forEach((l, i) => ctx.fillText(l, 8, H * 0.3 + 12 + i * 14)); ctx.restore(); }
function drawZones() { // TikTok Effect safe zones on a 390×694 canvas, scaled to this canvas height
  const k = H / 694; ctx.save(); ctx.lineWidth = 1.5;
  ctx.fillStyle = 'rgba(255,0,80,.18)'; ctx.fillRect(0, 0, 19 * k, H); ctx.fillRect(W - 19 * k, 0, 19 * k, H);
  ctx.strokeStyle = '#4ec9b0'; ctx.setLineDash([6, 6]); ctx.strokeRect(19 * k, 83 * k, 352 * k, 258 * k); ctx.strokeRect(65 * k, 83 * k, 260 * k, 462 * k);
  ctx.setLineDash([]); ctx.strokeStyle = '#ffe052'; ctx.lineWidth = 2; ctx.strokeRect(65 * k, 82 * k, 260 * k, 451 * k);
  ctx.font = '700 10px system-ui'; ctx.textAlign = 'left'; ctx.fillStyle = '#ffe052'; ctx.fillText('CORE 260×451', 68 * k, 78 * k); ctx.fillStyle = '#4ec9b0'; ctx.fillText('VISUAL', 22 * k, 352 * k); ctx.fillStyle = '#ff5c8a'; ctx.fillText('CLIP', 2, H - 6);
  ctx.restore();
}
function draw() { drawInner(); if (SHOW_ZONES) drawZones(); if (DEBUG) drawDebug(); }
function drawInner() {
  const nowMs = performance.now(), dt = Math.min(0.05, (nowMs - lastDraw) / 1000 || 0); lastDraw = nowMs;
  ctx.clearRect(0, 0, W, H);
  if (mode === 'result') {
    const t = (performance.now() - resultAt) / 1000;
    { // the crowd gives the verdict: dancing or sulking, big and close
      const n = crowd.length, t = (performance.now() - resultAt) / 1000;
      drawLights(dt); drawBooth(dt); drawFaceSticker();
      crowd.forEach((c, i) => { const x = 19 + (i + 0.5) * (W - 38) / n, good = crowdFinal === 'good'; const bob = good ? Math.abs(Math.sin(t * 8 + c.bob)) * 22 : Math.sin(t * 1.5 + c.bob) * 3; const k = Math.min(1, Math.max(0, (t - i * 0.08) / 0.4)); sprite(PEOPLE[c.who][good ? 'good' : 'bad'], x, H * 1.01 - bob + (1 - k) * 140, { scale: 0.85, rot: good ? Math.sin(t * 8 + c.bob) * 0.1 : 0 }); });
    }
    const dtc = (performance.now() - confettiAt) / 1000;
    for (const c of confetti) { const y = c.y + c.vy * dtc, x = c.x + c.vx * dtc + Math.sin(dtc * 3 + c.a) * 12; if (y > H + 10) continue; ctx.save(); ctx.translate(x, y); ctx.rotate(c.a + dtc * 4); ctx.fillStyle = c.c; ctx.fillRect(-c.r / 2, -c.r, c.r, c.r * 2); ctx.restore(); }
    return;
  }
  if (mode === 'setup') { drawHearts(dt); return; }
  if (!['playing', 'countdown', 'howto'].includes(mode)) return;
  const hy = H * HIT_Y;
  drawLights(dt); drawBooth(dt); drawCrowd();
  if (mode !== 'playing') return;
  // music notes dropping onto the decks
  ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
  for (const n of notes) {
    const dt2 = n.t - songTime; if (dt2 > LEAD || dt2 < -0.8) continue;
    const k = 1 - dt2 / LEAD, y = hy - (dt2 / LEAD) * (hy + 60);
    const lanes = n.lane === 2 ? [0, 1] : [n.lane];
    for (const l of lanes) {
      const src = NOTE[n.lane === 2 ? 2 : l];
      if (n.hit === 'miss') { const m = Math.min(1, (songTime - n.t) / 0.5); ctx.globalAlpha = 1 - m; ctx.font = '40px system-ui'; ctx.fillText('💥', LANE_X[l], hy - m * 30); ctx.globalAlpha = 1; continue; }
      if (n.hit) { const m = Math.min(1, (songTime - n.hitAt) / 0.5); if (!img(src, LANE_X[l], hy - m * 40, 64 + m * 50, { alpha: 1 - m, rot: m * 0.6 })) { ctx.globalAlpha = 1 - m; ctx.font = (40 + m * 40) + 'px system-ui'; ctx.fillText('🎵', LANE_X[l], hy - m * 40); ctx.globalAlpha = 1; } continue; }
      const near = Math.max(0, (k - 0.45) / 0.55); ctx.beginPath(); ctx.arc(LANE_X[l], y, 38, 0, TAU); ctx.fillStyle = `rgba(0,242,234,${0.06 + near * 0.3})`; ctx.fill();
      if (!img(src, LANE_X[l], y, (n.lane === 2 ? 60 : 50) + 22 * k, { rot: Math.sin(songTime * 6 + n.id) * 0.15 })) { ctx.font = (30 + 14 * k) + 'px system-ui'; ctx.fillText('🎵', LANE_X[l], y); }
    }
    if (n.lane === 2 && !n.hit) { ctx.strokeStyle = 'rgba(255,255,255,.35)'; ctx.lineWidth = 2; ctx.setLineDash([4, 6]); ctx.beginPath(); ctx.moveTo(LANE_X[0] + 34, y); ctx.lineTo(LANE_X[1] - 34, y); ctx.stroke(); ctx.setLineDash([]); }
  }
  for (const e of effects) {
    const k = (songTime - e.at) / 0.7; if (k > 1) continue;
    const xs = e.lane === 2 ? LANE_X : [LANE_X[e.lane]];
    for (const x of xs) {
      ctx.globalAlpha = 1 - k; ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
      if (e.kind === 'miss') { ctx.font = '30px system-ui'; ctx.fillText('💢', x + 40, hy - 90 - k * 40); }
      else { const n = e.kind === 'perfect' ? 8 : 4; for (let i = 0; i < n; i++) { const a = i * TAU / n + k * 2; ctx.font = (12 + (i % 3) * 6) + 'px system-ui'; ctx.fillText(['🎵', '✨', '🎶'][i % 3], x + Math.cos(a) * (36 + k * 90), hy - 20 - k * 110 + Math.sin(a) * 22); } }
      ctx.globalAlpha = 1;
    }
  }
  effects = effects.filter((e) => songTime - e.at < 0.7);
  drawHearts(dt);
  ctx.textBaseline = 'alphabetic';
}
function drawFaceSticker() { // the verdict on the player's own face: shades + chain, or a frustration cloud
  const eyeMid = eyePos.L && eyePos.R ? { x: (eyePos.L.x + eyePos.R.x) / 2, y: (eyePos.L.y + eyePos.R.y) / 2 } : { x: W / 2, y: H * 0.26 };
  const eyeDist = eyePos.L && eyePos.R ? Math.hypot(eyePos.R.x - eyePos.L.x, eyePos.R.y - eyePos.L.y) : 60;
  const tilt = eyePos.L && eyePos.R ? Math.atan2(eyePos.R.y - eyePos.L.y, eyePos.R.x - eyePos.L.x) : 0;
  const faceW = face ? Math.hypot(face.right.x - face.left.x, face.right.y - face.left.y) : eyeDist * 2.4;
  if (crowdFinal === 'good') {
    img(STICKER.glasses, eyeMid.x, eyeMid.y, eyeDist * 2.7, { rot: tilt });                           // glasses span both eyes
    const chin = face ? face.chin : { x: eyeMid.x, y: eyeMid.y + eyeDist * 1.9 };
    img(STICKER.chain, chin.x, chin.y + faceW * 0.12, faceW * 1.7, { ay: 0 });                          // chain hangs from under the chin
  } else {
    const top = face ? face.top : { x: eyeMid.x, y: eyeMid.y - eyeDist * 1.2 };
    const t = performance.now() / 1000;
    img(STICKER.frustrated, top.x, top.y - faceW * 0.08 + Math.sin(t * 3) * 3, faceW * 1.25, { ay: 1, rot: Math.sin(t * 2) * 0.04 }); // tangle hovers over the head
  }
}
function drawLights(dt) { // club lighting: a kick-synced pulse, two sweeping beams, a flash on every hit
  const beatPos = mode === 'playing' ? ((songTime % BEAT) + BEAT) % BEAT / BEAT : (performance.now() / 1000 % BEAT) / BEAT;
  const kick = Math.pow(1 - beatPos, 3);
  const hue = ((((mode === 'playing' ? Math.floor(songTime / (BEAT * 4)) : Math.floor(performance.now() / 3000)) % 4) + 4) % 4);
  const cols = [['0,242,234', '255,92,138'], ['255,92,138', '181,140,255'], ['181,140,255', '255,224,82'], ['255,224,82', '0,242,234']][hue];
  ctx.fillStyle = `rgba(${cols[0]},${0.05 + kick * 0.09})`; ctx.fillRect(0, 0, W, H);
  const t = performance.now() / 1000;
  [[0, 1], [W, -1]].forEach(([ox, dir], i) => { // beams from the top corners sweeping across
    const ang = Math.PI / 2 + dir * (0.55 + Math.sin(t * 0.9 + i * 2) * 0.45);
    const g = ctx.createLinearGradient(ox, 0, ox + Math.cos(ang) * H, Math.sin(ang) * H);
    g.addColorStop(0, `rgba(${cols[i]},${0.22 + kick * 0.15})`); g.addColorStop(1, `rgba(${cols[i]},0)`);
    ctx.save(); ctx.translate(ox, -10); ctx.rotate(ang - Math.PI / 2); ctx.fillStyle = g; ctx.beginPath(); ctx.moveTo(-14, 0); ctx.lineTo(14, 0); ctx.lineTo(90, H * 1.3); ctx.lineTo(-90, H * 1.3); ctx.closePath(); ctx.fill(); ctx.restore();
  });
  if (flash > 0) { ctx.fillStyle = `rgba(255,255,255,${flash * 0.28})`; ctx.fillRect(0, 0, W, H); flash = Math.max(0, flash - dt * 4); }
}
function drawCrowd() { // five people behind the booth, upper half showing
  const n = crowd.length, feet = H * 1.01; // in the band below the booth, feet at the bottom edge
  crowd.forEach((c, i) => {
    if (c.state !== 'wait' && songTime > c.until) c.state = 'wait';
    const x = 19 + (i + 0.5) * (W - 38) / n, t = performance.now() / 1000; // kept out of the 19 px clip strips
    const bob = c.state === 'good' ? Math.abs(Math.sin(t * 9 + c.bob)) * 18 : c.state === 'bad' ? Math.sin(t * 14 + c.bob) * 2 : Math.sin(t * 2.2 + c.bob) * 3;
    const rot = c.state === 'good' ? Math.sin(t * 9 + c.bob) * 0.08 : 0;
    sprite(PEOPLE[c.who][c.state], x, feet - bob, { scale: 0.72, rot });
  });
}
function drawBooth(dt) { // the booth, a little see-through; hands and targets on the platters; a dance floor below
  const hy = H * HIT_Y, bImg = IMG[BOOTH];
  const floorTop = BOOTH_TOP() + 800 * BOOTH_S; const fg = ctx.createLinearGradient(0, floorTop, 0, H); fg.addColorStop(0, 'rgba(11,11,22,.0)'); fg.addColorStop(0.3, 'rgba(11,11,22,.55)'); fg.addColorStop(1, 'rgba(11,11,22,.85)'); ctx.fillStyle = fg; ctx.fillRect(0, floorTop, W, H - floorTop);
  const beat = mode === 'playing' ? Math.pow(1 - (((songTime % BEAT) + BEAT) % BEAT) / BEAT, 3) : 0; for (let i = 0; i < 6; i++) { const y = floorTop + 18 + i * 22; ctx.strokeStyle = `rgba(0,242,234,${0.05 + beat * 0.12 - i * 0.008})`; ctx.lineWidth = 1; ctx.beginPath(); ctx.moveTo(W / 2 - (i + 1) * 45, y); ctx.lineTo(W / 2 + (i + 1) * 45, y); ctx.stroke(); }
  if (bImg && bImg.complete && bImg.naturalWidth) { ctx.save(); ctx.globalAlpha = 0.86; ctx.drawImage(bImg, (W - BOOTH_W) / 2, BOOTH_TOP(), BOOTH_W, 900 * BOOTH_S); ctx.restore(); }
  LANE_X.forEach((x, i) => {
    pulse[i] += dt; hand[i] += dt; const k = Math.min(1, pulse[i] / 0.45);
    ctx.beginPath(); ctx.arc(x, hy, 38, 0, TAU); ctx.strokeStyle = 'rgba(255,255,255,.4)'; ctx.lineWidth = 1.5; ctx.stroke();
    if (k < 1) { ctx.beginPath(); ctx.arc(x, hy, 38 * (1 + k * 0.55), 0, TAU); ctx.fillStyle = `rgba(0,242,234,${0.45 * (1 - k)})`; ctx.fill(); }
    const hImg = IMG[HAND[i]]; if (hImg && hImg.complete && hImg.naturalWidth) { const slam = Math.max(0, 1 - hand[i] / 0.18), hh = 104, hw = hh * hImg.naturalWidth / hImg.naturalHeight; ctx.save(); ctx.globalAlpha = 0.96; ctx.translate(x, hy + 18 + 12 * slam - Math.sin(performance.now() / 600 + i) * 3); ctx.scale(1, -1); ctx.drawImage(hImg, -hw / 2, 0, hw, hh); ctx.restore(); } // flipped: the player's hands come down from above
  });
}
function heartPath(cx, cy, r) { // simple heart outline, r ≈ half width
  ctx.beginPath(); const top = cy - r * 0.55;
  ctx.moveTo(cx, cy + r * 0.85);
  ctx.bezierCurveTo(cx - r * 1.35, cy - r * 0.05, cx - r * 0.95, top - r * 0.75, cx, top);
  ctx.bezierCurveTo(cx + r * 0.95, top - r * 0.75, cx + r * 1.35, cy - r * 0.05, cx, cy + r * 0.85);
  ctx.closePath();
}
function roundRect(x, y, w, h, r) { ctx.beginPath(); ctx.moveTo(x + r, y); ctx.arcTo(x + w, y, x + w, y + h, r); ctx.arcTo(x + w, y + h, x, y + h, r); ctx.arcTo(x, y + h, x, y, r); ctx.arcTo(x, y, x + w, y, r); ctx.closePath(); }

// ---------- loop ----------
function loop() {
  requestAnimationFrame(loop);
  if (mode === 'playing') songTime = audioCtx.currentTime - startAt;
  if (landmarker && stream && video.readyState >= 2 && video.currentTime !== lastVideoTime && ['setup', 'howto', 'playing', 'countdown', 'result'].includes(mode)) {
    lastVideoTime = video.currentTime;
    try {
      const res = landmarker.detectForVideo(video, performance.now());
      const bs = res.faceBlendshapes && res.faceBlendshapes[0];
      const lm = res.faceLandmarks && res.faceLandmarks[0];
      if (lm) { const toC = (i) => { // video is mirrored and cover-fitted into the phone frame
          const vw = video.videoWidth, vh = video.videoHeight, s = Math.max(W / vw, H / vh), dw = vw * s, dh = vh * s;
          return { x: (W - dw) / 2 + (1 - lm[i].x) * dw, y: (H - dh) / 2 + lm[i].y * dh }; };
        const mid = (a, b) => { const p = toC(a), q = toC(b); return { x: (p.x + q.x) / 2, y: (p.y + q.y) / 2 }; };
        eyePos = { L: mid(159, 145), R: mid(386, 374) }; face = { chin: toC(152), top: toC(10), left: toC(234), right: toC(454) }; }
      if (bs) { const get = (name) => (bs.categories.find((c) => c.categoryName === name) || {}).score || 0; handleEyes(get('eyeBlinkLeft'), get('eyeBlinkRight')); }

    } catch (e) { /* skip frame */ }
  }
  if (mode === 'playing') {
    songTime = audioCtx.currentTime - startAt;
    for (const n of notes) if (!n.hit && songTime - n.t > (n.id < 2 ? GOOD * 1.5 : GOOD)) missNote(n);
    $('time').textContent = Math.max(0, Math.ceil(SONG - songTime));
    if (songTime > SONG + 0.6) endRound();
  }
  draw();
}
setMode('idle'); loop();
