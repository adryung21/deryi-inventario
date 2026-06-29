import { firebaseConfig, APP_NAME, ADMIN_EMAIL, LOCK_TIMEOUT_MS } from './firebase-config.js';
import { initializeApp } from 'https://www.gstatic.com/firebasejs/10.12.5/firebase-app.js';
import {
  getAuth,
  setPersistence,
  browserLocalPersistence,
  signInWithEmailAndPassword,
  createUserWithEmailAndPassword,
  onAuthStateChanged,
  updatePassword,
  sendPasswordResetEmail,
  signOut
} from 'https://www.gstatic.com/firebasejs/10.12.5/firebase-auth.js';
import {
  getFirestore,
  enableIndexedDbPersistence,
  collection,
  doc,
  getDoc,
  getDocs,
  setDoc,
  updateDoc,
  deleteDoc,
  writeBatch,
  runTransaction,
  onSnapshot,
  serverTimestamp,
  query,
  orderBy
} from 'https://www.gstatic.com/firebasejs/10.12.5/firebase-firestore.js';

const $ = id => document.getElementById(id);
const getValue = (id, fallback = '') => {
  const node = $(id);
  return node ? node.value : fallback;
};
const nf = new Intl.NumberFormat('es-EC', { maximumFractionDigits: 2 });
const dtf = new Intl.DateTimeFormat('es-EC', { dateStyle: 'short', timeStyle: 'short' });
const appVersion = 'PWA Firebase v1.8 reset-login';

let app, auth, db;
let unsubscribers = [];
let heartbeatTimer = null;
let userHeartbeatTimer = null;
let deferredInstallPrompt = null;
let factorModalRowId = null;
const countSaveTimers = new Map();

const state = {
  user: null,
  profile: null,
  inventory: [],
  counts: {},
  locks: {},
  allowedUsers: {},
  registeredUsers: {},
  meta: {},
  activeLab: '',
  showOnlyDiff: false
};

function setupFirebase() {
  const placeholder = Object.values(firebaseConfig).some(v => String(v || '').startsWith('REEMPLAZAR'));
  if (placeholder) {
    $('setupWarning').classList.remove('hidden');
    $('setupWarning').textContent = 'Falta configurar Firebase. Abre firebase-config.js y reemplaza los valores del proyecto antes de publicar.';
    return false;
  }
  app = initializeApp(firebaseConfig);
  auth = getAuth(app);
  db = getFirestore(app);
  setPersistence(auth, browserLocalPersistence).catch(() => {});
  enableIndexedDbPersistence(db).catch(() => {});
  return true;
}

function normalizeText(value) {
  return String(value ?? '').replace(/\s+/g, ' ').trim();
}

function normalizeKey(value) {
  return normalizeText(value).normalize('NFD').replace(/[\u0300-\u036f]/g, '').toUpperCase();
}

function labKey(lab) {
  return normalizeKey(lab).replace(/[^A-Z0-9]+/g, '_').replace(/^_+|_+$/g, '').toLowerCase() || 'sin_laboratorio';
}

function escapeHtml(value) {
  return String(value ?? '').replace(/[&<>'"]/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', "'": '&#39;', '"': '&quot;' }[c]));
}

function toNumber(value) {
  if (typeof value === 'number') return Number.isFinite(value) ? value : 0;
  const s = String(value ?? '').trim();
  if (!s) return 0;
  const cleaned = s.replace(/\s/g, '').replace(/,/g, '.').replace(/[^0-9.-]/g, '');
  const n = Number(cleaned);
  return Number.isFinite(n) ? n : 0;
}

function hashString(str) {
  let h = 2166136261;
  for (let i = 0; i < str.length; i++) {
    h ^= str.charCodeAt(i);
    h = Math.imul(h, 16777619);
  }
  return (h >>> 0).toString(36);
}

function productId(row) {
  return 'p_' + hashString(`${normalizeKey(row.codigo)}|${normalizeKey(row.descripcion)}|${normalizeKey(row.laboratorio)}`);
}

function detectUnitsPerEntero(description) {
  const d = normalizeKey(description).replace(/\s+/g, ' ');
  if (!d) return { units: 1, source: 'Descripción vacía: unidad individual' };
  const measurementUnits = '(?:MG|MCG|UG|G|GR|KG|ML|L|LT|LTR|LTS|CC|UI|IU|U|V|VOL|VOLT|VOLTS|M|CM|MM|OZ|LB|%)';
  const containerWords = '\\b(?:FCO|FRA|FRASCO|FRASCOS|ENV|ENVASE|ENVASES|BOT|BOTELLA|BOTELLAS|AMP|AMPOLLA|AMPOLLAS|VIAL|VIALES|GOTERO|SPRAY|JBE|JARABE|LATA|LATAS)\\b';
  const packWords = '(?:CAJ|CAJA|CJ|DISPLAY|DISP|BLIS|BLISTER|BLI|SOB|SOBRES|SACH|SACHET|PAQ|PQT|PACK|FUNDA|TIRA|TIRAS|ESTUCHE|EST)';
  const patterns = [
    { re: new RegExp('\\b' + packWords + '\\s*(?:X|\\*)\\s*(\\d{1,4})(?!\\s*' + measurementUnits + '\\b)', 'i'), label: 'Empaque detectado' },
    { re: new RegExp('\\b' + packWords + '\\s+(\\d{1,4})(?!\\s*' + measurementUnits + '\\b)', 'i'), label: 'Empaque detectado' },
    { re: new RegExp('(?:^|[\\s\\-/])(?:X|\\*)\\s*(\\d{1,4})(?!\\s*' + measurementUnits + '\\b)', 'i'), label: 'Multiplicador detectado' }
  ];
  for (const p of patterns) {
    const m = d.match(p.re);
    if (m) {
      const n = parseInt(m[1], 10);
      if (n > 1 && n <= 1000) return { units: n, source: `${p.label}: ${m[0].trim()}` };
    }
  }
  if (new RegExp(containerWords, 'i').test(d) || new RegExp('\\b\\d+(?:[.,]\\d+)?\\s*' + measurementUnits + '\\b', 'i').test(d)) {
    return { units: 1, source: 'Unidad individual: frasco/envase/lata/medida' };
  }
  return { units: 1, source: 'No se encontró empaque múltiple' };
}

function calcStock(stockActual, unitsPerEntero) {
  const factor = Math.max(1, parseInt(unitsPerEntero, 10) || 1);
  const sign = stockActual < 0 ? -1 : 1;
  const absStock = Math.abs(stockActual);
  let enteros = Math.floor(absStock);
  let unidades = factor === 1 ? Math.round((absStock - enteros) * 100) / 100 : Math.round((absStock - enteros) * factor);
  if (factor > 1 && unidades >= factor) {
    enteros += Math.floor(unidades / factor);
    unidades = unidades % factor;
  }
  const totalUnits = factor === 1 ? stockActual : sign * ((enteros * factor) + unidades);
  return { enteros: sign * enteros, unidades: sign * unidades, totalUnits: Math.round(totalUnits * 100) / 100 };
}

function enrichRow(row) {
  const factorInfo = row.factorSource === 'Editado manualmente'
    ? { units: row.unitsPerEntero || 1, source: 'Editado manualmente' }
    : detectUnitsPerEntero(row.descripcion);
  const unitsPerEntero = Math.max(1, parseInt(row.unitsPerEntero || factorInfo.units, 10) || 1);
  const calc = calcStock(Number(row.stockActual) || 0, unitsPerEntero);
  return { ...row, id: row.id || productId(row), labKey: labKey(row.laboratorio), unitsPerEntero, factorSource: row.factorSource || factorInfo.source, ...calc };
}

function sortRowsByDescription(rows) {
  return [...rows].sort((a, b) => {
    const byDesc = normalizeText(a.descripcion).localeCompare(normalizeText(b.descripcion), 'es', { sensitivity: 'base', numeric: true });
    if (byDesc !== 0) return byDesc;
    return normalizeText(a.laboratorio).localeCompare(normalizeText(b.laboratorio), 'es', { sensitivity: 'base', numeric: true });
  });
}

function getLabs() {
  return [...new Set(state.inventory.map(r => r.laboratorio).filter(Boolean))].sort((a,b) => a.localeCompare(b, 'es'));
}

function isAdmin() {
  return state.profile?.role === 'admin' || state.user?.email?.toLowerCase() === ADMIN_EMAIL.toLowerCase();
}

function isLockActive(lock) {
  return lock && lock.status === 'active' && Number(lock.expiresAtMs || 0) > Date.now();
}

function lockForLab(lab) {
  return state.locks[labKey(lab)];
}

function isLabLockedByCurrent(lab) {
  const lock = lockForLab(lab);
  return isLockActive(lock) && lock.lockedByUid === state.user?.uid;
}

function countFor(row) {
  return state.counts[row.id] || {};
}

function hasPhysical(row) {
  const c = countFor(row);
  return c.physicalEnteros !== undefined || c.physicalUnidades !== undefined || c.total !== undefined;
}

function getPhysicalParts(row) {
  const c = countFor(row);
  const e = c.physicalEnteros === undefined || c.physicalEnteros === '' ? '' : Number(c.physicalEnteros);
  const u = c.physicalUnidades === undefined || c.physicalUnidades === '' ? '' : Number(c.physicalUnidades);
  const counted = e !== '' || u !== '' || c.total !== undefined;
  const factor = Number(row.unitsPerEntero) || 1;
  const total = counted ? ((Number(e) || 0) * factor + (Number(u) || 0)) : '';
  return { enteros: e, unidades: u, total, counted };
}

function getDifference(row) {
  const p = getPhysicalParts(row);
  if (!p.counted) return null;
  return Math.round(((Number(p.total) || 0) - (Number(row.totalUnits) || 0)) * 100) / 100;
}

function noveltyText(diff) {
  if (diff === null) return 'Pendiente';
  if (diff < 0) return 'Faltante';
  if (diff > 0) return 'Sobrante';
  return 'Sin diferencia';
}

function fmtDate(ms) {
  if (!ms) return 'Sin conteo registrado';
  try { return dtf.format(new Date(ms)); } catch { return 'Sin conteo registrado'; }
}

function userColorClass(value) {
  const raw = String(value || 'usuario').toLowerCase();
  let hash = 0;
  for (let i = 0; i < raw.length; i++) hash = ((hash << 5) - hash + raw.charCodeAt(i)) | 0;
  return 'user-color-' + (Math.abs(hash) % 8);
}

const USER_COLOR_LABELS = ['Azul', 'Verde', 'Amarillo', 'Rosa', 'Morado', 'Celeste', 'Naranja', 'Cian'];
function normalizeColor(value, fallback = 0) {
  const n = Number(value);
  return Number.isFinite(n) ? Math.max(0, Math.min(7, Math.round(n))) : fallback;
}
function userColorFromData(userLike) {
  if (userLike && userLike.color !== undefined && userLike.color !== null && userLike.color !== '') return 'user-color-' + normalizeColor(userLike.color);
  return userColorClass(userLike?.email || userLike?.uid || userLike?.name || 'usuario');
}
function userColorOptions(selected) {
  const s = normalizeColor(selected);
  return USER_COLOR_LABELS.map((label, idx) => `<option value="${idx}" ${idx === s ? 'selected' : ''}>${label}</option>`).join('');
}
function userOnline(data) {
  const last = Number(data?.lastActiveAtMs || data?.lastLoginAtMs || 0);
  return data?.isOnline === true && last && (Date.now() - last < 2 * 60 * 1000);
}

function safeFileName(value) {
  return normalizeKey(value || 'TODOS').replace(/[^A-Z0-9]+/g, '_').replace(/^_+|_+$/g, '').toLowerCase() || 'inventario';
}

function showMessage(el, message, type = 'info') {
  el.className = `notice ${type === 'danger' ? 'danger' : type === 'warn' ? 'warn' : type === 'info' ? 'info' : ''}`.trim();
  el.textContent = message;
  el.classList.remove('hidden');
}

function clearMessage(el) {
  el.classList.add('hidden');
}

function switchAuthTab(tab) {
  document.querySelectorAll('.auth-tab').forEach(b => b.classList.toggle('active', b.dataset.authTab === tab));
  $('loginForm').classList.toggle('hidden', tab !== 'login');
  $('registerForm').classList.toggle('hidden', tab !== 'register');
  const resetForm = $('resetForm');
  if (resetForm) resetForm.classList.toggle('hidden', tab !== 'reset');
  if (tab === 'reset') {
    const resetEmail = $('resetEmail');
    const loginEmail = getValue('loginEmail').trim();
    if (resetEmail && loginEmail && !resetEmail.value) resetEmail.value = loginEmail;
  }
  clearMessage($('authMessage'));
}

async function login(email, password) {
  await signInWithEmailAndPassword(auth, email, password);
}

async function sendLoginPasswordReset(email) {
  const lower = normalizeText(email).toLowerCase();
  if (!lower) throw new Error('Ingresa el correo registrado.');
  await sendPasswordResetEmail(auth, lower);
}

async function registerUser(name, email, password) {
  const lower = email.trim().toLowerCase();
  const cred = await createUserWithEmailAndPassword(auth, lower, password);
  const allowed = lower === ADMIN_EMAIL.toLowerCase()
    ? { name: normalizeText(name) || 'Administrador', role: 'admin', active: true, color: 0 }
    : await getAllowedUser(lower);
  if (!allowed) {
    await signOut(auth);
    throw new Error('Este correo no está autorizado o está inactivo. Solicita acceso al administrador.');
  }
  await setDoc(doc(db, 'users', cred.user.uid), {
    uid: cred.user.uid,
    name: normalizeText(name) || allowed.name || lower.split('@')[0],
    email: lower,
    role: allowed.role || 'inventariador',
    color: normalizeColor(allowed.color, 0),
    active: allowed.active !== false,
    createdAt: serverTimestamp(),
    createdAtMs: Date.now(),
    lastLoginAt: serverTimestamp(),
    lastLoginAtMs: Date.now(),
    lastActiveAt: serverTimestamp(),
    lastActiveAtMs: Date.now(),
    isOnline: true
  }, { merge: true });
}

async function getAllowedUser(email) {
  const lower = email.toLowerCase();
  const snap = await getDoc(doc(db, 'allowedEmails', lower));
  if (!snap.exists()) return null;
  const data = snap.data();
  if (data.active === false) return null;
  return { ...data, email: lower };
}

async function ensureProfile(user) {
  const ref = doc(db, 'users', user.uid);
  const lower = user.email.toLowerCase();
  const isBootstrap = lower === ADMIN_EMAIL.toLowerCase();
  const allowed = isBootstrap ? { name: 'Adrian', role: 'admin', active: true, color: 0 } : await getAllowedUser(lower);
  if (!allowed) throw new Error('Usuario autenticado, pero sin autorización activa en DERYI INVENTARIO.');

  const snap = await getDoc(ref);
  const existing = snap.exists() ? snap.data() : {};
  if (existing.active === false || allowed.active === false) throw new Error('Tu usuario está inactivo. Solicita activación al administrador.');

  const profile = {
    uid: user.uid,
    name: allowed.name || existing.name || user.displayName || lower.split('@')[0],
    email: lower,
    role: allowed.role || existing.role || 'inventariador',
    color: normalizeColor(allowed.color, normalizeColor(existing.color, 0)),
    active: true,
    lastLoginAt: serverTimestamp(),
    lastLoginAtMs: Date.now(),
    lastActiveAt: serverTimestamp(),
    lastActiveAtMs: Date.now(),
    isOnline: true
  };
  if (!snap.exists()) {
    profile.createdAt = serverTimestamp();
    profile.createdAtMs = Date.now();
  }
  await setDoc(ref, profile, { merge: true });
  return { ...existing, ...profile };
}

function applyRoleUI() {
  document.querySelectorAll('.admin-only, .admin-panel').forEach(el => el.classList.toggle('hidden', !isAdmin()));
  $('sideUserName').textContent = state.profile?.name || '-';
  $('sideUserEmail').textContent = state.user?.email || '-';
  $('sideUserRole').textContent = isAdmin() ? 'Administrador' : 'Inventariador';
  if (!isAdmin() && $('tab-carga').classList.contains('active')) switchTab('vista');
}

function switchTab(tab) {
  document.querySelectorAll('.tab-btn').forEach(b => b.classList.toggle('active', b.dataset.tab === tab));
  document.querySelectorAll('.panel').forEach(p => p.classList.remove('active'));
  const panel = $('tab-' + tab);
  if (panel) panel.classList.add('active');
  renderAll();
  setSideMenu(false);
}

function setSideMenu(open) {
  $('sideNav').classList.toggle('open', open);
  $('sideNavEdge').classList.toggle('open', open);
  $('sideNav').setAttribute('aria-hidden', open ? 'false' : 'true');
  $('sideNavEdge').setAttribute('aria-expanded', open ? 'true' : 'false');
}

function setSectionCollapsed(targetId, collapsed) {
  const section = $(targetId);
  const button = document.querySelector(`[data-toggle-section="${targetId}"]`);
  if (!section || !button) return;
  section.classList.toggle('collapsed', collapsed);
  button.setAttribute('aria-expanded', collapsed ? 'false' : 'true');
  const icon = button.querySelector('.toggle-icon');
  const label = button.querySelector('.toggle-text');
  if (icon) icon.textContent = collapsed ? '▸' : '▾';
  if (label) label.textContent = collapsed ? (button.dataset.labelShow || 'Mostrar') : (button.dataset.labelHide || 'Ocultar');
  try { localStorage.setItem('deryi_ui_' + targetId, collapsed ? '1' : '0'); } catch {}
}

function applyCollapsePrefs() {
  ['adminViewControls', 'viewControls', 'genControls', 'usersCreateBox'].forEach(id => {
    let collapsed = false;
    try { collapsed = localStorage.getItem('deryi_ui_' + id) === '1'; } catch {}
    setSectionCollapsed(id, collapsed);
  });
}

function attachRealtimeListeners() {
  unsubscribers.forEach(fn => fn());
  unsubscribers = [];
  unsubscribers.push(onSnapshot(collection(db, 'inventory'), snap => {
    state.inventory = sortRowsByDescription(snap.docs.map(d => enrichRow({ id: d.id, ...d.data() })));
    renderAll();
  }));
  unsubscribers.push(onSnapshot(collection(db, 'counts'), snap => {
    state.counts = Object.fromEntries(snap.docs.map(d => [d.id, { id: d.id, ...d.data() }]));
    renderAll();
  }));
  unsubscribers.push(onSnapshot(collection(db, 'labLocks'), snap => {
    state.locks = Object.fromEntries(snap.docs.map(d => [d.id, { id: d.id, ...d.data() }]));
    renderAll();
  }));
  unsubscribers.push(onSnapshot(doc(db, 'appMeta', 'current'), snap => {
    state.meta = snap.exists() ? snap.data() : {};
    renderAll();
  }));
  if (isAdmin()) {
    unsubscribers.push(onSnapshot(query(collection(db, 'allowedEmails'), orderBy('email')), snap => {
      state.allowedUsers = Object.fromEntries(snap.docs.map(d => [d.id, { id: d.id, ...d.data() }]));
      renderUsers();
    }));
    unsubscribers.push(onSnapshot(collection(db, 'users'), snap => {
      state.registeredUsers = Object.fromEntries(snap.docs.map(d => [d.id, { id: d.id, ...d.data() }]));
      const self = state.user ? state.registeredUsers[state.user.uid] : null;
      if (self && self.active === false) { alert('Tu usuario fue desactivado.'); signOut(auth); return; }
      renderUsers();
    }));
  }
}

function populateLabOptions() {
  $('labOptions').innerHTML = getLabs().map(l => `<option value="${escapeHtml(l)}"></option>`).join('');
}

function getLabSummary() {
  const map = new Map();
  for (const row of state.inventory) {
    const key = row.labKey;
    if (!map.has(key)) {
      map.set(key, {
        key,
        lab: row.laboratorio,
        total: 0,
        counted: 0,
        missing: 0,
        surplus: 0,
        lastMs: 0,
        lastUserName: '',
        lastUserEmail: '',
        lastUserUid: '',
        lastUserColor: ''
      });
    }
    const item = map.get(key);
    item.total++;
    const c = state.counts[row.id];
    if (c) {
      item.counted++;
      const updatedAtMs = Number(c.updatedAtMs || 0);
      if (updatedAtMs >= (item.lastMs || 0)) {
        item.lastMs = updatedAtMs;
        item.lastUserName = c.updatedByName || '';
        item.lastUserEmail = c.updatedByEmail || '';
        item.lastUserUid = c.updatedByUid || '';
        item.lastUserColor = c.updatedByColor ?? '';
      }
      const diff = getDifference(row);
      if (diff < 0) item.missing++;
      if (diff > 0) item.surplus++;
    }
  }
  return [...map.values()].sort((a,b) => a.lab.localeCompare(b.lab, 'es'));
}

function renderMetrics() {
  $('mItems').textContent = nf.format(state.inventory.length);
  $('mLabs').textContent = nf.format(getLabs().length);
  $('mCounts').textContent = nf.format(Object.keys(state.counts).length);
  $('mSkipped').textContent = nf.format(state.meta.skippedZero || 0);
  if (state.meta.fileName) {
    $('loadMessage').className = 'notice';
    $('loadMessage').textContent = `Archivo cargado: ${state.meta.fileName}. Guardados: ${nf.format(state.inventory.length)}. Eliminados por stock cero: ${nf.format(state.meta.skippedZero || 0)}.`;
  }
}

function buildLabListHtml() {
  const labs = getLabSummary();
  if (!labs.length) {
    return '<div class="inventory-card-empty">Cuando se cargue inventario aparecerá aquí la lista de laboratorios.</div>';
  }
  return labs.map(l => {
    const lock = state.locks[l.key];
    const locked = isLockActive(lock) && lock.lockedByUid !== state.user?.uid;
    const mine = isLockActive(lock) && lock.lockedByUid === state.user?.uid;
    const complete = l.total > 0 && l.counted >= l.total;
    const cls = complete ? 'complete' : locked ? 'locked' : '';
    const status = complete ? 'Completo' : locked ? `En proceso por ${escapeHtml(lock.userName || lock.userEmail || 'usuario')}` : mine ? 'En proceso por ti' : `${l.counted} / ${l.total}`;
    const sub = complete ? 'Inventario finalizado' : locked ? 'Laboratorio bloqueado temporalmente' : 'Tocar para generar inventario';
    const userLabel = l.lastUserName || l.lastUserEmail || '';
    const colorClass = l.lastUserColor !== '' ? 'user-color-' + normalizeColor(l.lastUserColor) : userColorClass(l.lastUserEmail || l.lastUserUid || l.lastUserName || l.lab);
    const userHtml = userLabel
      ? `<div class="lab-user-line">Último usuario: <span class="user-chip ${colorClass}">${escapeHtml(userLabel)}</span></div>`
      : '<div class="lab-user-line no-user">Usuario: sin registro</div>';
    return `<button class="lab-card ${cls}" type="button" data-lab-open="${escapeHtml(l.lab)}">
      <div>
        <div class="lab-name">${escapeHtml(l.lab)}</div>
        <div class="lab-sub">${sub}</div>
        <div class="lab-date">Último conteo: ${escapeHtml(fmtDate(l.lastMs))}</div>
        ${userHtml}
      </div>
      <div class="lab-stats">
        <div><div class="lab-badge-label">Productos</div><div class="lab-badge">${nf.format(l.total)}</div></div>
        <div><div class="lab-badge-label">Estado</div><div class="lab-badge state">${status}</div></div>
      </div>
    </button>`;
  }).join('');
}

function renderLabList() {
  const html = buildLabListHtml();
  ['labList', 'viewLabList'].forEach(id => {
    const box = $(id);
    if (box) box.innerHTML = html;
  });
}

function rowMatches(row, query) {
  const q = normalizeKey(query);
  if (!q) return true;
  return [row.codigo, row.descripcion, row.laboratorio, row.stockActual, row.unitsPerEntero, row.enteros, row.unidades, row.totalUnits]
    .some(v => normalizeKey(v).includes(q));
}

function filteredAdminRows() {
  const lab = normalizeKey(getValue('adminViewLab'));
  const desc = normalizeKey(getValue('adminViewDesc'));
  const any = getValue('adminViewAny');
  return sortRowsByDescription(state.inventory.filter(r => {
    if (lab && !normalizeKey(r.laboratorio).includes(lab)) return false;
    if (desc && !normalizeKey(r.descripcion).includes(desc)) return false;
    if (!rowMatches(r, any)) return false;
    return true;
  }));
}

function renderAdminInventory() {
  const body = $('adminViewCards');
  if (!body) return;
  const rows = filteredAdminRows();
  const setText = (id, value) => { const el = $(id); if (el) el.textContent = value; };
  setText('aItems', nf.format(rows.length));
  setText('aTotalUnits', nf.format(rows.reduce((s,r) => s + (Number(r.totalUnits) || 0), 0)));
  setText('aEnteros', nf.format(rows.reduce((s,r) => s + (Number(r.enteros) || 0), 0)));
  setText('aUnidades', nf.format(rows.reduce((s,r) => s + (Number(r.unidades) || 0), 0)));
  if (!state.inventory.length) {
    body.innerHTML = '<div class="inventory-card-empty">Carga primero un archivo de inventario.</div>';
    return;
  }
  if (!rows.length) {
    body.innerHTML = '<div class="inventory-card-empty">No hay resultados con los filtros actuales.</div>';
    return;
  }
  body.innerHTML = rows.map(r => `
    <article class="inventory-item-card">
      <div class="inventory-item-title">${escapeHtml(r.descripcion)}</div>
      <div class="inventory-item-meta">Lab: ${escapeHtml(r.laboratorio)} · Stock actual: ${nf.format(r.stockActual)}</div>
      <div class="inventory-system-panel system-panel">
        <div class="system-label">Sistema</div>
        <div class="system-values">
          <span class="system-chip"><strong>${nf.format(r.enteros)}</strong> ent</span>
          <span class="system-chip"><strong>${nf.format(r.unidades)}</strong> unid</span>
          <span class="system-chip total"><strong>${nf.format(r.totalUnits)}</strong> total</span>
        </div>
        <div class="factor-row"><span>Unid/Entero: <strong>${nf.format(r.unitsPerEntero)}</strong></span>${isAdmin() ? factorEditButton(r) : ''}</div>
        <div class="factor-source">Detección: ${escapeHtml(r.factorSource || 'Sin detalle')}</div>
      </div>
    </article>`).join('');
}

function renderView() {
  // La pestaña Vista ahora muestra laboratorios para todos los usuarios.
  // El detalle de productos se movió a Carga de inventario, solo para administrador.
  renderLabList();
}

function filteredGenerationRows() {
  const lab = normalizeKey(getValue('genLab', state.activeLab) || state.activeLab);
  const query = getValue('genSearch');
  let rows = sortRowsByDescription(state.inventory.filter(r => {
    if (lab && !normalizeKey(r.laboratorio).includes(lab)) return false;
    if (query && !rowMatches(r, query)) return false;
    return true;
  }));
  if (state.showOnlyDiff) rows = rows.filter(r => getDifference(r) !== 0 && hasPhysical(r));
  return rows;
}

function selectedExactLab() {
  const input = normalizeKey(getValue('genLab', state.activeLab) || state.activeLab);
  if (!input) return '';
  const exact = getLabs().find(l => normalizeKey(l) === input);
  if (exact) return exact;
  const starts = getLabs().find(l => normalizeKey(l).startsWith(input));
  return starts || '';
}

function diffClass(diff) {
  if (diff === null) return '';
  if (diff < 0) return 'diff-negative';
  if (diff > 0) return 'diff-positive';
  return 'diff-zero';
}

function diffInline(diff) {
  if (diff === null) return '<span class="pending">Diferencia: -</span>';
  if (diff < 0) return `<span class="neg">Diferencia: ${nf.format(diff)} · Faltante</span>`;
  if (diff > 0) return `<span class="pos">Diferencia: ${nf.format(diff)} · Sobrante</span>`;
  return '<span class="zero">Diferencia: 0 · Sin diferencia</span>';
}

function renderGeneration() {
  const rows = filteredGenerationRows();
  const lab = selectedExactLab();
  const body = $('genBody');
  const counted = rows.filter(r => hasPhysical(r));
  $('gItems').textContent = nf.format(rows.length);
  $('gCounted').textContent = nf.format(counted.length);
  $('gMissing').textContent = nf.format(counted.filter(r => getDifference(r) < 0).length);
  $('gSurplus').textContent = nf.format(counted.filter(r => getDifference(r) > 0).length);

  renderLockBanner(lab);

  if (!state.inventory.length) {
    body.innerHTML = '<div class="inventory-card-empty">El administrador debe cargar un inventario.</div>';
    return;
  }
  if (!lab) {
    body.innerHTML = '<div class="inventory-card-empty">Selecciona o escribe un laboratorio exacto para generar inventario.</div>';
    return;
  }
  if (!rows.length) {
    body.innerHTML = '<div class="inventory-card-empty">No hay productos para el filtro actual.</div>';
    return;
  }
  const canEdit = isLabLockedByCurrent(lab);
  const otherLock = isLockActive(lockForLab(lab)) && !canEdit;
  body.innerHTML = rows.map(r => generationCard(r, canEdit, otherLock)).join('');
}

function generationCard(r, canEdit, otherLock) {
  const parts = getPhysicalParts(r);
  const diff = getDifference(r);
  const cls = diffClass(diff);
  const c = countFor(r);
  const disabled = canEdit ? '' : 'disabled';
  const lockNote = otherLock ? 'Bloqueado por otro usuario' : canEdit ? 'Editable' : 'Toma el laboratorio para editar';
  return `<article class="gen-product-card" data-row-id="${escapeHtml(r.id)}">
    <div class="gen-product-title">${escapeHtml(r.descripcion)}</div>
    <div class="gen-card-body">
      <div class="system-panel">
        <div class="system-label">Sistema</div>
        <div class="system-values">
          <span class="system-chip"><strong>${nf.format(r.enteros)}</strong> ent</span>
          <span class="system-chip"><strong>${nf.format(r.unidades)}</strong> unid</span>
          <span class="system-chip total"><strong>${nf.format(r.totalUnits)}</strong> total</span>
        </div>
        <div class="factor-row"><span>Unid/Entero: <strong>${nf.format(r.unitsPerEntero)}</strong></span>${isAdmin() ? factorEditButton(r) : ''}</div>
        <div class="factor-source">Detección: ${escapeHtml(r.factorSource || 'Sin detalle')}</div>
        <div class="diff-inline">${diffInline(diff)}</div>
      </div>
      <div class="physical-panel">
        <div class="physical-label">Conteo físico</div>
        <div class="physical-inputs">
          <div class="physical-input-group"><label>Enteros</label><input class="count-input ${cls}" type="tel" inputmode="numeric" pattern="[0-9]*" data-row-id="${escapeHtml(r.id)}" data-count-kind="enteros" value="${parts.enteros === '' ? '' : Number(parts.enteros)}" oninput="window.deryiHandleCountInput && window.deryiHandleCountInput(this)" onchange="window.deryiHandleCountCommit && window.deryiHandleCountCommit(this)" onblur="window.deryiHandleCountCommit && window.deryiHandleCountCommit(this)" ${disabled}></div>
          <div class="physical-input-group"><label>Unidades</label><input class="count-input ${cls}" type="tel" inputmode="numeric" pattern="[0-9]*" data-row-id="${escapeHtml(r.id)}" data-count-kind="unidades" value="${parts.unidades === '' ? '' : Number(parts.unidades)}" oninput="window.deryiHandleCountInput && window.deryiHandleCountInput(this)" onchange="window.deryiHandleCountCommit && window.deryiHandleCountCommit(this)" onblur="window.deryiHandleCountCommit && window.deryiHandleCountCommit(this)" ${disabled}></div>
        </div>
        <div class="physical-total-row"><span>Total físico</span><span class="count-total-value ${cls}">${parts.counted ? nf.format(parts.total) : '-'}</span></div>
        <div class="count-meta">${escapeHtml(lockNote)}${c.updatedByName ? `<br>Último: ${escapeHtml(c.updatedByName)} · ${escapeHtml(fmtDate(c.updatedAtMs))}` : ''}</div>
      </div>
    </div>
  </article>`;
}

function factorEditButton(row) {
  return `<button type="button" class="factor-edit-btn" data-factor-edit="${escapeHtml(row.id)}">Editar</button>`;
}

function renderLockBanner(lab) {
  const banner = $('lockBanner');
  if (!lab) {
    banner.className = 'notice info lock-banner';
    banner.textContent = 'Selecciona un laboratorio para iniciar.';
    return;
  }
  const lock = lockForLab(lab);
  if (isLabLockedByCurrent(lab)) {
    banner.className = 'notice lock-banner';
    banner.textContent = `Laboratorio en proceso por ti. Se libera al finalizar, al salir o por 10 minutos sin actividad.`;
  } else if (isLockActive(lock)) {
    banner.className = 'notice warn lock-banner';
    banner.textContent = `Laboratorio bloqueado por ${lock.userName || lock.userEmail || 'otro usuario'}. Última actividad: ${fmtDate(lock.updatedAtMs)}.`;
  } else {
    banner.className = 'notice info lock-banner';
    banner.textContent = 'Laboratorio disponible. Pulsa “Tomar laboratorio” para bloquearlo y registrar conteos.';
  }
}

function registeredByEmail() {
  const byEmail = new Map();
  for (const u of Object.values(state.registeredUsers || {})) {
    if (u.email) byEmail.set(String(u.email).toLowerCase(), u);
  }
  return byEmail;
}

function countStatsForUser(email, uid) {
  const e = String(email || '').toLowerCase();
  const list = Object.values(state.counts || {}).filter(c => {
    const ce = String(c.updatedByEmail || '').toLowerCase();
    return (uid && c.updatedByUid === uid) || (e && ce === e);
  }).sort((a,b) => Number(b.updatedAtMs || 0) - Number(a.updatedAtMs || 0));
  return { total: list.length, last: list[0] || null, list };
}

function mergedUsers() {
  const byEmail = registeredByEmail();
  const map = new Map();
  for (const a of Object.values(state.allowedUsers || {})) {
    const email = String(a.email || a.id || '').toLowerCase();
    if (!email) continue;
    map.set(email, { ...a, email, registered: byEmail.get(email) || null });
  }
  for (const r of byEmail.values()) {
    const email = String(r.email || '').toLowerCase();
    if (!email || map.has(email)) continue;
    map.set(email, { name: r.name, email, role: r.role, active: r.active, color: r.color, registered: r, onlyRegistered: true });
  }
  return [...map.values()].sort((a,b) => (a.name || a.email || '').localeCompare(b.name || b.email || '', 'es'));
}

function renderUsers() {
  const body = $('usersBody');
  if (!body) return;
  const queryText = normalizeKey(getValue('userSearch'));
  let users = mergedUsers();
  if (queryText) {
    users = users.filter(u => normalizeKey([u.name, u.email, u.role, u.active === false ? 'inactivo' : 'activo', u.registered ? 'registrado' : 'pendiente'].join(' ')).includes(queryText));
  }
  const total = mergedUsers();
  const setText = (id, value) => { const el = $(id); if (el) el.textContent = nf.format(value); };
  setText('uTotal', total.length);
  setText('uActive', total.filter(u => u.active !== false).length);
  setText('uOnline', total.filter(u => userOnline(u.registered)).length);
  setText('uAdmins', total.filter(u => (u.role || '') === 'admin').length);

  if (!users.length) {
    body.innerHTML = '<div class="inventory-card-empty">No hay usuarios autorizados con ese filtro.</div>';
    return;
  }

  body.innerHTML = users.map(u => {
    const email = String(u.email || u.id || '').toLowerCase();
    const registered = u.registered || null;
    const active = u.active !== false && registered?.active !== false;
    const online = userOnline(registered);
    const stats = countStatsForUser(email, registered?.uid || registered?.id);
    const color = normalizeColor(u.color ?? registered?.color, 0);
    const colorClass = 'user-color-' + color;
    const isMainAdmin = email === ADMIN_EMAIL.toLowerCase();
    const lastAccess = registered?.lastLoginAtMs ? fmtDate(registered.lastLoginAtMs) : 'Sin ingreso registrado';
    const lastActive = registered?.lastActiveAtMs ? fmtDate(registered.lastActiveAtMs) : 'Sin actividad registrada';
    const lastCount = stats.last?.updatedAtMs ? fmtDate(stats.last.updatedAtMs) : 'Sin conteos';
    return `<article class="user-card ${active ? '' : 'inactive'}" data-user-email="${escapeHtml(email)}" data-user-uid="${escapeHtml(registered?.uid || registered?.id || '')}">
      <div class="user-card-main">
        <div class="user-avatar ${colorClass}">${escapeHtml((u.name || email || '?').slice(0,1).toUpperCase())}</div>
        <div class="user-info">
          <div class="user-title-row">
            <input class="user-name-input" data-user-field="name" value="${escapeHtml(u.name || registered?.name || '')}" ${isMainAdmin ? 'readonly' : ''} />
            <span class="online-pill ${online ? 'online' : ''}">${online ? 'En línea' : 'Fuera de línea'}</span>
          </div>
          <div class="user-email">${escapeHtml(email)}</div>
          <div class="user-meta">
            <span class="role-pill ${(u.role || registered?.role) === 'admin' ? 'admin' : ''}">${escapeHtml(u.role || registered?.role || 'inventariador')}</span>
            <span class="state-pill ${active ? 'active' : 'inactive'}">${active ? 'Activo' : 'Inactivo'}</span>
            <span class="state-pill ${registered ? 'registered' : 'pending'}">${registered ? 'Registrado' : 'Pendiente'}</span>
            <span class="user-chip ${colorClass}">${USER_COLOR_LABELS[color]}</span>
          </div>
        </div>
      </div>
      <div class="user-edit-grid">
        <div><label>Rol</label><select data-user-field="role" ${isMainAdmin ? 'disabled' : ''}><option value="inventariador" ${(u.role || registered?.role) !== 'admin' ? 'selected' : ''}>Inventariador</option><option value="admin" ${(u.role || registered?.role) === 'admin' ? 'selected' : ''}>Administrador</option></select></div>
        <div><label>Estado</label><select data-user-field="active" ${isMainAdmin ? 'disabled' : ''}><option value="true" ${active ? 'selected' : ''}>Activo</option><option value="false" ${!active ? 'selected' : ''}>Inactivo</option></select></div>
        <div><label>Color</label><select data-user-field="color">${userColorOptions(color)}</select></div>
      </div>
      <div class="user-stats-row">
        <div><span>Conteos</span><strong>${nf.format(stats.total)}</strong></div>
        <div><span>Último conteo</span><strong>${escapeHtml(lastCount)}</strong></div>
        <div><span>Último acceso</span><strong>${escapeHtml(lastAccess)}</strong></div>
        <div><span>Última actividad</span><strong>${escapeHtml(lastActive)}</strong></div>
      </div>
      <div class="user-actions">
        <button class="btn" type="button" data-user-action="save">Guardar</button>
        <button class="btn secondary" type="button" data-user-action="history">Historial</button>
        <button class="btn secondary" type="button" data-user-action="reset">Restablecer contraseña</button>
        <button class="btn danger" type="button" data-user-action="delete" ${isMainAdmin ? 'disabled' : ''}>Borrar usuario</button>
      </div>
    </article>`;
  }).join('');
}

function isEditingCountInput() {
  const active = document.activeElement;
  return !!(active && active.classList && active.classList.contains('count-input') && active.closest('#tab-generacion'));
}


function updateGenerationSummary() {
  // Actualiza solo métricas y aviso del laboratorio sin redibujar las tarjetas.
  // Esto evita borrar lo que el usuario está digitando y corrige el error:
  // updateGenerationSummary is not defined.
  const rows = filteredGenerationRows();
  const counted = rows.filter(r => hasPhysical(r));
  const setText = (id, value) => { const el = $(id); if (el) el.textContent = value; };
  setText('gItems', nf.format(rows.length));
  setText('gCounted', nf.format(counted.length));
  setText('gMissing', nf.format(counted.filter(r => getDifference(r) < 0).length));
  setText('gSurplus', nf.format(counted.filter(r => getDifference(r) > 0).length));
  const lab = selectedExactLab();
  if ($('lockBanner')) renderLockBanner(lab);
}

function renderAll() {
  const keepEditing = isEditingCountInput();
  populateLabOptions();
  renderMetrics();
  renderLabList();
  renderAdminInventory();
  renderView();
  if (keepEditing) {
    updateGenerationSummary();
  } else {
    renderGeneration();
  }
  renderUsers();
}

async function createAllowedUser() {
  const name = normalizeText(getValue('newUserName'));
  const email = normalizeText(getValue('newUserEmail')).toLowerCase();
  const role = getValue('newUserRole', 'inventariador');
  const color = normalizeColor(getValue('newUserColor', '0'));
  if (!name || !email) return showMessage($('userMessage'), 'Ingresa nombre y correo.', 'warn');
  await setDoc(doc(db, 'allowedEmails', email), {
    name, email, role, color, active: true,
    createdByUid: state.user.uid,
    createdByEmail: state.user.email,
    createdAt: serverTimestamp(),
    createdAtMs: Date.now(),
    updatedAt: serverTimestamp(),
    updatedAtMs: Date.now()
  }, { merge: true });
  $('newUserName').value = '';
  $('newUserEmail').value = '';
  $('newUserColor').value = String((color + 1) % 8);
  showMessage($('userMessage'), `Usuario autorizado: ${email}. Ya puede crear su contraseña desde “Crear acceso”.`, 'info');
}

function getUserCardData(card) {
  const email = card?.dataset?.userEmail || '';
  const uid = card?.dataset?.userUid || '';
  const field = name => card.querySelector(`[data-user-field="${name}"]`);
  return {
    email,
    uid,
    name: normalizeText(field('name')?.value || ''),
    role: field('role')?.value || 'inventariador',
    active: (field('active')?.value || 'true') === 'true',
    color: normalizeColor(field('color')?.value || 0)
  };
}

async function saveUserCard(card) {
  const data = getUserCardData(card);
  if (!data.email) return;
  if (data.email === ADMIN_EMAIL.toLowerCase()) {
    data.role = 'admin';
    data.active = true;
  }
  if (!data.name) return showMessage($('userMessage'), 'El nombre no puede quedar vacío.', 'warn');
  await setDoc(doc(db, 'allowedEmails', data.email), {
    name: data.name,
    email: data.email,
    role: data.role,
    active: data.active,
    color: data.color,
    updatedByUid: state.user.uid,
    updatedByEmail: state.user.email,
    updatedAt: serverTimestamp(),
    updatedAtMs: Date.now()
  }, { merge: true });
  if (data.uid) {
    await setDoc(doc(db, 'users', data.uid), {
      name: data.name,
      role: data.role,
      active: data.active,
      color: data.color,
      updatedByUid: state.user.uid,
      updatedByEmail: state.user.email,
      updatedAt: serverTimestamp(),
      updatedAtMs: Date.now()
    }, { merge: true });
  }
  showMessage($('userMessage'), `Usuario actualizado: ${data.email}`, 'info');
}

async function deleteUserCard(card) {
  const data = getUserCardData(card);
  if (!data.email || data.email === ADMIN_EMAIL.toLowerCase()) return;
  if (!confirm(`Se borrará el usuario ${data.email} del aplicativo. Se eliminará su autorización y perfil de la app. La cuenta de Firebase Authentication no se borra desde GitHub Pages; si quieres eliminarla totalmente, hazlo desde Firebase Console > Authentication. ¿Continuar?`)) return;
  await deleteDoc(doc(db, 'allowedEmails', data.email));
  if (data.uid) {
    try { await deleteDoc(doc(db, 'users', data.uid)); } catch (err) {
      await setDoc(doc(db, 'users', data.uid), {
        active: false,
        deleted: true,
        isOnline: false,
        disabledAt: serverTimestamp(),
        disabledAtMs: Date.now(),
        disabledByUid: state.user.uid,
        disabledByEmail: state.user.email
      }, { merge: true });
    }
  }
  showMessage($('userMessage'), `Usuario borrado del aplicativo: ${data.email}`, 'warn');
}

async function resetUserPassword(card) {
  const data = getUserCardData(card);
  if (!data.email) return;
  await sendPasswordResetEmail(auth, data.email);
  showMessage($('userMessage'), `Firebase envió un correo de restablecimiento a ${data.email}. El usuario debe abrir el enlace del correo y crear una nueva contraseña.`, 'info');
}

function showUserHistory(card) {
  const data = getUserCardData(card);
  const panel = $('userHistoryPanel');
  if (!panel || !data.email) return;
  const stats = countStatsForUser(data.email, data.uid);
  const rows = stats.list.slice(0, 30);
  panel.classList.remove('hidden');
  panel.innerHTML = `<div class="panel-head"><h3>Historial de ${escapeHtml(data.name || data.email)}</h3><button class="btn secondary" type="button" data-user-action="close-history">Cerrar historial</button></div>
    <div class="notice info">Mostrando los últimos ${nf.format(rows.length)} movimientos de ${nf.format(stats.total)} conteos registrados para este usuario.</div>
    ${rows.length ? `<div class="history-list">${rows.map(c => `<div class="history-item">
      <div><strong>${escapeHtml(c.laboratorio || '-')}</strong><div class="small">${escapeHtml(c.descripcion || '-')}</div></div>
      <div class="history-numbers"><span>Físico: <strong>${nf.format(c.total ?? 0)}</strong></span><span>Diferencia: <strong>${c.diff === null || c.diff === undefined ? '-' : nf.format(c.diff)}</strong></span><span>${escapeHtml(noveltyText(c.diff))}</span></div>
      <div class="small">${escapeHtml(fmtDate(c.updatedAtMs))}</div>
    </div>`).join('')}</div>` : '<div class="inventory-card-empty">Este usuario todavía no tiene conteos registrados.</div>'}`;
  panel.scrollIntoView({ behavior: 'smooth', block: 'start' });
}

function findHeaderRow(rows) {
  const keys = {
    codigo: ['CODIGO', 'COD', 'CODE'],
    descripcion: ['DESCRIPCION', 'DESCRIPCIÓN', 'PRODUCTO', 'ARTICULO', 'ARTÍCULO'],
    laboratorio: ['LABORATORIO', 'LAB', 'PROVEEDOR'],
    stock: ['STOCK ACTUAL', 'STOCK', 'EXISTENCIA', 'CANTIDAD']
  };
  for (let i = 0; i < Math.min(rows.length, 30); i++) {
    const row = rows[i].map(c => normalizeKey(c));
    const map = {};
    for (const [field, aliases] of Object.entries(keys)) {
      map[field] = row.findIndex(cell => aliases.includes(cell));
      if (map[field] < 0) map[field] = row.findIndex(cell => aliases.some(a => cell.includes(a)));
    }
    if (map.descripcion >= 0 && map.laboratorio >= 0 && map.stock >= 0) {
      if (map.codigo < 0) map.codigo = -1;
      return { index: i, map };
    }
  }
  return null;
}

async function loadFile() {
  if (!isAdmin()) return alert('Solo administrador puede cargar inventario.');
  const file = $('fileInput').files[0];
  if (!file) return alert('Selecciona un archivo.');
  if (!window.XLSX) return alert('No se pudo cargar la librería de Excel. Revisa internet y vuelve a abrir la app.');
  if (!confirm('Esto reemplazará el inventario actual y eliminará conteos anteriores. ¿Continuar?')) return;
  showMessage($('loadMessage'), 'Leyendo archivo...', 'info');
  try {
    const buffer = await file.arrayBuffer();
    const wb = XLSX.read(buffer, { type: 'array' });
    const ws = wb.Sheets[wb.SheetNames[0]];
    const rows = XLSX.utils.sheet_to_json(ws, { header: 1, raw: false, defval: '' });
    const header = findHeaderRow(rows);
    if (!header) throw new Error('No se encontraron columnas requeridas: Descripción, Laboratorio y Stock Actual.');
    const cleaned = [];
    let skippedZero = 0;
    let skippedEmpty = 0;
    for (let i = header.index + 1; i < rows.length; i++) {
      const row = rows[i];
      const codigo = header.map.codigo >= 0 ? normalizeText(row[header.map.codigo]) : '';
      const descripcion = normalizeText(row[header.map.descripcion]);
      const laboratorio = normalizeText(row[header.map.laboratorio]);
      const stockActual = toNumber(row[header.map.stock]);
      if (!descripcion || !laboratorio) { skippedEmpty++; continue; }
      if (stockActual === 0) { skippedZero++; continue; }
      const base = { codigo, descripcion, laboratorio, stockActual };
      cleaned.push(enrichRow({ ...base, id: productId(base) }));
    }
    await replaceInventory(cleaned, { fileName: file.name, skippedZero, skippedEmpty, totalRows: rows.length - header.index - 1 });
    showMessage($('loadMessage'), `Carga lista. Guardados: ${cleaned.length}. Eliminados por stock cero: ${skippedZero}. Filas vacías: ${skippedEmpty}.`, 'info');
  } catch (err) {
    console.error(err);
    showMessage($('loadMessage'), 'Error al cargar archivo: ' + err.message, 'danger');
  }
}

async function deleteCollection(collName) {
  const snap = await getDocs(collection(db, collName));
  let batch = writeBatch(db);
  let count = 0;
  for (const d of snap.docs) {
    batch.delete(d.ref);
    count++;
    if (count % 450 === 0) { await batch.commit(); batch = writeBatch(db); }
  }
  if (count % 450 !== 0) await batch.commit();
}

async function replaceInventory(rows, meta) {
  await Promise.all(['inventory', 'counts', 'labLocks', 'labCompletions'].map(deleteCollection));
  let batch = writeBatch(db);
  let count = 0;
  for (const row of rows) {
    const ref = doc(db, 'inventory', row.id);
    batch.set(ref, {
      codigo: row.codigo || '',
      descripcion: row.descripcion,
      laboratorio: row.laboratorio,
      labKey: row.labKey,
      stockActual: row.stockActual,
      unitsPerEntero: row.unitsPerEntero,
      factorSource: row.factorSource,
      enteros: row.enteros,
      unidades: row.unidades,
      totalUnits: row.totalUnits,
      createdAt: serverTimestamp(),
      createdAtMs: Date.now()
    });
    count++;
    if (count % 450 === 0) { await batch.commit(); batch = writeBatch(db); }
  }
  if (count % 450 !== 0) await batch.commit();
  await setDoc(doc(db, 'appMeta', 'current'), {
    ...meta,
    totalSaved: rows.length,
    loadedByUid: state.user.uid,
    loadedByName: state.profile?.name || state.user.email,
    loadedByEmail: state.user.email,
    loadedAt: serverTimestamp(),
    loadedAtMs: Date.now(),
    appVersion
  }, { merge: true });
}

async function takeSelectedLab() {
  const lab = selectedExactLab();
  if (!lab) return alert('Selecciona un laboratorio exacto.');
  await takeLab(lab);
}

async function takeLab(lab) {
  const key = labKey(lab);
  const now = Date.now();
  try {
    await runTransaction(db, async tx => {
      const ref = doc(db, 'labLocks', key);
      const snap = await tx.get(ref);
      if (snap.exists()) {
        const lock = snap.data();
        if (lock.status === 'active' && Number(lock.expiresAtMs || 0) > now && lock.lockedByUid !== state.user.uid) {
          throw new Error(`Laboratorio bloqueado por ${lock.userName || lock.userEmail || 'otro usuario'}.`);
        }
      }
      tx.set(ref, {
        lab,
        labKey: key,
        status: 'active',
        lockedByUid: state.user.uid,
        userName: state.profile?.name || state.user.email,
        userEmail: state.user.email,
        startedAt: serverTimestamp(),
        startedAtMs: now,
        updatedAt: serverTimestamp(),
        updatedAtMs: now,
        expiresAtMs: now + LOCK_TIMEOUT_MS
      }, { merge: true });
    });
    state.activeLab = lab;
    if ($('genLab')) $('genLab').value = lab;
    if ($('genSearch')) $('genSearch').value = '';
    switchTab('generacion');
    startHeartbeat();
  } catch (err) {
    alert(err.message);
  }
}

function startHeartbeat() {
  stopHeartbeat();
  heartbeatTimer = setInterval(() => touchActiveLock(), 60 * 1000);
}

function stopHeartbeat() {
  if (heartbeatTimer) clearInterval(heartbeatTimer);
  heartbeatTimer = null;
}

async function touchActiveLock() {
  if (!state.activeLab || !state.user) return;
  const key = labKey(state.activeLab);
  const lock = state.locks[key];
  if (lock && lock.lockedByUid !== state.user.uid) return;
  try {
    await setDoc(doc(db, 'labLocks', key), {
      lab: state.activeLab,
      labKey: key,
      status: 'active',
      lockedByUid: state.user.uid,
      userName: state.profile?.name || state.user.email,
      userEmail: state.user.email,
      updatedAt: serverTimestamp(),
      updatedAtMs: Date.now(),
      expiresAtMs: Date.now() + LOCK_TIMEOUT_MS
    }, { merge: true });
  } catch (err) { console.warn('No se pudo actualizar actividad', err); }
}

async function releaseActiveLab() {
  if (!state.activeLab || !state.user) return;
  const lab = state.activeLab;
  const key = labKey(lab);
  try {
    const lock = state.locks[key];
    if (!lock || lock.lockedByUid === state.user.uid) {
      await setDoc(doc(db, 'labLocks', key), {
        lab,
        labKey: key,
        status: 'released',
        releasedByUid: state.user.uid,
        releasedByEmail: state.user.email,
        releasedAt: serverTimestamp(),
        releasedAtMs: Date.now(),
        expiresAtMs: Date.now()
      }, { merge: true });
    }
  } catch (err) { console.warn('No se pudo liberar laboratorio', err); }
  state.activeLab = '';
  stopHeartbeat();
  renderGeneration();
}

async function finishActiveLab() {
  const lab = selectedExactLab();
  if (!lab) return alert('Selecciona un laboratorio.');
  if (!isLabLockedByCurrent(lab)) return alert('Primero debes tomar este laboratorio.');
  const rows = state.inventory.filter(r => r.laboratorio === lab);
  const counted = rows.filter(r => hasPhysical(r)).length;
  if (counted < rows.length) return alert(`Faltan productos por contar: ${rows.length - counted}.`);
  await setDoc(doc(db, 'labCompletions', labKey(lab)), {
    lab,
    labKey: labKey(lab),
    completed: true,
    completedByUid: state.user.uid,
    completedByName: state.profile?.name || state.user.email,
    completedByEmail: state.user.email,
    completedAt: serverTimestamp(),
    completedAtMs: Date.now()
  }, { merge: true });
  await releaseActiveLab();
  alert('Laboratorio finalizado y liberado.');
}

function readCountCard(input) {
  const row = state.inventory.find(r => r.id === input.dataset.rowId);
  // El input también tiene data-row-id; por eso NO debemos usar
  // input.closest('[data-row-id]'), porque devuelve el propio input y no la tarjeta.
  // Esto impedía encontrar el otro campo, el total y la diferencia.
  const card = input.closest('.gen-product-card');
  if (!row || !card) return null;
  const enteroInput = card.querySelector('input.count-input[data-count-kind="enteros"]');
  const unidadInput = card.querySelector('input.count-input[data-count-kind="unidades"]');
  if (!enteroInput || !unidadInput) return null;
  const enteros = enteroInput.value === '' ? '' : Math.max(0, Math.round(Number(String(enteroInput.value).replace(',', '.')) || 0));
  const unidades = unidadInput.value === '' ? '' : Math.max(0, Math.round(Number(String(unidadInput.value).replace(',', '.')) || 0));
  const counted = enteroInput.value !== '' || unidadInput.value !== '';
  const total = counted ? ((Number(enteros) || 0) * (Number(row.unitsPerEntero) || 1)) + (Number(unidades) || 0) : '';
  const diff = counted ? Math.round(((Number(total) || 0) - (Number(row.totalUnits) || 0)) * 100) / 100 : null;
  return { row, card, enteroInput, unidadInput, enteros, unidades, total, diff, counted };
}

function updateCountCardVisual(input) {
  const data = readCountCard(input);
  if (!data) return null;
  const cls = diffClass(data.diff);
  [data.enteroInput, data.unidadInput, data.card.querySelector('.count-total-value')].filter(Boolean).forEach(el => {
    el.classList.remove('diff-negative', 'diff-positive', 'diff-zero');
    if (cls) el.classList.add(cls);
  });
  const totalEl = data.card.querySelector('.count-total-value');
  if (totalEl) totalEl.textContent = data.counted ? nf.format(data.total) : '-';
  const diffEl = data.card.querySelector('.diff-inline');
  if (diffEl) diffEl.innerHTML = diffInline(data.diff);
  // Guardado local inmediato para evitar que una actualización en tiempo real borre lo digitado
  // antes de que Firebase confirme el cambio.
  state.counts[data.row.id] = {
    ...(state.counts[data.row.id] || {}),
    productId: data.row.id,
    laboratorio: data.row.laboratorio,
    labKey: data.row.labKey,
    descripcion: data.row.descripcion,
    unitsPerEntero: data.row.unitsPerEntero,
    systemEnteros: data.row.enteros,
    systemUnidades: data.row.unidades,
    systemTotal: data.row.totalUnits,
    physicalEnteros: data.enteros === '' ? '' : data.enteros,
    physicalUnidades: data.unidades === '' ? '' : data.unidades,
    total: data.counted ? data.total : '',
    diff: data.diff,
    novelty: noveltyText(data.diff),
    updatedByUid: state.user?.uid || '',
    updatedByName: state.profile?.name || state.user?.email || '',
    updatedByEmail: state.user?.email || '',
    updatedByColor: normalizeColor(state.profile?.color, 0),
    updatedAtMs: Date.now(),
    localDraft: true
  };
  return data;
}

async function updateCountFromInput(input) {
  const data = updateCountCardVisual(input);
  if (!data) return;
  const { row, enteros, unidades, total, diff } = data;
  if (!isLabLockedByCurrent(row.laboratorio)) {
    input.blur();
    alert('Este laboratorio no está tomado por tu usuario.');
    renderGeneration();
    return;
  }
  const payload = {
    productId: row.id,
    laboratorio: row.laboratorio,
    labKey: row.labKey,
    descripcion: row.descripcion,
    unitsPerEntero: row.unitsPerEntero,
    systemEnteros: row.enteros,
    systemUnidades: row.unidades,
    systemTotal: row.totalUnits,
    physicalEnteros: enteros === '' ? 0 : enteros,
    physicalUnidades: unidades === '' ? 0 : unidades,
    total: total === '' ? 0 : total,
    diff,
    novelty: noveltyText(diff),
    updatedByUid: state.user.uid,
    updatedByName: state.profile?.name || state.user.email,
    updatedByEmail: state.user.email,
    updatedByColor: normalizeColor(state.profile?.color, 0),
    updatedAt: serverTimestamp(),
    updatedAtMs: Date.now()
  };
  state.counts[row.id] = { ...(state.counts[row.id] || {}), ...payload };
  updateGenerationSummary();
  await setDoc(doc(db, 'counts', row.id), payload, { merge: true });
  await touchActiveLock();
}

function scheduleCountSave(input) {
  const data = updateCountCardVisual(input);
  if (!data) return;
  const key = data.row.id;
  clearTimeout(countSaveTimers.get(key));
  countSaveTimers.set(key, setTimeout(() => {
    updateCountFromInput(input).catch(err => {
      console.error(err);
      alert('No se pudo guardar el conteo: ' + (err.message || err));
    });
  }, 450));
}

function handleCountInputInline(input) {
  updateCountCardVisual(input);
  scheduleCountSave(input);
}

function handleCountCommitInline(input) {
  const data = readCountCard(input);
  if (data) clearTimeout(countSaveTimers.get(data.row.id));
  updateCountFromInput(input).catch(err => {
    console.error(err);
    alert('No se pudo guardar el conteo: ' + (err.message || err));
  });
}

window.deryiHandleCountInput = handleCountInputInline;
window.deryiHandleCountCommit = handleCountCommitInline;

function openFactorModal(id) {
  const row = state.inventory.find(r => r.id === id);
  if (!row) return;
  factorModalRowId = id;
  $('modalDesc').textContent = row.descripcion;
  $('modalLab').textContent = row.laboratorio;
  $('modalStock').textContent = nf.format(row.stockActual);
  $('modalFactor').value = row.unitsPerEntero;
  updateModalCalc();
  $('factorModal').classList.remove('hidden');
  $('modalFactor').focus();
}

function closeFactorModal() {
  factorModalRowId = null;
  $('factorModal').classList.add('hidden');
}

function updateModalCalc() {
  const row = state.inventory.find(r => r.id === factorModalRowId);
  if (!row) return;
  const factor = Math.max(1, parseInt(getValue('modalFactor'), 10) || 1);
  const calc = calcStock(row.stockActual, factor);
  $('modalCalc').textContent = `${nf.format(calc.enteros)} enteros + ${nf.format(calc.unidades)} unidades = ${nf.format(calc.totalUnits)} unidades totales`;
}

async function saveFactorFromModal() {
  if (!isAdmin()) return alert('Solo administrador puede editar Unid/Entero.');
  const row = state.inventory.find(r => r.id === factorModalRowId);
  if (!row) return;
  const factor = Math.max(1, parseInt(getValue('modalFactor'), 10) || 1);
  const calc = calcStock(row.stockActual, factor);
  await setDoc(doc(db, 'inventory', row.id), {
    unitsPerEntero: factor,
    factorSource: 'Editado manualmente',
    enteros: calc.enteros,
    unidades: calc.unidades,
    totalUnits: calc.totalUnits,
    updatedAt: serverTimestamp(),
    updatedAtMs: Date.now(),
    updatedByUid: state.user.uid,
    updatedByEmail: state.user.email
  }, { merge: true });
  closeFactorModal();
}

function reportRows(onlyNovelties = false) {
  const lab = selectedExactLab();
  let rows = state.inventory.filter(r => !lab || r.laboratorio === lab);
  rows = sortRowsByDescription(rows.map(r => {
    const p = getPhysicalParts(r);
    const c = countFor(r);
    const diff = getDifference(r);
    return { ...r, physicalParts: p, physical: p.total, diff, novelty: noveltyText(diff), count: c };
  }));
  if (onlyNovelties) rows = rows.filter(r => r.diff !== null && r.diff !== 0);
  return rows;
}

function generatePdf() {
  if (!window.jspdf || !window.jspdf.jsPDF) return alert('No se pudo cargar la librería PDF. Revisa internet.');
  const rows = reportRows(false);
  const lab = selectedExactLab() || 'Todos los laboratorios';
  const { jsPDF } = window.jspdf;
  const docPdf = new jsPDF({ orientation: 'landscape', unit: 'pt', format: 'a4' });
  const now = new Date();
  docPdf.setFontSize(16);
  docPdf.text('DERYI INVENTARIO - Informe de conteo', 40, 40);
  docPdf.setFontSize(10);
  docPdf.text(`Laboratorio: ${lab}`, 40, 60);
  docPdf.text(`Generado: ${now.toLocaleString('es-EC')}`, 40, 76);
  docPdf.text(`Usuario: ${state.profile?.name || state.user?.email}`, 40, 92);
  if (!rows.length) {
    docPdf.text('No hay artículos para el filtro actual.', 40, 120);
  } else {
    docPdf.autoTable({
      startY: 112,
      head: [['Laboratorio','Descripción','Unid/Entero','Sistema ent.','Sistema unid.','Sistema total','Físico ent.','Físico unid.','Físico total','Diferencia','Usuario','Fecha','Novedad']],
      body: rows.map(r => [
        r.laboratorio, r.descripcion, String(r.unitsPerEntero), String(r.enteros), String(r.unidades), String(r.totalUnits),
        r.physicalParts.counted ? String(r.physicalParts.enteros || 0) : '',
        r.physicalParts.counted ? String(r.physicalParts.unidades || 0) : '',
        r.physicalParts.counted ? String(r.physical) : '',
        r.diff === null ? '' : String(r.diff),
        r.count.updatedByName || '',
        r.count.updatedAtMs ? fmtDate(r.count.updatedAtMs) : '',
        r.novelty
      ]),
      styles: { fontSize: 6.5, cellPadding: 3, overflow: 'linebreak' },
      headStyles: { fillColor: [6, 36, 82] },
      columnStyles: { 1: { cellWidth: 170 }, 0: { cellWidth: 85 }, 10: { cellWidth: 65 }, 11: { cellWidth: 55 } },
      didParseCell: function(data) {
        if (data.section === 'body' && data.column.index === 9) {
          const v = Number(data.cell.raw);
          if (v < 0) data.cell.styles.fillColor = [254,226,226];
          if (v > 0) data.cell.styles.fillColor = [219,234,254];
          if (v === 0 && data.cell.raw !== '') data.cell.styles.fillColor = [198,224,180];
        }
      }
    });
  }
  docPdf.save(`deryi_inventario_${safeFileName(lab)}_${now.toISOString().slice(0,10)}.pdf`);
}

function exportCsv() {
  const rows = reportRows(true);
  const header = ['Laboratorio','Descripcion','Unid/Entero','Sistema Enteros','Sistema Unidades','Sistema Total','Fisico Enteros','Fisico Unidades','Fisico Total','Diferencia','Usuario','Fecha','Novedad'];
  const lines = [header, ...rows.map(r => [r.laboratorio, r.descripcion, r.unitsPerEntero, r.enteros, r.unidades, r.totalUnits, r.physicalParts.enteros, r.physicalParts.unidades, r.physical, r.diff, r.count.updatedByName || '', r.count.updatedAtMs ? fmtDate(r.count.updatedAtMs) : '', r.novelty])]
    .map(cols => cols.map(c => '"' + String(c ?? '').replace(/"/g, '""') + '"').join(','));
  const blob = new Blob([lines.join('\n')], { type: 'text/csv;charset=utf-8' });
  const a = document.createElement('a');
  a.href = URL.createObjectURL(blob);
  a.download = `deryi_novedades_${new Date().toISOString().slice(0,10)}.csv`;
  document.body.appendChild(a);
  a.click();
  URL.revokeObjectURL(a.href);
  a.remove();
}

async function updateCurrentUserPresence(isOnline = true) {
  if (!state.user) return;
  try {
    await setDoc(doc(db, 'users', state.user.uid), {
      isOnline,
      lastActiveAt: serverTimestamp(),
      lastActiveAtMs: Date.now()
    }, { merge: true });
  } catch (err) { console.warn('No se pudo actualizar presencia', err); }
}

function startUserPresence() {
  stopUserPresence();
  updateCurrentUserPresence(true);
  userHeartbeatTimer = setInterval(() => updateCurrentUserPresence(true), 60 * 1000);
}

function stopUserPresence() {
  if (userHeartbeatTimer) clearInterval(userHeartbeatTimer);
  userHeartbeatTimer = null;
}

function attachEvents() {
  document.querySelectorAll('.auth-tab').forEach(btn => btn.addEventListener('click', () => switchAuthTab(btn.dataset.authTab)));
  $('loginForm').addEventListener('submit', async e => {
    e.preventDefault();
    try { await login(getValue('loginEmail'), getValue('loginPassword')); }
    catch (err) { showMessage($('authMessage'), 'Error al ingresar: ' + err.message, 'danger'); }
  });
  $('registerForm').addEventListener('submit', async e => {
    e.preventDefault();
    try {
      await registerUser(getValue('registerName'), getValue('registerEmail'), getValue('registerPassword'));
      showMessage($('authMessage'), 'Cuenta creada correctamente.', 'info');
    } catch (err) { showMessage($('authMessage'), 'Error al crear cuenta: ' + err.message, 'danger'); }
  });

  const resetForm = $('resetForm');
  if (resetForm) resetForm.addEventListener('submit', async e => {
    e.preventDefault();
    try {
      await sendLoginPasswordReset(getValue('resetEmail'));
      showMessage($('authMessage'), 'Correo de recuperación enviado. Revisa tu bandeja de entrada o spam.', 'info');
      switchAuthTab('login');
    } catch (err) {
      showMessage($('authMessage'), 'No se pudo enviar el correo: ' + err.message, 'danger');
    }
  });

  $('sideNavEdge').addEventListener('click', () => setSideMenu(!$('sideNav').classList.contains('open')));
  document.addEventListener('click', e => {
    if (!$('sideNav').classList.contains('open')) return;
    if ($('sideNav').contains(e.target) || $('sideNavEdge').contains(e.target)) return;
    setSideMenu(false);
  });
  document.querySelectorAll('.tab-btn').forEach(btn => btn.addEventListener('click', () => switchTab(btn.dataset.tab)));
  document.querySelectorAll('[data-toggle-section]').forEach(btn => btn.addEventListener('click', () => {
    const target = $(btn.dataset.toggleSection);
    setSectionCollapsed(btn.dataset.toggleSection, !target.classList.contains('collapsed'));
  }));

  $('logoutBtn').addEventListener('click', async () => { await releaseActiveLab(); await updateCurrentUserPresence(false); stopUserPresence(); await signOut(auth); });
  $('btnLoadFile').addEventListener('click', loadFile);
  $('btnRefreshCloud').addEventListener('click', renderAll);
  $('btnCreateUser').addEventListener('click', () => createAllowedUser().catch(err => showMessage($('userMessage'), err.message, 'danger')));
  const userSearch = $('userSearch');
  if (userSearch) userSearch.addEventListener('input', renderUsers);
  ['adminViewLab','adminViewDesc','adminViewAny'].forEach(id => { const el = $(id); if (el) el.addEventListener('input', renderAdminInventory); });
  ['genLab','genSearch'].forEach(id => $(id).addEventListener('input', renderGeneration));
  $('btnOnlyDiff').addEventListener('click', () => { state.showOnlyDiff = !state.showOnlyDiff; renderGeneration(); });
  $('btnTakeLab').addEventListener('click', takeSelectedLab);
  $('btnReleaseLab').addEventListener('click', releaseActiveLab);
  $('btnFinishLab').addEventListener('click', finishActiveLab);
  $('btnPdf').addEventListener('click', generatePdf);
  $('btnCsv').addEventListener('click', exportCsv);

  document.body.addEventListener('click', e => {
    const labBtn = e.target.closest('[data-lab-open]');
    if (labBtn) takeLab(labBtn.dataset.labOpen);
    const factorBtn = e.target.closest('[data-factor-edit]');
    if (factorBtn) openFactorModal(factorBtn.dataset.factorEdit);
    const userAction = e.target.closest('[data-user-action]');
    if (userAction) {
      const action = userAction.dataset.userAction;
      const card = userAction.closest('.user-card');
      if (action === 'save') saveUserCard(card).catch(err => showMessage($('userMessage'), err.message, 'danger'));
      if (action === 'delete') deleteUserCard(card).catch(err => showMessage($('userMessage'), err.message, 'danger'));
      if (action === 'reset') resetUserPassword(card).catch(err => showMessage($('userMessage'), 'No se pudo enviar correo: ' + err.message, 'danger'));
      if (action === 'history') showUserHistory(card);
      if (action === 'close-history') $('userHistoryPanel')?.classList.add('hidden');
    }
  });
  document.body.addEventListener('input', e => {
    if (e.target.classList.contains('count-input')) scheduleCountSave(e.target);
  });
  document.body.addEventListener('change', e => {
    if (e.target.classList.contains('count-input')) {
      const data = readCountCard(e.target);
      if (data) clearTimeout(countSaveTimers.get(data.row.id));
      updateCountFromInput(e.target).catch(err => { console.error(err); alert('No se pudo guardar el conteo: ' + (err.message || err)); });
    }
  });
  document.body.addEventListener('keydown', e => {
    if (e.key === 'Escape') { closeFactorModal(); setSideMenu(false); }
  });
  $('btnCloseFactor').addEventListener('click', closeFactorModal);
  $('btnCancelFactor').addEventListener('click', closeFactorModal);
  $('modalFactor').addEventListener('input', updateModalCalc);
  $('btnSaveFactor').addEventListener('click', () => saveFactorFromModal().catch(err => alert(err.message)));
  $('factorModal').addEventListener('click', e => { if (e.target.id === 'factorModal') closeFactorModal(); });

  window.addEventListener('beforeunload', () => { releaseActiveLab(); updateCurrentUserPresence(false); });
  window.addEventListener('pagehide', () => { releaseActiveLab(); updateCurrentUserPresence(false); });
  window.addEventListener('online', () => $('syncState').textContent = 'En línea');
  window.addEventListener('offline', () => $('syncState').textContent = 'Sin conexión');

  window.addEventListener('beforeinstallprompt', e => {
    e.preventDefault();
    deferredInstallPrompt = e;
    $('installBtn').classList.remove('hidden');
  });
  $('installBtn').addEventListener('click', async () => {
    if (!deferredInstallPrompt) return;
    deferredInstallPrompt.prompt();
    await deferredInstallPrompt.userChoice;
    deferredInstallPrompt = null;
    $('installBtn').classList.add('hidden');
  });
}

function authReady() {
  onAuthStateChanged(auth, async user => {
    state.user = user;
    if (!user) {
      state.profile = null;
      unsubscribers.forEach(fn => fn());
      unsubscribers = [];
      stopHeartbeat();
      stopUserPresence();
      $('authPage').classList.remove('hidden');
      $('appPage').classList.add('hidden');
      return;
    }
    try {
      state.profile = await ensureProfile(user);
      $('authPage').classList.add('hidden');
      $('appPage').classList.remove('hidden');
      applyRoleUI();
      startUserPresence();
      attachRealtimeListeners();
      applyCollapsePrefs();
      switchTab(isAdmin() ? 'carga' : 'vista');
      $('syncState').textContent = navigator.onLine ? 'En línea' : 'Sin conexión';
    } catch (err) {
      console.error(err);
      showMessage($('authMessage'), err.message, 'danger');
      await signOut(auth);
    }
  });
}

if ('serviceWorker' in navigator) {
  window.addEventListener('load', () => navigator.serviceWorker.register('./sw.js').catch(() => {}));
}

attachEvents();
if (setupFirebase()) authReady();
