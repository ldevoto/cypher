"use strict";
(() => {
  const APP_VERSION = "1.0.0";
  const CFG = window.CYPHER_CONFIG || {};
  const $ = (id) => document.getElementById(id);
  const te = new TextEncoder();
  const td = new TextDecoder("utf-8", { fatal: true });
  class UserError extends Error {}
  class WrongKeyError extends UserError {}

  // =====================================================================
  // Utilidades
  // =====================================================================
  function b64urlEncode(bytes) {
    let s = "";
    for (let i = 0; i < bytes.length; i += 0x8000) s += String.fromCharCode.apply(null, bytes.subarray(i, i + 0x8000));
    return btoa(s).replace(/\+/g, "-").replace(/\//g, "_").replace(/=+$/, "");
  }
  function b64urlDecode(str) {
    const clean = str.replace(/\s+/g, "");
    if (!/^[A-Za-z0-9_-]*$/.test(clean)) throw new UserError("El texto cifrado contiene caracteres inválidos. ¿Lo copiaste completo y sin modificar?");
    if (clean.length % 4 === 1) throw new UserError("El texto cifrado está incompleto (longitud inválida). Revisá que lo hayas copiado entero.");
    const b64 = clean.replace(/-/g, "+").replace(/_/g, "/") + "===".slice((clean.length + 3) % 4);
    const bin = atob(b64);
    const out = new Uint8Array(bin.length);
    for (let i = 0; i < bin.length; i++) out[i] = bin.charCodeAt(i);
    return out;
  }
  function concat(...arrs) {
    const out = new Uint8Array(arrs.reduce((n, a) => n + a.length, 0));
    let o = 0; for (const a of arrs) { out.set(a, o); o += a.length; }
    return out;
  }
  const rand = (n) => crypto.getRandomValues(new Uint8Array(n));
  const sleep = (ms) => new Promise((r) => setTimeout(r, ms));
  const uuid = () => (crypto.randomUUID ? crypto.randomUUID() : b64urlEncode(rand(16)));
  const now = () => Date.now();
  const fold = (s) => (s || "").normalize("NFD").replace(/[̀-ͯ]/g, "").toLowerCase();
  function fmtDate(ms) {
    if (!ms) return "nunca";
    return new Date(ms).toLocaleString("es", { day: "numeric", month: "short", year: "numeric", hour: "2-digit", minute: "2-digit" });
  }
  function el(tag, attrs, ...kids) {
    const e = document.createElement(tag);
    if (attrs) for (const [k, v] of Object.entries(attrs)) {
      if (v == null || v === false) continue;
      if (k === "class") e.className = v;
      else if (k === "text") e.textContent = v;
      else if (k.startsWith("on")) e.addEventListener(k.slice(2), v);
      else if (k === "style") Object.assign(e.style, v);
      else if (k === "value") e.value = v;
      else if (k in e && typeof v !== "string") e[k] = v;
      else e.setAttribute(k, v === true ? "" : v);
    }
    for (const k of kids) if (k != null) e.append(k);
    return e;
  }
  function showMsg(id, kind, text) { const m = $(id); m.className = "msg show " + kind; m.textContent = text; }
  function hideMsg(id) { const m = $(id); m.className = "msg"; m.textContent = ""; }
  let toastTimer;
  function toast(text, ms = 2600) {
    const t = $("toast");
    t.textContent = text; t.classList.add("show");
    clearTimeout(toastTimer); toastTimer = setTimeout(() => t.classList.remove("show"), ms);
  }
  function errText(e) { return e instanceof UserError ? e.message : "Error inesperado: " + (e && e.message ? e.message : e); }
  function loadJSON(key, fallback) { try { const v = JSON.parse(localStorage.getItem(key)); return v == null ? fallback : v; } catch { return fallback; } }
  function saveJSON(key, v) { try { localStorage.setItem(key, JSON.stringify(v)); } catch (e) { console.warn("localStorage", e); } }

  // Copia al portapapeles; si es un secreto, intenta limpiarlo a los 30 s.
  let clipTimer = null;
  async function copyText(text, secret) {
    if (!text) { toast("No hay nada para copiar."); return false; }
    try {
      await navigator.clipboard.writeText(text);
      toast(secret ? "Copiado. Se borra del portapapeles en 30 s." : "Copiado.");
      if (secret) {
        clearTimeout(clipTimer);
        clipTimer = setTimeout(() => { if (document.hasFocus()) navigator.clipboard.writeText("").catch(() => {}); }, 30000);
      }
      return true;
    } catch {
      toast("El navegador no permitió copiar automáticamente.");
      return false;
    }
  }

  // =====================================================================
  // Cifrado de texto suelto (mismo formato que el cifrador anterior)
  // Formato: Base64URL de sal(16) | iv(16) | cuerpo. Sin cabecera.
  // =====================================================================
  const MIN_ITER = 100000, MAX_ITER = 10000000;
  const SALT_LEN = 16, IV_LEN = 16, MAC_LEN = 32, BLOCK = 32, OVERHEAD = 48;
  const ALGS = {
    1: { name: "AES-256-GCM", extra: 32 },
    2: { name: "AES-256-CBC + HMAC-SHA256", extra: 0 },
    3: { name: "AES-256-CTR + HMAC-SHA256", extra: 16 },
  };
  const KDFS = { 1: "SHA-256", 2: "SHA-512" };

  function pad(data, size) {
    const out = new Uint8Array(size);
    new DataView(out.buffer).setUint32(0, data.length, false);
    out.set(data, 4);
    return out;
  }
  function unpad(buf) {
    if (buf.length < 4) return null;
    const n = new DataView(buf.buffer, buf.byteOffset).getUint32(0, false);
    if (n > buf.length - 4) return null;
    for (let i = 4 + n; i < buf.length; i++) if (buf[i] !== 0) return null;
    return buf.subarray(4, 4 + n);
  }
  async function deriveRaw(password, salt, kdfId, iter) {
    const base = await crypto.subtle.importKey("raw", te.encode(password), "PBKDF2", false, ["deriveBits"]);
    return new Uint8Array(await crypto.subtle.deriveBits({ name: "PBKDF2", hash: KDFS[kdfId], salt, iterations: iter }, base, 512));
  }
  async function keysFor(raw, algId) {
    const cipherName = algId === 1 ? "AES-GCM" : algId === 2 ? "AES-CBC" : "AES-CTR";
    const encKey = await crypto.subtle.importKey("raw", raw.subarray(0, 32), cipherName, false, ["encrypt", "decrypt"]);
    const macKey = algId === 1 ? null :
      await crypto.subtle.importKey("raw", raw.subarray(32, 64), { name: "HMAC", hash: "SHA-256" }, false, ["sign", "verify"]);
    return { encKey, macKey };
  }
  const authData = (algId, salt, iv) => concat(new Uint8Array([algId]), salt, iv);
  function cipherParams(algId, iv, aad) {
    if (algId === 1) return { name: "AES-GCM", iv: iv.subarray(0, 12), additionalData: aad, tagLength: 128 };
    if (algId === 2) return { name: "AES-CBC", iv };
    return { name: "AES-CTR", counter: iv, length: 64 };
  }
  async function encrypt(plaintext, password, algId, kdfId, iter, fixed) {
    const data = te.encode(plaintext);
    const L = Math.max(BLOCK, Math.ceil((data.length + 4) / BLOCK) * BLOCK);
    const salt = fixed ? fixed.salt : rand(SALT_LEN), iv = fixed ? fixed.iv : rand(IV_LEN);
    const raw = await deriveRaw(password, salt, kdfId, iter);
    const { encKey, macKey } = await keysFor(raw, algId);
    raw.fill(0);
    const aad = authData(algId, salt, iv);
    let body = new Uint8Array(await crypto.subtle.encrypt(cipherParams(algId, iv, aad), encKey, pad(data, L + ALGS[algId].extra)));
    if (macKey) body = concat(body, new Uint8Array(await crypto.subtle.sign("HMAC", macKey, concat(aad, body))));
    if (body.length !== L + OVERHEAD) throw new Error("Largo de salida inesperado.");
    return b64urlEncode(concat(salt, iv, body));
  }
  async function tryAlg(raw, algId, salt, iv, body) {
    const { encKey, macKey } = await keysFor(raw, algId);
    const aad = authData(algId, salt, iv);
    let ct = body;
    if (macKey) {
      ct = body.subarray(0, body.length - MAC_LEN);
      const ok = await crypto.subtle.verify("HMAC", macKey, body.subarray(body.length - MAC_LEN), concat(aad, ct));
      if (!ok) return null;
    }
    let pt;
    try { pt = new Uint8Array(await crypto.subtle.decrypt(cipherParams(algId, iv, aad), encKey, ct)); }
    catch { return null; }
    return unpad(pt);
  }
  function splitToken(token) {
    const s = token.trim();
    if (!s) throw new UserError("Pegá el texto cifrado en la entrada.");
    const blob = b64urlDecode(s);
    const bodyLen = blob.length - SALT_LEN - IV_LEN;
    if (bodyLen < BLOCK + OVERHEAD || (bodyLen - OVERHEAD) % BLOCK !== 0)
      throw new UserError("Esto no parece un texto cifrado por esta herramienta, o está incompleto.");
    return { salt: blob.subarray(0, SALT_LEN), iv: blob.subarray(SALT_LEN, SALT_LEN + IV_LEN), body: blob.subarray(SALT_LEN + IV_LEN) };
  }
  async function decrypt(token, password, algId, kdfId, iter) {
    const { salt, iv, body } = splitToken(token);
    const raw = await deriveRaw(password, salt, kdfId, iter);
    let data;
    try { data = await tryAlg(raw, algId, salt, iv, body); } finally { raw.fill(0); }
    if (!data) throw new UserError("No se pudo descifrar. Revisá la clave, el algoritmo, la derivación y las iteraciones: tienen que ser exactamente los mismos que al cifrar. También puede ser que el texto se haya modificado.");
    try { return td.decode(data); }
    catch { throw new UserError("El contenido descifrado no es texto UTF-8 válido."); }
  }
  // Prueba todas las combinaciones de algoritmo y derivación (para el importador).
  async function decryptAny(token, password, iter) {
    const { salt, iv, body } = splitToken(token);
    for (const kdfId of [1, 2]) {
      const raw = await deriveRaw(password, salt, kdfId, iter);
      try {
        for (const algId of [1, 2, 3]) {
          const data = await tryAlg(raw, algId, salt, iv, body);
          if (data) { try { return { text: td.decode(data), algId, kdfId }; } catch { /* sigue */ } }
        }
      } finally { raw.fill(0); }
    }
    return null;
  }

  // =====================================================================
  // Fortaleza de clave (estimación simple)
  // =====================================================================
  function strength(pw) {
    if (!pw) return { bits: 0, label: "" };
    let pool = 0;
    if (/[a-z]/.test(pw)) pool += 26;
    if (/[A-Z]/.test(pw)) pool += 26;
    if (/[0-9]/.test(pw)) pool += 10;
    if (/[^A-Za-z0-9]/.test(pw)) pool += 33;
    let bits = pw.length * Math.log2(Math.max(pool, 2));
    if (/^(.)\1+$/.test(pw)) bits = 4;
    if (/(1234|abcd|qwer|asdf|password|contrase|admin|0000)/i.test(pw)) bits = Math.min(bits, 28);
    let label;
    if (bits < 40) label = "Muy débil: se puede adivinar con fuerza bruta.";
    else if (bits < 60) label = "Débil: insuficiente para proteger contraseñas.";
    else if (bits < 80) label = "Aceptable. Mejor si es más larga.";
    else label = "Fuerte.";
    return { bits, label };
  }
  function paintMeter(barId, textId, pw, emptyText) {
    const { bits, label } = strength(pw);
    const bar = $(barId);
    bar.style.width = Math.min(100, bits) + "%";
    bar.style.background = bits < 40 ? "var(--err)" : bits < 60 ? "var(--warn)" : "var(--ok)";
    $(textId).textContent = pw ? label + " (~" + Math.round(bits) + " bits)" : emptyText;
  }

  // =====================================================================
  // Generador de contraseñas
  // =====================================================================
  const GEN_SETS = { genLower: "abcdefghijklmnopqrstuvwxyz", genUpper: "ABCDEFGHIJKLMNOPQRSTUVWXYZ", genDigits: "0123456789" };
  const DEFAULT_SYMBOLS = "!@#$%^&*()-_=+[]{};:,.?/~";
  function randIndex(n) {
    const limit = Math.floor(0x100000000 / n) * n;
    const buf = new Uint32Array(1);
    do { crypto.getRandomValues(buf); } while (buf[0] >= limit);
    return buf[0] % n;
  }
  function generatePassword(length, sets) {
    const all = sets.join("");
    for (;;) {
      let pw = "";
      for (let i = 0; i < length; i++) pw += all[randIndex(all.length)];
      if (sets.every((set) => [...pw].some((c) => set.includes(c)))) return pw;
    }
  }
  const cleanSymbols = (str) => [...new Set([...str].filter((c) => c.trim() && !/[A-Za-z0-9]/.test(c)))].join("");
  function genOptions() {
    const lenStr = $("genLen").value.trim(), length = Number(lenStr);
    if (!/^\d+$/.test(lenStr) || length < 8 || length > 128) throw new UserError("La longitud debe ser un número entero entre 8 y 128.");
    const sets = Object.keys(GEN_SETS).filter((id) => $(id).checked).map((id) => GEN_SETS[id]);
    if ($("genSymbols").checked) {
      const sym = cleanSymbols($("genSymbolSet").value);
      if (!sym) throw new UserError("Elegiste símbolos pero la lista de símbolos permitidos está vacía.");
      sets.push(sym);
    }
    if (!sets.length) throw new UserError("Elegí al menos un tipo de carácter.");
    if (length < sets.length) throw new UserError("La longitud tiene que ser al menos igual a la cantidad de tipos elegidos.");
    return { length, sets };
  }
  function quickGenerate() {
    try { const o = genOptions(); return generatePassword(o.length, o.sets); }
    catch { return generatePassword(20, [...Object.values(GEN_SETS), DEFAULT_SYMBOLS]); }
  }

  // =====================================================================
  // Bóveda: archivo cifrado
  // Sobre (JSON): { format, version, vaultId, name, kdf:{name,hash,iterations,salt}, cipher, iv, data }
  // El contenido (entradas) va cifrado con AES-256-GCM; el nombre queda visible para poder listarla.
  // =====================================================================
  const VAULT_FORMAT = "cypher-vault", VAULT_VERSION = 1, VAULT_ITER = 600000, VAULT_PAD = 1024;
  const vaultAad = (vaultId, saltB64, iter) => te.encode(`${VAULT_FORMAT}|${VAULT_VERSION}|${vaultId}|PBKDF2-SHA256|${iter}|${saltB64}`);

  async function deriveVaultKey(password, saltB64, iter) {
    const base = await crypto.subtle.importKey("raw", te.encode(password), "PBKDF2", false, ["deriveKey"]);
    return crypto.subtle.deriveKey({ name: "PBKDF2", hash: "SHA-256", salt: b64urlDecode(saltB64), iterations: iter },
      base, { name: "AES-GCM", length: 256 }, false, ["encrypt", "decrypt"]);
  }
  async function sealVault(meta, data, key) {
    let json = JSON.stringify(data);
    const bytes = te.encode(json);
    const target = Math.ceil((bytes.length + 1) / VAULT_PAD) * VAULT_PAD;
    json += " ".repeat(target - bytes.length); // relleno para no revelar el tamaño exacto
    const iv = rand(12);
    const ct = new Uint8Array(await crypto.subtle.encrypt(
      { name: "AES-GCM", iv, additionalData: vaultAad(meta.vaultId, meta.salt, meta.iter), tagLength: 128 }, key, te.encode(json)));
    return {
      format: VAULT_FORMAT, version: VAULT_VERSION, vaultId: meta.vaultId, name: meta.name,
      kdf: { name: "PBKDF2", hash: "SHA-256", iterations: meta.iter, salt: meta.salt },
      cipher: "AES-256-GCM", iv: b64urlEncode(iv), data: b64urlEncode(ct),
    };
  }
  function parseEnvelope(textOrObj) {
    let o = textOrObj;
    if (typeof o === "string") { try { o = JSON.parse(o); } catch { o = null; } }
    const bad = () => new UserError("Esto no es un archivo de bóveda de Cypher, o está dañado.");
    if (!o || o.format !== VAULT_FORMAT || typeof o.data !== "string" || typeof o.iv !== "string" || !o.kdf) throw bad();
    if (o.version !== VAULT_VERSION) throw new UserError("Esta bóveda es de una versión más nueva de la app. Actualizá la app.");
    if (typeof o.vaultId !== "string" || !o.vaultId || typeof o.kdf.salt !== "string") throw bad();
    const it = o.kdf.iterations;
    if (o.kdf.hash !== "SHA-256" || !Number.isInteger(it) || it < MIN_ITER || it > MAX_ITER) throw bad();
    if (typeof o.name !== "string") o.name = "Bóveda";
    return o;
  }
  async function openVault(env, key) {
    let pt;
    try {
      pt = await crypto.subtle.decrypt({ name: "AES-GCM", iv: b64urlDecode(env.iv), additionalData: vaultAad(env.vaultId, env.kdf.salt, env.kdf.iterations), tagLength: 128 },
        key, b64urlDecode(env.data));
    } catch { throw new WrongKeyError("Clave maestra incorrecta."); }
    let data;
    try { data = JSON.parse(td.decode(new Uint8Array(pt))); } catch { throw new UserError("La bóveda se descifró pero su contenido está dañado."); }
    if (!data || !Array.isArray(data.entries)) throw new UserError("La bóveda se descifró pero su contenido está dañado.");
    data.entries = data.entries.filter((e) => e && typeof e.id === "string").map(normEntry);
    return data;
  }
  async function unlockEnvelope(env, password) {
    const key = await deriveVaultKey(password, env.kdf.salt, env.kdf.iterations);
    const data = await openVault(env, key);
    return { key, data };
  }

  // Entradas
  const str = (v) => (typeof v === "string" ? v : "");
  function normEntry(e) {
    if (e.deleted) return { id: e.id, deleted: true, updatedAt: Number(e.updatedAt) || 0 };
    return { id: e.id, title: str(e.title), url: str(e.url), username: str(e.username), password: str(e.password), notes: str(e.notes),
      createdAt: Number(e.createdAt) || 0, updatedAt: Number(e.updatedAt) || 0 };
  }
  function mergeEntries(a, b) {
    const m = new Map();
    for (const e of [...a, ...b]) {
      const cur = m.get(e.id);
      if (!cur || e.updatedAt > cur.updatedAt || (e.updatedAt === cur.updatedAt && e.deleted && !cur.deleted)) m.set(e.id, e);
    }
    return [...m.values()];
  }
  const canon = (entries) => JSON.stringify(entries.map(normEntry).sort((x, y) => (x.id < y.id ? -1 : x.id > y.id ? 1 : 0)));
  async function sha256(s) { return b64urlEncode(new Uint8Array(await crypto.subtle.digest("SHA-256", te.encode(s)))); }
  // Huella del contenido + clave (solo en memoria) para saber si hay cambios por subir.
  const stateHash = (salt, iter, name, entries) => sha256(salt + "|" + iter + "|" + name + "|" + canon(entries));

  // =====================================================================
  // Almacenamiento local
  // =====================================================================
  const LS_SETTINGS = "cypher.settings.v1", LS_VAULTS = "cypher.vaults.v1";
  const settings = Object.assign({
    autoLockMin: 5, rememberLocal: true, driveLinked: false, lastVaultId: null,
    gen: { len: 20, lower: true, upper: true, digits: true, symbols: true, symbolSet: DEFAULT_SYMBOLS },
  }, loadJSON(LS_SETTINGS, {}));
  const saveSettings = () => saveJSON(LS_SETTINGS, settings);

  // Registro de bóvedas conocidas: { [vaultId]: { id, name, env, driveFileId, lastExportAt, updatedAt } }
  // Si "rememberLocal" está apagado, el sobre cifrado queda solo en memoria.
  const vaults = loadJSON(LS_VAULTS, {});
  const memEnv = {};
  function saveVaults() {
    const copy = {};
    for (const [id, v] of Object.entries(vaults)) copy[id] = Object.assign({}, v, { env: settings.rememberLocal ? v.env : null });
    saveJSON(LS_VAULTS, copy);
  }
  function getEnv(id) { return memEnv[id] || (vaults[id] && vaults[id].env) || null; }
  function setEnv(id, env) { memEnv[id] = env; vaults[id].env = env; vaults[id].name = env.name; saveVaults(); }

  // Bóvedas vistas en Drive en esta sesión (sin descargar): { vaultId: {fileId, name, modifiedTime} }
  const driveSeen = {};

  // =====================================================================
  // Google Drive (Google Identity Services + Drive API v3, permiso drive.file)
  // =====================================================================
  const DRIVE_SCOPE = "https://www.googleapis.com/auth/drive.file";
  const API = "https://www.googleapis.com/drive/v3";
  const UPLOAD = "https://www.googleapis.com/upload/drive/v3";
  class DriveAuthError extends UserError {}
  const Drive = {
    token: null, exp: 0, client: null, gisPromise: null, pending: null,
    configured() {
      return !!CFG.googleClientId && (location.protocol === "https:" || location.hostname === "localhost" || location.hostname === "127.0.0.1");
    },
    load() {
      if (!this.configured()) return Promise.reject(new UserError("Google Drive todavía no está configurado en esta app."));
      if (this.gisPromise) return this.gisPromise;
      this.gisPromise = new Promise((resolve, reject) => {
        const done = () => {
          this.client = google.accounts.oauth2.initTokenClient({
            client_id: CFG.googleClientId, scope: DRIVE_SCOPE,
            callback: (r) => this._onToken(r),
            error_callback: (e) => this._onError(e),
          });
          resolve();
        };
        if (window.google && google.accounts && google.accounts.oauth2) return done();
        const s = document.createElement("script");
        s.src = "https://accounts.google.com/gsi/client"; s.async = true;
        s.onload = done;
        s.onerror = () => { this.gisPromise = null; reject(new UserError("No se pudo cargar el inicio de sesión de Google. ¿Hay internet?")); };
        document.head.appendChild(s);
      });
      return this.gisPromise;
    },
    ready() { return !!this.client; },
    hasToken() { return !!this.token && now() < this.exp - 60000; },
    _onToken(r) {
      const p = this.pending; this.pending = null;
      if (r && r.access_token && google.accounts.oauth2.hasGrantedAllScopes(r, DRIVE_SCOPE)) {
        this.token = r.access_token; this.exp = now() + (Number(r.expires_in) || 3600) * 1000;
        if (!settings.driveLinked) { settings.driveLinked = true; saveSettings(); }
        p && p.resolve();
      } else {
        p && p.reject(new UserError(r && r.error ? "Google rechazó el acceso: " + r.error : "No se otorgó el permiso para Google Drive."));
      }
    },
    _onError(e) {
      const p = this.pending; this.pending = null;
      const t = e && e.type;
      p && p.reject(new UserError(t === "popup_closed" ? "Se cerró la ventana de Google antes de terminar." :
        t === "popup_failed_to_open" ? "El navegador bloqueó la ventana de Google. Permití ventanas emergentes para este sitio." : "No se pudo conectar con Google."));
    },
    // Debe llamarse directamente desde un clic (si no, el navegador bloquea la ventana de Google).
    requestToken() {
      if (!this.client) return Promise.reject(new UserError("Google todavía está cargando. Probá de nuevo en un segundo."));
      if (this.pending) this.pending.reject(new UserError("Reemplazado por otra solicitud."));
      return new Promise((resolve, reject) => {
        this.pending = { resolve, reject };
        this.client.requestAccessToken({ prompt: settings.driveLinked ? "" : "consent" });
      });
    },
    revoke() {
      if (this.token && window.google) try { google.accounts.oauth2.revoke(this.token, () => {}); } catch { /* nada */ }
      this.token = null; this.exp = 0;
    },
    async api(url, opts = {}) {
      if (!this.hasToken()) throw new DriveAuthError("Hay que volver a conectar Google Drive.");
      const headers = Object.assign({ Authorization: "Bearer " + this.token }, opts.headers || {});
      let res;
      try { res = await fetch(url, Object.assign({}, opts, { headers })); }
      catch { throw new UserError("Sin conexión con Google Drive."); }
      if (res.status === 401) { this.token = null; throw new DriveAuthError("La sesión de Google venció. Volvé a conectar Drive."); }
      if (!res.ok) {
        let msg = res.status + "";
        try { const j = await res.json(); msg += " " + ((j.error && j.error.message) || ""); } catch { /* nada */ }
        const err = new UserError("Error de Google Drive (" + msg.trim() + ").");
        err.status = res.status;
        throw err;
      }
      return res;
    },
    async listVaults() {
      const q = "appProperties has { key='cypherVault' and value='1' } and trashed=false";
      const url = API + "/files?" + new URLSearchParams({ q, spaces: "drive", pageSize: "100", orderBy: "modifiedTime desc",
        fields: "files(id,name,version,modifiedTime,appProperties)" });
      const j = await (await this.api(url)).json();
      return (j.files || []).filter((f) => f.appProperties && f.appProperties.vaultId);
    },
    async getMeta(id) {
      const url = API + "/files/" + encodeURIComponent(id) + "?fields=id,name,version,modifiedTime,trashed,appProperties";
      return (await this.api(url)).json();
    },
    async download(id) {
      return (await this.api(API + "/files/" + encodeURIComponent(id) + "?alt=media")).text();
    },
    _multipart(meta, content) {
      const boundary = "cypher" + b64urlEncode(rand(12));
      const body = "--" + boundary + "\r\nContent-Type: application/json; charset=UTF-8\r\n\r\n" + JSON.stringify(meta) +
        "\r\n--" + boundary + "\r\nContent-Type: application/octet-stream\r\n\r\n" + content + "\r\n--" + boundary + "--";
      return { body, type: "multipart/related; boundary=" + boundary };
    },
    fileMeta(env) {
      const safe = env.name.replace(/[\\/:*?"<>|]/g, "_");
      return { name: "Cypher - " + safe + ".cypher", appProperties: { cypherVault: "1", vaultId: env.vaultId, vaultName: env.name.slice(0, 60) } };
    },
    async create(env) {
      const m = Object.assign({ mimeType: "application/octet-stream", description: "Bóveda cifrada de Cypher. No la edites a mano." }, this.fileMeta(env));
      const { body, type } = this._multipart(m, JSON.stringify(env));
      const res = await this.api(UPLOAD + "/files?uploadType=multipart&fields=id,version,modifiedTime", { method: "POST", headers: { "Content-Type": type }, body });
      return res.json();
    },
    async update(id, env) {
      const { body, type } = this._multipart(this.fileMeta(env), JSON.stringify(env));
      const res = await this.api(UPLOAD + "/files/" + encodeURIComponent(id) + "?uploadType=multipart&fields=id,version,modifiedTime",
        { method: "PATCH", headers: { "Content-Type": type }, body });
      return res.json();
    },
  };

  // =====================================================================
  // Sesión abierta
  // =====================================================================
  // S = { vaultId, name, key, salt, iter, data:{entries,createdAt}, driveVersion, syncedHash }
  let S = null;
  let persistChain = Promise.resolve();
  const live = () => (S ? S.data.entries.filter((e) => !e.deleted) : []);

  function persist() {
    if (!S) return persistChain;
    const snap = S;
    persistChain = persistChain.then(async () => {
      if (S !== snap) return;
      snap.data.updatedAt = now();
      const env = await sealVault({ vaultId: snap.vaultId, name: snap.name, salt: snap.salt, iter: snap.iter }, snap.data, snap.key);
      if (S !== snap) return;
      setEnv(snap.vaultId, env);
      vaults[snap.vaultId].updatedAt = now();
      saveVaults();
    }).catch((e) => { console.error(e); toast("No se pudo guardar localmente: " + errText(e), 5000); });
    scheduleSync();
    return persistChain;
  }

  // ---------- sincronización ----------
  let syncing = false, syncAgain = false, syncTimer = null, syncState = "off", syncDetail = "";
  function setSync(state, detail) {
    syncState = state; syncDetail = detail || "";
    const chip = $("syncChip");
    const map = {
      off: ["💾 Solo en este dispositivo", ""], auth: ["☁️ Conectar Drive", "warn"], syncing: ["⟳ Sincronizando…", ""],
      ok: ["✓ Guardado en Drive", "ok"], pending: ["● Cambios sin subir", "warn"], offline: ["⚠ Sin conexión", "warn"],
      error: ["⚠ Error al sincronizar", "err"], paused: ["⚠ Sincronización en pausa", "warn"], noconfig: ["💾 Solo en este dispositivo", ""],
    };
    const [txt, cls] = map[state] || map.off;
    chip.textContent = txt; chip.className = "chip " + cls;
    chip.title = detail || txt;
    renderDriveSettings();
  }
  function scheduleSync(delay = 1200) {
    if (!S || !settings.driveLinked || !Drive.configured()) return;
    clearTimeout(syncTimer);
    if (syncState === "ok") setSync("pending");
    syncTimer = setTimeout(() => sync(), delay);
  }
  async function sync() {
    if (!S) return;
    if (!Drive.configured()) { setSync("noconfig"); return; }
    if (!settings.driveLinked) { setSync("off"); return; }
    if (syncing) { syncAgain = true; return; }
    if (!Drive.hasToken()) { setSync("auth", "Tocá para conectar Google Drive y guardar los cambios."); return; }
    if (!navigator.onLine) { setSync("offline", "Los cambios quedan guardados en este dispositivo y se suben cuando vuelva internet."); return; }
    const snap = S;
    syncing = true; setSync("syncing");
    try {
      await persistChain;
      const rec = vaults[snap.vaultId];
      let fileId = rec.driveFileId, meta = null;
      if (fileId) {
        try { meta = await Drive.getMeta(fileId); } catch (e) { if (e.status !== 404) throw e; }
        if (meta && (meta.trashed || !meta.appProperties || meta.appProperties.vaultId !== snap.vaultId)) meta = null;
      }
      if (!meta) {
        const found = (await Drive.listVaults()).find((f) => f.appProperties.vaultId === snap.vaultId);
        if (found) { meta = found; fileId = found.id; } else fileId = null;
        rec.driveFileId = fileId; saveVaults();
        snap.driveVersion = null;
      }
      if (S !== snap) return;

      // 1) Si el archivo de Drive cambió desde la última vez, bajarlo y combinarlo.
      if (meta && meta.version !== snap.driveVersion) {
        const env = parseEnvelope(await Drive.download(fileId));
        if (env.vaultId !== snap.vaultId) throw new UserError("El archivo de Drive no corresponde a esta bóveda.");
        let remote;
        if (env.kdf.salt === snap.salt && env.kdf.iterations === snap.iter) {
          remote = await openVault(env, snap.key);
        } else {
          // La clave maestra se cambió en otro dispositivo: hay que pedir la nueva.
          const r = await askPassword({
            title: "La clave maestra cambió",
            text: "La bóveda “" + env.name + "” en Google Drive está cifrada con otra clave maestra (seguramente la cambiaste en otro dispositivo). Ingresá la clave actual para seguir sincronizando.",
            verify: (pw) => unlockEnvelope(env, pw),
          });
          if (S !== snap) return;
          if (!r) { setSync("paused", "No se ingresó la nueva clave maestra. Los cambios siguen guardados en este dispositivo."); return; }
          snap.key = r.key; snap.salt = env.kdf.salt; snap.iter = env.kdf.iterations;
          remote = r.data;
          toast("Clave maestra actualizada con la de Drive.");
        }
        if (S !== snap) return;
        const before = canon(snap.data.entries);
        snap.data.entries = mergeEntries(snap.data.entries, remote.entries);
        if (env.name !== snap.name && snap.syncedHash == null) snap.name = env.name;
        snap.driveVersion = meta.version;
        snap.syncedHash = await stateHash(env.kdf.salt, env.kdf.iterations, env.name, remote.entries);
        if (canon(snap.data.entries) !== before || !getEnv(snap.vaultId) || getEnv(snap.vaultId).kdf.salt !== snap.salt) {
          await persistNow(snap);
          renderEntries();
        }
        refreshVaultLabels();
      }

      // 2) Subir si hay diferencias.
      const localHash = await stateHash(snap.salt, snap.iter, snap.name, snap.data.entries);
      if (S !== snap) return;
      if (!fileId || localHash !== snap.syncedHash) {
        await persistChain;
        const env = getEnv(snap.vaultId);
        const r = fileId ? await Drive.update(fileId, env) : await Drive.create(env);
        rec.driveFileId = r.id; saveVaults();
        snap.driveVersion = r.version; snap.syncedHash = localHash;
      }
      if (S !== snap) return;
      rec.lastSyncAt = now(); saveVaults();
      setSync("ok", "Última sincronización: " + fmtDate(rec.lastSyncAt));
    } catch (e) {
      console.warn("sync", e);
      if (e instanceof DriveAuthError) setSync("auth", e.message);
      else setSync(navigator.onLine ? "error" : "offline", errText(e));
    } finally {
      syncing = false;
      if (syncAgain && S) { syncAgain = false; scheduleSync(300); }
    }
  }
  async function persistNow(snap) {
    snap.data.updatedAt = now();
    const env = await sealVault({ vaultId: snap.vaultId, name: snap.name, salt: snap.salt, iter: snap.iter }, snap.data, snap.key);
    setEnv(snap.vaultId, env);
  }
  // Conectar Drive desde un clic, y sincronizar.
  function connectAndSync() {
    if (!Drive.configured()) { toast("Google Drive todavía no está configurado en esta app."); return; }
    if (!Drive.ready()) { Drive.load().then(() => toast("Listo. Tocá de nuevo para conectar.")).catch((e) => toast(errText(e))); return; }
    Drive.requestToken().then(() => sync()).catch((e) => { setSync("auth", errText(e)); toast(errText(e), 4000); });
  }

  // =====================================================================
  // Pantalla de inicio: lista de bóvedas
  // =====================================================================
  let selectedVault = null; // { id, fromDrive }
  function homePanel(which) {
    $("homeList").hidden = which !== "list";
    $("unlockForm").hidden = which !== "unlock";
    $("createForm").hidden = which !== "create";
    if (which === "unlock") setTimeout(() => $("unlockPw").focus(), 30);
    if (which === "create") setTimeout(() => $("createName").focus(), 30);
  }
  function allVaultRows() {
    const rows = new Map();
    for (const v of Object.values(vaults)) rows.set(v.id, { id: v.id, name: v.name, local: !!getEnv(v.id), drive: !!v.driveFileId, updatedAt: v.updatedAt || 0 });
    for (const [id, d] of Object.entries(driveSeen)) {
      const r = rows.get(id) || { id, name: d.name, local: false, drive: true, updatedAt: Date.parse(d.modifiedTime) || 0 };
      r.drive = true; rows.set(id, r);
    }
    return [...rows.values()].filter((r) => r.local || driveSeen[r.id])
      .sort((a, b) => (a.id === settings.lastVaultId ? -1 : b.id === settings.lastVaultId ? 1 : a.name.localeCompare(b.name, "es")));
  }
  function renderHome() {
    const list = $("vaultList");
    list.textContent = "";
    const rows = allVaultRows();
    for (const r of rows) {
      const where = r.local && r.drive ? "En este dispositivo y en Drive" : r.local ? "Solo en este dispositivo" : "En Google Drive";
      list.append(el("li", null, el("button", { type: "button", onclick: () => selectVault(r.id) },
        el("span", { class: "v-ico", text: "🗄️" }),
        el("span", { class: "grow" }, el("div", { class: "v-name", text: r.name }), el("div", { class: "v-meta", text: where })),
        el("span", { class: "small", text: "Abrir ›" }))));
    }
    $("vaultListEmpty").hidden = rows.length > 0;
    const drv = $("homeDrive");
    drv.hidden = !Drive.configured();
    $("homeDriveState").textContent = !Drive.configured() ? "" : Drive.hasToken() ? "Drive conectado" : "";
  }
  function selectVault(id) {
    const rec = vaults[id];
    selectedVault = { id, name: (rec && rec.name) || (driveSeen[id] && driveSeen[id].name) || "Bóveda" };
    $("unlockTitle").textContent = "Abrir “" + selectedVault.name + "”";
    $("unlockWhere").textContent = getEnv(id) ? "" : "Se va a descargar de tu Google Drive.";
    $("unlockPw").value = ""; hideMsg("unlockMsg");
    homePanel("unlock");
  }
  async function homeFindInDrive() {
    hideMsg("homeMsg");
    if (!Drive.ready()) {
      showMsg("homeMsg", "info", "Cargando Google…");
      try { await Drive.load(); showMsg("homeMsg", "info", "Listo. Tocá “Buscar en Google Drive” otra vez."); } catch (e) { showMsg("homeMsg", "err", errText(e)); }
      return;
    }
    const tokenP = Drive.hasToken() ? Promise.resolve() : Drive.requestToken();
    try {
      await tokenP;
      showMsg("homeMsg", "info", "Buscando bóvedas en tu Drive…");
      const files = await Drive.listVaults();
      for (const f of files) {
        const id = f.appProperties.vaultId;
        if (!driveSeen[id]) driveSeen[id] = { fileId: f.id, name: f.appProperties.vaultName || f.name, modifiedTime: f.modifiedTime };
        if (vaults[id] && !vaults[id].driveFileId) { vaults[id].driveFileId = f.id; saveVaults(); }
      }
      renderHome();
      showMsg("homeMsg", files.length ? "ok" : "info", files.length ? "Encontré " + files.length + (files.length === 1 ? " bóveda" : " bóvedas") + " en tu Drive."
        : "No hay bóvedas de Cypher en tu Drive todavía. Las que crees se van a guardar ahí automáticamente.");
    } catch (e) { showMsg("homeMsg", "err", errText(e)); }
  }

  async function doUnlock(ev) {
    ev.preventDefault();
    if (!selectedVault) return;
    const id = selectedVault.id, pw = $("unlockPw").value;
    hideMsg("unlockMsg");
    if (!pw) { showMsg("unlockMsg", "err", "Ingresá la clave maestra."); return; }
    // Pedir el permiso de Drive ya, mientras el clic todavía cuenta (si no, se bloquea la ventana de Google).
    let tokenP = null;
    if (settings.driveLinked && Drive.ready() && !Drive.hasToken() && navigator.onLine) tokenP = Drive.requestToken().catch((e) => e);
    const btn = $("unlockBtn"); btn.disabled = true; btn.textContent = "Abriendo…";
    try {
      let env = getEnv(id);
      if (!env) {
        const d = driveSeen[id];
        if (!d) throw new UserError("No encuentro esta bóveda.");
        if (tokenP) { const r = await tokenP; tokenP = null; if (r instanceof Error) throw r; }
        env = parseEnvelope(await Drive.download(d.fileId));
        if (env.vaultId !== id) throw new UserError("El archivo de Drive no corresponde a esta bóveda.");
        vaults[id] = vaults[id] || { id, name: env.name };
        vaults[id].driveFileId = d.fileId;
        setEnv(id, env);
      }
      const { key, data } = await unlockEnvelope(env, pw);
      $("unlockPw").value = "";
      startSession({ vaultId: id, name: env.name, key, salt: env.kdf.salt, iter: env.kdf.iterations, data });
      if (tokenP) { const r = await tokenP; if (r instanceof Error) setSync("auth", errText(r)); }
      sync();
    } catch (e) {
      showMsg("unlockMsg", "err", e instanceof WrongKeyError ? "Clave maestra incorrecta." : errText(e));
      $("unlockPw").select();
    } finally { btn.disabled = false; btn.textContent = "Abrir"; }
  }

  async function doCreate(ev) {
    ev.preventDefault();
    hideMsg("createMsg");
    const name = $("createName").value.trim(), pw = $("createPw").value, pw2 = $("createPw2").value;
    try {
      if (!name) throw new UserError("Poné un nombre para la bóveda.");
      if (pw.length < 8) throw new UserError("La clave maestra tiene que tener al menos 8 caracteres (mejor 16 o más).");
      if (pw !== pw2) throw new UserError("Las claves no coinciden.");
      if (strength(pw).bits < 50 && !confirm("La clave maestra es débil. Si alguien consigue el archivo cifrado podría adivinarla. ¿Crear igual?")) return;
      let tokenP = null;
      if (settings.driveLinked && Drive.ready() && !Drive.hasToken() && navigator.onLine) tokenP = Drive.requestToken().catch((e) => e);
      const btn = $("createBtn"); btn.disabled = true; btn.textContent = "Creando…";
      try {
        const vaultId = uuid(), salt = b64urlEncode(rand(16)), iter = VAULT_ITER;
        const key = await deriveVaultKey(pw, salt, iter);
        const data = { entries: [], createdAt: now() };
        // Verificación: se cifra y se vuelve a abrir antes de dar por creada la bóveda.
        const env = await sealVault({ vaultId, name, salt, iter }, data, key);
        await unlockEnvelope(env, pw);
        vaults[vaultId] = { id: vaultId, name, driveFileId: null, lastExportAt: null, updatedAt: now() };
        setEnv(vaultId, env);
        ["createName", "createPw", "createPw2"].forEach((i) => ($(i).value = ""));
        startSession({ vaultId, name, key, salt, iter, data });
        if (tokenP) { const r = await tokenP; if (r instanceof Error) setSync("auth", errText(r)); }
        sync();
        toast("Bóveda “" + name + "” creada.");
      } finally { btn.disabled = false; btn.textContent = "Crear bóveda"; }
    } catch (e) { showMsg("createMsg", "err", errText(e)); }
  }

  async function importVaultFileHome(file) {
    hideMsg("homeMsg");
    try {
      const env = parseEnvelope(await file.text());
      if (getEnv(env.vaultId)) {
        showMsg("homeMsg", "warn", "La bóveda “" + env.name + "” ya está en este dispositivo. Abrila y usá Ajustes → “Combinar con una copia” para traer los datos de este archivo.");
        return;
      }
      vaults[env.vaultId] = { id: env.vaultId, name: env.name, driveFileId: null, lastExportAt: now(), updatedAt: now() };
      setEnv(env.vaultId, env);
      renderHome();
      selectVault(env.vaultId);
      toast("Archivo cargado. Ingresá su clave maestra.");
    } catch (e) { showMsg("homeMsg", "err", errText(e)); }
  }

  // =====================================================================
  // Abrir / cerrar sesión
  // =====================================================================
  let toolsOnly = false;
  function startSession(s) {
    S = Object.assign({ driveVersion: null, syncedHash: null }, s);
    toolsOnly = false;
    settings.lastVaultId = s.vaultId; saveSettings();
    vaults[s.vaultId].lastOpenedAt = now(); saveVaults();
    $("home").hidden = true; $("app").hidden = false;
    document.querySelectorAll("[data-needs-vault]").forEach((n) => (n.hidden = false));
    $("addEntry").hidden = false;
    refreshVaultLabels();
    $("search").value = "";
    setSync(!Drive.configured() ? "noconfig" : settings.driveLinked ? (Drive.hasToken() ? "syncing" : "auth") : "off");
    showView("vault");
    renderEntries();
    renderBackup();
    touch();
  }
  function openToolsOnly() {
    S = null; toolsOnly = true;
    $("home").hidden = true; $("app").hidden = false;
    document.querySelectorAll("[data-needs-vault]").forEach((n) => (n.hidden = true));
    $("tbVault").textContent = "Cypher · herramientas";
    $("syncChip").hidden = true;
    $("lockBtn").innerHTML = "";
    $("lockBtn").append("← ", el("span", { class: "hide-sm", text: "Bóvedas" }));
    showView("gen");
  }
  function refreshVaultLabels() {
    if (!S) return;
    $("tbVault").textContent = S.name;
    $("renameInput").value = S.name;
    $("syncChip").hidden = false;
    $("lockBtn").innerHTML = "";
    $("lockBtn").append("🔒 ", el("span", { class: "hide-sm", text: "Bloquear" }));
  }
  async function lock(reason) {
    if (S) { try { await persistChain; } catch { /* ya avisado */ } }
    const lastId = S ? S.vaultId : null;
    S = null; toolsOnly = false;
    clearTimeout(syncTimer);
    document.querySelectorAll("dialog[open]").forEach((d) => d.close());
    $("entryList").textContent = "";
    ["search", "fTitle", "fUrl", "fUser", "fPass", "fNotes", "ioText", "ioPw", "pw", "pw2", "input", "output", "genOut", "unlockPw"].forEach((i) => ($(i).value = ""));
    $("ioNotes").textContent = "";
    ioResults = [];
    setOutputSecret(false); hideMsg("msg"); hideMsg("genMsg");
    $("app").hidden = true; $("home").hidden = false;
    renderHome();
    hideMsg("homeMsg");
    if (lastId && (getEnv(lastId) || driveSeen[lastId])) {
      selectVault(lastId);
      if (reason) showMsg("unlockMsg", "info", reason);
    } else {
      homePanel("list");
      if (reason) showMsg("homeMsg", "info", reason);
    }
  }

  // Bloqueo automático por inactividad.
  let lastActivity = now();
  function touch() { lastActivity = now(); }
  ["pointerdown", "keydown", "input", "scroll"].forEach((t) => window.addEventListener(t, touch, { passive: true, capture: true }));
  function checkIdle() {
    if (S && now() - lastActivity > settings.autoLockMin * 60000) lock("La bóveda se bloqueó sola por inactividad.");
  }
  setInterval(checkIdle, 10000);
  document.addEventListener("visibilitychange", () => {
    if (!document.hidden) { checkIdle(); if (S && Drive.hasToken() && syncState !== "syncing") sync(); }
  });
  window.addEventListener("online", () => { if (S) sync(); });
  window.addEventListener("offline", () => { if (S && settings.driveLinked) setSync("offline", "Los cambios quedan guardados en este dispositivo."); });

  // =====================================================================
  // Vistas
  // =====================================================================
  function showView(v) {
    for (const n of ["vault", "gen", "text", "settings"]) $("view-" + n).hidden = n !== v;
    document.querySelectorAll(".nv").forEach((b) => b.setAttribute("aria-current", b.dataset.view === v ? "page" : "false"));
    $("nav").querySelector('[data-view="vault"]').hidden = toolsOnly;
    if (v === "vault" && toolsOnly) return showView("gen");
    window.scrollTo(0, 0);
  }

  // ---------- lista de entradas ----------
  const COLORS = ["#4f8cff", "#2fb46e", "#e0a526", "#e5534b", "#9b6bff", "#1fb5b5", "#e06bb1", "#7a8b99"];
  function colorFor(s) { let h = 0; for (const c of s) h = (h * 31 + c.codePointAt(0)) >>> 0; return COLORS[h % COLORS.length]; }
  function hostOf(url) { try { return new URL(/^[a-z]+:\/\//i.test(url) ? url : "https://" + url).hostname; } catch { return ""; } }
  function renderEntries() {
    const list = $("entryList");
    list.textContent = "";
    if (!S) return;
    const q = fold($("search").value.trim());
    const all = live().sort((a, b) => a.title.localeCompare(b.title, "es", { sensitivity: "base" }));
    const items = q ? all.filter((e) => fold([e.title, e.url, e.username, e.notes].join("\n")).includes(q)) : all;
    for (const e of items) {
      const title = e.title || hostOf(e.url) || "(sin nombre)";
      const sub = e.username || hostOf(e.url) || "";
      const li = el("li", { class: "entry", onclick: () => openEntry(e.id) },
        el("div", { class: "avatar", style: { background: colorFor(title) }, text: [...title][0] || "?" }),
        el("div", { class: "e-main" }, el("div", { class: "e-title", text: title }), el("div", { class: "e-sub", text: sub })),
        el("div", { class: "e-act" },
          e.username ? el("button", { type: "button", title: "Copiar usuario", text: "👤", onclick: (ev) => { ev.stopPropagation(); copyText(e.username, false); } }) : null,
          e.password ? el("button", { type: "button", title: "Copiar contraseña", text: "🔑", onclick: (ev) => { ev.stopPropagation(); copyText(e.password, true); } }) : null));
      list.append(li);
    }
    const empty = $("entryEmpty");
    empty.hidden = items.length > 0;
    empty.firstElementChild.textContent = all.length ? "No hay resultados para esa búsqueda." : "Esta bóveda está vacía.";
    empty.lastElementChild.hidden = all.length > 0;
  }

  // ---------- recordatorio de copia offline ----------
  function renderBackup() {
    if (!S) return;
    const rec = vaults[S.vaultId];
    $("lastExport").textContent = "Última copia descargada: " + fmtDate(rec.lastExportAt) + ".";
    const due = live().length > 0 && (!rec.lastExportAt || now() - rec.lastExportAt > 30 * 86400000);
    const b = $("backupBanner");
    b.textContent = "";
    if (due && !S.backupDismissed) {
      b.className = "msg warn show";
      b.append(rec.lastExportAt ? "Hace más de 30 días que no descargás una copia offline de esta bóveda. " : "Todavía no descargaste una copia offline de esta bóveda. ",
        el("button", { type: "button", class: "link", text: "Descargar ahora", onclick: exportVault }), " · ",
        el("button", { type: "button", class: "link", text: "Más tarde", onclick: () => { S.backupDismissed = true; renderBackup(); } }));
    } else b.className = "msg";
  }
  async function exportVault() {
    if (!S) return;
    await persistChain;
    const env = getEnv(S.vaultId);
    const blob = new Blob([JSON.stringify(env)], { type: "application/octet-stream" });
    const a = el("a", { href: URL.createObjectURL(blob), download: "cypher-" + S.name.replace(/[^\w\-áéíóúñÁÉÍÓÚÑ ]+/g, "_").replace(/\s+/g, "-") + "-" + new Date().toISOString().slice(0, 10) + ".cypher" });
    document.body.append(a); a.click(); a.remove();
    setTimeout(() => URL.revokeObjectURL(a.href), 5000);
    vaults[S.vaultId].lastExportAt = now(); saveVaults();
    renderBackup();
    toast("Copia cifrada descargada. Guardala fuera de Google.", 3500);
  }
  async function mergeVaultFile(file) {
    hideMsg("backupMsg");
    try {
      const env = parseEnvelope(await file.text());
      let data;
      if (env.kdf.salt === S.salt && env.kdf.iterations === S.iter && env.vaultId === S.vaultId) data = await openVault(env, S.key);
      else {
        const r = await askPassword({ title: "Clave del archivo", text: "Ingresá la clave maestra de “" + env.name + "” (la del archivo que estás importando).", verify: (pw) => unlockEnvelope(env, pw) });
        if (!r) return;
        data = r.data;
      }
      const incoming = env.vaultId === S.vaultId ? data.entries : data.entries.filter((e) => !e.deleted).map((e) => Object.assign({}, e, { id: uuid(), updatedAt: now() }));
      const before = live().length;
      S.data.entries = mergeEntries(S.data.entries, incoming);
      await persist();
      renderEntries();
      showMsg("backupMsg", "ok", "Listo. Entradas antes: " + before + ", ahora: " + live().length + ".");
    } catch (e) { showMsg("backupMsg", "err", errText(e)); }
  }

  // ---------- editor de entrada ----------
  let editingId = null;
  function openEntry(id, preset) {
    if (!S) return;
    editingId = id || null;
    const e = id ? S.data.entries.find((x) => x.id === id) : null;
    const v = e || Object.assign({ title: "", url: "", username: "", password: "", notes: "" }, preset || {});
    $("entryDialogTitle").textContent = e ? "Editar entrada" : "Nueva entrada";
    $("fTitle").value = v.title; $("fUrl").value = v.url; $("fUser").value = v.username; $("fPass").value = v.password; $("fNotes").value = v.notes;
    setPwVisible("fPass", false);
    $("fDelete").hidden = !e;
    $("fDates").textContent = e ? "Creada: " + fmtDate(e.createdAt) + " · Modificada: " + fmtDate(e.updatedAt) : "";
    updateEntryStrength();
    $("entryDialog").showModal();
    if (!e) setTimeout(() => $("fTitle").focus(), 30);
  }
  function updateEntryStrength() {
    const p = $("fPass").value;
    $("fPassStrength").textContent = p ? "· " + strength(p).label : "";
  }
  async function saveEntry(ev) {
    ev.preventDefault();
    if (!S) return;
    const vals = { title: $("fTitle").value.trim(), url: $("fUrl").value.trim(), username: $("fUser").value.trim(), password: $("fPass").value, notes: $("fNotes").value };
    if (!vals.title && !vals.url && !vals.username && !vals.password && !vals.notes) { toast("La entrada está vacía."); return; }
    const t = now();
    if (editingId) {
      const i = S.data.entries.findIndex((x) => x.id === editingId);
      if (i >= 0) S.data.entries[i] = normEntry(Object.assign({}, S.data.entries[i], vals, { updatedAt: t }));
    } else {
      S.data.entries.push(normEntry(Object.assign({ id: uuid(), createdAt: t, updatedAt: t }, vals)));
    }
    $("entryDialog").close();
    renderEntries(); renderBackup();
    await persist();
    toast("Guardado.");
  }
  async function deleteEntry() {
    if (!S || !editingId) return;
    const e = S.data.entries.find((x) => x.id === editingId);
    if (!confirm("¿Eliminar “" + (e.title || "esta entrada") + "”? Si te arrepentís, podés recuperarla de una copia o de las versiones anteriores en Drive.")) return;
    const i = S.data.entries.findIndex((x) => x.id === editingId);
    S.data.entries[i] = { id: editingId, deleted: true, updatedAt: now() };
    $("entryDialog").close();
    renderEntries();
    await persist();
    toast("Entrada eliminada.");
  }

  // ---------- diálogo genérico para pedir una clave ----------
  // verify(pw) -> resultado; si lanza WrongKeyError se vuelve a pedir. Devuelve null si se cancela.
  function askPassword({ title, text, verify, confirmField, okText }) {
    return new Promise((resolve) => {
      const d = $("promptDialog");
      $("promptTitle").textContent = title; $("promptText").textContent = text || "";
      const f = $("promptFields"); f.textContent = "";
      const mk = (id, label) => {
        f.append(el("label", { for: id, text: label }), el("div", { class: "pw" }, el("input", { type: "password", id, autocomplete: "off", spellcheck: "false" }),
          el("button", { type: "button", text: "Mostrar", onclick: (ev) => { const i = $(id); i.type = i.type === "password" ? "text" : "password"; ev.target.textContent = i.type === "password" ? "Mostrar" : "Ocultar"; } })));
      };
      mk("promptPw", confirmField ? "Clave maestra actual" : "Clave maestra");
      if (confirmField) { mk("promptNew", "Nueva clave maestra"); mk("promptNew2", "Repetir nueva clave maestra"); }
      $("promptOk").textContent = okText || "Aceptar";
      hideMsg("promptMsg");
      let busy = false;
      const finish = (v) => { cleanup(); d.close(); resolve(v); };
      const onSubmit = async (ev) => {
        ev.preventDefault();
        if (busy) return;
        const pw = $("promptPw").value;
        if (!pw) { showMsg("promptMsg", "err", "Ingresá la clave."); return; }
        if (confirmField) {
          const n1 = $("promptNew").value, n2 = $("promptNew2").value;
          if (n1.length < 8) { showMsg("promptMsg", "err", "La nueva clave tiene que tener al menos 8 caracteres."); return; }
          if (n1 !== n2) { showMsg("promptMsg", "err", "Las claves nuevas no coinciden."); return; }
        }
        busy = true; $("promptOk").disabled = true;
        try {
          const r = await verify(pw, confirmField ? $("promptNew").value : undefined);
          finish(r);
        } catch (e) {
          showMsg("promptMsg", "err", e instanceof WrongKeyError ? "Clave incorrecta." : errText(e));
        } finally { busy = false; $("promptOk").disabled = false; }
      };
      const onCancel = (ev) => { if (ev) ev.preventDefault(); finish(null); };
      const cleanup = () => {
        $("promptForm").removeEventListener("submit", onSubmit);
        $("promptCancel").removeEventListener("click", onCancel);
        d.removeEventListener("cancel", onCancel);
        f.textContent = "";
      };
      $("promptForm").addEventListener("submit", onSubmit);
      $("promptCancel").addEventListener("click", onCancel);
      d.addEventListener("cancel", onCancel);
      d.showModal();
      setTimeout(() => $("promptPw").focus(), 30);
    });
  }

  // ---------- ajustes de bóveda ----------
  async function changeMasterPassword() {
    if (!S) return;
    const snap = S;
    const r = await askPassword({
      title: "Cambiar clave maestra", okText: "Cambiar", confirmField: true,
      text: "En tus otros dispositivos te la va a pedir la próxima vez que sincronicen. Las copias descargadas antes siguen abriéndose con la clave vieja.",
      verify: async (oldPw, newPw) => {
        const env = getEnv(snap.vaultId);
        await unlockEnvelope(env, oldPw); // verifica la clave actual
        const salt = b64urlEncode(rand(16)), iter = VAULT_ITER;
        const key = await deriveVaultKey(newPw, salt, iter);
        const test = await sealVault({ vaultId: snap.vaultId, name: snap.name, salt, iter }, snap.data, key);
        await unlockEnvelope(test, newPw);
        return { key, salt, iter };
      },
    });
    if (!r || S !== snap) return;
    S.key = r.key; S.salt = r.salt; S.iter = r.iter;
    await persist();
    showMsg("vaultMsg", "ok", "Clave maestra cambiada." + (settings.driveLinked ? " Se va a subir a Drive." : "") + " Te conviene descargar una copia nueva.");
  }
  async function renameVault() {
    if (!S) return;
    const n = $("renameInput").value.trim();
    if (!n) { showMsg("vaultMsg", "err", "El nombre no puede quedar vacío."); return; }
    S.name = n; vaults[S.vaultId].name = n;
    refreshVaultLabels();
    await persist();
    showMsg("vaultMsg", "ok", "Nombre cambiado.");
  }
  async function forgetVault() {
    if (!S) return;
    const rec = vaults[S.vaultId];
    const safe = rec.driveFileId && syncState === "ok";
    const msg = safe
      ? "Se va a quitar “" + S.name + "” de este dispositivo. Sigue estando en tu Google Drive y la podés volver a abrir desde ahí. ¿Continuar?"
      : "ATENCIÓN: “" + S.name + "” no está sincronizada con Google Drive. Si la quitás y no tenés una copia descargada, la vas a perder. ¿Quitar igual de este dispositivo?";
    if (!confirm(msg)) return;
    const id = S.vaultId;
    await lock();
    delete vaults[id]; delete memEnv[id];
    if (settings.lastVaultId === id) settings.lastVaultId = null;
    saveVaults(); saveSettings();
    renderHome();
    showMsg("homeMsg", "ok", "Bóveda quitada de este dispositivo.");
  }
  function renderDriveSettings() {
    const info = $("driveInfo");
    if (!info) return;
    const conn = $("driveConnect"), syncBtn = $("driveSyncNow"), disc = $("driveDisconnect");
    if (!Drive.configured()) {
      info.textContent = "Google Drive todavía no está configurado en esta copia de la app. Mientras tanto, la bóveda se guarda solo en este dispositivo: descargá copias seguido.";
      conn.hidden = syncBtn.hidden = disc.hidden = true;
      return;
    }
    const rec = S && vaults[S.vaultId];
    const linked = settings.driveLinked;
    conn.hidden = linked && Drive.hasToken();
    conn.textContent = linked ? "Reconectar Google Drive" : "Conectar Google Drive";
    syncBtn.hidden = !linked || !Drive.hasToken();
    disc.hidden = !linked;
    info.textContent = !linked
      ? "Conectá tu Google Drive para que cada bóveda se guarde ahí automáticamente (cifrada) y la tengas en todos tus dispositivos. La app solo puede ver los archivos que ella misma crea."
      : (Drive.hasToken() ? "Conectado. " : "Vinculado, pero hay que reconectar en esta sesión. ") +
        (rec && rec.driveFileId ? "Esta bóveda está en tu Drive. " : "Esta bóveda todavía no se subió. ") +
        (rec && rec.lastSyncAt ? "Última sincronización: " + fmtDate(rec.lastSyncAt) + "." : "") + (syncDetail && syncState !== "ok" ? "\n" + syncDetail : "");
  }

  // =====================================================================
  // Importador de notas cifradas viejas
  // =====================================================================
  let ioResults = [];
  const FIELD_KEYS = {
    title: /^(sitio|site|web|servicio|cuenta|nombre|app|title|t[ií]tulo)$/i,
    url: /^(url|link|enlace|p[aá]gina|direcci[oó]n)$/i,
    username: /^(usuario|user|username|login|mail|e-?mail|correo|id)$/i,
    password: /^(contrase[nñ]a|password|pass|clave|pwd|pin|psw)$/i,
    notes: /^(nota|notas|notes|obs|observaciones)$/i,
  };
  function fieldOf(key) { for (const [f, re] of Object.entries(FIELD_KEYS)) if (re.test(key.trim())) return f; return null; }
  function splitUserPass(value) {
    const m = value.match(/^(\S+)\s*(?:\s\/\s|\s\|\s|\s+)\s*(\S+)$/);
    if (m && (m[1].includes("@") || /^[\w.\-]+$/.test(m[1]))) return { username: m[1], password: m[2], review: true };
    return { username: "", password: value, review: /\s/.test(value) };
  }
  // Convierte el texto de una nota en una o varias entradas candidatas.
  function parseOldNote(text) {
    const lines = text.split(/\r?\n/).map((l) => l.trim()).filter(Boolean);
    const kv = lines.map((l) => {
      if (/^https?:\/\//i.test(l)) return { url: l };
      const m = l.match(/^([^:]{1,40}?)\s*[:=]\s*(.*)$/);
      return m ? { key: m[1], value: m[2], field: fieldOf(m[1]) } : { text: l };
    });
    const hasFields = kv.some((x) => x.field === "username" || x.field === "password");
    if (hasFields) {
      // Una sola entrada con campos "usuario: …", "contraseña: …".
      const e = { title: "", url: "", username: "", password: "", notes: "" };
      const extra = [];
      for (const x of kv) {
        if (x.url) { if (!e.url) e.url = x.url; else extra.push(x.url); }
        else if (x.field && !e[x.field]) e[x.field] = x.value;
        else if (x.text && !e.title) e.title = x.text;
        else extra.push(x.text || x.key + ": " + x.value);
      }
      e.notes = [e.notes, ...extra].filter(Boolean).join("\n");
      if (!e.title) e.title = hostOf(e.url) || "Nota importada";
      return [e];
    }
    // Una entrada por línea "sitio: contraseña" (o "sitio: usuario contraseña").
    const out = [];
    for (const x of kv) {
      if (x.key != null && x.value) {
        const up = splitUserPass(x.value);
        out.push({ title: x.key, url: "", username: up.username, password: up.password, notes: "", review: up.review });
      } else {
        const t = x.url || x.text || (x.key != null ? x.key + ":" : "");
        if (out.length) {
          const last = out[out.length - 1];
          if (x.url && !last.url) last.url = x.url; else last.notes = [last.notes, t].filter(Boolean).join("\n");
        } else out.push({ title: x.text || hostOf(x.url) || "Nota importada", url: x.url || "", username: "", password: "", notes: "", review: true });
      }
    }
    if (!out.length) out.push({ title: "Nota importada", url: "", username: "", password: "", notes: text, review: true });
    return out;
  }
  function openImportOld() {
    $("ioStep1").hidden = false; $("ioStep2").hidden = true; $("ioFoot").hidden = true;
    hideMsg("ioMsg");
    $("importOldDialog").showModal();
  }
  async function ioDecrypt() {
    hideMsg("ioMsg");
    const pw = $("ioPw").value, iterStr = $("ioIter").value.trim(), iter = Number(iterStr);
    const tokens = $("ioText").value.split(/\s+/).map((t) => t.trim()).filter(Boolean);
    try {
      if (!tokens.length) throw new UserError("Pegá al menos un texto cifrado.");
      if (!pw) throw new UserError("Ingresá la clave con la que cifraste las notas.");
      if (!/^\d+$/.test(iterStr) || iter < MIN_ITER || iter > MAX_ITER) throw new UserError("Las iteraciones deben ser un número entero entre 100.000 y 10.000.000.");
    } catch (e) { showMsg("ioMsg", "err", e.message); return; }
    const btn = $("ioDecrypt"); btn.disabled = true;
    ioResults = [];
    const existing = new Set(live().map((e) => fold(e.title) + "\u0000" + e.password));
    try {
      for (let i = 0; i < tokens.length; i++) {
        btn.textContent = "Descifrando " + (i + 1) + " de " + tokens.length + "…";
        let r = null, err = null;
        try { r = await decryptAny(tokens[i], pw, iter); } catch (e) { err = e; }
        if (!r) { ioResults.push({ ok: false, why: err ? errText(err) : "No se pudo descifrar con esa clave e iteraciones.", token: tokens[i] }); continue; }
        const cands = parseOldNote(r.text).map((c) => {
          const dup = existing.has(fold(c.title) + "\u0000" + c.password);
          return Object.assign(c, { selected: !dup, dup });
        });
        ioResults.push({ ok: true, text: r.text, alg: ALGS[r.algId].name + " · PBKDF2-" + KDFS[r.kdfId], cands });
      }
    } finally { btn.disabled = false; btn.textContent = "Descifrar"; }
    renderIo();
  }
  function renderIo() {
    const box = $("ioNotes"); box.textContent = "";
    const okN = ioResults.filter((r) => r.ok).length, failN = ioResults.length - okN;
    $("ioSummary").textContent = "Se descifraron " + okN + " de " + ioResults.length + " notas." + (failN ? " Las que fallaron pueden tener otra clave o iteraciones: volvé atrás y probalas aparte." : "") +
      " Revisá cada entrada detectada: corregí lo que haga falta y destildá lo que no quieras importar.";
    ioResults.forEach((r, ni) => {
      const card = el("div", { class: "io-note" });
      if (!r.ok) {
        card.append(el("div", { class: "io-note-head" }, el("b", { text: "Nota " + (ni + 1) + ": no se pudo descifrar" })), el("div", { class: "small", text: r.why }),
          el("div", { class: "io-raw", text: r.token.slice(0, 60) + (r.token.length > 60 ? "…" : "") }));
        box.append(card); return;
      }
      const raw = el("div", { class: "io-raw", hidden: true, text: r.text });
      card.append(el("div", { class: "io-note-head" },
        el("b", { text: "Nota " + (ni + 1) + " · " + r.cands.length + (r.cands.length === 1 ? " entrada" : " entradas") }),
        el("button", { type: "button", class: "link", text: "Ver texto descifrado", onclick: (ev) => { raw.hidden = !raw.hidden; ev.target.textContent = raw.hidden ? "Ver texto descifrado" : "Ocultar texto"; } })),
      el("div", { class: "small", text: r.alg }), raw);
      r.cands.forEach((c) => {
        const inp = (field, ph, type) => el("input", { type: type || "text", value: c[field], placeholder: ph, spellcheck: "false", oninput: (ev) => { c[field] = ev.target.value; } });
        card.append(el("div", { class: "io-cand" },
          el("input", { type: "checkbox", checked: c.selected, title: "Importar", onchange: (ev) => { c.selected = ev.target.checked; updateIoCount(); } }),
          inp("title", "Nombre o sitio"), inp("username", "Usuario"), inp("password", "Contraseña", "password"),
          el("textarea", { placeholder: "Notas", value: c.notes, oninput: (ev) => { c.notes = ev.target.value; } }),
          c.dup ? el("div", { class: "tag", text: "Ya existe una entrada igual en la bóveda (destildada)." }) :
            c.review ? el("div", { class: "tag", text: "Revisá que usuario y contraseña hayan quedado bien separados." }) : null));
      });
      box.append(card);
    });
    $("ioStep1").hidden = true; $("ioStep2").hidden = false; $("ioFoot").hidden = false;
    updateIoCount();
  }
  function updateIoCount() {
    const n = ioResults.reduce((s, r) => s + (r.ok ? r.cands.filter((c) => c.selected).length : 0), 0);
    $("ioImport").textContent = "Importar " + n + (n === 1 ? " entrada" : " entradas");
    $("ioImport").disabled = n === 0;
  }
  async function ioImport() {
    if (!S) return;
    const t = now();
    let n = 0;
    for (const r of ioResults) if (r.ok) for (const c of r.cands) if (c.selected) {
      S.data.entries.push(normEntry({ id: uuid(), title: c.title.trim(), url: c.url.trim(), username: c.username.trim(), password: c.password, notes: c.notes, createdAt: t, updatedAt: t }));
      n++;
    }
    ioResults = []; $("ioNotes").textContent = ""; $("ioText").value = ""; $("ioPw").value = "";
    $("importOldDialog").close();
    renderEntries();
    await persist();
    showView("vault");
    toast("Se importaron " + n + (n === 1 ? " entrada." : " entradas."), 3500);
  }

  // =====================================================================
  // Herramienta: cifrar / descifrar texto suelto
  // =====================================================================
  let mode = "enc";
  function setOutputSecret(isSecret) {
    $("reveal").classList.toggle("hidden", !isSecret);
    $("output").style.webkitTextSecurity = isSecret ? "disc" : "";
    $("output").dataset.secret = isSecret ? "1" : "";
    $("reveal").textContent = "Mostrar texto";
  }
  function setMode(m) {
    mode = m;
    const enc = m === "enc";
    $("tabEnc").setAttribute("aria-selected", enc);
    $("tabDec").setAttribute("aria-selected", !enc);
    $("confirmBox").style.display = enc ? "" : "none";
    $("inputLabel").textContent = enc ? "Texto a cifrar" : "Texto cifrado";
    $("input").placeholder = enc ? "Escribí o pegá el texto…" : "Pegá el texto cifrado…";
    $("run").textContent = enc ? "Cifrar" : "Descifrar";
    hideMsg("msg");
    updateMatch();
  }
  function updateMatch() {
    const t = $("matchText");
    if (mode !== "enc" || !$("pw2").value) { t.textContent = ""; return; }
    const ok = $("pw").value === $("pw2").value;
    t.textContent = ok ? "Coinciden." : "No coinciden.";
    t.style.color = ok ? "var(--ok)" : "var(--err)";
  }
  async function runText() {
    hideMsg("msg");
    const pw = $("pw").value, input = $("input").value;
    const run = $("run");
    try {
      if (!window.crypto || !crypto.subtle) throw new UserError("Este navegador no ofrece Web Crypto.");
      if (!pw) throw new UserError("Ingresá la clave.");
      const algId = Number($("alg").value), kdfId = Number($("kdf").value);
      const iterStr = $("iter").value.trim(), iter = Number(iterStr);
      if (!/^\d+$/.test(iterStr) || iter < MIN_ITER || iter > MAX_ITER)
        throw new UserError("Las iteraciones deben ser un número entero entre 100.000 y 10.000.000 (sin puntos ni comas).");
      if (mode === "enc") {
        if (pw !== $("pw2").value) throw new UserError("Las claves no coinciden. Si cifrás con una clave mal tipeada, no vas a poder descifrar después.");
        if (!input) throw new UserError("Escribí el texto a cifrar.");
        run.disabled = true; run.textContent = "Cifrando…";
        const out = await encrypt(input, pw, algId, kdfId, iter);
        if (await decrypt(out, pw, algId, kdfId, iter) !== input) throw new Error("La verificación posterior al cifrado falló.");
        setOutputSecret(false);
        $("output").value = out;
        if (strength(pw).bits < 60) showMsg("msg", "warn", "Cifrado y verificado, pero la clave es débil.");
        else showMsg("msg", "ok", "Cifrado y verificado con " + ALGS[algId].name + ", PBKDF2-" + KDFS[kdfId] + " y " + iter.toLocaleString("es") + " iteraciones.");
      } else {
        run.disabled = true; run.textContent = "Descifrando…";
        $("output").value = await decrypt(input, pw, algId, kdfId, iter);
        setOutputSecret(true);
        showMsg("msg", "ok", "Descifrado correctamente.");
      }
    } catch (e) {
      $("output").value = ""; setOutputSecret(false);
      showMsg("msg", "err", errText(e));
    } finally { run.disabled = false; run.textContent = mode === "enc" ? "Cifrar" : "Descifrar"; }
  }

  // =====================================================================
  // Autoprueba
  // =====================================================================
  const TEST_PW = "clave-de-prueba", TEST_ITER = 1000;
  const TEST_TEXT = "Autoprueba Cypher ✓ ñ 🔑 0123456789";
  const TEST_SALT = Uint8Array.from({ length: 16 }, (_, i) => i + 1);
  const TEST_IV = Uint8Array.from({ length: 16 }, (_, i) => 0xA0 + i);
  const TEST_VECTORS = [
    [1, 1, "AQIDBAUGBwgJCgsMDQ4PEKChoqOkpaanqKmqq6ytrq8rCvrERx0_KIUDvhqAYZ7tQ1FvbvkLe7gWpwPoT5O6e5DZ0XEMxNXTZNxYnBoufYCJGeqrJab841A_MpffLdFMWrFZIP6Z1uQgzkq_lQb1UbcQZO_vzuU2XYmqzf5W2Cl8xOhLL8FiUQuoLsmP6NtO"],
    [2, 1, "AQIDBAUGBwgJCgsMDQ4PEKChoqOkpaanqKmqq6ytrq8IdniDESCRk7aoWI2_joDR1wjXG9tWUlSdh3M18_SVkYtNvFG-Vonr6P0WBvjge53jL3iUtg59VXJLE1Hv6sxWeXkfZgYoHQhWDLiEoeaZEoP0D7exeBHmVh-vND8OhmcgYLfd4-wnUYSW1K9AnJIt"],
    [3, 1, "AQIDBAUGBwgJCgsMDQ4PEKChoqOkpaanqKmqq6ytrq_X1nuAIsskAZSEaTpPDPrFNDga8U-BQFkBc-cPrxf7RjxY27c6PfhwUJTf31N7ZhVHAHxDFnGjXjdj4syXDvQBWz8ZBY1DanFSt20fkWYjqaQPNt2uKEQAoLc5GE-DrLcTIbBwa51S_5VGNkffpbEW"],
    [1, 2, "AQIDBAUGBwgJCgsMDQ4PEKChoqOkpaanqKmqq6ytrq-AiNxKXKz4V84wfu-LukDkajYYfkJClLaEgryGLO3mYT406GK4ny7KGRvGjiTM9iP32qqRHKiS7REWXpGBo0wrKSIcDzSrbMqzkN7ZTEamldo-8KwKL5ZdjulLMKfZQFQeOXgpjxLxt3_-sqYGt_Mq"],
    [2, 2, "AQIDBAUGBwgJCgsMDQ4PEKChoqOkpaanqKmqq6ytrq-1xQ5P-aBKmu792pe81zsoWq1bEBRIiz9pxp6uWvfnCOdK0ZuHj62VOM4gTMMMMXPZaYc6vuoat-_AVDEoaTw0AtYb4UuQLk78-uEBDVa_dYz9movSpWrH05ChSlEF-Z4mpo4_lSq_rORcBoHmgA4p"],
    [3, 2, "AQIDBAUGBwgJCgsMDQ4PEKChoqOkpaanqKmqq6ytrq_ldKOE819-6amPhNKf2Y0YXedBOBEspx1sRGhhCnQ1TuqWbGgM3je3oD7awjuSiD8paEXPNbJM4dDCS-8xaOMfPcaIs9CYY1IQ_voqNn-y0bSW7HvtNSdhNArJB-OhijObYM-BfcyttiexYnNyg4u9"],
  ];
  const CHECKS = ["Descifra el texto fijo", "Rechaza una clave incorrecta", "Cifrar da exactamente el texto fijo", "Cifra y descifra con datos al azar"];
  const GEN_CHECKS = ["El navegador da números aleatorios seguros", "Respeta largo y caracteres permitidos", "Incluye al menos uno de cada tipo elegido", "200 contraseñas distintas que usan todos los caracteres"];
  const VAULT_CHECKS = ["Cifra y abre una bóveda", "Rechaza una clave incorrecta", "Detecta un archivo alterado", "Combina cambios de dos dispositivos"];
  const GEN_TEST_SYMBOLS = DEFAULT_SYMBOLS;
  function selfTestRows() {
    const fixed = { salt: TEST_SALT, iv: TEST_IV };
    const rows = TEST_VECTORS.map(([algId, kdfId, vec]) => ({
      label: "Texto · " + ALGS[algId].name + " · PBKDF2-" + KDFS[kdfId],
      checks: [
        async () => { if (await decrypt(vec, TEST_PW, algId, kdfId, TEST_ITER) !== TEST_TEXT) throw new Error("resultado distinto"); },
        async () => { let rej = false; try { await decrypt(vec, TEST_PW + "x", algId, kdfId, TEST_ITER); } catch { rej = true; } if (!rej) throw new Error("aceptó una clave incorrecta"); },
        async () => { if (await encrypt(TEST_TEXT, TEST_PW, algId, kdfId, TEST_ITER, fixed) !== vec) throw new Error("el cifrado no coincide con el esperado"); },
        async () => {
          const ct = await encrypt(TEST_TEXT, TEST_PW, algId, kdfId, TEST_ITER);
          if (ct.length !== vec.length) throw new Error("largo de salida distinto");
          if (await decrypt(ct, TEST_PW, algId, kdfId, TEST_ITER) !== TEST_TEXT) throw new Error("ida y vuelta falló");
        },
      ].map((fn, i) => ({ name: CHECKS[i], fn })),
    }));
    const vmeta = { vaultId: "test-vault", name: "Prueba", salt: b64urlEncode(TEST_SALT), iter: TEST_ITER };
    const vdata = { entries: [normEntry({ id: "a", title: "Sitio ñ 🔑", username: "yo@x.com", password: "p@ss", notes: "n", createdAt: 1, updatedAt: 1 })], createdAt: 1 };
    rows.push({
      label: "Bóveda · AES-256-GCM",
      checks: [
        async () => {
          const env = JSON.parse(JSON.stringify(await sealVault(vmeta, vdata, await deriveVaultKey(TEST_PW, vmeta.salt, TEST_ITER))));
          let rejected = false; try { parseEnvelope(env); } catch { rejected = true; } // 1000 iteraciones: debe rechazarse como archivo real
          if (!rejected) throw new Error("aceptó un archivo con pocas iteraciones");
          parseEnvelope(Object.assign({}, env, { kdf: Object.assign({}, env.kdf, { iterations: VAULT_ITER }) }));
          const r = await unlockEnvelope(env, TEST_PW);
          if (canon(r.data.entries) !== canon(vdata.entries)) throw new Error("el contenido no coincide");
        },
        async () => {
          const env = await sealVault(vmeta, vdata, await deriveVaultKey(TEST_PW, vmeta.salt, TEST_ITER));
          let rej = false; try { await unlockEnvelope(env, TEST_PW + "x"); } catch (e) { rej = e instanceof WrongKeyError; }
          if (!rej) throw new Error("aceptó una clave incorrecta");
        },
        async () => {
          const env = await sealVault(vmeta, vdata, await deriveVaultKey(TEST_PW, vmeta.salt, TEST_ITER));
          const b = b64urlDecode(env.data); b[5] ^= 1;
          let rej = false; try { await unlockEnvelope(Object.assign({}, env, { data: b64urlEncode(b) }), TEST_PW); } catch { rej = true; }
          if (!rej) throw new Error("no detectó la alteración");
          let rej2 = false; try { await unlockEnvelope(Object.assign({}, env, { vaultId: "otra" }), TEST_PW); } catch { rej2 = true; }
          if (!rej2) throw new Error("no detectó un cambio en la cabecera");
        },
        async () => {
          const a = [normEntry({ id: "1", title: "A", updatedAt: 5 }), normEntry({ id: "2", title: "B", updatedAt: 5 })];
          const b = [normEntry({ id: "1", title: "A2", updatedAt: 9 }), { id: "2", deleted: true, updatedAt: 7 }, normEntry({ id: "3", title: "C", updatedAt: 1 })];
          const m = mergeEntries(a, b);
          const g = (id) => m.find((x) => x.id === id);
          if (m.length !== 3 || g("1").title !== "A2" || !g("2").deleted || g("3").title !== "C") throw new Error("combinación incorrecta");
          if (canon(mergeEntries(a, b)) !== canon(mergeEntries(b, a))) throw new Error("el orden cambia el resultado");
        },
      ].map((fn, i) => ({ name: VAULT_CHECKS[i], fn })),
    });
    const all4 = [GEN_SETS.genLower, GEN_SETS.genUpper, GEN_SETS.genDigits, GEN_TEST_SYMBOLS];
    rows.push({
      label: "Generador de contraseñas",
      checks: [
        async () => {
          const a = crypto.getRandomValues(new Uint8Array(32)), b = crypto.getRandomValues(new Uint8Array(32));
          if (a.every((x) => x === 0) || a.every((x, i) => x === b[i])) throw new Error("los valores aleatorios no varían");
        },
        async () => {
          const combos = [all4, [GEN_SETS.genLower], [GEN_SETS.genDigits, "-_"], [GEN_SETS.genUpper, GEN_SETS.genLower]];
          for (const sets of combos) for (const len of [8, 20, 64, 128]) {
            const pool = sets.join(""), pw = generatePassword(len, sets);
            if (pw.length !== len) throw new Error("largo " + pw.length + " en vez de " + len);
            if (![...pw].every((c) => pool.includes(c))) throw new Error("usó un carácter no permitido");
          }
        },
        async () => {
          for (let i = 0; i < 50; i++) {
            const pw = generatePassword(8, all4);
            if (!all4.every((set) => [...pw].some((c) => set.includes(c)))) throw new Error("faltó algún tipo de carácter");
          }
        },
        async () => {
          const seen = new Set(), used = new Set();
          for (let i = 0; i < 200; i++) { const pw = generatePassword(20, all4); seen.add(pw); for (const c of pw) used.add(c); }
          if (seen.size !== 200) throw new Error("se repitieron contraseñas");
          if (used.size !== new Set(all4.join("")).size) throw new Error("hay caracteres que nunca salieron");
        },
      ].map((fn, i) => ({ name: GEN_CHECKS[i], fn })),
    });
    return rows;
  }
  function buildGrid(rows) {
    const g = $("selfTestGrid");
    g.textContent = "";
    g.append(el("div"));
    ["①", "②", "③", "④"].forEach((n) => g.append(el("div", { class: "h", text: n })));
    return rows.map((row) => {
      g.append(el("div", { class: "lbl", text: row.label }));
      return row.checks.map((c) => { const d = el("div", { class: "dot", title: c.name + ": pendiente" }); g.append(d); return d; });
    });
  }
  let selfTestDone = null;
  async function selfTest() {
    const btn = $("selfTestBtn"), status = $("selfTestStatus");
    btn.disabled = true; status.textContent = "Autoprueba: ejecutando…"; status.style.color = "";
    const rows = selfTestRows();
    const dots = buildGrid(rows);
    const fails = [];
    let total = 0;
    for (let r = 0; r < rows.length; r++) for (let i = 0; i < rows[r].checks.length; i++) {
      const { name, fn } = rows[r].checks[i], dot = dots[r][i];
      total++; dot.className = "dot run";
      try { await fn(); dot.className = "dot ok"; dot.title = name + ": OK"; }
      catch (e) {
        const why = e && e.message ? e.message : String(e);
        dot.className = "dot err"; dot.title = name + ": FALLÓ (" + why + ")";
        fails.push(rows[r].label + ", " + name.toLowerCase() + " (" + why + ")");
      }
    }
    const alert = $("globalAlert");
    if (fails.length) {
      status.textContent = "Autoprueba: FALLARON " + fails.length + " de " + total + " chequeos."; status.style.color = "var(--err)";
      alert.className = "msg global show err";
      alert.textContent = "La autoprueba de cifrado falló en este navegador. Tus datos guardados no se dañaron, pero no cifres ni guardes nada nuevo acá: usá otro navegador. Detalle en Ajustes → Autoprueba.";
      $("selfTestPanel").open = true;
      console.warn("Autoprueba:", fails);
    } else {
      status.textContent = "Autoprueba OK: " + total + " de " + total + " chequeos correctos."; status.style.color = "var(--ok)";
      alert.className = "msg global"; alert.textContent = "";
    }
    btn.disabled = false;
    return fails.length === 0;
  }
  // Para pruebas automáticas
  window.__cypherTest = { parseOldNote, mergeEntries, selfTest: () => selfTestDone };

  // =====================================================================
  // Eventos
  // =====================================================================
  function setPwVisible(id, show) {
    const i = $(id); i.type = show ? "text" : "password";
    const b = document.querySelector('[data-toggle="' + id + '"]');
    if (b) b.textContent = show ? "Ocultar" : "Mostrar";
  }
  document.querySelectorAll("[data-toggle]").forEach((b) => b.addEventListener("click", () => setPwVisible(b.dataset.toggle, $(b.dataset.toggle).type === "password")));
  document.querySelectorAll("[data-home-back]").forEach((b) => b.addEventListener("click", () => { homePanel("list"); renderHome(); }));
  document.querySelectorAll("dialog [data-close]").forEach((b) => b.addEventListener("click", () => b.closest("dialog").close()));
  document.querySelectorAll(".nv").forEach((b) => b.addEventListener("click", () => showView(b.dataset.view)));

  // Inicio
  $("homeCreate").onclick = () => { hideMsg("createMsg"); paintMeter("createMeterBar", "createMeterText", "", "Usá una frase larga: 4–6 palabras al azar o 16+ caracteres."); homePanel("create"); };
  $("homeDrive").onclick = homeFindInDrive;
  $("homeImport").onclick = () => $("fileImportHome").click();
  $("fileImportHome").onchange = (ev) => { const f = ev.target.files[0]; ev.target.value = ""; if (f) importVaultFileHome(f); };
  $("homeTools").onclick = openToolsOnly;
  $("unlockForm").addEventListener("submit", doUnlock);
  $("createForm").addEventListener("submit", doCreate);
  $("createPw").addEventListener("input", () => { paintMeter("createMeterBar", "createMeterText", $("createPw").value, "Usá una frase larga: 4–6 palabras al azar o 16+ caracteres."); createMatch(); });
  $("createPw2").addEventListener("input", createMatch);
  function createMatch() {
    const t = $("createMatch"), a = $("createPw").value, b = $("createPw2").value;
    if (!b) { t.textContent = ""; return; }
    t.textContent = a === b ? "Coinciden." : "No coinciden."; t.style.color = a === b ? "var(--ok)" : "var(--err)";
  }

  // Barra superior
  $("lockBtn").onclick = () => lock();
  $("syncChip").onclick = () => {
    if (!Drive.configured() || !settings.driveLinked) { showView("settings"); return; }
    if (!Drive.hasToken()) connectAndSync(); else sync();
  };

  // Bóveda
  $("search").addEventListener("input", renderEntries);
  $("addEntry").onclick = () => openEntry(null);
  $("entryForm").addEventListener("submit", saveEntry);
  $("fDelete").onclick = deleteEntry;
  $("fCopyUser").onclick = () => copyText($("fUser").value, false);
  $("fCopyPass").onclick = () => copyText($("fPass").value, true);
  $("fOpenUrl").onclick = () => {
    const u = $("fUrl").value.trim(); if (!u) return;
    const url = /^https?:\/\//i.test(u) ? u : "https://" + u;
    window.open(url, "_blank", "noopener,noreferrer");
  };
  $("fGen").onclick = () => {
    if ($("fPass").value && !confirm("¿Reemplazar la contraseña actual por una nueva? (Recordá cambiarla también en el sitio.)")) return;
    $("fPass").value = quickGenerate(); setPwVisible("fPass", true); updateEntryStrength();
  };
  $("fPass").addEventListener("input", updateEntryStrength);

  // Generador
  function loadGenPrefs() {
    const g = settings.gen;
    $("genLen").value = g.len; $("genLower").checked = g.lower; $("genUpper").checked = g.upper; $("genDigits").checked = g.digits; $("genSymbols").checked = g.symbols; $("genSymbolSet").value = g.symbolSet;
  }
  function saveGenPrefs() {
    settings.gen = { len: Number($("genLen").value) || 20, lower: $("genLower").checked, upper: $("genUpper").checked, digits: $("genDigits").checked, symbols: $("genSymbols").checked, symbolSet: $("genSymbolSet").value };
    saveSettings();
  }
  ["genLen", "genLower", "genUpper", "genDigits", "genSymbols", "genSymbolSet"].forEach((i) => $(i).addEventListener("change", saveGenPrefs));
  $("genRun").onclick = async () => {
    hideMsg("genMsg");
    let o;
    try { o = genOptions(); } catch (e) { showMsg("genMsg", "err", e.message); return; }
    const pw = generatePassword(o.length, o.sets);
    $("genOut").value = pw;
    const pool = new Set(o.sets.join("")).size;
    $("genInfo").textContent = "~" + Math.round(o.length * Math.log2(pool)) + " bits de entropía (" + pool + " caracteres posibles). Cada vez que generás sale una nueva e irrepetible.";
    try { await navigator.clipboard.writeText(pw); showMsg("genMsg", "ok", "Contraseña nueva generada y copiada."); }
    catch { setPwVisible("genOut", true); $("genOut").select(); showMsg("genMsg", "warn", "Generada, pero el navegador no permitió copiarla. Quedó seleccionada."); }
  };
  $("genToEntry").onclick = () => {
    const v = $("genOut").value;
    if (!v) { showMsg("genMsg", "err", "Primero generá una contraseña."); return; }
    if (!S) { showMsg("genMsg", "err", "Abrí una bóveda para guardarla."); return; }
    showView("vault"); openEntry(null, { password: v });
  };
  $("genToText").onclick = () => {
    const v = $("genOut").value;
    if (!v) { showMsg("genMsg", "err", "Primero generá una contraseña."); return; }
    showView("text"); if (mode !== "enc") setMode("enc");
    const cur = $("input").value;
    const sep = !cur || /[\n ]$/.test(cur) ? "" : cur.endsWith(":") ? " " : "\n";
    $("input").value = cur + sep + v; $("input").focus();
  };

  // Cifrar texto
  $("tabEnc").onclick = () => setMode("enc");
  $("tabDec").onclick = () => setMode("dec");
  $("run").onclick = runText;
  $("pw").addEventListener("input", () => { paintMeter("meterBar", "meterText", $("pw").value, "Usá una frase larga: 4–6 palabras al azar o 16+ caracteres."); updateMatch(); });
  $("pw2").addEventListener("input", updateMatch);
  ["pw", "pw2"].forEach((i) => $(i).addEventListener("keydown", (e) => { if (e.key === "Enter") runText(); }));
  $("input").addEventListener("keydown", (e) => { if (e.key === "Enter" && (e.ctrlKey || e.metaKey)) runText(); });
  $("reveal").onclick = () => {
    const o = $("output"), hidden = o.dataset.secret === "1";
    o.style.webkitTextSecurity = hidden ? "" : "disc"; o.dataset.secret = hidden ? "" : "1";
    $("reveal").textContent = hidden ? "Ocultar texto" : "Mostrar texto";
  };
  $("copy").onclick = () => copyText($("output").value, mode === "dec");
  $("swap").onclick = () => {
    if (!$("output").value) { showMsg("msg", "err", "No hay resultado para usar."); return; }
    $("input").value = $("output").value; $("output").value = ""; setOutputSecret(false);
    setMode(mode === "enc" ? "dec" : "enc");
  };
  $("clear").onclick = () => {
    ["pw", "pw2", "input", "output"].forEach((i) => ($(i).value = ""));
    setOutputSecret(false); hideMsg("msg"); paintMeter("meterBar", "meterText", "", "Usá una frase larga: 4–6 palabras al azar o 16+ caracteres."); updateMatch();
  };

  // Ajustes
  $("driveConnect").onclick = connectAndSync;
  $("driveSyncNow").onclick = () => sync();
  $("driveDisconnect").onclick = () => {
    if (!confirm("¿Desconectar Google Drive en este dispositivo? Tus bóvedas siguen en Drive y en este dispositivo; solo se deja de sincronizar hasta que vuelvas a conectar.")) return;
    Drive.revoke(); settings.driveLinked = false; saveSettings(); setSync("off");
  };
  $("exportBtn").onclick = exportVault;
  $("importFileBtn").onclick = () => $("fileImportApp").click();
  $("fileImportApp").onchange = (ev) => { const f = ev.target.files[0]; ev.target.value = ""; if (f) mergeVaultFile(f); };
  $("openImportOld").onclick = openImportOld;
  $("ioDecrypt").onclick = ioDecrypt;
  $("ioBack").onclick = () => { $("ioStep1").hidden = false; $("ioStep2").hidden = true; $("ioFoot").hidden = true; };
  $("ioImport").onclick = ioImport;
  $("renameBtn").onclick = renameVault;
  $("changePwBtn").onclick = changeMasterPassword;
  $("forgetVaultBtn").onclick = forgetVault;
  $("autoLock").value = String(settings.autoLockMin);
  $("autoLock").onchange = () => { settings.autoLockMin = Number($("autoLock").value) || 5; saveSettings(); };
  $("rememberLocal").checked = settings.rememberLocal;
  $("rememberLocal").onchange = () => {
    settings.rememberLocal = $("rememberLocal").checked; saveSettings(); saveVaults();
    toast(settings.rememberLocal ? "Las bóvedas se guardan (cifradas) en este dispositivo." : "Las bóvedas ya no se guardan en este dispositivo: al cerrar la app quedan solo en Drive.", 4000);
  };
  $("selfTestBtn").onclick = (e) => { e.preventDefault(); selfTest(); };
  $("appVersion").textContent = APP_VERSION;

  // Instalación como app
  let installEvt = null;
  window.addEventListener("beforeinstallprompt", (e) => { e.preventDefault(); installEvt = e; $("installBox").hidden = false; });
  $("installBtn").onclick = async () => { if (!installEvt) return; installEvt.prompt(); await installEvt.userChoice; installEvt = null; $("installBox").hidden = true; };
  const standalone = window.matchMedia("(display-mode: standalone)").matches || navigator.standalone;
  if (/iphone|ipad|ipod/i.test(navigator.userAgent) && !standalone) $("iosInstallHint").hidden = false;

  // Service worker (funciona sin internet) y aviso de versión nueva
  if ("serviceWorker" in navigator && location.protocol !== "file:") {
    navigator.serviceWorker.register("sw.js").then((reg) => {
      const offer = (w) => {
        if (!w) return;
        $("updateBar").hidden = false;
        $("updateBtn").onclick = () => w.postMessage("skipWaiting");
      };
      if (reg.waiting && navigator.serviceWorker.controller) offer(reg.waiting);
      reg.addEventListener("updatefound", () => {
        const w = reg.installing;
        w && w.addEventListener("statechange", () => { if (w.state === "installed" && navigator.serviceWorker.controller) offer(w); });
      });
      setInterval(() => reg.update().catch(() => {}), 60 * 60 * 1000);
    }).catch((e) => console.warn("SW", e));
    let reloaded = false;
    navigator.serviceWorker.addEventListener("controllerchange", () => {
      if (reloaded) return; reloaded = true;
      if (S) toast("Versión nueva lista: se aplica al bloquear o recargar."); else location.reload();
    });
  }

  // Arranque
  loadGenPrefs();
  setMode("enc");
  paintMeter("meterBar", "meterText", "", "Usá una frase larga: 4–6 palabras al azar o 16+ caracteres.");
  renderHome();
  homePanel("list");
  if (!window.crypto || !crypto.subtle) {
    showMsg("globalAlert", "err", "Este navegador no ofrece cifrado seguro (Web Crypto). Abrí la app desde https:// en un navegador actualizado.");
  } else {
    selfTestDone = selfTest();
  }
  // Se precarga el inicio de sesión de Google para que el botón “Conectar” funcione al primer toque.
  if (Drive.configured()) Drive.load().then(() => { renderHome(); renderDriveSettings(); }).catch(() => {});
  const rows = allVaultRows();
  if (rows.length === 1 || (settings.lastVaultId && getEnv(settings.lastVaultId))) selectVault(settings.lastVaultId && getEnv(settings.lastVaultId) ? settings.lastVaultId : rows[0].id);
})();
