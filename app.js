"use strict";
(() => {
  const APP_VERSION = "1.1.0";
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
  // Preferencias (lo único que se guarda en el dispositivo: nada sensible)
  // =====================================================================
  const LS_PREFS = "cypher.prefs.v2";
  const LEGACY_SETTINGS = "cypher.settings.v1", LEGACY_VAULTS = "cypher.vaults.v1";
  const prefs = Object.assign({
    autoLockMin: 5,
    gen: { len: 20, lower: true, upper: true, digits: true, symbols: true, symbolSet: DEFAULT_SYMBOLS },
  }, loadJSON(LS_PREFS, {}));
  (() => { // migra preferencias de la versión anterior y borra lo demás
    const old = loadJSON(LEGACY_SETTINGS, null);
    if (old) {
      if (!localStorage.getItem(LS_PREFS)) { if (old.autoLockMin) prefs.autoLockMin = old.autoLockMin; if (old.gen) prefs.gen = old.gen; saveJSON(LS_PREFS, prefs); }
      localStorage.removeItem(LEGACY_SETTINGS);
    }
  })();
  const savePrefs = () => saveJSON(LS_PREFS, prefs);

  // Bóvedas que guardaba la versión anterior en este navegador. Las que ya estaban subidas a Drive se borran;
  // las que no, se ofrecen para descargar antes de borrarlas.
  let legacyVaults = [];
  (() => {
    const old = loadJSON(LEGACY_VAULTS, null);
    if (!old) return;
    legacyVaults = Object.values(old).filter((v) => v && v.env && !(v.driveFileId && (v.lastSyncAt || 0) >= (v.updatedAt || 0) - 5000));
    if (!legacyVaults.length) localStorage.removeItem(LEGACY_VAULTS);
  })();

  // =====================================================================
  // Google: inicio de sesión (Google Identity Services) + Drive API v3 (permiso drive.file)
  // El token vive solo en memoria: al cerrar o recargar la app hay que volver a iniciar sesión.
  // =====================================================================
  const DRIVE_SCOPE = "https://www.googleapis.com/auth/drive.file";
  const API = "https://www.googleapis.com/drive/v3";
  const UPLOAD = "https://www.googleapis.com/upload/drive/v3";
  const FOLDER_MIME = "application/vnd.google-apps.folder";
  class DriveAuthError extends UserError {}
  class OfflineError extends UserError {}
  const Drive = {
    token: null, exp: 0, client: null, gisPromise: null, pending: null, nextPrompt: "",
    configured() {
      return !!CFG.googleClientId && (location.protocol === "https:" || location.hostname === "localhost" || location.hostname === "127.0.0.1");
    },
    load() {
      if (!this.configured()) return Promise.reject(new UserError("El inicio de sesión con Google no está configurado en esta copia de la app."));
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
        s.onerror = () => { this.gisPromise = null; reject(new OfflineError("No se pudo cargar el inicio de sesión de Google. ¿Hay internet?")); };
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
        this.nextPrompt = "";
        p && p.resolve();
      } else {
        p && p.reject(new UserError(r && r.error ? "Google rechazó el acceso: " + r.error : "No se otorgó el permiso para Google Drive. Para usar bóvedas tenés que tildar el acceso a Drive."));
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
        this.client.requestAccessToken({ prompt: this.nextPrompt });
      });
    },
    forget() {
      this.token = null; this.exp = 0;
      this.nextPrompt = "select_account"; // al volver a entrar, que deje elegir la cuenta
    },
    async api(url, opts = {}) {
      if (!navigator.onLine) throw new OfflineError("Sin conexión a internet.");
      if (!this.hasToken()) throw new DriveAuthError("La sesión de Google venció. Volvé a iniciar sesión.");
      const headers = Object.assign({ Authorization: "Bearer " + this.token }, opts.headers || {});
      let res;
      // cache: "no-store" para que el navegador no guarde copias de las respuestas (ni siquiera cifradas).
      try { res = await fetch(url, Object.assign({ cache: "no-store" }, opts, { headers })); }
      catch { throw new OfflineError("Sin conexión con Google Drive."); }
      if (res.status === 401) { this.token = null; throw new DriveAuthError("La sesión de Google venció. Volvé a iniciar sesión."); }
      if (!res.ok) {
        let msg = res.status + "";
        try { const j = await res.json(); msg += " " + ((j.error && j.error.message) || ""); } catch { /* nada */ }
        const err = new UserError("Error de Google Drive (" + msg.trim() + ").");
        err.status = res.status;
        throw err;
      }
      return res;
    },
    async about() {
      const j = await (await this.api(API + "/about?fields=user(displayName,emailAddress,photoLink)")).json();
      const u = j.user || {};
      return { name: u.displayName || "", email: u.emailAddress || "", photo: u.photoLink || "" };
    },
    async listVaults(trashed) {
      const q = "appProperties has { key='cypherVault' and value='1' } and trashed=" + (trashed ? "true" : "false");
      const url = API + "/files?" + new URLSearchParams({ q, spaces: "drive", pageSize: "200", orderBy: "name",
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
    async setTrashed(id, trashed) {
      return (await this.api(API + "/files/" + encodeURIComponent(id) + "?fields=id,trashed",
        { method: "PATCH", headers: { "Content-Type": "application/json" }, body: JSON.stringify({ trashed }) })).json();
    },
    // Carpeta "Cypher" en Mi unidad (la crea la app, así que la puede ver con drive.file).
    async folderId() {
      if (this._folder) return this._folder;
      const q = "appProperties has { key='cypherFolder' and value='1' } and mimeType='" + FOLDER_MIME + "' and trashed=false";
      const j = await (await this.api(API + "/files?" + new URLSearchParams({ q, spaces: "drive", fields: "files(id)" }))).json();
      if (j.files && j.files.length) return (this._folder = j.files[0].id);
      const r = await (await this.api(API + "/files?fields=id", { method: "POST", headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ name: "Cypher", mimeType: FOLDER_MIME, appProperties: { cypherFolder: "1" },
          description: "Bóvedas cifradas de Cypher. Podés moverlas, pero no las edites a mano." }) })).json();
      return (this._folder = r.id);
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
      const parents = [await this.folderId()];
      const m = Object.assign({ mimeType: "application/octet-stream", parents, description: "Bóveda cifrada de Cypher. No la edites a mano." }, this.fileMeta(env));
      const { body, type } = this._multipart(m, JSON.stringify(env));
      return (await this.api(UPLOAD + "/files?uploadType=multipart&fields=id,version,modifiedTime", { method: "POST", headers: { "Content-Type": type }, body })).json();
    },
    async update(id, env) {
      const { body, type } = this._multipart(this.fileMeta(env), JSON.stringify(env));
      return (await this.api(UPLOAD + "/files/" + encodeURIComponent(id) + "?uploadType=multipart&fields=id,version,modifiedTime",
        { method: "PATCH", headers: { "Content-Type": type }, body })).json();
    },
  };

  // =====================================================================
  // Cuenta y lista de bóvedas (en memoria)
  // =====================================================================
  let account = null;          // { name, email, photo }
  let vaultIndex = null;       // [{ fileId, vaultId, name, modifiedTime, version }] o null si no se cargó
  let trashIndex = [];
  let loginBusy = false;

  function renderAccount() {
    const signedIn = !!account;
    $("signInTop").hidden = signedIn;
    $("acctBtn").hidden = !signedIn;
    if (!signedIn) { $("acctMenu").hidden = true; return; }
    const img = $("acctPhoto");
    if (account.photo) { img.src = account.photo; img.hidden = false; } else { img.removeAttribute("src"); }
    $("acctName").textContent = account.name || account.email;
    $("acctEmail").textContent = account.name ? account.email : "";
    $("acctMenuName").textContent = account.name || "";
    $("acctMenuEmail").textContent = account.email;
    $("acctBtn").title = "Sesión iniciada: " + account.email;
  }

  // Iniciar sesión: tiene que arrancar desde un clic.
  function signIn(msgId) {
    if (loginBusy) return;
    if (!navigator.onLine) { showVaults(); return; }
    if (!Drive.configured()) { showMsg(msgId, "err", "El inicio de sesión con Google no está configurado en esta copia de la app."); return; }
    if (!Drive.ready()) {
      showMsg(msgId, "info", "Cargando Google…");
      Drive.load().then(() => showMsg(msgId, "info", "Listo. Tocá “Iniciar sesión” otra vez.")).catch((e) => showMsg(msgId, "err", errText(e)));
      return;
    }
    loginBusy = true;
    hideMsg(msgId);
    Drive.requestToken()
      .then(async () => {
        account = await Drive.about();
        renderAccount();
        await refreshVaults();
        if (current === "vaults" || current === "unlock" || current === "create") showView("vaults");
        if (S) sync();
      })
      .catch((e) => { showMsg(msgId, "err", errText(e)); if (current === "vaults") showView("vaults"); })
      .finally(() => { loginBusy = false; });
  }
  async function signOut() {
    $("acctMenu").hidden = true;
    if (S && hasUnsyncedChanges() && !confirm("Hay cambios en la bóveda abierta que todavía no se subieron a Drive. Si cerrás sesión ahora se pierden. ¿Cerrar sesión igual?")) return;
    lockVault(null, true);
    Drive.forget();
    account = null; vaultIndex = null; trashIndex = [];
    renderAccount(); renderNavVaults();
    showView("vaults");
    toast("Sesión cerrada. No quedó nada de tus bóvedas en este dispositivo.");
  }
  function onAuthLost(e) {
    // El token venció (dura ~1 hora): se mantiene la cuenta visible pero hay que reconectar.
    setSync("auth", e.message);
  }

  async function refreshVaults() {
    if (!Drive.hasToken()) return;
    try {
      const [files, trashed] = await Promise.all([Drive.listVaults(false), Drive.listVaults(true)]);
      vaultIndex = files.map((f) => ({ fileId: f.id, vaultId: f.appProperties.vaultId, name: f.appProperties.vaultName || f.name, modifiedTime: f.modifiedTime, version: f.version }));
      const live = new Set(vaultIndex.map((v) => v.vaultId));
      trashIndex = trashed.filter((f) => !live.has(f.appProperties.vaultId))
        .map((f) => ({ fileId: f.id, vaultId: f.appProperties.vaultId, name: f.appProperties.vaultName || f.name, modifiedTime: f.modifiedTime }));
      hideMsg("vaultsMsg");
    } catch (e) {
      if (e instanceof DriveAuthError) onAuthLost(e);
      showMsg("vaultsMsg", "err", errText(e));
    }
    renderVaultList(); renderNavVaults();
  }

  function renderNavVaults() {
    const box = $("navVaults");
    box.textContent = "";
    if (!account || !vaultIndex) return;
    for (const v of vaultIndex) {
      const open = S && S.vaultId === v.vaultId;
      const b = el("button", { type: "button", class: "nv-sub", title: v.name, onclick: () => goVault(v.vaultId) },
        el("span", { text: open ? "🔓" : "🔒" }), el("span", { text: v.name }));
      if ((current === "vault" && open) || (current === "unlock" && selected && selected.vaultId === v.vaultId)) b.setAttribute("aria-current", "page");
      box.append(b);
    }
  }
  function renderVaultList() {
    const list = $("vaultList");
    list.textContent = "";
    const rows = vaultIndex || [];
    for (const v of rows) {
      const open = S && S.vaultId === v.vaultId;
      list.append(el("li", null, el("div", { class: "v-row" + (open ? " current" : "") },
        el("span", { class: "v-ico", text: open ? "🔓" : "🗄️" }),
        el("span", { class: "grow", onclick: () => goVault(v.vaultId) },
          el("div", { class: "v-name", text: v.name }),
          el("div", { class: "v-meta", text: (open ? "Abierta · " : "") + "Modificada: " + fmtDate(Date.parse(v.modifiedTime)) })),
        el("button", { type: "button", class: "btn small", text: open ? "Ver" : "Abrir", onclick: () => goVault(v.vaultId) }),
        el("button", { type: "button", class: "btn small danger", title: "Eliminar (solo si está vacía)", text: "🗑", onclick: () => deleteVault(v) }))));
    }
    $("vaultListEmpty").hidden = rows.length > 0;
    $("vaultsCount").textContent = account ? account.email : "";
    const tl = $("trashList"); tl.textContent = "";
    for (const v of trashIndex) {
      tl.append(el("li", null, el("div", { class: "v-row" },
        el("span", { class: "v-ico", text: "🗑️" }),
        el("span", { class: "grow" }, el("div", { class: "v-name", text: v.name }), el("div", { class: "v-meta", text: "En la papelera desde: " + fmtDate(Date.parse(v.modifiedTime)) })),
        el("button", { type: "button", class: "btn small", text: "Restaurar", onclick: () => restoreVault(v) }))));
    }
    $("trashBox").hidden = trashIndex.length === 0;
    renderLegacy();
  }
  function renderLegacy() {
    const b = $("legacyBanner");
    b.textContent = "";
    if (!legacyVaults.length) { b.className = "msg"; return; }
    b.className = "msg warn show";
    b.append("La versión anterior dejó guardadas en este navegador " + legacyVaults.length + (legacyVaults.length === 1 ? " bóveda que quizás no esté" : " bóvedas que quizás no estén") +
      " en Drive (" + legacyVaults.map((v) => v.name).join(", ") + "). Ahora no se guarda nada en el dispositivo. ",
      el("button", { type: "button", class: "link", text: "Subirlas a mi Drive", onclick: uploadLegacy }), " · ",
      el("button", { type: "button", class: "link", text: "Descargar copias", onclick: downloadLegacy }), " · ",
      el("button", { type: "button", class: "link", text: "Borrarlas de este navegador", onclick: () => {
        if (!confirm("¿Borrar de este navegador las bóvedas de la versión anterior? Si no las subiste a Drive ni descargaste copia, se pierden.")) return;
        localStorage.removeItem(LEGACY_VAULTS); legacyVaults = []; renderLegacy();
      } }));
  }
  function downloadEnv(env) {
    const blob = new Blob([JSON.stringify(env)], { type: "application/octet-stream" });
    const a = el("a", { href: URL.createObjectURL(blob), download: "cypher-" + env.name.replace(/[^\w\-áéíóúñÁÉÍÓÚÑ ]+/g, "_").replace(/\s+/g, "-") + "-" + new Date().toISOString().slice(0, 10) + ".cypher" });
    document.body.append(a); a.click(); a.remove();
    setTimeout(() => URL.revokeObjectURL(a.href), 5000);
  }
  function downloadLegacy() { legacyVaults.forEach((v) => downloadEnv(v.env)); }
  async function uploadLegacy() {
    try {
      let n = 0;
      for (const v of legacyVaults) {
        const env = parseEnvelope(v.env);
        const ex = (vaultIndex || []).find((x) => x.vaultId === env.vaultId);
        if (ex) {
          showMsg("vaultsMsg", "warn", "“" + env.name + "” ya está en tu Drive. Descargá la copia, abrila y usá Opciones de la bóveda → “Combinar con una copia” para no perder cambios.");
          continue;
        }
        await Drive.create(env); n++;
      }
      if (n) { localStorage.removeItem(LEGACY_VAULTS); legacyVaults = []; }
      await refreshVaults();
      if (n) showMsg("vaultsMsg", "ok", "Se subieron " + n + " bóvedas a tu Drive y se borraron de este navegador.");
    } catch (e) { showMsg("vaultsMsg", "err", errText(e)); }
  }

  async function deleteVault(v) {
    hideMsg("vaultsMsg"); hideMsg("vaultMsg");
    const r = await askPassword({
      title: "Eliminar “" + v.name + "”", okText: "Eliminar",
      text: "Solo se puede eliminar una bóveda vacía. Ingresá su clave maestra para confirmar. Va a ir a la papelera de Google Drive, donde queda 30 días.",
      verify: async (pw) => {
        const env = parseEnvelope(await Drive.download(v.fileId));
        const { data } = await unlockEnvelope(env, pw);
        const n = data.entries.filter((e) => !e.deleted).length;
        if (n > 0) throw new UserError("La bóveda tiene " + n + (n === 1 ? " entrada" : " entradas") + ". Para eliminarla, primero borralas una por una.");
        if (S && S.vaultId === v.vaultId && live().length > 0) throw new UserError("La bóveda abierta tiene entradas sin subir. Esperá a que se guarde en Drive.");
        await Drive.setTrashed(v.fileId, true);
        return true;
      },
    });
    if (!r) return;
    if (S && S.vaultId === v.vaultId) lockVault(null, true);
    await refreshVaults();
    showView("vaults");
    showMsg("vaultsMsg", "ok", "“" + v.name + "” se movió a la papelera de Google Drive. La podés restaurar desde acá durante 30 días.");
  }
  async function restoreVault(v) {
    try {
      await Drive.setTrashed(v.fileId, false);
      await refreshVaults();
      showMsg("vaultsMsg", "ok", "“" + v.name + "” restaurada.");
    } catch (e) { showMsg("vaultsMsg", "err", errText(e)); }
  }
  async function importCopyAsVault(file) {
    hideMsg("vaultsMsg");
    try {
      const env = parseEnvelope(await file.text());
      if ((vaultIndex || []).some((v) => v.vaultId === env.vaultId)) {
        showMsg("vaultsMsg", "warn", "“" + env.name + "” ya está en tu Drive. Abrila y usá Opciones de la bóveda → “Combinar con una copia” para traer los datos de este archivo.");
        return;
      }
      await Drive.create(env);
      await refreshVaults();
      showMsg("vaultsMsg", "ok", "Copia subida a tu Drive como “" + env.name + "”. Se abre con la clave maestra que tenía.");
    } catch (e) { showMsg("vaultsMsg", "err", errText(e)); }
  }

  // =====================================================================
  // Bóveda abierta (solo en memoria)
  // S = { vaultId, fileId, name, key, salt, iter, data, env, driveVersion, syncedHash, dirty }
  // =====================================================================
  let S = null;
  let selected = null; // bóveda elegida para abrir: { vaultId, fileId, name }
  let persistChain = Promise.resolve();
  const live = () => (S ? S.data.entries.filter((e) => !e.deleted) : []);
  const hasUnsyncedChanges = () => !!(S && (S.dirty || syncing));

  function persist() {
    if (!S) return persistChain;
    const snap = S;
    snap.dirty = true;
    persistChain = persistChain.then(async () => {
      if (S !== snap) return;
      snap.data.updatedAt = now();
      snap.env = await sealVault({ vaultId: snap.vaultId, name: snap.name, salt: snap.salt, iter: snap.iter }, snap.data, snap.key);
    }).catch((e) => { console.error(e); toast("No se pudo cifrar: " + errText(e), 5000); });
    scheduleSync(600);
    return persistChain;
  }

  // ---------- sincronización con Drive ----------
  let syncing = false, syncAgain = false, syncTimer = null, syncState = "ok", syncDetail = "";
  function setSync(state, detail) {
    syncState = state; syncDetail = detail || "";
    const chip = $("syncChip");
    const map = {
      auth: ["⚠ Reconectar Google", "warn"], syncing: ["⟳ Guardando…", ""],
      ok: ["✓ Guardado en Drive", "ok"], pending: ["● Cambios sin guardar", "warn"], offline: ["⚠ Sin internet: cambios sin guardar", "err"],
      error: ["⚠ Error al guardar", "err"], paused: ["⚠ Guardado en pausa", "warn"],
    };
    const [txt, cls] = map[state] || map.ok;
    chip.textContent = txt; chip.className = "chip " + cls;
    chip.title = detail || txt;
    chip.hidden = !S;
    renderDriveInfo();
    renderVaultBanner();
  }
  function renderDriveInfo() {
    if (!S) return;
    $("driveInfo").textContent = (account ? "Cuenta: " + account.email + ". " : "") +
      (S.lastSyncAt ? "Último guardado en Drive: " + fmtDate(S.lastSyncAt) + "." : "") + (syncDetail && syncState !== "ok" ? "\n" + syncDetail : "");
  }
  function renderVaultBanner() {
    const b = $("vaultBanner");
    b.textContent = "";
    if (!S || syncState === "ok" || syncState === "syncing" || syncState === "pending") { b.className = "msg"; return; }
    b.className = "msg show " + (syncState === "auth" || syncState === "paused" ? "warn" : "err");
    if (syncState === "offline") b.append("Sin conexión a internet. Los cambios quedan solo en memoria y se suben cuando vuelva la conexión: no cierres la app.");
    else if (syncState === "auth") b.append("La sesión de Google venció. ", el("button", { type: "button", class: "link", text: "Reconectar", onclick: () => signIn("vaultMsg") }), " para seguir guardando.");
    else b.append(syncDetail || "No se pudo guardar en Drive.", " ", el("button", { type: "button", class: "link", text: "Reintentar", onclick: () => sync() }));
  }
  function scheduleSync(delay = 1200) {
    if (!S) return;
    clearTimeout(syncTimer);
    if (syncState === "ok") setSync("pending");
    syncTimer = setTimeout(() => sync(), delay);
  }
  async function sync() {
    if (!S) return;
    if (syncing) { syncAgain = true; return; }
    if (!navigator.onLine) { setSync("offline"); return; }
    if (!Drive.hasToken()) { setSync("auth", "La sesión de Google venció. Volvé a iniciar sesión para guardar."); return; }
    const snap = S;
    syncing = true; setSync("syncing");
    try {
      await persistChain;
      let meta = null;
      try { meta = await Drive.getMeta(snap.fileId); } catch (e) { if (e.status !== 404) throw e; }
      if (!meta || meta.trashed) throw new UserError(meta && meta.trashed
        ? "El archivo de esta bóveda está en la papelera de Drive. Restauralo desde la lista de bóvedas para seguir guardando."
        : "No encuentro el archivo de esta bóveda en tu Drive. Descargá una copia desde Opciones para no perder los cambios.");
      if (S !== snap) return;

      // 1) Si el archivo cambió en Drive (otro dispositivo), se baja y se combina.
      if (meta.version !== snap.driveVersion) {
        const env = parseEnvelope(await Drive.download(snap.fileId));
        if (env.vaultId !== snap.vaultId) throw new UserError("El archivo de Drive no corresponde a esta bóveda.");
        let remote;
        if (env.kdf.salt === snap.salt && env.kdf.iterations === snap.iter) remote = await openVault(env, snap.key);
        else {
          const r = await askPassword({
            title: "La clave maestra cambió",
            text: "La bóveda “" + env.name + "” está cifrada con otra clave maestra (seguramente la cambiaste en otro dispositivo). Ingresá la clave actual para seguir.",
            verify: (pw) => unlockEnvelope(env, pw),
          });
          if (S !== snap) return;
          if (!r) { setSync("paused", "No se ingresó la nueva clave maestra. Los cambios de esta sesión no se guardaron."); return; }
          snap.key = r.key; snap.salt = env.kdf.salt; snap.iter = env.kdf.iterations;
          remote = r.data;
        }
        if (S !== snap) return;
        const before = canon(snap.data.entries);
        snap.data.entries = mergeEntries(snap.data.entries, remote.entries);
        if (env.name !== snap.name && !snap.dirty) snap.name = env.name;
        snap.driveVersion = meta.version;
        snap.syncedHash = await stateHash(env.kdf.salt, env.kdf.iterations, env.name, remote.entries);
        if (canon(snap.data.entries) !== before) renderEntries();
        refreshVaultLabels();
      }
      // 2) Subir si hay diferencias.
      const localHash = await stateHash(snap.salt, snap.iter, snap.name, snap.data.entries);
      if (S !== snap) return;
      if (localHash !== snap.syncedHash) {
        snap.env = await sealVault({ vaultId: snap.vaultId, name: snap.name, salt: snap.salt, iter: snap.iter }, snap.data, snap.key);
        const r = await Drive.update(snap.fileId, snap.env);
        snap.driveVersion = r.version; snap.syncedHash = localHash;
        const idx = (vaultIndex || []).find((v) => v.vaultId === snap.vaultId);
        if (idx) { idx.name = snap.name; idx.modifiedTime = r.modifiedTime || new Date().toISOString(); }
      }
      if (S !== snap) return;
      snap.dirty = false;
      snap.lastSyncAt = now();
      setSync("ok", "Último guardado: " + fmtDate(snap.lastSyncAt));
    } catch (e) {
      console.warn("sync", e);
      if (e instanceof DriveAuthError) onAuthLost(e);
      else if (e instanceof OfflineError || !navigator.onLine) setSync("offline");
      else setSync("error", errText(e));
    } finally {
      syncing = false;
      if (syncAgain && S) { syncAgain = false; scheduleSync(300); }
    }
  }

  // ---------- abrir / crear / cerrar ----------
  function goVault(vaultId) {
    if (S && S.vaultId === vaultId) { showView("vault"); return; }
    const v = (vaultIndex || []).find((x) => x.vaultId === vaultId);
    if (!v) return;
    if (S) {
      if (hasUnsyncedChanges() && !confirm("La bóveda “" + S.name + "” tiene cambios que todavía no se subieron a Drive. Si la cerrás ahora se pierden. ¿Cerrarla igual?")) return;
      lockVault(null, true);
    }
    selected = { vaultId: v.vaultId, fileId: v.fileId, name: v.name };
    $("unlockTitle").textContent = "Abrir “" + v.name + "”";
    $("unlockPw").value = ""; hideMsg("unlockMsg");
    showView("unlock");
    setTimeout(() => $("unlockPw").focus(), 30);
  }
  async function doUnlock(ev) {
    ev.preventDefault();
    if (!selected) return;
    const pw = $("unlockPw").value;
    hideMsg("unlockMsg");
    if (!pw) { showMsg("unlockMsg", "err", "Ingresá la clave maestra."); return; }
    const btn = $("unlockBtn"); btn.disabled = true; btn.textContent = "Abriendo…";
    try {
      const meta = await Drive.getMeta(selected.fileId);
      const env = parseEnvelope(await Drive.download(selected.fileId));
      if (env.vaultId !== selected.vaultId) throw new UserError("El archivo de Drive no corresponde a esta bóveda.");
      const { key, data } = await unlockEnvelope(env, pw);
      $("unlockPw").value = "";
      startSession({ vaultId: env.vaultId, fileId: selected.fileId, name: env.name, key, salt: env.kdf.salt, iter: env.kdf.iterations, data, env,
        driveVersion: meta.version, syncedHash: await stateHash(env.kdf.salt, env.kdf.iterations, env.name, data.entries) });
    } catch (e) {
      if (e instanceof DriveAuthError) onAuthLost(e);
      showMsg("unlockMsg", "err", e instanceof WrongKeyError ? "Clave maestra incorrecta." : errText(e));
      $("unlockPw").select();
    } finally { btn.disabled = false; btn.textContent = "Abrir"; }
  }
  async function doCreate(ev) {
    ev.preventDefault();
    hideMsg("createMsg");
    const name = $("createName").value.trim(), pw = $("createPw").value, pw2 = $("createPw2").value;
    try {
      if (!Drive.hasToken()) throw new UserError("Iniciá sesión con Google para crear una bóveda.");
      if (!name) throw new UserError("Poné un nombre para la bóveda.");
      if (pw.length < 8) throw new UserError("La clave maestra tiene que tener al menos 8 caracteres (mejor 16 o más).");
      if (pw !== pw2) throw new UserError("Las claves no coinciden.");
      if (strength(pw).bits < 50 && !confirm("La clave maestra es débil. Si alguien consigue el archivo cifrado podría adivinarla. ¿Crear igual?")) return;
      const btn = $("createBtn"); btn.disabled = true; btn.textContent = "Creando…";
      try {
        const vaultId = uuid(), salt = b64urlEncode(rand(16)), iter = VAULT_ITER;
        const key = await deriveVaultKey(pw, salt, iter);
        const data = { entries: [], createdAt: now() };
        const env = await sealVault({ vaultId, name, salt, iter }, data, key);
        await unlockEnvelope(env, pw); // verificación antes de subir
        const r = await Drive.create(env);
        ["createName", "createPw", "createPw2"].forEach((i) => ($(i).value = ""));
        await refreshVaults();
        startSession({ vaultId, fileId: r.id, name, key, salt, iter, data, env, driveVersion: r.version,
          syncedHash: await stateHash(salt, iter, name, data.entries) });
        S.lastSyncAt = now(); setSync("ok");
        toast("Bóveda “" + name + "” creada en tu Drive.");
      } finally { btn.disabled = false; btn.textContent = "Crear bóveda"; }
    } catch (e) {
      if (e instanceof DriveAuthError) onAuthLost(e);
      showMsg("createMsg", "err", errText(e));
    }
  }
  function startSession(s) {
    S = Object.assign({ dirty: false, lastSyncAt: now() }, s);
    selected = null;
    $("search").value = "";
    vaultTab("entries");
    refreshVaultLabels();
    setSync("ok");
    showView("vault");
    renderEntries();
    renderVaultList();
    touch();
  }
  function refreshVaultLabels() {
    if (!S) return;
    $("vaultTitle").textContent = "🔓 " + S.name;
    $("renameInput").value = S.name;
    if (current === "vault") $("tbTitle").textContent = S.name;
    renderNavVaults();
  }
  // Cierra la bóveda abierta y borra de memoria todo lo descifrado.
  function lockVault(reason, silent) {
    if (!S) return;
    const name = S.name, vaultId = S.vaultId;
    if (S.key) S.key = null;
    if (S.data) S.data.entries = [];
    S = null;
    clearTimeout(syncTimer);
    document.querySelectorAll("dialog[open]").forEach((d) => d.close());
    $("entryList").textContent = "";
    ["search", "fTitle", "fUrl", "fUser", "fPass", "fNotes", "ioText", "ioPw", "renameInput"].forEach((i) => ($(i).value = ""));
    $("ioNotes").textContent = "";
    ioResults = [];
    $("syncChip").hidden = true;
    renderNavVaults(); renderVaultList();
    if (!silent) {
      const v = (vaultIndex || []).find((x) => x.vaultId === vaultId);
      if (v) { goVault(vaultId); if (reason) showMsg("unlockMsg", "info", reason); }
      else showView("vaults");
      if (!v && reason) toast(reason, 4000);
    }
    void name;
  }

  // Bloqueo automático por inactividad.
  let lastActivity = now();
  function touch() { lastActivity = now(); }
  ["pointerdown", "keydown", "input", "scroll"].forEach((t) => window.addEventListener(t, touch, { passive: true, capture: true }));
  function checkIdle() {
    if (S && now() - lastActivity > prefs.autoLockMin * 60000) {
      if (hasUnsyncedChanges() && navigator.onLine && Drive.hasToken()) { sync(); return; } // primero intenta guardar
      lockVault("La bóveda se cerró sola por inactividad.");
    }
  }
  setInterval(checkIdle, 10000);
  document.addEventListener("visibilitychange", () => {
    if (!document.hidden) { checkIdle(); if (S && Drive.hasToken() && syncState !== "syncing") sync(); }
  });
  window.addEventListener("online", () => { if (S) sync(); if (current === "vaults") showView("vaults"); });
  window.addEventListener("offline", () => { if (S && S.dirty) setSync("offline"); if (current === "vaults") showView("vaults"); });
  window.addEventListener("beforeunload", (e) => { if (hasUnsyncedChanges()) { e.preventDefault(); e.returnValue = ""; } });
  window.addEventListener("pagehide", () => { if (S) { S.key = null; S.data.entries = []; } });

  // =====================================================================
  // Vistas
  // =====================================================================
  let current = "vaults";
  const TITLES = { vaults: "Bóvedas", unlock: "Abrir bóveda", create: "Nueva bóveda", gen: "Generar contraseña", text: "Cifrar texto", settings: "Ajustes" };
  function showView(v) {
    if (v === "vault" && !S) v = "vaults";
    current = v;
    for (const n of ["vaults", "unlock", "create", "vault", "gen", "text", "settings"]) $("view-" + n).hidden = n !== v;
    const navKey = v === "unlock" || v === "create" || v === "vault" ? "vaults" : v;
    document.querySelectorAll(".nv").forEach((b) => b.setAttribute("aria-current", b.dataset.view === navKey && !(v === "vault" || v === "unlock") ? "page" : "false"));
    // En celular el botón “Bóvedas” queda marcado también dentro de una bóveda.
    if (window.matchMedia("(max-width: 899px)").matches) document.querySelectorAll(".nv").forEach((b) => { if (b.dataset.view === navKey) b.setAttribute("aria-current", "page"); });
    $("tbTitle").textContent = v === "vault" && S ? S.name : TITLES[v] || "Cypher";
    if (v === "vaults") {
      const offline = !navigator.onLine;
      $("vaultsOffline").hidden = !offline;
      $("vaultsLogin").hidden = offline || !!account;
      $("vaultsList").hidden = offline || !account;
      if (!offline && account && vaultIndex) renderVaultList();
    }
    renderNavVaults();
    window.scrollTo(0, 0);
  }
  function vaultTab(t) {
    $("tabEntries").setAttribute("aria-selected", t === "entries");
    $("tabVaultOpts").setAttribute("aria-selected", t !== "entries");
    $("paneEntries").hidden = t !== "entries";
    $("paneVaultOpts").hidden = t === "entries";
    if (t !== "entries") renderDriveInfo();
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
      list.append(el("li", { class: "entry", onclick: () => openEntry(e.id) },
        el("div", { class: "avatar", style: { background: colorFor(title) }, text: [...title][0] || "?" }),
        el("div", { class: "e-main" }, el("div", { class: "e-title", text: title }), el("div", { class: "e-sub", text: sub })),
        el("div", { class: "e-act" },
          e.username ? el("button", { type: "button", title: "Copiar usuario", text: "👤", onclick: (ev) => { ev.stopPropagation(); copyText(e.username, false); } }) : null,
          e.password ? el("button", { type: "button", title: "Copiar contraseña", text: "🔑", onclick: (ev) => { ev.stopPropagation(); copyText(e.password, true); } }) : null)));
    }
    const empty = $("entryEmpty");
    empty.hidden = items.length > 0;
    empty.firstElementChild.textContent = all.length ? "No hay resultados para esa búsqueda." : "Esta bóveda está vacía.";
    empty.lastElementChild.hidden = all.length > 0;
  }

  // ---------- respaldo manual ----------
  async function exportVault() {
    if (!S) return;
    await persistChain;
    S.env = await sealVault({ vaultId: S.vaultId, name: S.name, salt: S.salt, iter: S.iter }, S.data, S.key);
    downloadEnv(S.env);
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
  function clearEntryForm() { ["fTitle", "fUrl", "fUser", "fPass", "fNotes"].forEach((i) => ($(i).value = "")); }
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
    $("entryDialog").close(); clearEntryForm();
    renderEntries();
    await persist();
  }
  async function deleteEntry() {
    if (!S || !editingId) return;
    const e = S.data.entries.find((x) => x.id === editingId);
    if (!confirm("¿Eliminar “" + (e.title || "esta entrada") + "”? Si te arrepentís, podés recuperarla de una copia o de las versiones anteriores del archivo en Drive.")) return;
    const i = S.data.entries.findIndex((x) => x.id === editingId);
    S.data.entries[i] = { id: editingId, deleted: true, updatedAt: now() };
    $("entryDialog").close(); clearEntryForm();
    renderEntries();
    await persist();
    toast("Entrada eliminada.");
  }

  // ---------- diálogo genérico para pedir una clave ----------
  // verify(pw) -> resultado; si lanza un error se muestra y se vuelve a pedir. Devuelve null si se cancela.
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
      $("promptOk").className = "btn " + (okText === "Eliminar" ? "danger" : "primary");
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
        try { finish(await verify(pw, confirmField ? $("promptNew").value : undefined)); }
        catch (e) { showMsg("promptMsg", "err", e instanceof WrongKeyError ? "Clave incorrecta." : errText(e)); }
        finally { busy = false; $("promptOk").disabled = false; }
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

  // ---------- opciones de la bóveda ----------
  async function changeMasterPassword() {
    if (!S) return;
    const snap = S;
    const r = await askPassword({
      title: "Cambiar clave maestra", okText: "Cambiar", confirmField: true,
      text: "En tus otros dispositivos te la va a pedir la próxima vez que abran esta bóveda. Las copias descargadas antes siguen abriéndose con la clave vieja.",
      verify: async (oldPw, newPw) => {
        await persistChain;
        const check = await sealVault({ vaultId: snap.vaultId, name: snap.name, salt: snap.salt, iter: snap.iter }, { entries: [] }, snap.key);
        try { await unlockEnvelope(check, oldPw); } catch { throw new WrongKeyError("Clave incorrecta."); }
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
    showMsg("vaultMsg", "ok", "Clave maestra cambiada. Te conviene descargar una copia nueva.");
  }
  async function renameVault() {
    if (!S) return;
    const n = $("renameInput").value.trim();
    if (!n) { showMsg("vaultMsg", "err", "El nombre no puede quedar vacío."); return; }
    S.name = n;
    const idx = (vaultIndex || []).find((v) => v.vaultId === S.vaultId);
    if (idx) idx.name = n;
    refreshVaultLabels();
    await persist();
    showMsg("vaultMsg", "ok", "Nombre cambiado.");
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
  const METER_HINT = "Usá una frase larga: 4–6 palabras al azar o 16+ caracteres.";
  document.querySelectorAll("[data-toggle]").forEach((b) => b.addEventListener("click", () => setPwVisible(b.dataset.toggle, $(b.dataset.toggle).type === "password")));
  document.querySelectorAll("[data-go]").forEach((b) => b.addEventListener("click", () => showView(b.dataset.go)));
  document.querySelectorAll("dialog [data-close]").forEach((b) => b.addEventListener("click", () => { b.closest("dialog").close(); if (b.closest("#entryDialog")) clearEntryForm(); }));
  document.querySelectorAll(".nv").forEach((b) => b.addEventListener("click", () => {
    if (b.dataset.view === "vaults" && S && window.matchMedia("(max-width: 899px)").matches && current !== "vault") { showView("vault"); return; }
    showView(b.dataset.view);
  }));

  // Cuenta
  $("signInTop").onclick = () => { showView("vaults"); signIn("loginMsg"); };
  $("signInMain").onclick = () => signIn("loginMsg");
  $("acctBtn").onclick = (e) => {
    e.stopPropagation();
    const m = $("acctMenu"); m.hidden = !m.hidden;
    $("acctBtn").setAttribute("aria-expanded", String(!m.hidden));
  };
  document.addEventListener("click", (e) => { if (!$("acctMenu").hidden && !$("accountBox").contains(e.target)) $("acctMenu").hidden = true; });
  $("signOutBtn").onclick = signOut;

  // Bóvedas
  $("createOpen").onclick = () => {
    hideMsg("createMsg");
    paintMeter("createMeterBar", "createMeterText", "", METER_HINT);
    if (S) { if (hasUnsyncedChanges() && !confirm("La bóveda abierta tiene cambios sin subir. ¿Cerrarla igual?")) return; lockVault(null, true); }
    showView("create");
    setTimeout(() => $("createName").focus(), 30);
  };
  $("refreshVaults").onclick = () => refreshVaults();
  $("importCopyBtn").onclick = () => $("fileImportCopy").click();
  $("fileImportCopy").onchange = (ev) => { const f = ev.target.files[0]; ev.target.value = ""; if (f) importCopyAsVault(f); };
  $("unlockForm").addEventListener("submit", doUnlock);
  $("createForm").addEventListener("submit", doCreate);
  $("createPw").addEventListener("input", () => { paintMeter("createMeterBar", "createMeterText", $("createPw").value, METER_HINT); createMatch(); });
  $("createPw2").addEventListener("input", createMatch);
  function createMatch() {
    const t = $("createMatch"), a = $("createPw").value, b = $("createPw2").value;
    if (!b) { t.textContent = ""; return; }
    t.textContent = a === b ? "Coinciden." : "No coinciden."; t.style.color = a === b ? "var(--ok)" : "var(--err)";
  }

  // Bóveda abierta
  $("lockBtn").onclick = () => {
    if (hasUnsyncedChanges() && !confirm("Hay cambios que todavía no se subieron a Drive. Si cerrás la bóveda ahora se pierden. ¿Cerrar igual?")) return;
    lockVault(null, true); showView("vaults");
  };
  $("syncChip").onclick = () => { if (!Drive.hasToken()) signIn("vaultMsg"); else sync(); };
  $("tabEntries").onclick = () => vaultTab("entries");
  $("tabVaultOpts").onclick = () => vaultTab("opts");
  $("search").addEventListener("input", renderEntries);
  $("addEntry").onclick = () => openEntry(null);
  $("entryForm").addEventListener("submit", saveEntry);
  $("entryDialog").addEventListener("cancel", clearEntryForm);
  $("fDelete").onclick = deleteEntry;
  $("fCopyUser").onclick = () => copyText($("fUser").value, false);
  $("fCopyPass").onclick = () => copyText($("fPass").value, true);
  $("fOpenUrl").onclick = () => {
    const u = $("fUrl").value.trim(); if (!u) return;
    window.open(/^https?:\/\//i.test(u) ? u : "https://" + u, "_blank", "noopener,noreferrer");
  };
  $("fGen").onclick = () => {
    if ($("fPass").value && !confirm("¿Reemplazar la contraseña actual por una nueva? (Recordá cambiarla también en el sitio.)")) return;
    $("fPass").value = quickGenerate(); setPwVisible("fPass", true); updateEntryStrength();
  };
  $("fPass").addEventListener("input", updateEntryStrength);
  $("driveSyncNow").onclick = () => sync();
  $("exportBtn").onclick = exportVault;
  $("importFileBtn").onclick = () => $("fileImportApp").click();
  $("fileImportApp").onchange = (ev) => { const f = ev.target.files[0]; ev.target.value = ""; if (f) mergeVaultFile(f); };
  $("openImportOld").onclick = openImportOld;
  $("ioDecrypt").onclick = ioDecrypt;
  $("ioBack").onclick = () => { $("ioStep1").hidden = false; $("ioStep2").hidden = true; $("ioFoot").hidden = true; };
  $("ioImport").onclick = ioImport;
  $("renameBtn").onclick = renameVault;
  $("changePwBtn").onclick = changeMasterPassword;
  $("deleteVaultBtn").onclick = () => {
    if (!S) return;
    const v = (vaultIndex || []).find((x) => x.vaultId === S.vaultId);
    if (live().length > 0) { showMsg("vaultMsg", "warn", "Para eliminar la bóveda primero tiene que estar vacía: borrá sus " + live().length + " entradas una por una."); return; }
    if (hasUnsyncedChanges()) { showMsg("vaultMsg", "warn", "Esperá a que se terminen de guardar los cambios en Drive."); return; }
    if (v) deleteVault(v);
  };

  // Generador
  function loadGenPrefs() {
    const g = prefs.gen;
    $("genLen").value = g.len; $("genLower").checked = g.lower; $("genUpper").checked = g.upper; $("genDigits").checked = g.digits; $("genSymbols").checked = g.symbols; $("genSymbolSet").value = g.symbolSet;
  }
  function saveGenPrefs() {
    prefs.gen = { len: Number($("genLen").value) || 20, lower: $("genLower").checked, upper: $("genUpper").checked, digits: $("genDigits").checked, symbols: $("genSymbols").checked, symbolSet: $("genSymbolSet").value };
    savePrefs();
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
    if (!S) { showMsg("genMsg", "err", "Abrí una bóveda para guardarla (Bóvedas → elegí una → clave maestra)."); return; }
    showView("vault"); vaultTab("entries"); openEntry(null, { password: v });
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
  $("pw").addEventListener("input", () => { paintMeter("meterBar", "meterText", $("pw").value, METER_HINT); updateMatch(); });
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
    setOutputSecret(false); hideMsg("msg"); paintMeter("meterBar", "meterText", "", METER_HINT); updateMatch();
  };

  // Ajustes
  $("autoLock").value = String(prefs.autoLockMin);
  $("autoLock").onchange = () => { prefs.autoLockMin = Number($("autoLock").value) || 5; savePrefs(); };
  $("wipeLocal").onclick = async () => {
    if (!confirm("Se van a borrar de este navegador las preferencias de la app y los archivos de la app guardados para usarla sin internet. Tus bóvedas en Drive no se tocan. ¿Continuar?")) return;
    Object.keys(localStorage).filter((k) => k.startsWith("cypher.")).forEach((k) => localStorage.removeItem(k));
    try { if (window.caches) for (const k of await caches.keys()) if (k.startsWith("cypher-")) await caches.delete(k); } catch { /* nada */ }
    try { if (navigator.serviceWorker) for (const r of await navigator.serviceWorker.getRegistrations()) await r.unregister(); } catch { /* nada */ }
    legacyVaults = []; renderLegacy();
    showMsg("settingsMsg", "ok", "Listo: no quedó nada de la app en este navegador. Si cerrás la pestaña ahora, no queda rastro.");
  };
  $("selfTestBtn").onclick = (e) => { e.preventDefault(); selfTest(); };
  $("appVersion").textContent = APP_VERSION;

  // Instalación como app
  let installEvt = null;
  window.addEventListener("beforeinstallprompt", (e) => { e.preventDefault(); installEvt = e; $("installBox").hidden = false; });
  $("installBtn").onclick = async () => { if (!installEvt) return; installEvt.prompt(); await installEvt.userChoice; installEvt = null; $("installBox").hidden = true; };
  const standalone = window.matchMedia("(display-mode: standalone)").matches || navigator.standalone;
  if (/iphone|ipad|ipod/i.test(navigator.userAgent) && !standalone) $("iosInstallHint").hidden = false;

  // Service worker: guarda solo los archivos de la app (nunca datos de bóvedas) y avisa si hay versión nueva.
  if ("serviceWorker" in navigator && location.protocol !== "file:") {
    navigator.serviceWorker.register("sw.js").then((reg) => {
      const offer = (w) => {
        if (!w) return;
        $("updateBar").hidden = false;
        $("updateBtn").onclick = () => {
          if (hasUnsyncedChanges() && !confirm("Hay cambios sin subir a Drive que se perderían al actualizar. ¿Actualizar igual?")) return;
          w.postMessage("skipWaiting");
        };
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
      if (!S) location.reload(); else toast("Versión nueva lista: se aplica al recargar la app.");
    });
  }

  // Arranque
  loadGenPrefs();
  setMode("enc");
  paintMeter("meterBar", "meterText", "", METER_HINT);
  renderAccount();
  showView("vaults");
  if (!window.crypto || !crypto.subtle) {
    showMsg("globalAlert", "err", "Este navegador no ofrece cifrado seguro (Web Crypto). Abrí la app desde https:// en un navegador actualizado.");
  } else {
    selfTestDone = selfTest();
  }
  // Se precarga el inicio de sesión de Google para que el botón funcione al primer toque.
  if (Drive.configured() && navigator.onLine) Drive.load().catch(() => {});
})();
