// Service worker: guarda la app para que funcione sin internet.
// Cambiá VERSION en cada publicación para que los dispositivos bajen la versión nueva.
const VERSION = "cypher-v1.2.3";
const SHELL = ["./", "index.html", "styles.css", "app.js", "config.js", "manifest.webmanifest",
  "cifrador.html", "privacy.html", "icons/icon.svg", "icons/icon-192.png", "icons/icon-512.png", "icons/maskable-512.png", "icons/apple-touch-icon.png"];

self.addEventListener("install", (e) => {
  e.waitUntil(caches.open(VERSION).then((c) => c.addAll(SHELL.map((u) => new Request(u, { cache: "reload" })))));
});
self.addEventListener("activate", (e) => {
  e.waitUntil(caches.keys().then((keys) => Promise.all(keys.filter((k) => k.startsWith("cypher-") && k !== VERSION).map((k) => caches.delete(k))))
    .then(() => self.clients.claim()));
});
self.addEventListener("message", (e) => { if (e.data === "skipWaiting") self.skipWaiting(); });
self.addEventListener("fetch", (e) => {
  const req = e.request;
  const url = new URL(req.url);
  // Solo archivos propios de la app. Google (inicio de sesión y Drive) va siempre directo a la red.
  if (req.method !== "GET" || url.origin !== self.location.origin) return;
  if (req.mode === "navigate") {
    // La raíz abre la app; cualquier otro archivo (ej. cifrador.html) se sirve tal cual.
    const isRoot = url.pathname.endsWith("/") || url.pathname.endsWith("/index.html");
    e.respondWith(caches.match(isRoot ? "index.html" : req, { ignoreSearch: true })
      .then((r) => r || fetch(req).catch(() => caches.match("index.html"))));
    return;
  }
  e.respondWith(caches.match(req, { ignoreSearch: true }).then((r) => r || fetch(req)));
});
