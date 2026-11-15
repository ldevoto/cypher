# Cypher

Bóvedas de contraseñas cifradas con clave maestra, como app instalable (PWA).

- Todo se cifra en el navegador (AES-256-GCM, PBKDF2-SHA256 600.000 iteraciones). La clave maestra nunca sale del dispositivo.
- Varias bóvedas, cada una con su clave. Se guardan cifradas en el dispositivo y, si conectás Google Drive, en tu Drive (permiso `drive.file`: la app solo ve los archivos que ella crea).
- Funciona sin internet una vez abierta.
- Herramientas: generador de contraseñas y cifrado/descifrado de texto suelto (compatible con el cifrador anterior), más un importador de esas notas viejas.

## Configuración

`config.js` tiene el ID de cliente OAuth de Google (no es secreto). En cada publicación, cambiá `VERSION` en `sw.js` para que los dispositivos bajen la versión nueva.

Este repositorio no contiene datos: las bóvedas viven en tus dispositivos y en tu Google Drive.
