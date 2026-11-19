# Cypher

Gestor de contraseñas gratuito y de código abierto, como app instalable (PWA): https://ldevoto.github.io/cypher/

- Todo se cifra en el navegador (AES-256-GCM, PBKDF2-SHA256 con 600.000 iteraciones y sal por bóveda). La clave maestra nunca sale del dispositivo.
- Varias bóvedas, cada una con su clave maestra. Se guardan cifradas solo en tu Google Drive (permiso `drive.file`: la app solo ve los archivos que ella crea). En el dispositivo no queda nada: las bóvedas viven en memoria.
- Herramientas sin cuenta: generador de contraseñas y cifrado/descifrado de texto (compatible con el cifrador anterior), más un importador de esas notas viejas.
- [Política de privacidad](privacy.html)

## Configuración

`config.js` tiene el ID de cliente OAuth de Google (no es secreto). En cada publicación, cambiá `VERSION` en `sw.js` para que los dispositivos bajen la versión nueva.

Este repositorio no contiene datos de nadie.
