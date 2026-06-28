# DERYI INVENTARIO - PWA + Firebase

Aplicativo de inventario instalable como PWA, con usuarios, roles, bloqueo por laboratorio y sincronización en Firebase.

## Archivos principales

- `index.html`: interfaz principal.
- `styles.css`: diseño visual.
- `app.js`: lógica del aplicativo y conexión a Firebase.
- `firebase-config.js`: configuración de Firebase. Debes reemplazar los valores `REEMPLAZAR_*`.
- `manifest.json`: configuración PWA instalable.
- `sw.js`: service worker para caché básica.
- `firestore.rules`: reglas recomendadas para Firestore.
- `assets/logo.png`: logo horizontal.
- `assets/icons/`: íconos PWA.

## Configuración inicial

1. Crea un proyecto en Firebase.
2. En Firebase Authentication, activa el método Email/Password.
3. En Firestore Database, crea la base de datos.
4. Reemplaza los datos de `firebase-config.js` con la configuración web del proyecto.
5. Publica las reglas de `firestore.rules` en Firebase.
6. Sube todos los archivos a GitHub Pages.

## Primer administrador

El correo administrador inicial está configurado en:

`adrian90.2y@gmail.com`

Ese usuario puede crear su cuenta desde “Crear acceso” aunque todavía no exista en `allowedEmails`.

## Creación de usuarios

El administrador entra a la pestaña `Usuarios` y preautoriza:

- nombre
- correo
- rol

Luego el usuario abre la app, entra en `Crear acceso`, usa su correo autorizado y define su contraseña.

## Carga de inventario

Solo el administrador ve `Carga de inventario`.

Al cargar archivo:

- reemplaza inventario anterior,
- borra conteos anteriores,
- elimina productos con `Stock Actual = 0`,
- guarda productos con stock diferente de cero.

## Bloqueo de laboratorio

- Un laboratorio solo puede ser tomado por un usuario a la vez.
- Al tomarlo, queda bloqueado para otros usuarios.
- Se intenta liberar al cerrar sesión o cerrar la app.
- Si no hay actividad por 10 minutos, el bloqueo vence automáticamente.
- Al finalizar todos los productos del laboratorio, se marca completo.

## Instalación como PWA

- Android: abrir el enlace y tocar “Instalar app” o “Agregar a pantalla principal”.
- iOS: abrir en Safari, compartir, “Agregar a pantalla de inicio”.

## Nota

Esta es una primera versión funcional preparada para Firebase. Se recomienda probar primero con una copia del inventario antes de usarla en inventario real.
