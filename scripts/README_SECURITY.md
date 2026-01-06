# Scripts de Seguridad y Verificación

Este directorio contiene scripts para garantizar la seguridad y reproducibilidad del proyecto P-NP.

## Scripts de Verificación de Entorno

### `verify_env_integrity.sh`

Verifica la integridad del entorno Python comparando el estado actual con `ENV.lock`.

**Uso:**
```bash
bash scripts/verify_env_integrity.sh
```

**Qué hace:**
- ✓ Verifica que ENV.lock existe
- ✓ Compara el entorno actual con ENV.lock
- ✓ Detecta paquetes agregados, removidos o actualizados
- ✓ Verifica conflictos de dependencias
- ✓ Verifica Lean toolchain
- ✓ Genera hash SHA-256 de ENV.lock para verificación de integridad

**Salida:**
- Código de salida 0: Entorno coincide exactamente con ENV.lock
- Código de salida 1: Diferencias detectadas (ver output para detalles)

**Ejemplo de salida exitosa:**
```
================================================
  Verificación de Integridad del Entorno P-NP
================================================

✓ ENV.lock encontrado
✓ Python version: 3.11.0
✓ Paquetes en ENV.lock: 82
✓ Paquetes en entorno actual: 82

Comparando ENV.lock con el entorno actual...
✓✓✓ PERFECTO: El entorno actual coincide exactamente con ENV.lock

El entorno es 100% reproducible.
```

---

### `update_env_lock.sh`

Actualiza `ENV.lock` con el estado actual del entorno Python.

**Uso:**
```bash
bash scripts/update_env_lock.sh
```

**⚠️ IMPORTANTE:** Usa este script solo cuando actualices dependencias intencionalmente.

**Qué hace:**
- ✓ Crea backup de ENV.lock actual (ENV.lock.backup)
- ✓ Genera nuevo ENV.lock desde `pip freeze`
- ✓ Muestra diferencias entre versión antigua y nueva
- ✓ Verifica conflictos de dependencias
- ✓ Genera hash SHA-256 en ENV.lock.sha256
- ✓ Proporciona instrucciones para commit

**Cuándo usar:**
- ✅ Después de agregar nuevas dependencias a `requirements.txt`
- ✅ Después de actualizar versiones de paquetes existentes
- ✅ Después de cambios en el entorno de desarrollo

**Cuándo NO usar:**
- ❌ Sin una razón específica para actualizar dependencias
- ❌ Si no entiendes las diferencias mostradas
- ❌ Antes de revisar y aprobar los cambios

**Ejemplo de salida:**
```
================================================
  Actualización de ENV.lock
================================================

Creando backup de ENV.lock actual...
✓ Backup creado: ENV.lock.backup

Generando nuevo ENV.lock desde el entorno actual...
✓ ENV.lock actualizado exitosamente

Cambios detectados:
  + 3 paquete(s) agregado(s) o actualizado(s)
  - 3 paquete(s) removido(s) o desactualizado(s)

Paquetes nuevos o actualizados:
  + numpy==1.24.3
  + scipy==1.11.0
  + pandas==2.0.2
```

---

## Otros Scripts de Verificación

### `verify_all_proofs.sh`

Verifica todas las pruebas formales en Lean 4.

**Uso:**
```bash
bash scripts/verify_all_proofs.sh
```

### `formal_verification.sh`

Ejecuta verificación formal completa del proyecto.

**Uso:**
```bash
bash scripts/formal_verification.sh
```

### `final_verification.sh`

Verificación final antes de release.

**Uso:**
```bash
bash scripts/final_verification.sh
```

---

## Flujo de Trabajo Recomendado

### 1. Verificación Regular

Ejecuta periódicamente para asegurar que tu entorno es consistente:

```bash
# Verificar integridad del entorno
bash scripts/verify_env_integrity.sh

# Si hay diferencias no esperadas, restaurar desde requirements.txt
pip install -r requirements.txt
```

### 2. Actualización de Dependencias

Cuando necesites actualizar dependencias:

```bash
# 1. Actualizar requirements.txt manualmente
# Ejemplo: cambiar numpy>=1.21 a numpy>=1.24

# 2. Instalar nuevas dependencias
pip install -r requirements.txt

# 3. Verificar que no hay conflictos
python -m pip check

# 4. Actualizar ENV.lock
bash scripts/update_env_lock.sh

# 5. Revisar los cambios
git diff ENV.lock

# 6. Commitear si los cambios son correctos
git add ENV.lock ENV.lock.sha256
git commit -m "Update dependencies: numpy 1.21 -> 1.24"

# 7. Limpiar backup
rm ENV.lock.backup
```

### 3. Configuración de Nuevo Entorno

Para configurar un entorno desde cero:

```bash
# 1. Clonar repositorio
git clone https://github.com/motanova84/P-NP.git
cd P-NP

# 2. Crear entorno virtual (recomendado)
python -m venv venv
source venv/bin/activate  # En Windows: venv\Scripts\activate

# 3. Opción A: Instalar dependencias principales
pip install -r requirements.txt

# 3. Opción B: Replicar entorno exacto (para debugging)
# Extraer solo nombres de paquetes de ENV.lock
cat ENV.lock | awk -F'==' '{print $1"=="$2}' > /tmp/exact_deps.txt
pip install -r /tmp/exact_deps.txt

# 4. Verificar instalación
bash scripts/verify_env_integrity.sh
```

---

## Integración con CI/CD

El workflow `.github/workflows/verify-security-reproducibility.yml` ejecuta automáticamente:

- Verificación de integridad de ENV.lock
- Detección de conflictos de dependencias
- Búsqueda de secretos hardcodeados
- Verificación de documentación de seguridad

Ejecuta en:
- ✓ Cada push a `main`
- ✓ Cada pull request
- ✓ Semanalmente (lunes a las 8am UTC)

---

## Solución de Problemas

### Problema: "ENV.lock difiere del entorno actual"

**Solución 1** (dependencias desactualizadas localmente):
```bash
pip install -r requirements.txt
```

**Solución 2** (actualización intencional):
```bash
bash scripts/update_env_lock.sh
git add ENV.lock ENV.lock.sha256
git commit -m "Update ENV.lock"
```

### Problema: "Hash de ENV.lock no coincide"

Esto indica que ENV.lock fue modificado. Verifica:
```bash
git diff ENV.lock
```

Si la modificación fue intencional, regenera el hash:
```bash
sha256sum ENV.lock > ENV.lock.sha256
```

### Problema: "Conflictos de dependencias detectados"

```bash
# Ver conflictos específicos
python -m pip check

# Resolver actualizando dependencias conflictivas
pip install --upgrade [paquete-conflictivo]

# Actualizar ENV.lock después de resolver
bash scripts/update_env_lock.sh
```

---

## Referencias

- **SEGURIDAD.md**: Documentación completa de seguridad
- **RESUMEN DE SEGURIDAD.md**: Resumen ejecutivo de seguridad
- **ENV.lock**: Snapshot del entorno Python
- **ENV.lock.sha256**: Hash de verificación de integridad

---

## Contacto

Para preguntas sobre seguridad o reproducibilidad, consulta:
- [SEGURIDAD.md](../SEGURIDAD.md) - Documentación completa
- [RESUMEN DE SEGURIDAD.md](../RESUMEN%20DE%20SEGURIDAD.md) - Resumen ejecutivo

---

**Última actualización**: 2026-01-06
