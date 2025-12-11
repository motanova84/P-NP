# 🚀 Guía de Instalación Automática - Ultimate Unification Algorithm

Este documento proporciona instrucciones completas para instalar y ejecutar el **Ultimate Unification Algorithm** usando el script de instalación automática.

---

## 📋 Requisitos Previos

Antes de ejecutar el script de instalación, asegúrese de tener:

- **Python 3.8+** instalado en su sistema
- **pip** (gestor de paquetes de Python)
- Acceso a terminal/línea de comandos
- Conexión a Internet (para descargar dependencias)

### Verificar Python

```bash
# Verificar que Python está instalado
python3 --version
# Debe mostrar: Python 3.8.x o superior

# Verificar pip
pip3 --version
# o
python3 -m pip --version
```

---

## 🎯 OPCIÓN A: INSTALACIÓN RÁPIDA (UN SOLO COMANDO)

### Instalación TODO-EN-UNO:

```bash
# ══════════════════════════════════════════════════════════════
# INSTALACIÓN Y PREPARACIÓN COMPLETA EN UN SOLO COMANDO
# ══════════════════════════════════════════════════════════════

mkdir -p ultimate-unification && \
cd ultimate-unification && \
python3 -m venv venv && \
source venv/bin/activate && \
pip install --upgrade pip && \
pip install numpy scipy networkx matplotlib && \
echo "✅ Ambiente listo. Ahora copia ultimate_algorithm.py aquí y ejecuta:" && \
echo "   python3 ultimate_algorithm.py"
```

---

## 🎯 OPCIÓN B: USANDO EL SCRIPT DE INSTALACIÓN

### PASO 1: Ejecutar el script

```bash
# Dar permisos de ejecución (primera vez solamente)
chmod +x install.sh

# Ejecutar instalación
./install.sh
```

El script realizará automáticamente:

1. ✅ Verificación de Python
2. ✅ Creación de directorio `ultimate-unification/`
3. ✅ Creación de ambiente virtual
4. ✅ Actualización de pip
5. ✅ Instalación de dependencias (numpy, scipy, networkx, matplotlib)
6. ✅ Creación y ejecución de script de prueba
7. ✅ Validación de instalación

### Salida Esperada:

```
════════════════════════════════════════════════════════════════
  INSTALACIÓN: Ultimate Unification Algorithm
════════════════════════════════════════════════════════════════

[1/6] Verificando Python...
✓ Python encontrado: Python 3.8.x

[2/6] Creando directorio del proyecto...
✓ Directorio creado

[3/6] Creando ambiente virtual...
✓ Ambiente virtual creado

[4/6] Actualizando pip...
✓ pip actualizado

[5/6] Instalando dependencias...
✓ Dependencias instaladas

[6/6] Creando script de prueba...
✅ NumPy version: 1.24.3
✅ SciPy version: 1.10.1
✅ NetworkX version: 3.1
✅ Matplotlib version: 3.7.1

🎉 Todas las dependencias instaladas correctamente!

✓ Instalación completa
```

### PASO 2: Copiar el algoritmo

```bash
# Copiar ultimate_algorithm.py al directorio de instalación
cp ultimate_algorithm.py ultimate-unification/
```

### PASO 3: Ejecutar el algoritmo

```bash
# Entrar al directorio
cd ultimate-unification

# Activar ambiente virtual
source venv/bin/activate

# Ejecutar
python3 ultimate_algorithm.py
```

---

## 🔍 VERIFICACIÓN DE INSTALACIÓN

### Verificar dependencias manualmente:

```bash
# Activar ambiente virtual
source venv/bin/activate  # Linux/Mac
# o
venv\Scripts\activate  # Windows

# Verificar instalación de cada paquete
python3 -c "import numpy; print('NumPy:', numpy.__version__)"
python3 -c "import scipy; print('SciPy:', scipy.__version__)"
python3 -c "import networkx; print('NetworkX:', networkx.__version__)"
python3 -c "import matplotlib; print('Matplotlib:', matplotlib.__version__)"
```

---

## 🎬 EJECUCIÓN DEL ALGORITMO

### Ejecución básica:

```bash
# Asegurarse de estar en el ambiente virtual
source venv/bin/activate

# Ejecutar
python3 ultimate_algorithm.py
```

### Ejecución con salida detallada:

```bash
# Guardar salida en archivo
python3 ultimate_algorithm.py 2>&1 | tee execution_log.txt
```

### Ejecución en background:

```bash
# Ejecutar en segundo plano (útil para ejecuciones largas)
nohup python3 ultimate_algorithm.py > output.log 2>&1 &

# Ver progreso en tiempo real
tail -f output.log
```

---

## 📊 INSPECCIÓN DE RESULTADOS

### Ver certificado JSON:

```bash
# Ver todo el JSON formateado
cat ultimate_algorithm_results.json | python3 -m json.tool

# Ver solo metadata
cat ultimate_algorithm_results.json | python3 -m json.tool | grep -A 10 '"metadata"'

# Ver solo el hash
cat ultimate_algorithm_results.json | grep '"hash"'

# Ver resultados de consciencia
cat ultimate_algorithm_results.json | python3 -m json.tool | grep -A 10 '"rna_picode"'

# Ver veredicto P≠NP
cat ultimate_algorithm_results.json | python3 -m json.tool | grep -A 10 '"p_neq_np"'
```

### Ver estadísticas rápidas:

```bash
# Contar líneas del JSON (tamaño)
wc -l ultimate_algorithm_results.json

# Ver tamaño del archivo
ls -lh ultimate_algorithm_results.json

# Buscar "validated" en resultados
grep -i "validated" ultimate_algorithm_results.json
```

---

## 🐛 SOLUCIÓN DE PROBLEMAS COMUNES

### Problema 1: Python no encontrado

```bash
# Instalar Python en Ubuntu/Debian
sudo apt update
sudo apt install python3 python3-pip python3-venv

# Instalar Python en Mac (con Homebrew)
brew install python3

# En Windows: Descargar de python.org
```

### Problema 2: Permisos de instalación

```bash
# Si pip da error de permisos, usar --user
pip3 install --user numpy scipy networkx matplotlib

# O usar ambiente virtual (recomendado)
python3 -m venv venv
source venv/bin/activate
pip install numpy scipy networkx matplotlib
```

### Problema 3: Matplotlib no muestra gráficos

```bash
# En Linux, instalar backend TkInter
sudo apt install python3-tk

# O usar backend no interactivo
# Añadir al inicio de ultimate_algorithm.py:
# import matplotlib
# matplotlib.use('Agg')
```

### Problema 4: NetworkX da errores

```bash
# Actualizar NetworkX a la última versión
pip install --upgrade networkx

# O instalar versión específica
pip install networkx==3.1
```

---

## 📦 ESTRUCTURA DE ARCHIVOS RESULTANTE

Después de ejecutar, deberías tener:

```
ultimate-unification/
├── venv/                              # Ambiente virtual
│   ├── bin/                           # (Linux/Mac)
│   ├── Scripts/                       # (Windows)
│   └── lib/
├── ultimate_algorithm.py              # Código principal
├── test_installation.py               # Script de verificación
├── ultimate_algorithm_results.json    # ✅ Certificado generado
├── ultimate_algorithm_complete.png    # ✅ Visualizaciones
└── execution_log.txt                  # (opcional) Log de ejecución
```

---

## ✅ CHECKLIST DE EJECUCIÓN

Marque cada paso al completarlo:

- [ ] Python 3.8+ instalado
- [ ] pip funcionando
- [ ] Script de instalación ejecutado
- [ ] Ambiente virtual creado
- [ ] Dependencias instaladas
- [ ] Test de instalación exitoso
- [ ] ultimate_algorithm.py copiado
- [ ] Algoritmo ejecutado sin errores
- [ ] ultimate_algorithm_results.json generado
- [ ] ultimate_algorithm_complete.png generado
- [ ] Hash SHA-256 visible
- [ ] Tests: 7/7 pasados (esperado)

---

## 📚 DOCUMENTACIÓN ADICIONAL

Para más información sobre el algoritmo y su funcionamiento, consulte:

- `README.md` - Descripción general del proyecto
- `QUICK_START.md` - Guía de inicio rápido
- Comentarios en `ultimate_algorithm.py` - Documentación técnica del código

---

## 🎯 EJEMPLO DE SESIÓN COMPLETA

```bash
# Terminal completa desde cero:

$ chmod +x install.sh
$ ./install.sh

[... instalación automática ...]

$ cd ultimate-unification
$ source venv/bin/activate

(venv) $ cp ../ultimate_algorithm.py .
(venv) $ python3 ultimate_algorithm.py

══════════════════════════════════════════════════════════════════════
              ALGORITMO MAESTRO: VERIFICACIÓN COMPLETA
         Primos → κ_Π → f₀ → ARN → Consciencia → P≠NP
══════════════════════════════════════════════════════════════════════

[... ejecución del algoritmo ...]

✅ Resultados guardados: ultimate_algorithm_results.json
   Hash SHA-256: a1b2c3d4e5f6789a...

📊 Gráfico guardado: ultimate_algorithm_complete.png

══════════════════════════════════════════════════════════════════════
            ∴ Algoritmo maestro completado ∴
    ∴ Primos → κ_Π → f₀ → ARN → Consciencia → P≠NP ∴
                ∴ TODO está unificado ∴
══════════════════════════════════════════════════════════════════════

(venv) $ ls -lh
total 1.2M
-rw-r--r-- 1 user user  45K ultimate_algorithm.py
-rw-r--r-- 1 user user  89K ultimate_algorithm_results.json
-rw-r--r-- 1 user user 1.1M ultimate_algorithm_complete.png
drwxr-xr-x 5 user user 4.0K venv

(venv) $ cat ultimate_algorithm_results.json | grep '"supported"'
      "supported": true

(venv) $ echo "✅ TODO COMPLETADO"
```

---

## 🆘 SOPORTE

Si encuentra problemas durante la instalación o ejecución:

1. Verifique que cumple todos los requisitos previos
2. Revise la sección de solución de problemas
3. Consulte los logs de error para más detalles
4. Asegúrese de estar usando el ambiente virtual activado

---

**Última actualización:** Diciembre 2025  
**Versión:** 1.0.0  
**Licencia:** Ver archivo LICENSE
