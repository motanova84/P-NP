#!/bin/bash
# Script de Verificación de Integridad del Entorno
# Verifica que el entorno actual coincida con ENV.lock

set -e

echo "================================================"
echo "  Verificación de Integridad del Entorno P-NP"
echo "================================================"
echo ""

# Colores para output
GREEN='\033[0;32m'
RED='\033[0;31m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Verificar que ENV.lock existe
if [ ! -f "ENV.lock" ]; then
    echo -e "${RED}✗ ERROR: ENV.lock no encontrado${NC}"
    echo "  El archivo ENV.lock debe existir en el directorio raíz."
    exit 1
fi

echo -e "${GREEN}✓${NC} ENV.lock encontrado"

# Verificar versión de Python (usar python3 explícitamente)
PYTHON_CMD="python3"
if ! command -v python3 &> /dev/null; then
    PYTHON_CMD="python"
fi

PYTHON_VERSION=$($PYTHON_CMD --version 2>&1 | awk '{print $2}')
echo -e "${GREEN}✓${NC} Python version: $PYTHON_VERSION"

# Verificar que Python 3.10+ está instalado
PYTHON_MAJOR=$(echo $PYTHON_VERSION | cut -d. -f1)
PYTHON_MINOR=$(echo $PYTHON_VERSION | cut -d. -f2)

if [ "$PYTHON_MAJOR" -lt 3 ] || ([ "$PYTHON_MAJOR" -eq 3 ] && [ "$PYTHON_MINOR" -lt 10 ]); then
    echo -e "${YELLOW}⚠ ADVERTENCIA: Se recomienda Python 3.10 o superior${NC}"
    echo "  Versión actual: $PYTHON_VERSION"
fi

# Generar snapshot del entorno actual
echo ""
echo "Generando snapshot del entorno actual..."
TEMP_SNAPSHOT=$(mktemp)
$PYTHON_CMD -m pip freeze > "$TEMP_SNAPSHOT"

# Contar paquetes
ENV_LOCK_COUNT=$(wc -l < ENV.lock)
CURRENT_COUNT=$(wc -l < "$TEMP_SNAPSHOT")

echo -e "${GREEN}✓${NC} Paquetes en ENV.lock: $ENV_LOCK_COUNT"
echo -e "${GREEN}✓${NC} Paquetes en entorno actual: $CURRENT_COUNT"

# Comparar ENV.lock con el entorno actual
echo ""
echo "Comparando ENV.lock con el entorno actual..."

if diff -q ENV.lock "$TEMP_SNAPSHOT" > /dev/null 2>&1; then
    echo -e "${GREEN}✓✓✓ PERFECTO: El entorno actual coincide exactamente con ENV.lock${NC}"
    echo ""
    echo "El entorno es 100% reproducible."
    RESULT=0
else
    echo -e "${YELLOW}⚠ DIFERENCIAS DETECTADAS${NC}"
    echo ""
    echo "El entorno actual difiere de ENV.lock. Diferencias:"
    echo ""
    
    # Mostrar diferencias de manera clara
    echo "--- Paquetes solo en ENV.lock (faltantes en entorno actual) ---"
    diff ENV.lock "$TEMP_SNAPSHOT" | grep "^<" | sed 's/^< /  - /' || echo "  (ninguno)"
    
    echo ""
    echo "--- Paquetes solo en entorno actual (no en ENV.lock) ---"
    diff ENV.lock "$TEMP_SNAPSHOT" | grep "^>" | sed 's/^> /  + /' || echo "  (ninguno)"
    
    echo ""
    echo -e "${YELLOW}Recomendaciones:${NC}"
    echo "1. Si las diferencias son esperadas (actualización intencional):"
    echo "   python -m pip freeze > ENV.lock"
    echo "   git add ENV.lock"
    echo "   git commit -m 'Update ENV.lock'"
    echo ""
    echo "2. Si quieres restaurar el entorno desde ENV.lock:"
    echo "   pip install -r requirements.txt"
    echo ""
    RESULT=1
fi

# Verificar conflictos de dependencias
echo ""
echo "Verificando conflictos de dependencias..."
if $PYTHON_CMD -m pip check > /dev/null 2>&1; then
    echo -e "${GREEN}✓${NC} No hay conflictos de dependencias"
else
    echo -e "${RED}✗${NC} Conflictos de dependencias detectados:"
    $PYTHON_CMD -m pip check
    RESULT=1
fi

# Verificar Lean toolchain
echo ""
echo "Verificando Lean toolchain..."
if [ -f "lean-toolchain" ]; then
    LEAN_VERSION=$(cat lean-toolchain)
    echo -e "${GREEN}✓${NC} Lean toolchain: $LEAN_VERSION"
    
    # Verificar si elan está instalado
    if command -v lean &> /dev/null; then
        INSTALLED_LEAN=$(lean --version 2>&1 | head -1)
        echo -e "${GREEN}✓${NC} Lean instalado: $INSTALLED_LEAN"
    else
        echo -e "${YELLOW}⚠${NC} Lean no está instalado (ejecutar: install.sh)"
    fi
else
    echo -e "${YELLOW}⚠${NC} lean-toolchain no encontrado"
fi

# Verificar requirements.txt
echo ""
echo "Verificando requirements.txt..."
if [ -f "requirements.txt" ]; then
    REQ_COUNT=$(grep -v '^#' requirements.txt | grep -v '^$' | wc -l)
    echo -e "${GREEN}✓${NC} requirements.txt encontrado ($REQ_COUNT dependencias principales)"
else
    echo -e "${RED}✗${NC} requirements.txt no encontrado"
    RESULT=1
fi

# Generar hash de verificación de ENV.lock
echo ""
echo "Generando hash de verificación..."
if command -v sha256sum &> /dev/null; then
    HASH=$(sha256sum ENV.lock | awk '{print $1}')
    echo -e "${GREEN}✓${NC} SHA-256 de ENV.lock:"
    echo "  $HASH"
    echo ""
    echo "  Para verificar integridad en el futuro:"
    echo "  echo '$HASH  ENV.lock' | sha256sum -c"
elif command -v shasum &> /dev/null; then
    HASH=$(shasum -a 256 ENV.lock | awk '{print $1}')
    echo -e "${GREEN}✓${NC} SHA-256 de ENV.lock:"
    echo "  $HASH"
    echo ""
    echo "  Para verificar integridad en el futuro:"
    echo "  echo '$HASH  ENV.lock' | shasum -a 256 -c"
else
    echo -e "${YELLOW}⚠${NC} sha256sum/shasum no disponible, no se puede generar hash"
fi

# Resumen final
echo ""
echo "================================================"
if [ $RESULT -eq 0 ]; then
    echo -e "${GREEN}  ✓✓✓ VERIFICACIÓN EXITOSA ✓✓✓${NC}"
    echo "================================================"
    echo ""
    echo "El entorno está correctamente configurado y es reproducible."
else
    echo -e "${YELLOW}  ⚠ VERIFICACIÓN CON ADVERTENCIAS ⚠${NC}"
    echo "================================================"
    echo ""
    echo "Se detectaron diferencias. Revisa las recomendaciones arriba."
fi

echo ""
echo "Para documentación completa, ver: SEGURIDAD.md"
echo ""

# Limpiar archivo temporal
rm -f "$TEMP_SNAPSHOT"

exit $RESULT
