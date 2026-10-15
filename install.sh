#!/bin/bash

echo "════════════════════════════════════════════════════════════════"
echo "  INSTALACIÓN: Ultimate Unification Algorithm"
echo "════════════════════════════════════════════════════════════════"

# Colores
GREEN='\033[0;32m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Verificar Python
echo -e "\n${BLUE}[1/6]${NC} Verificando Python..."
if command -v python3 &> /dev/null; then
    PYTHON_VERSION=$(python3 --version)
    echo -e "${GREEN}✓${NC} Python encontrado: $PYTHON_VERSION"
else
    echo "❌ Python 3 no encontrado. Por favor instalar Python 3.8+"
    exit 1
fi

# Crear directorio
echo -e "\n${BLUE}[2/6]${NC} Creando directorio del proyecto..."
mkdir -p ultimate-unification
cd ultimate-unification
echo -e "${GREEN}✓${NC} Directorio creado"

# Crear ambiente virtual
echo -e "\n${BLUE}[3/6]${NC} Creando ambiente virtual..."
python3 -m venv venv
source venv/bin/activate
echo -e "${GREEN}✓${NC} Ambiente virtual creado"

# Actualizar pip
echo -e "\n${BLUE}[4/6]${NC} Actualizando pip..."
pip install --upgrade pip --quiet
echo -e "${GREEN}✓${NC} pip actualizado"

# Instalar dependencias
echo -e "\n${BLUE}[5/6]${NC} Instalando dependencias..."
pip install numpy scipy networkx matplotlib pandas pytest seaborn --quiet
echo -e "${GREEN}✓${NC} Dependencias instaladas"

# Crear archivo de prueba
echo -e "\n${BLUE}[6/6]${NC} Creando script de prueba..."
cat > test_installation.py << 'PYCODE'
import numpy as np
import scipy
import networkx as nx
import matplotlib
import pandas as pd
import pytest

print("✅ NumPy version:", np.__version__)
print("✅ SciPy version:", scipy.__version__)
print("✅ NetworkX version:", nx.__version__)
print("✅ Matplotlib version:", matplotlib.__version__)
print("✅ Pandas version:", pd.__version__)
print("✅ Pytest version:", pytest.__version__)
print("\n🎉 Todas las dependencias instaladas correctamente!")
PYCODE

python3 test_installation.py
echo -e "\n${GREEN}✓${NC} Instalación completa"

echo -e "\n════════════════════════════════════════════════════════════════"
echo -e "  ${GREEN}INSTALACIÓN COMPLETADA${NC}"
echo -e "════════════════════════════════════════════════════════════════"
echo -e "\nPróximos pasos:"
echo -e "  1. cd ultimate-unification"
echo -e "  2. source venv/bin/activate"
echo -e "  3. Copiar ultimate_algorithm.py a este directorio"
echo -e "  4. python3 ultimate_algorithm.py"
echo -e "\n════════════════════════════════════════════════════════════════"
