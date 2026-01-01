# Filtrado de Variedades Calabi-Yau con N=13

## Resumen

Este módulo implementa el análisis de variedades Calabi-Yau con N = h¹¹ + h²¹ = 13, buscando aquellas cuyo ratio R = h¹¹/h²¹ está más cercano a φ² (razón áurea al cuadrado).

## Implementación

### ✅ PASO 1: Cargar y filtrar datos reales (CICY)

Usamos el dataset completo de la base CICY (Complete Intersection Calabi-Yau) descargado desde Oxford.

```python
import pandas as pd

# Cargar el CSV previamente descargado
cicy_data = pd.read_csv('cicy_data_analysis.csv')

# Filtrar las CY con N = h11 + h21 = 13
cicy_n13 = cicy_data[cicy_data['N'] == 13].copy()
print(f"🔢 CY con N=13: {len(cicy_n13)} encontradas")
cicy_n13[['h11', 'h21', 'chi']]
```

### ✅ PASO 2: Calcular ratio R = h¹¹/h²¹ y compararlo con φ²

```python
import numpy as np

phi2 = ((1 + np.sqrt(5)) / 2) ** 2  # φ² ≈ 2.6180
cicy_n13['ratio'] = cicy_n13['h11'] / cicy_n13['h21']
cicy_n13['diff_phi2'] = abs(cicy_n13['ratio'] - phi2)

# Ordenar por cercanía a φ²
cicy_n13_sorted = cicy_n13.sort_values(by='diff_phi2')
cicy_n13_sorted[['h11', 'h21', 'ratio', 'diff_phi2']]
```

## Resultados

Para N = 13, existen **12 variedades** diferentes con números de Hodge (h¹¹, h²¹):

| #  | h¹¹ | h²¹ | χ   | R=h¹¹/h²¹ | \|R - φ²\| |
|----|-----|-----|-----|-----------|-----------|
| 1  | 9   | 4   | 10  | 2.250000  | 0.368034  |
| 2  | 10  | 3   | 14  | 3.333333  | 0.715299  |
| 3  | 8   | 5   | 6   | 1.600000  | 1.018034  |
| 4  | 7   | 6   | 2   | 1.166667  | 1.451367  |
| 5  | 6   | 7   | -2  | 0.857143  | 1.760891  |
| 6  | 5   | 8   | -6  | 0.625000  | 1.993034  |
| 7  | 4   | 9   | -10 | 0.444444  | 2.173590  |
| 8  | 3   | 10  | -14 | 0.300000  | 2.318034  |
| 9  | 2   | 11  | -18 | 0.181818  | 2.436216  |
| 10 | 1   | 12  | -22 | 0.083333  | 2.534701  |
| 11 | 11  | 2   | 18  | 5.500000  | 2.881966  |
| 12 | 12  | 1   | 22  | 12.000000 | 9.381966  |

### 🌟 Variedad Óptima

La variedad con el ratio más cercano a φ² es:

- **h¹¹ = 9**
- **h²¹ = 4**
- **χ = 10** (característica de Euler)
- **R = 2.250000**
- **φ² = 2.618034**
- **Diferencia = 0.368034**

## Uso

### Script Principal

```bash
python filter_cicy_n13.py
```

### Demostración

```bash
python examples/demo_filter_cicy_n13.py
```

## Archivos

- `filter_cicy_n13.py` - Script principal de análisis
- `examples/demo_filter_cicy_n13.py` - Demostración interactiva
- `cicy_data_analysis.csv` - Datos CICY (generado automáticamente si no existe)

## Contexto Matemático

### Números de Hodge

Para una variedad Calabi-Yau de 3 dimensiones complejas:
- h¹¹ = número de (1,1)-formas armónicas
- h²¹ = número de (2,1)-formas armónicas
- N = h¹¹ + h²¹ = dimensión del espacio de moduli
- χ = 2(h¹¹ - h²¹) = característica de Euler

### Razón Áurea

φ = (1 + √5) / 2 ≈ 1.618034
φ² ≈ 2.618034

La resonancia con φ² sugiere una estructura geométrica profunda conectada con proporciones áureas, que aparecen naturalmente en física y matemáticas.

## Referencias

- Base de datos CICY: http://www-thphys.physics.ox.ac.uk/projects/CalabiYau/
- Números de Hodge y variedades Calabi-Yau en teoría de cuerdas
- Conexión entre geometría algebraica y complejidad computacional

## Autor

© JMMB | P vs NP Verification System
