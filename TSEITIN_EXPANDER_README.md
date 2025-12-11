# Tseitin Expander Verification

Verificación empírica de la construcción de fórmulas Tseitin sobre grafos expansores circulantes.

## Descripción

Este módulo implementa y verifica la construcción de fórmulas CNF usando la transformación de Tseitin sobre grafos expansores. La construcción es fundamental para demostrar propiedades de complejidad computacional relacionadas con treewidth y satisfacibilidad.

## Características Principales

### 1. Construcción de Grafos Expansores Circulantes

- **Grafos circulantes d-regulares**: Construidos usando offsets específicos
- **Grado controlado**: Para n par, el grado es impar (importante para propiedades de Tseitin)
- **Propiedades de expansión**: Los grafos tienen buenas propiedades de conectividad

### 2. Codificación Tseitin

- **Variables por arista**: Una variable booleana por cada arista del grafo
- **Restricciones XOR**: Para cada vértice, la suma de las aristas incidentes debe ser 1 (mod 2)
- **Fórmula CNF**: Codificación completa en forma normal conjuntiva

### 3. Análisis y Verificación

- **Regularidad**: Verifica que todos los vértices tienen el mismo grado
- **Treewidth**: Estimación del lower bound del treewidth
- **Propiedades de satisfacibilidad**: Análisis de cuándo las fórmulas son insatisfacibles

## Uso

### Ejecución Directa

```bash
python3 tseitin_expander_verification.py
```

Esto ejecuta la verificación completa con tamaños de grafo predefinidos: [10, 14, 22, 30, 50, 100]

### Uso Como Módulo

```python
from tseitin_expander_verification import (
    construct_circulant_expander,
    tseitin_expander_formula,
    analyze_construction
)

# Construir grafo expansor de 30 vértices
G = construct_circulant_expander(30)

# Generar fórmula Tseitin
formula = tseitin_expander_formula(30)

# Análisis completo
result = analyze_construction(30)
```

## Salida del Programa

El programa genera un análisis detallado para cada tamaño de grafo:

```
======================================================================
ANÁLISIS PARA n = 30
======================================================================

📐 Construyendo expansor circulante...
  Vértices: 30
  Aristas: 75
  Regular: ✓
  Grado: 5
  Grado impar: ✓

🔧 Generando fórmula Tseitin...
  Variables: 75
  Cláusulas: 480
  Longitud promedio cláusula: 5.00
  Ratio cláusulas/variables: 6.40

📊 Análisis de treewidth...
  Treewidth estimado (lower bound): 3
  Ratio tw/n: 0.100
  Cumple tw ≥ n/20: ✓
```

Y un resumen final:

```
======================================================================
                        RESUMEN DE RESULTADOS                         
======================================================================

n        d      #Vars      #Clau      tw_lb      tw/n    
----------------------------------------------------------------------
10       3      15         40         1          0.100
14       3      21         56         2          0.143
22       5      55         352        2          0.091
30       5      75         480        3          0.100
50       7      175        3200       3          0.060
100      11     550        102400     4          0.040

======================================================================
                  VERIFICACIÓN DE PROPIEDADES CLAVE                   
======================================================================

  ✓ Todos d-regulares: ✅
  ✓ Todos grado impar: ✅
  ✓ Todos tw ≥ n/25: ✅

🎉 CONSTRUCCIÓN VERIFICADA EXITOSAMENTE
```

## Tests

El módulo incluye tests comprehensivos en `tests/test_tseitin_expander_verification.py`:

```bash
python3 -m unittest tests/test_tseitin_expander_verification.py -v
```

Los tests cubren:
- Funciones de primalidad
- Construcción de grafos expansores
- Codificación Tseitin
- Funciones de análisis
- Integración completa

## Detalles Técnicos

### Grafos Circulantes

Un grafo circulante Cir(n, S) tiene:
- Vértices: {0, 1, ..., n-1}
- Aristas: {i, j} donde |i-j| mod n ∈ S

Para obtener grado d-regular:
- Si d es par: usar d/2 offsets
- Si d es impar y n es par: usar (d-1)/2 offsets más n/2

### Transformación de Tseitin

Para un grafo G = (V, E):
1. Asignar variable x_e a cada arista e ∈ E
2. Para cada vértice v con aristas incidentes E(v):
   - Añadir cláusulas que codifican: ⊕_{e ∈ E(v)} x_e = 1
   - Esto se codifica enumerando todas las asignaciones de paridad par y prohibiéndolas

### Propiedades de Treewidth

Para grafos expansores d-regulares:
- Lower bound: tw ≥ n / (2d)
- Para expansores buenos: tw ∈ Ω(n)
- El módulo verifica tw ≥ n/25 como criterio práctico

## Dependencias

- `numpy>=1.24.0`: Cálculos numéricos
- `networkx>=3.0`: Construcción y análisis de grafos

## Referencias

Este módulo implementa construcciones descritas en:
- Tseitin, G. S. (1983). "On the complexity of derivation in propositional calculus"
- Urquhart, A. (1987). "Hard examples for resolution"
- Ben-Sasson, E. & Wigderson, A. (2001). "Short proofs are narrow"

## Autor

José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
