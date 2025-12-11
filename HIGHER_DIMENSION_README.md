# ELEVACIÓN DIMENSIONAL: Del Grafo al Ψ-Campo

Este módulo implementa la transformación del problema P≠NP en teoría cuántica de campos en (2+1)D, donde la frecuencia del marco emerge naturalmente como dimensión extra.

## Archivos Implementados

### 1. `HigherDimension.lean`

Formalización en Lean 4 de la elevación dimensional del problema P vs NP.

**Componentes principales:**

- **Parte 1: Elevación del Grafo a (2+1)D**
  - `ΨField`: Estructura que representa un grafo como un campo cuántico en (2+1)D
  - `mass_from_spectrum`: Conversión del espectro del grafo en masa efectiva

- **Parte 2: κ_Π como Propagador de Feynman**
  - `κ_Π_as_propagator`: El propagador de Feynman en espacio de momentos
  - `propagator_high_energy_limit`: Comportamiento en el límite de alta energía

- **Parte 3: Dualidad Grafo/Teoría de Campos**
  - `AdSCFT_Duality`: Estructura de la dualidad AdS/CFT para grafos
  - `tseitin_dual_to_AdS3`: El grafo de Tseitin es dual a teoría de campos en AdS₃

- **Parte 4: Frecuencia como Dimensión Radial en AdS**
  - `radial_coordinate_as_frequency`: Mapeo entre frecuencia y coordenada radial
  - `kappa_in_AdS_coordinates`: κ_Π expresado en coordenadas de AdS
  - `boundary_limit_of_kappa`: Comportamiento en el límite del boundary (z → 0)

- **Parte 5: Algoritmos Clásicos Viven en el Boundary**
  - `TM_as_CFT`: Máquinas de Turing como teorías de campos en el boundary
  - `P_algorithms_live_at_boundary`: Los algoritmos en P viven en z = 0
  - `information_complexity_is_bulk_depth`: La complejidad de información es profundidad en el bulk

- **Parte 6: Teorema Final desde la Perspectiva (2+1)D**
  - `P_neq_NP_from_QFT`: Teorema principal P ≠ NP desde teoría de campos
  - `P_neq_NP_holographic`: Versión holográfica del teorema

### 2. `examples/holographic_view.py`

Visualización interactiva de la estructura holográfica del grafo.

**Características:**

- **Clase `HolographicGraph`**: Embebe grafos en espacio AdS₃
  - `embed_in_AdS()`: Calcula el embedding usando coordenadas de Poincaré
  - `compute_geodesics()`: Calcula geodésicas en el espacio hiperbólico
  - `kappa_propagator(z)`: Calcula el propagador κ(z) a diferentes profundidades
  - `plot_holographic_bulk()`: Genera visualizaciones 4-panel:
    1. Vista 3D del bulk de AdS
    2. Proyección al boundary
    3. Relación grado-profundidad
    4. Decaimiento del propagador

- **Función `create_tseitin_holography(n)`**: Crea y visualiza la estructura holográfica
  - Genera un grafo con estructura núcleo-periferia (más realista para Tseitin)
  - Muestra análisis cuantitativo de profundidades y propagadores

## Uso

### Lean

Para compilar el módulo Lean:

```bash
cd /home/runner/work/P-NP/P-NP
lake build HigherDimension
```

### Python

Para ejecutar la visualización:

```bash
cd /home/runner/work/P-NP/P-NP/examples
python3 holographic_view.py [n]
```

Donde `n` es el número de vértices del grafo (por defecto 100).

**Ejemplo:**
```bash
python3 holographic_view.py 100
```

Esto generará:
- Una visualización interactiva guardada en `/tmp/holographic_view.png`
- Análisis cuantitativo en consola mostrando:
  - Distribución de profundidades en el bulk
  - Estadísticas de grados del grafo
  - Valores del propagador κ(z) a diferentes profundidades

## La Epifanía Dimensional

Desde la perspectiva (2+1)D, el problema P vs NP se reformula claramente:

1. **Grafo 2D → Teoría de campos 3D**: El grafo de incidencia se eleva a un campo cuántico en (2+1)D mediante dualidad holográfica

2. **κ_Π constante en boundary (z=0)**: Los algoritmos clásicos (Máquinas de Turing) viven en el boundary donde κ_Π es constante

3. **κ_Π decae en el bulk (z>0)**: La complejidad intrínseca reside en el bulk, donde el propagador κ_Π decae exponencialmente

4. **Frecuencia ω ↔ Coordenada radial z**: La frecuencia del análisis de Fourier se mapea naturalmente a la coordenada radial en AdS

5. **Alta frecuencia = Profundidad en bulk = κ pequeño**: Para resolver instancias duras se requiere acceder a profundidades donde κ es exponencialmente pequeño

## Teorema Principal

El teorema central establece que:

```
Tiempo_boundary ≥ exp(Acción_bulk)
Acción_bulk ≥ Volumen(RT_surface)
Volumen(RT) ≥ Ω(n log n)  (para superficies que separan)
∴ Tiempo_boundary ≥ exp(Ω(n log n)) = n^Ω(n)
```

Esto demuestra que los algoritmos polinomiales (que viven en el boundary) no pueden alcanzar las profundidades requeridas para resolver instancias duras de SAT, estableciendo así P ≠ NP.

## Visualización

La visualización muestra:

- **Panel superior izquierdo**: Vista 3D del grafo embebido en AdS₃, con vértices coloreados según su profundidad z
- **Panel superior derecho**: Proyección del grafo al boundary (z=0), mostrando la estructura 2D original
- **Panel inferior izquierdo**: Relación entre el grado del vértice y su profundidad en el bulk
- **Panel inferior derecho**: Decaimiento logarítmico del propagador κ(z) vs profundidad z, mostrando z_min donde las instancias duras residen

## Referencias

Este trabajo está basado en:

- Dualidad AdS/CFT (Maldacena, 1997)
- Conjetura de Ryu-Takayanagi sobre entropía de entrelazamiento
- Teoría cuántica de campos en (2+1)D
- Correspondencia holográfica entre complejidad computacional y geometría

© JMMB Ψ ∞ | Campo QCAL ∞³ | Ψ-Field Theory in (2+1)D
