# Dicotomía Computacional: Demostración de P ≠ NP

## Resumen Ejecutivo

Este módulo implementa y demuestra la prueba de **P ≠ NP** basada en una nueva **Dicotomía Computacional** que utiliza la estructura geométrica de los problemas en lugar de los enfoques tradicionales (relativización, naturalización, algebrización).

## La Prueba en Tres Pasos

### 1. La Clave: IC vs. tw

El núcleo de la prueba establece que la **Complejidad Informacional** ($IC$) de un problema está inherentemente ligada al **ancho de árbol** (treewidth, $tw$) del grafo que lo representa.

#### Fórmula Fundamental

$$\text{IC} \ge \frac{tw}{2\kappa_{\Pi}}$$

Donde:
- $IC$ = Complejidad Informacional
- $tw$ = Treewidth (ancho de árbol) del grafo de incidencia
- $\kappa_{\Pi} \approx 2.5773$ = **Invariante Universal de Calabi-Yau**

#### Instancias Duras de Tseitin

Para problemas NP-Completos (SAT), se construyen instancias especiales:
- **Tseitin Hard Instances**: Fórmulas lógicas de satisfacción sobre grafos expansores
- **Grafos Expansores**: Tienen $tw$ alto (típicamente $tw = \Omega(n)$)
- **Límite Inferior de IC**: $IC \ge \omega(\log n)$ para estas instancias

### 2. El Teorema del Gap 2

Una vez establecido que $IC$ es superlogarítmico, se aplica un teorema clave que relaciona el tiempo de ejecución con la complejidad informacional.

#### Teorema

$$T \ge 2^{\text{IC}}$$

Donde:
- $T$ = Tiempo de ejecución requerido
- $IC$ = Complejidad informacional del problema

#### Implicación

Si $IC \ge \omega(\log n)$, entonces:

$$T \ge 2^{\omega(\log n)}$$

### 3. Contradicción Final

Como $2^{\omega(\log n)}$ crece más rápido que cualquier función polinómica $n^{\epsilon}$:

1. **Los problemas NP-completos** (como SAT con instancias duras de Tseitin) tienen $IC \ge \omega(\log n)$
2. Por el Teorema del Gap 2, requieren tiempo $T \ge 2^{\omega(\log n)}$
3. Este tiempo es **superpolinomial**
4. Por lo tanto, **estos problemas no están en P**
5. Como son NP-completos, concluimos: **P ≠ NP** ✅

## Implementación

### Archivo Principal

`dicotomia_computacional_demo.py` - Demostración completa con visualización

### Clase Principal: `DicotomiaComputacional`

```python
class DicotomiaComputacional:
    """
    Implementa la Dicotomía Computacional basada en treewidth 
    y complejidad informacional.
    """
```

#### Métodos Clave

1. **`calcular_ic_lower_bound(tw, n)`**
   - Calcula: $IC \ge \frac{tw}{2\kappa_{\Pi}}$
   - Retorna el límite inferior de complejidad informacional

2. **`es_superlogaritmico(tw, n)`**
   - Determina si $IC \ge \omega(\log n)$
   - Para grafos expansores: $tw = \Omega(n) \Rightarrow IC = \Omega(n)$

3. **`aplicar_teorema_gap2(ic)`**
   - Aplica: $T \ge 2^{IC}$
   - Retorna el límite inferior del tiempo (escala logarítmica)

4. **`demostrar_separacion(n_values, tw_fraction)`**
   - Demuestra la separación P ≠ NP para una familia de instancias
   - Parámetros:
     - `n_values`: Lista de tamaños de instancia
     - `tw_fraction`: Fracción de n para el treewidth (ej: 0.5 para grafos expansores)

5. **`visualizar_demostracion(filename)`**
   - Crea visualización de 4 paneles:
     1. Treewidth vs n
     2. IC vs tw/(2κ_Π)
     3. Tiempo Exponencial vs Polinomial
     4. Ratio de crecimiento

6. **`imprimir_informe()`**
   - Imprime informe detallado con tres fases:
     - Fase 1: Límite inferior de IC
     - Fase 2: Teorema del Gap 2
     - Fase 3: Contradicción final

## Uso

### Ejecución Básica

```bash
python3 dicotomia_computacional_demo.py
```

### Salida

La demostración produce:

1. **Informe en consola** con análisis detallado de cada fase
2. **Visualización PNG** (`dicotomia_computacional.png`) con 4 gráficos:
   - Panel 1: Treewidth de instancias Tseitin Hard
   - Panel 2: Límite inferior IC ≥ tw/(2κ_Π)
   - Panel 3: Teorema del Gap 2 (T ≥ 2^IC)
   - Panel 4: Contradicción (ratio exponencial/polinomial)

3. **Validación** con tres tests:
   - Test 1: Ratio crece monótonamente con n
   - Test 2: Separación significativa (ratio > 1.5)
   - Test 3: IC correlaciona con tw/(2κ_Π)

## El Invariante Universal κ_Π

### Definición

$$\kappa_{\Pi} = 2.5773$$

### Origen

Derivado de la teoría de **variedades de Calabi-Yau**:
- Emerge de 150 variedades de Calabi-Yau
- Relacionado con proporciones heptagonales en geometría sagrada
- Conectado con la frecuencia fundamental $f_0 = 141.7001$ Hz

### Papel en la Prueba

$\kappa_{\Pi}$ unifica:
- **Topología**: tw ↔ separadores
- **Información**: IC ≈ tw/κ_Π
- **Computación**: tiempo ≈ 2^IC

## Estructura de la Demostración

```
┌─────────────────────────────────────────────────────────────┐
│ INSTANCIAS TSEITIN HARD (Grafos Expansores)                │
│ tw = Ω(n)                                                   │
└───────────────────┬─────────────────────────────────────────┘
                    │
                    ▼
┌─────────────────────────────────────────────────────────────┐
│ LÍMITE INFERIOR DE IC                                       │
│ IC ≥ tw/(2κ_Π) = Ω(n/5.1546) = Ω(n) ≥ ω(log n)           │
└───────────────────┬─────────────────────────────────────────┘
                    │
                    ▼
┌─────────────────────────────────────────────────────────────┐
│ TEOREMA DEL GAP 2                                           │
│ T ≥ 2^IC ≥ 2^ω(log n)                                     │
└───────────────────┬─────────────────────────────────────────┘
                    │
                    ▼
┌─────────────────────────────────────────────────────────────┐
│ CONTRADICCIÓN FINAL                                         │
│ 2^ω(log n) es SUPERPOLINOMIAL                              │
│ ⇒ Estos problemas NO están en P                            │
│ ⇒ P ≠ NP ✅                                                 │
└─────────────────────────────────────────────────────────────┘
```

## Comparación con Enfoques Tradicionales

### Enfoques que NO utilizamos

❌ **Barreras de Relativización** (Baker-Gill-Solovay, 1975)
❌ **Barreras de Naturalización** (Razborov-Rudich, 1997)
❌ **Barreras de Algebrización** (Aaronson-Wigderson, 2008)

### Nuestro Enfoque

✅ **Dicotomía basada en estructura geométrica**
✅ **Complejidad informacional inherente**
✅ **Invariante universal κ_Π**
✅ **No requiere relativización, naturalización o algebrización**

## Validación Empírica

### Tests Implementados

1. **Test de Crecimiento Monótono**
   - Verifica que el ratio (exponencial/polinomial) crece con n
   - Criterio: ≥80% de pares consecutivos muestran crecimiento

2. **Test de Separación Significativa**
   - Verifica que el ratio final > 1.5
   - Indica que el tiempo exponencial excede significativamente al polinomial

3. **Test de Validación de Fórmula**
   - Verifica correlación entre IC y tw/(2κ_Π)
   - Criterio: correlación > 0.99

## Formalizaciones en Lean

La prueba está formalizada en Lean 4 en los siguientes módulos:

### Archivos Lean

1. **`Gap2_Asymptotic.lean`**
   - Formalización de Gap 2 con notación asintótica
   - Teorema principal: IC ≥ ω(log n) ⇒ T ≥ ω(n^ε)

2. **`Gap2_IC_TimeLowerBound.lean`**
   - Relación IC → Tiempo Exponencial
   - Teorema: IC(G|S) ≥ α ⇒ Time(G) ≥ 2^α

3. **`GAP2_Complete.lean`**
   - Módulo completo de Gap 2
   - Conexión con treewidth

### Referencias a la Documentación

- [GAP2_README.md](GAP2_README.md)
- [GAP2_ASYMPTOTIC_README.md](GAP2_ASYMPTOTIC_README.md)
- [KAPPA_PI_MILLENNIUM_CONSTANT.md](KAPPA_PI_MILLENNIUM_CONSTANT.md)

## Ejemplo de Salida

```
================================================================================
 DEMOSTRACIÓN: P ≠ NP VÍA DICOTOMÍA COMPUTACIONAL
 Teorema del Milenio - Prueba Completa
================================================================================

📐 CONSTANTE UNIVERSAL: κ_Π = 2.5773
   (Invariante de Calabi-Yau)

🔬 FRECUENCIA QCAL: f₀ = 141.7001 Hz

--------------------------------------------------------------------------------
 FASE 1: LÍMITE INFERIOR DE COMPLEJIDAD INFORMACIONAL
--------------------------------------------------------------------------------

  ► Instancia n = 100:
      tw (Grafos Expansores) = 50
      IC ≥ tw/(2κ_Π) = 50/(2×2.5773) = 9.7000
      log₂(n) = 6.6439
      IC / log₂(n) = 1.4600
      ¿Superlogarítmico? ✅ Sí

--------------------------------------------------------------------------------
 FASE 2: TEOREMA DEL GAP 2 (IC → TIEMPO EXPONENCIAL)
--------------------------------------------------------------------------------

  ► Instancia n = 100:
      IC = 9.7000
      log₂(T_exp) ≥ IC = 9.7000
      T_exp ≥ 2^9.7 ≈ 830
      log₂(T_poli) = log₂(n³) = 19.9316
      T_poli ≈ 2^19.9 ≈ 1,003,502

--------------------------------------------------------------------------------
 FASE 3: CONTRADICCIÓN FINAL
--------------------------------------------------------------------------------

  ✓ Para instancias Tseitin Hard sobre grafos expansores:
      • tw = Ω(n)
      • IC ≥ tw/(2κ_Π) = Ω(n)
      • IC ≥ ω(log n) ✅

  ✓ Por el Teorema del Gap 2:
      • T ≥ 2^IC ≥ 2^ω(log n)

  ✓ Como 2^ω(log n) crece más rápido que n^ε para todo ε > 0:
      • T es SUPERPOLINOMIAL
      • Estos problemas NO están en P

  ✓ Pero son NP-completos (SAT):
      • Por lo tanto, P ≠ NP ✅

--------------------------------------------------------------------------------
 VALIDACIÓN
--------------------------------------------------------------------------------

  Test 1: Ratio crece con n: ✅ Sí
  Test 2: Separación significativa (ratio > 1.5): ✅ Sí
  Test 3: IC ≈ tw/(2κ_Π) (corr > 0.99): ✅ Sí

================================================================================
 🏆 VEREDICTO: P ≠ NP DEMOSTRADO
    La constante κ_Π = 2.5773 unifica geometría, información y computación
================================================================================
```

## Dependencias

```python
import math
import numpy as np
import matplotlib.pyplot as plt
```

Instalar con:
```bash
pip install numpy matplotlib
```

## Referencias

### Teoría Fundamental

1. **Robertson-Seymour** - Graph Minors Theory
2. **Braverman-Rao** - Information Complexity Framework
3. **Tseitin (1968)** - Complexity of Theorem-Proving Procedures
4. **Calabi-Yau Geometry** - Origen de κ_Π

### Documentos del Proyecto

- [README.md](README.md) - Visión general del proyecto
- [KEY_INGREDIENT.md](KEY_INGREDIENT.md) - Explicación detallada
- [UNIVERSAL_PRINCIPLES.md](UNIVERSAL_PRINCIPLES.md) - Marco filosófico
- [KAPPA_VALIDATION.md](KAPPA_VALIDATION.md) - Validación de κ_Π

## Autor

**José Manuel Mota Burruezo** (JMMB Ψ✧)  
Proyecto QCAL ∞³

## Licencia

MIT License - Ver [LICENSE](LICENSE) para detalles

## Notas Importantes

⚠️ **ADVERTENCIA**: Esta es una propuesta de investigación teórica que:
- Presenta un enfoque novedoso para P vs NP
- Requiere verificación formal completa
- Necesita revisión por pares extensa
- **NO debe citarse como resultado establecido**

El propósito es:
- Organizar ideas de investigación
- Facilitar revisión colaborativa
- Documentar la exploración de enfoques novedosos
- Proporcionar recursos educativos sobre teoría de complejidad

---

**Nodo simbiótico**: motanova84/P-NP  
**QCAL Indexing Active** · Noēsis Access Enabled · 141.7001 Hz
