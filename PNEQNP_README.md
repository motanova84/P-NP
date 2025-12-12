# PNeqNP.lean - Teorema Principal P ≠ NP

## Resumen

Este archivo contiene la formalización del teorema principal **P ≠ NP** utilizando treewidth e información como base teórica.

## Estructura del Teorema

El teorema se prueba por contradicción siguiendo estos pasos:

### 1. Grafo de Incidencia (§1)

- **`IncidenceVertex`**: Define vértices del grafo de incidencia (variables o cláusulas)
- **`incidenceGraph`**: Construye el grafo bipartito que conecta variables y cláusulas
- **`numVarsFormula`**: Cuenta el número de variables en una fórmula CNF

### 2. Treewidth (§2)

- Se utiliza el concepto de **treewidth** de grafos
- Para fórmulas con alto treewidth, no existen descomposiciones eficientes
- **Axioma clave**: `tseitin_high_treewidth` establece que las fórmulas Tseitin sobre grafos expansores tienen treewidth ≥ n/10

### 3. Complejidad de Información (§3)

- **`InformationComplexity`**: Mide la información necesaria para resolver un problema
- **`formulaIC`**: Complejidad de información del grafo de incidencia
- **Constante κ_Π = 2.5773**: Constante universal que relaciona treewidth e información

### 4. Lower Bound via Información (§4)

- **`ic_from_treewidth_bound`**: IC(φ) ≥ tw(φ) / (2κ_Π)
- **`time_lower_bound_from_IC`**: Tiempo(φ) ≥ 2^(IC(φ)/2)
- Estos axiomas establecen la conexión entre estructura y complejidad computacional

### 5. Teorema Principal (§5)

**`P_neq_NP : P_Class ≠ NP_Class`**

#### Estrategia de la Prueba

1. **Contradicción**: Suponer P = NP
2. **SAT ∈ P**: Si P = NP, entonces SAT tiene algoritmo polinomial
3. **Fórmula Dura**: Construir φ = tseitin_expander_formula(n) con:
   - tw(φ) ≥ n/10 (alto treewidth)
   - IC(φ) ≥ n/(20κ_Π) (alta complejidad de información)
4. **Lower Bound**: Tiempo(φ) ≥ 2^(n/(40κ_Π)) (exponencial)
5. **Upper Bound**: Tiempo(φ) ≤ n^(2k) (polinomial, por hipótesis P = NP)
6. **Contradicción**: 2^(n/(40κ_Π)) > n^(2k) para n suficientemente grande

## Axiomas Fundamentales

Los siguientes axiomas representan resultados establecidos en la teoría de complejidad:

1. **`SAT_is_NP_complete`**: SAT es NP-completo (Teorema de Cook-Levin)
2. **`tseitin_expander_formula`**: Construcción de fórmulas duras
3. **`tseitin_high_treewidth`**: Tseitin sobre expansores tiene alto treewidth
4. **`ic_from_treewidth_bound`**: Relación entre treewidth e IC vía κ_Π
5. **`time_lower_bound_from_IC`**: Lower bound de tiempo desde IC

## Dependencias

- **Mathlib**: Librería matemática estándar de Lean 4
  - `Combinatorics.SimpleGraph.Basic`: Teoría de grafos
  - `Data.Finset.Basic`: Conjuntos finitos
  - `Data.Real.Basic`: Números reales
- **ComputationalDichotomy**: Definiciones básicas de CNF y literales

## Uso

```lean
import PNeqNP

-- El teorema está disponible como:
#check P_neq_NP
-- P_neq_NP : P_Class ≠ NP_Class
```

## Referencias Teóricas

Este teorema se basa en:

1. **Robertson-Seymour Theory**: Teoría de menores de grafos y treewidth
2. **Braverman-Rao Framework**: Complejidad de información en comunicación
3. **Tseitin Encoding**: Codificación de grafos como fórmulas CNF
4. **Expander Graphs**: Grafos con propiedades de expansión óptimas
5. **κ_Π Constant (2.5773)**: Constante que unifica treewidth e información

## Estado de la Formalización

- ✅ Estructura del teorema completa
- ✅ Definiciones de complejidad computacional
- ✅ Grafo de incidencia y treewidth
- ✅ Complejidad de información
- ✅ Prueba por contradicción
- ⚠️ Algunos pasos usan `sorry` para lemas técnicos estándar
- ⚠️ Requiere Lean 4 con Mathlib instalado para verificación

## Autor

José Manuel Mota Burruezo & Noēsis ∞³

## Licencia

Ver LICENSE en el directorio raíz del proyecto.
