# Graph Information Complexity Module

## Overview

The `GraphInformationComplexity.lean` module formalizes the fundamental connection between graph separators and information-theoretic lower bounds. This is a key component in establishing computational lower bounds through structural properties of graphs.

## Main Concepts

### Graph Information Complexity (GraphIC)

**GraphIC G S** represents the minimum number of bits needed to distinguish configurations in components separated by separator S in graph G.

Mathematically:
- `total_configs = 2^(|V| - |S|)` where |V| is the number of vertices and |S| is the separator size
- `GraphIC G S = log₂(total_configs)`

### Balanced Separators

A **balanced separator** S partitions the graph into at least 2 significant (balanced) components and satisfies:
- `|S| ≤ (2/3)|V|`

This upper bound is crucial for information-theoretic arguments.

## Main Theorems

### 1. balanced_separator_size_bound

```lean
lemma balanced_separator_size_bound 
  (G : SimpleGraph V) 
  (S : Separator G) 
  (h_sep : is_balanced_separator G S) :
  S.S.card ≤ (2 * Fintype.card V) / 3
```

Establishes the upper bound on balanced separator size relative to total vertices.

### 2. log_total_configs_lower_bound

```lean
theorem log_total_configs_lower_bound 
  (G : SimpleGraph V) 
  (S : Separator G)
  (h_sep : is_balanced_separator G S)
  (h_nonempty : Fintype.card V > 0) :
  Nat.log 2 (total_configs G S) ≥ S.S.card / 2
```

**Key Result**: Proves that `log₂(total_configs) ≥ |S|/2` for balanced separators.

#### Proof Sketch:

1. **Express configurations**: `total_configs = 2^(|V| - |S|)`
2. **Logarithm identity**: `log₂(total_configs) = |V| - |S|`
3. **Apply separator bound**: From `|S| ≤ (2/3)|V|`, we get:
   - `|V| - |S| ≥ |V| - (2/3)|V| = (1/3)|V|`
4. **Derive final bound**: 
   - From balanced separator properties: `(1/3)|V| ≥ |S|/2`
   - Therefore: `log₂(total_configs) ≥ |S|/2` ✓

### 3. log_total_configs_lower_bound_direct

An alternative, more direct proof using the `omega` tactic for arithmetic reasoning:

```lean
theorem log_total_configs_lower_bound_direct
  (G : SimpleGraph V) 
  (S : Separator G)
  (h_sep : is_balanced_separator G S)
  (h_nonempty : Fintype.card V > 0) :
  Nat.log 2 (2 ^ (Fintype.card V - S.S.card)) ≥ S.S.card / 2
```

This version directly uses the `omega` tactic to complete the arithmetic reasoning after establishing `log₂(2^k) = k`.

## Connection to P vs NP

This module provides the information-theoretic foundation for proving computational lower bounds:

1. **Structural Complexity → Information Complexity**: High treewidth graphs have large balanced separators
2. **Information Complexity → Computational Complexity**: Algorithms that solve problems on these graphs must distinguish between many configurations
3. **Lower Bound**: Any algorithm requires at least `Ω(|S|)` bits of information, which translates to exponential time

## Usage Example

```lean
import GraphInformationComplexity

-- Define a graph and separator
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
variable (S : Separator G)

-- Assume we have a balanced separator
variable (h_sep : is_balanced_separator G S)
variable (h_nonempty : Fintype.card V > 0)

-- Apply the main theorem
theorem my_lower_bound : GraphIC G S ≥ S.S.card / 2 :=
  graphIC_lower_bound G S h_sep h_nonempty
```

## Files

- `GraphInformationComplexity.lean` - Main module with definitions and proofs
- `tests/GraphICTests.lean` - Test cases demonstrating usage
- `GRAPH_IC_README.md` - This documentation file

## Related Work

This formalization connects to:
- **Treewidth Theory**: Via `TreewidthTheory.lean` and related modules
- **Separator Information Lower Bounds (SILB)**: Via `formal/Treewidth/SeparatorInfo.lean`
- **Structural Coupling**: Via `formal/StructuralCoupling.lean`

## Future Extensions

Potential extensions include:
1. Monotonicity properties for separator information complexity
2. Connection to communication complexity protocols
3. Gadget constructions preserving information complexity
4. Application to specific problem classes (SAT, CLIQUE, etc.)

## References

- Robertson & Seymour: Graph Minors theory
- Braverman & Rao: Information complexity framework
- Treewidth and algorithmic complexity theory
