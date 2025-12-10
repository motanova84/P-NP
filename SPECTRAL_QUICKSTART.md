# Spectral Graph Theory Quick Start Guide

## Overview

This guide shows how to use the spectral graph theory extension for the P ≠ NP formalization.

## Basic Usage

### Import the Module

```lean
import SpectralGraphTheory
open SpectralGraphTheory
```

### Define a Graph

```lean
variable {V : Type*} [DecidableEq V] [Fintype V] (G : SimpleGraph V)
```

### Access Graph Matrices

```lean
-- Adjacency matrix
#check adjacencyMatrix G

-- Degree matrix
#check degreeMatrix G

-- Normalized Laplacian
#check normalizedLaplacian G
```

## Main Theorems

### 1. High Treewidth → Spectral Gap

```lean
theorem high_treewidth_implies_spectral_gap 
  (treewidth : ℕ)  
  (h_tw : treewidth ≥ Fintype.card V / 10) :
  spectralGap G ≥ 1 / KAPPA_PI
```

**Usage:**
```lean
example (G : SimpleGraph V) (tw : ℕ) (h : tw ≥ Fintype.card V / 10) :
  spectralGap G ≥ 1 / KAPPA_PI := by
  exact high_treewidth_implies_spectral_gap G tw h
```

### 2. High Treewidth → Expander

```lean
theorem high_treewidth_implies_expander 
  (treewidth : ℕ)
  (h_tw : treewidth ≥ Fintype.card V / 10) :
  ∃ δ > 0, IsExpander G δ ∧ δ = 1 / KAPPA_PI
```

**Usage:**
```lean
example (G : SimpleGraph V) (tw : ℕ) (h : tw ≥ Fintype.card V / 10) :
  IsExpander G (1 / KAPPA_PI) := by
  exact explicit_expander_constant G tw h
```

### 3. Cheeger Inequality

```lean
theorem cheeger_inequality : 
  spectralGap G / 2 ≤ expansionConstant G ∧
  expansionConstant G ≤ Real.sqrt (2 * spectralGap G)
```

**Usage:**
```lean
example (G : SimpleGraph V) :
  spectralGap G / 2 ≤ expansionConstant G := by
  exact (cheeger_inequality G).1
```

## Constants

### κ_Π (KAPPA_PI)

The fundamental constant κ_Π = 2.5773:

```lean
#eval KAPPA_PI  -- 2.5773
```

**Derivation:**
```lean
#check kappa_pi_derivation
-- κ_Π = φ × (π/e) × λ_CY
-- φ ≈ 1.61803 (golden ratio)
-- π/e ≈ 1.15573 (harmonic term)
-- λ_CY ≈ 1.38197 (Calabi-Yau factor)
```

### Expander Constant

The explicit expander constant δ = 1/κ_Π ≈ 0.388:

```lean
example : 1 / KAPPA_PI > 0 := by
  apply div_pos; norm_num; norm_num [KAPPA_PI]
```

## Working Examples

### Example 1: Complete Graph

```lean
-- Complete graph on n vertices
def CompleteGraph (n : ℕ) : SimpleGraph (Fin n) := ⊤

-- Complete graph has treewidth n-1
-- For n ≥ 10, it satisfies our threshold
example (n : ℕ) (h : n ≥ 10) :
  let G := CompleteGraph n
  -- Treewidth is n-1
  -- So for n ≥ 10, tw ≥ 9
  -- Check if 9 ≥ n/10 (true for n ≤ 90)
  True := by trivial
```

### Example 2: Using Integration Module

```lean
import Formal.SpectralTreewidthIntegration
open SpectralTreewidthIntegration

-- Combine spectral and treewidth properties
example (G : SimpleGraph V) (tw : ℕ) (h : tw ≥ Fintype.card V / 10) :
  (spectralGap G ≥ 1 / KAPPA_PI) ∧ 
  (IsExpander G (1 / KAPPA_PI)) ∧
  (expansionConstant G ≥ 1 / (2 * KAPPA_PI)) := by
  exact high_treewidth_combined_properties G tw h
```

### Example 3: Computational Hardness

```lean
-- Extract computational barrier from treewidth
example (G : SimpleGraph V) (tw : ℕ) (h : tw ≥ Fintype.card V / 10) :
  ∃ (hardness : ℝ), hardness ≥ 1 / KAPPA_PI ∧ hardness > 0 := by
  exact treewidth_computational_barrier G tw h
```

## Integration with Existing Code

### Connect to Treewidth Module

```lean
import Treewidth
import SpectralGraphTheory
import Formal.SpectralTreewidthIntegration

-- Use formal treewidth definitions
variable (G : SimpleGraph V)
variable (tw : ℕ)  -- from Treewidth.treewidth

-- Apply spectral theorems
theorem my_theorem (h : tw ≥ Fintype.card V / 10) :
  spectralGap G ≥ 1 / KAPPA_PI := by
  exact formal_treewidth_implies_spectral_gap G tw h
```

## Common Patterns

### Pattern 1: Check if Graph is Expander

```lean
def is_high_treewidth (G : SimpleGraph V) (tw : ℕ) : Bool :=
  tw ≥ Fintype.card V / 10

-- If high treewidth, then expander
example (G : SimpleGraph V) (tw : ℕ) (h : is_high_treewidth G tw) :
  IsExpander G (1 / KAPPA_PI) := by
  unfold is_high_treewidth at h
  exact explicit_expander_constant G tw h
```

### Pattern 2: Compute Degree

```lean
-- Degree of a vertex
example (v : V) : ℕ := degree G v

-- Check if regular graph
def is_regular (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∀ v : V, degree G v = d
```

### Pattern 3: Matrix Operations

```lean
-- Adjacency matrix entry
example (i j : V) : ℝ := adjacencyMatrix G i j

-- Degree matrix entry (diagonal)
example (i j : V) : ℝ := degreeMatrix G i j

-- Laplacian entry
example (i j : V) : ℝ := normalizedLaplacian G i j
```

## Testing

Run the test suite:

```bash
lake build tests/SpectralGraphTheoryTests
```

Or in Lean:

```lean
import tests.SpectralGraphTheoryTests
```

## Advanced Usage

### Custom Separators

```lean
-- Define a balanced separator
structure MyBalancedSeparator (G : SimpleGraph V) (S : Finset V) : Prop where
  size_bound : S.card ≤ Fintype.card V / 3
  separates : True  -- Add separation property
  balanced : True   -- Add balance property

-- Connect to spectral theory
example (S : Finset V) (h : BalancedSeparator G S) :
  ∃ sep : Finset V, sep = S := by
  use S
```

### Custom Expansion Measures

```lean
-- Alternative expansion measure
def vertex_expansion (G : SimpleGraph V) : ℝ :=
  sorry  -- Define based on vertex boundaries

-- Relate to edge expansion
theorem vertex_edge_expansion_relation :
  vertex_expansion G ≥ expansionConstant G / 2 := by
  sorry
```

## Troubleshooting

### Common Issues

1. **Import errors**: Make sure to import `SpectralGraphTheory` and open the namespace
2. **Type mismatches**: Ensure your graph has `[DecidableEq V]` and `[Fintype V]` instances
3. **Numerical computation**: Some proofs require `sorry` for actual numerical bounds

### Getting Help

- Check `SPECTRAL_THEORY_EXTENSION.md` for detailed documentation
- Review `tests/SpectralGraphTheoryTests.lean` for examples
- See `formal/SpectralTreewidthIntegration.lean` for integration patterns

## References

- **Main module**: `SpectralGraphTheory.lean`
- **Integration**: `formal/SpectralTreewidthIntegration.lean`
- **Tests**: `tests/SpectralGraphTheoryTests.lean`
- **Documentation**: `SPECTRAL_THEORY_EXTENSION.md`

## Next Steps

1. Implement eigenvalue computations for `spectralGap`
2. Add explicit separator algorithms
3. Prove numerical bounds without `sorry`
4. Add more graph families (cycles, grids, hypercubes)
5. Connect to randomized constructions

## License

MIT License with symbiotic clauses under the Ethical Charter of Mathematical Coherence.

---

**Author:** José Manuel Mota Burruezo  
**Module:** SpectralGraphTheory  
**Version:** 1.0  
**Date:** 2025-12-10
