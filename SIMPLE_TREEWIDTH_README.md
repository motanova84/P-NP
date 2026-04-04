# Simple Treewidth - Building Real Theorems Incrementally

## Overview

This module demonstrates the correct approach to formalizing mathematics in Lean4:
1. **Start simple** - Begin with trivial but complete proofs
2. **Use real Mathlib** - Check what actually exists before using it
3. **Build gradually** - Layer complexity incrementally
4. **No sorry** - Aim for complete proofs in core theorems

## Problem Statement

The original problem highlighted common mistakes:
- Writing huge theorems with `sorry`
- Assuming Mathlib definitions exist (e.g., `SimpleGraph.edgeExpansion`)
- Jumping to complex proofs without foundation

## Solution: SimpleTreewidth.lean

### Step 1: Simple Starting Points

```lean
lemma simple_lemma : 2 + 2 = 4 := by norm_num
```

This proves we can actually write proofs that work!

### Step 2: Check What Exists

```lean
#check SimpleGraph.Adj  -- ✓ Exists
-- SimpleGraph.edgeExpansion  -- ✗ Does NOT exist
```

We verified that `SimpleGraph.edgeExpansion` is **not** in Mathlib, so we need to define it ourselves.

### Step 3: Define What's Missing

```lean
def edgeExpansion (G : SimpleGraph V) (S : Finset V) : ℚ :=
  if S.card = 0 then 0
  else (G.edgeBoundary S).card / S.card
```

### Step 4: Prove Simple Properties

```lean
lemma edgeExpansion_nonneg (G : SimpleGraph V) (S : Finset V) : 
    0 ≤ edgeExpansion G S := by
  -- Complete proof without sorry
```

This lemma is **completely proven** - no `sorry`!

### Step 5: Build Toward Real Theorems

The ultimate goal is:

```lean
theorem cycle_treewidth_two (n : ℕ) (hn : n ≥ 3) :
    (cycleGraph n).treewidth = 2
```

Currently simplified, but the infrastructure is in place.

## Complete Proofs (No Sorry)

The following theorems are **completely proven** without `sorry`:

1. `simple_lemma` - Basic arithmetic
2. `three_plus_one` - More basic arithmetic  
3. `edgeExpansion_nonneg` - Edge expansion is non-negative
4. `edgeExpansion_empty` - Empty set has zero expansion
5. `edgeExpansion_singleton` - Singleton expansion is well-defined
6. `nonneg_composition` - Composition of non-negative numbers
7. `pathGraph_edge_count` - Path graph edge counting
8. `finset_card_nonneg` - Finset cardinality is non-negative
9. `edgeExpansion_monotone_in_boundary` - Monotonicity property
10. `cycleGraph_symm` - Cycle graph symmetry
11. `not_adj_self` - No self-loops

## Work in Progress (With Sorry)

These require more infrastructure but have clear paths to completion:

- `cycleGraph_connected` - Requires path construction
- `pathGraph_is_tree` - Requires tree characterization
- `cycle_treewidth_two` - The ultimate goal

## Building Instructions

If Lean 4 is installed:

```bash
lake build SimpleTreewidth
```

To check the file:

```bash
lean SimpleTreewidth.lean
```

## Key Insights

1. **Incremental Development**: Start with what you can prove, build up
2. **Mathlib Reality Check**: Don't assume - verify what exists
3. **Documentation**: Explain what's proven vs. what's aspirational
4. **Quality over Quantity**: One complete proof > ten incomplete ones

## Next Steps

To complete the `cycle_treewidth_two` theorem:

1. Define tree decomposition structure properly
2. Construct explicit decomposition for cycle graph
3. Prove lower bound (requires 2 bags for some vertex)
4. Prove upper bound (explicit decomposition with width 2)
5. Combine for exact characterization

## Integration with Main Project

This module can be imported and used by:
- `Treewidth.lean` - For core treewidth theory
- `GraphInformationComplexity.lean` - For expansion properties
- `SpectralTheory.lean` - For spectral graph theory connections

The definitions (especially `edgeExpansion` and `cycleGraph`) fill gaps in the existing formalization.

## Author

José Manuel Mota Burruezo · JMMB Ψ✧ ∞³

## License

MIT License - Part of the P-NP formalization project
