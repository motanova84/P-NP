# Lean Formalization Directory

This directory contains additional Lean 4 formalization modules for the P-NP computational dichotomy framework.

## Structure

```
lean/
├── README.md              # This file
├── Treewidth.lean        # Graph treewidth definitions
└── InfoComplexity.lean   # Information complexity definitions
```

## Modules

### `Treewidth.lean`

Provides foundational definitions for graph treewidth:

**Key Definitions:**
- `Graph V`: Simple graph structure with vertices and edges
- `TreeDecomposition`: Formal definition of tree decompositions
  - Bags: Sets of vertices at each tree node
  - Coverage properties: vertices and edges
  - Coherence: running intersection property
- `treewidth`: Minimum width over all tree decompositions
- `treewidth_le`: Predicate for bounded treewidth

**Axioms:**
- `path_graph_treewidth`: Path graphs have treewidth ≤ 1
- `complete_graph_treewidth`: Complete graphs have treewidth n-1
- `expander_high_treewidth`: Expander graphs have high treewidth Ω(n)

### `InfoComplexity.lean`

Provides foundational definitions for information complexity:

**Key Definitions:**
- `Protocol`: Communication protocol structure
  - Rounds, communication cost, correctness
- `information_complexity`: IC of a protocol (mutual information)
- `IC_function`: Minimum IC over all protocols computing a function

**Axioms:**
- `IC_lower_bound_CC`: Communication complexity ≥ Information complexity
- `IC_lower_bound_SAT`: For high-treewidth formulas, IC is high
- `IC_treewidth_coupling`: Key connection IC(SAT) ≥ Ω(tw(G_I))
- `IC_monotone`: IC is monotone under reductions
- `IC_direct_product`: IC compounds under direct product

## Integration with Main Formalization

These modules support the main formalization in:
- `../ComputationalDichotomy.lean`: Main dichotomy theorem
- `../Main.lean`: Entry point and verification checks

To use these modules in the main formalization:

```lean
import Treewidth
import InfoComplexity

-- Access definitions
open Treewidth
open InformationComplexity
```

## Building

These modules are part of the main Lean project:

```bash
# Build entire project including these modules
lake build

# Check individual module
lake env lean lean/Treewidth.lean
lake env lean lean/InfoComplexity.lean
```

## Dependencies

- **Mathlib**: The Lean mathematical library
  - `Mathlib.Data.Nat.Basic`: Natural numbers
  - `Mathlib.Data.Finset.Basic`: Finite sets
  - `Mathlib.Data.Real.Basic`: Real numbers
  - `Mathlib.Probability.*`: Probability theory (for IC)

See `../lakefile.lean` for dependency configuration.

## Status

**Current Status**: Axiomatized definitions with proof obligations marked as `sorry`

**Future Work:**
1. Complete proofs of treewidth properties
2. Formalize information complexity measures using Mathlib probability
3. Prove the IC-treewidth coupling theorem rigorously
4. Connect to concrete expander constructions
5. Integrate with Mathlib.Combinatorics.SimpleGraph

## Contributing

To contribute to the Lean formalization:

1. Focus on completing `sorry` placeholders
2. Add lemmas that bridge gaps in reasoning
3. Improve type definitions to be more general
4. Add documentation comments for complex definitions
5. Ensure all proofs compile with `lake build`

See `../CONTRIBUTING.md` for detailed guidelines.

---

**Note**: This formalization is part of a research framework and requires 
rigorous peer review and validation.
