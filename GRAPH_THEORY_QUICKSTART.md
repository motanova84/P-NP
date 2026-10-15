# GraphTheory Module - Quick Start Guide

This guide helps you get started with the GraphTheory module for edge expansion analysis and small Ramanujan graphs.

## What's Included

### Core Definitions

1. **Edge Boundary** - Edges crossing a vertex set boundary
2. **Edge Expansion** - Ratio of boundary size to set size  
3. **Cheeger Constant** - Minimum expansion over balanced cuts
4. **Cycle Graphs** - Standard n-vertex cycle construction
5. **Petersen Graph** - Classic 3-regular Ramanujan graph

## Quick Examples

### Example 1: Computing Edge Expansion

```lean
import GraphTheory
open SimpleGraph

-- Define a graph and a vertex set
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (S : Finset V)

-- The edge expansion is always non-negative
example : 0 ≤ G.edgeExpansion S := by
  apply edgeExpansion_nonneg
```

### Example 2: Using the Petersen Graph

```lean
-- The Petersen graph is 3-regular (every vertex has degree 3)
-- This has been computationally verified (see verify_petersen_graph.py)

#check petersenGraph  -- SimpleGraph (Fin 10)

-- Properties (to be proven):
-- - 3-regular: ∀ v, petersenGraph.degree v = 3
-- - Diameter 2
-- - Ramanujan graph (optimal spectral gap)
```

### Example 3: Cycle Graphs

```lean
-- Define a 5-cycle
def C5 := cycleGraph 5 (by norm_num : 3 ≤ 5)

-- Properties (to be proven):
-- - 2-regular: ∀ v, (cycleGraph n hn).degree v = 2
-- - Treewidth 2 for n ≥ 3
```

## Key Theorems

### Theorem 1: Edge Boundary Bounds

```lean
theorem edgeBoundary_card_le_sum_degrees :
    (G.edgeBoundary S).card ≤ ∑ v in S, G.degree v
```

**Interpretation:** The number of edges leaving a set S is bounded by the sum of degrees of vertices in S.

### Theorem 2: Edge Expansion Bound

```lean
lemma edgeExpansion_bounded_by_avg_degree (hS : S.Nonempty) :
    G.edgeExpansion S ≤ (∑ v in S, G.degree v : ℝ) / S.card
```

**Interpretation:** Edge expansion is bounded by the average degree of vertices in the set.

## Verification

We've included Python scripts to verify our implementations:

### Verify Petersen Graph

```bash
python3 verify_petersen_graph.py
```

**Checks:**
- ✓ 3-regularity (all vertices have degree 3)
- ✓ Symmetry of adjacency
- ✓ No self-loops
- ✓ Correct edge count (15 edges)
- ✓ Diameter = 2

### Verify Cycle Graphs

```bash
python3 verify_cycle_graph.py
```

**Checks for C₃, C₄, C₅, C₆, C₁₀, C₂₀:**
- ✓ 2-regularity
- ✓ Connectivity
- ✓ Correct edge count
- ✓ Correct diameter

## File Structure

```
P-NP/
├── GraphTheory.lean                    # Main module
├── examples/
│   └── GraphTheoryExamples.lean       # Usage examples
├── GRAPH_THEORY_IMPLEMENTATION.md     # Detailed documentation
├── GRAPH_THEORY_QUICKSTART.md         # This file
├── verify_petersen_graph.py           # Verification script
└── verify_cycle_graph.py              # Verification script
```

## Building with Lean

To use this module in your Lean project:

```lean
import GraphTheory
open SimpleGraph
open Finset
open BigOperators
```

**Note:** This module requires Mathlib. Ensure you have:
- Lean 4.20.0 (as specified in lean-toolchain)
- Mathlib v4.20.0

## Next Steps

### For Users

1. **Explore Examples:**
   ```bash
   lean --check examples/GraphTheoryExamples.lean
   ```

2. **Run Verifications:**
   ```bash
   python3 verify_petersen_graph.py
   python3 verify_cycle_graph.py
   ```

3. **Study Documentation:**
   - Read `GRAPH_THEORY_IMPLEMENTATION.md` for theory
   - Check the source code in `GraphTheory.lean` for proofs

### For Contributors

1. **Complete Remaining Proofs:**
   - Prove `petersenGraph_is_3_regular` formally in Lean
   - Prove `cycle_treewidth_two` (requires tree decomposition)
   - Add Cheeger's inequality (relating to spectral gap)

2. **Add More Examples:**
   - Implement other small Ramanujan graphs
   - Add complete graphs, bipartite graphs
   - Demonstrate expansion properties

3. **Contribute to Mathlib:**
   - Submit edge boundary/expansion definitions
   - Submit Cheeger constant theory
   - Submit small graph examples

## Connection to P vs NP

This module supports the computational dichotomy theorem:

**High Expansion → High Treewidth → Hard SAT Instances**

- Expander graphs have large Cheeger constant
- Tseitin formulas over expanders have high treewidth  
- High treewidth forces exponential communication complexity
- Ramanujan graphs are optimal expanders

## References

1. **Edge Expansion:**
   - Alon & Milman (1985) - λ₁ and isoperimetric inequalities

2. **Ramanujan Graphs:**
   - Lubotzky, Phillips & Sarnak (1988) - Ramanujan graphs
   - Hoory, Linial & Wigderson (2006) - Expander applications

3. **Petersen Graph:**
   - Holton & Sheehan (1993) - The Petersen Graph

## Support

For questions or issues:
- Check `GRAPH_THEORY_IMPLEMENTATION.md` for detailed documentation
- Review examples in `examples/GraphTheoryExamples.lean`
- Run verification scripts to check implementations

## License

MIT License - See project root for details

---

**Author:** José Manuel Mota Burruezo & Implementation Team  
**Last Updated:** 2026-01-31
