# Treewidth Module

This directory contains the formal Lean 4 implementation of treewidth theory for graphs.

## Files

### Treewidth.lean (283 lines)
Complete formalization of tree decompositions and treewidth with proven theorems.

**Main Definitions:**
- `TreeDecomposition G`: Structure representing a tree decomposition of graph G
- `width D`: The width of a tree decomposition (max bag size - 1)
- `treewidth G`: The treewidth of graph G (minimum width over all decompositions)

**Proven Theorems (without sorry):**
- `complete_has_decomposition`: Constructs a tree decomposition for complete graphs
- `treewidth_clique`: **tw(Kₙ) = n - 1** for complete graphs on n vertices
- `tree_has_simple_decomposition`: Constructs a tree decomposition for trees with width ≤ 1
- `treewidth_le_one_of_tree`: **tw(tree) ≤ 1** for any tree graph

**Theorems with documented sorries:**
- `tree_of_treewidth_one`: Reverse direction requiring deep graph theory
- `treewidth_eq_one_iff_tree`: Full characterization (forward direction proven)

### SeparatorInfo.lean (72 lines)
Separator Information Lower Bound (SILB) lemma connecting treewidth to information complexity.

**Main Results:**
- `separator_information_lower_bound`: High treewidth forces high information complexity
- `high_treewidth_exponential_communication`: Corollary for exponential bounds

## Usage

Import the module in your Lean 4 code:

```lean
import Treewidth.Treewidth
import Treewidth.SeparatorInfo

open Treewidth

-- Use the definitions and theorems
theorem my_theorem {V : Type*} [Fintype V] [DecidableEq V] [Inhabited V]
  (G : SimpleGraph V) (n : ℕ) (h : Fintype.card V = n) :
  treewidth (completeGraph : SimpleGraph V) = n - 1 :=
  treewidth_clique n h (by omega)
```

## Theoretical Background

Treewidth is a fundamental graph parameter that measures how "tree-like" a graph is:
- Trees have treewidth 1
- Complete graphs Kₙ have treewidth n - 1
- Low treewidth enables efficient algorithms
- High treewidth indicates structural complexity

### Tree Decompositions

A tree decomposition of a graph G = (V, E) consists of:
1. A tree T
2. A bag Xᵢ ⊆ V for each node i of T

Satisfying:
1. **Coverage**: Every vertex v ∈ V appears in at least one bag
2. **Edge Coverage**: For each edge (u,v) ∈ E, there exists a bag containing both u and v
3. **Connected Subtree**: For each vertex v, the set of bags containing v induces a connected subtree of T

The **width** of a decomposition is max{|Xᵢ| - 1 : i ∈ T}.
The **treewidth** of G is the minimum width over all tree decompositions of G.

## Implementation Notes

This implementation uses axiomatized `SimpleGraph` types for compatibility across different parts of the codebase. The axioms mirror the structure of Mathlib's SimpleGraph but provide flexibility for integration with other modules.

## Future Work

Remaining sorries require formalization of:
1. Cycle detection from treewidth constraints
2. Connectivity propagation in tree decompositions
3. Structural properties of graph minors
4. Complete characterization of treewidth-1 graphs

These are deep graph-theoretic results that require substantial additional formalization effort beyond the core definitions and main theorems.

## References

- Robertson, N., & Seymour, P. D. (1984). Graph minors. III. Planar tree-width.
- Bodlaender, H. L. (1996). A linear-time algorithm for finding tree-decompositions of small treewidth.
- Cygan, M., et al. (2015). Parameterized Algorithms. Chapter on treewidth.

## Integration

This module is imported by `FormalVerification.lean` and provides the foundation for:
- Complexity analysis via treewidth bounds
- Connection to information complexity (SeparatorInfo.lean)
- SAT hardness characterization (TreewidthTheory.lean)
