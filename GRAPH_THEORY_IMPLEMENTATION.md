# Graph Theory Module - Implementation Summary

This document describes the implementation of fundamental graph-theoretic concepts for the P-NP project, focusing on edge expansion properties and small Ramanujan graphs.

## Overview

The GraphTheory module provides:

1. **Edge Boundary** - Definition and properties of the edge boundary of a vertex set
2. **Edge Expansion** - Expansion ratio measuring connectivity to the rest of the graph
3. **Cheeger Constant** - Minimum expansion over balanced cuts
4. **Cycle Graphs** - Standard cycle graph construction
5. **Petersen Graph** - Small example of a Ramanujan (optimal expander) graph

## Key Definitions

### Edge Boundary

For a graph G and a subset S of vertices, the edge boundary ∂S consists of all edges with exactly one endpoint in S:

```lean
def edgeBoundary (G : SimpleGraph V) (S : Finset V) : Finset (V × V) :=
  (S ×ˢ (univ \ S)).filter fun ⟨v, w⟩ => G.Adj v w
```

**Characterization:**
```lean
lemma mem_edgeBoundary_iff : e ∈ G.edgeBoundary S ↔ 
    e.1 ∈ S ∧ e.2 ∉ S ∧ G.Adj e.1 e.2
```

### Edge Expansion

The edge expansion h(S) = |∂S|/|S| measures how well-connected S is to its complement:

```lean
def edgeExpansion (G : SimpleGraph V) (S : Finset V) : ℝ :=
  if h : S.Nonempty then
    (G.edgeBoundary S).card / S.card
  else 0
```

**Properties:**
- Always non-negative: `edgeExpansion_nonneg`
- Bounded by average degree: `edgeExpansion_bounded_by_avg_degree`

### Cheeger Constant

The Cheeger constant h(G) is the minimum edge expansion over all nonempty balanced cuts:

```lean
def cheegerConstant (G : SimpleGraph V) : ℝ :=
  ⨅ (S : Finset V) (h : S.Nonempty ∧ S.card ≤ (Fintype.card V)/2), 
    G.edgeExpansion S
```

The Cheeger constant is a fundamental measure of graph expansion and is closely related to:
- The spectral gap (via Cheeger's inequality)
- Mixing time of random walks
- Algorithmic complexity of various graph problems

## Main Theorems

### 1. Edge Boundary Cardinality Bounds

**Theorem (MaxDegree Bound):**
```lean
theorem edgeBoundary_card_le : 
    (G.edgeBoundary S).card ≤ G.maxDegree * S.card
```

Each vertex in S can contribute at most maxDegree edges to the boundary.

**Theorem (Sum of Degrees Bound):**
```lean
theorem edgeBoundary_card_le_sum_degrees :
    (G.edgeBoundary S).card ≤ ∑ v in S, G.degree v
```

This is a tighter bound: the boundary size is bounded by the sum of degrees of vertices in S.

**Proof Strategy:**
1. Show that edges in ∂S can be partitioned by their source vertex in S
2. Each vertex v ∈ S contributes at most degree(v) edges
3. Use biUnion to formalize this counting argument

### 2. Edge Expansion Bound

**Lemma:**
```lean
lemma edgeExpansion_bounded_by_avg_degree :
    G.edgeExpansion S ≤ (∑ v in S, G.degree v : ℝ) / S.card
```

The edge expansion is bounded by the average degree of vertices in S.

## Graph Constructions

### Cycle Graph

The cycle graph Cₙ on n vertices (n ≥ 3) forms a single cycle:

```lean
def cycleGraph (n : ℕ) (hn : n ≥ 3) : SimpleGraph (Fin n) where
  Adj i j := 
    i ≠ j ∧ ((i.val + 1) % n = j.val ∨ (j.val + 1) % n = i.val)
```

**Properties:**
- Each vertex has degree 2 (2-regular)
- Connected
- Has diameter ⌊n/2⌋
- **Treewidth = 2** (future work to prove)

### Petersen Graph

The Petersen graph is a famous 3-regular graph on 10 vertices:

```lean
def petersenGraph : SimpleGraph (Fin 10)
```

**Structure:**
- Outer pentagon (vertices 0-4): 5-cycle
- Inner star (vertices 5-9): connects vertices at distance 2
- Spokes: connect i to i+5 for i = 0..4

**Properties:**
- 3-regular (every vertex has degree 3)
- Diameter 2
- Strongly regular with parameters (10, 3, 0, 1)
- **Ramanujan graph**: optimal spectral gap for a 3-regular graph
- Non-planar
- Has girth 5 (shortest cycle length)

## Connection to P vs NP

These graph-theoretic concepts are crucial for the computational dichotomy:

1. **High Expansion ⟹ Hard SAT Instances**
   - Expander graphs have large Cheeger constant
   - Tseitin formulas over expanders have high treewidth
   - High treewidth forces exponential communication complexity

2. **Cheeger Constant and Spectral Gap**
   - Cheeger's inequality: λ₂/2 ≤ h(G) ≤ √(2λ₂)
   - Where λ₂ is the spectral gap of the normalized Laplacian
   - Ramanujan graphs achieve optimal spectral gap

3. **Ramanujan Graphs as Hard Instances**
   - Petersen graph: smallest Ramanujan graph
   - Used to construct hard SAT instances
   - Demonstrates tightness of complexity bounds

## Future Work

### Immediate Priorities

1. **Complete Treewidth Theory:**
   ```lean
   theorem cycle_treewidth_two (n : ℕ) (hn : 3 ≤ n) :
       treewidth (cycleGraph n hn) = 2
   ```
   Requires explicit tree decomposition construction.

2. **Verify Regularity:**
   ```lean
   lemma petersenGraph_is_3_regular : 
       ∀ v : Fin 10, petersenGraph.degree v = 3
   ```
   Can be verified by computation for all 10 vertices.

3. **Spectral Properties:**
   - Connect Cheeger constant to eigenvalues
   - Prove Cheeger's inequality
   - Verify Ramanujan property of Petersen graph

### Long-term Goals

1. **General Ramanujan Graph Construction:**
   - Implement Lubotzky-Phillips-Sarnak construction
   - Prove Ramanujan property formally
   - Connect to number theory (Ramanujan conjecture)

2. **Expander Mixing Lemma:**
   - Relate edge distribution to eigenvalues
   - Applications to derandomization

3. **Integration with Mathlib:**
   - Contribute edge boundary/expansion definitions
   - Contribute Cheeger constant theory
   - Contribute small graph examples

## Implementation Notes

### Design Decisions

1. **Edge Representation:**
   - Edges as ordered pairs (V × V) rather than unordered
   - Simplifies counting and membership proofs
   - Each undirected edge counted once (from smaller to larger vertex)

2. **Real-Valued Expansion:**
   - Use ℝ for edge expansion to handle division naturally
   - Avoids complications with rational arithmetic
   - Standard in graph theory literature

3. **Nonempty Sets:**
   - Edge expansion defined as 0 for empty sets
   - Avoids division by zero
   - Matches standard conventions

### Proof Techniques

1. **Cardinality Bounds:**
   - Use `card_biUnion_le` for disjoint union bounds
   - Partition edges by source vertex
   - Sum over individual contributions

2. **Graph Symmetry:**
   - Adjacency relation is symmetric by definition
   - Loopless enforced by requiring i ≠ j
   - Simplifies many proofs

3. **Modular Arithmetic:**
   - Cycle graph uses (i + 1) % n for successor
   - Handles wrap-around naturally
   - Requires n ≥ 3 to avoid degenerate cases

## References

1. **Edge Expansion and Cheeger Constant:**
   - Alon & Milman, "λ₁, Isoperimetric inequalities for graphs, and superconcentrators" (1985)
   - Cheeger, "A lower bound for the smallest eigenvalue of the Laplacian" (1970)

2. **Ramanujan Graphs:**
   - Lubotzky, Phillips & Sarnak, "Ramanujan graphs" (1988)
   - Hoory, Linial & Wigderson, "Expander graphs and their applications" (2006)

3. **Treewidth:**
   - Robertson & Seymour, "Graph Minors" series
   - Bodlaender, "A partial k-arboretum of graphs with bounded treewidth" (1998)

4. **Applications to Complexity:**
   - Urquhart, "Hard examples for resolution" (1987)
   - Ben-Sasson & Wigderson, "Short proofs are narrow" (2001)

## Author

José Manuel Mota Burruezo & Implementation Team

## License

MIT License - See project root for details
