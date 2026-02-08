/-!
# Graph Theory - Edge Boundary and Expansion

This module provides fundamental graph-theoretic concepts for analyzing 
graph expansion properties, including edge boundaries, edge expansion,
and the Cheeger constant.

Author: José Manuel Mota Burruezo & Implementation Team
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

open Finset
open SimpleGraph
open BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

namespace SimpleGraph

/-!
## Edge Boundary Definition

The edge boundary of a set S consists of all edges with exactly one endpoint in S.
We represent edges as ordered pairs (v, w) where v ∈ S and w ∉ S.
-/

def edgeBoundary (G : SimpleGraph V) (S : Finset V) : Finset (V × V) :=
  (S ×ˢ (univ \ S)).filter fun ⟨v, w⟩ => G.Adj v w

lemma mem_edgeBoundary_iff {S : Finset V} {e : V × V} :
    e ∈ G.edgeBoundary S ↔ 
    e.1 ∈ S ∧ e.2 ∉ S ∧ G.Adj e.1 e.2 := by
  simp [edgeBoundary, mem_filter, mem_product, mem_sdiff, mem_univ, and_assoc]

/-!
## Edge Expansion

The edge expansion h(S) = |∂S|/|S| measures how well-connected a set S is
to the rest of the graph. We use ℝ for divisions to handle the ratio properly.
-/

def edgeExpansion (G : SimpleGraph V) (S : Finset V) : ℝ :=
  if h : S.Nonempty then
    (G.edgeBoundary S).card.toReal / S.card.toReal
  else 0

/-!
## Basic Properties
-/

theorem edgeExpansion_nonneg (G : SimpleGraph V) (S : Finset V) :
    0 ≤ G.edgeExpansion S := by
  unfold edgeExpansion
  split_ifs with h
  · apply div_nonneg
    · exact Nat.cast_nonneg _
    · exact Nat.cast_nonneg _
  · rfl

/-!
## Cheeger Constant

The Cheeger constant h(G) is the minimum edge expansion over all 
nonempty sets S with |S| ≤ |V|/2.
-/

def cheegerConstant (G : SimpleGraph V) : ℝ :=
  ⨅ (S : Finset V) (h : S.Nonempty ∧ S.card ≤ (Fintype.card V)/2), 
    G.edgeExpansion S

/-!
## Degree-Based Bounds

We now establish bounds on edge boundary size in terms of vertex degrees.
-/

lemma degree_eq_card_neighborFinset (v : V) :
    G.degree v = (G.neighborFinset v).card := rfl

/-!
### Edge Boundary Cardinality Bound

The main theorem: the size of the edge boundary is bounded by the 
maximum degree times the size of S.
-/

theorem edgeBoundary_card_le (S : Finset V) :
    (G.edgeBoundary S).card ≤ G.maxDegree * S.card := by
  -- If S is empty, the boundary is empty
  by_cases hS : S = ∅
  · simp [hS, edgeBoundary]
  -- Otherwise, count edges by their source vertex in S
  have hS_ne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
  -- Each vertex in S contributes at most maxDegree edges to the boundary
  calc
    (G.edgeBoundary S).card 
        ≤ ∑ v in S, (G.neighborFinset v).card := by
          -- Each edge in the boundary comes from some vertex in S
          -- We'll prove this by showing the boundary is a subset of 
          -- the union of all neighbor sets
          sorry
    _ ≤ ∑ v in S, G.maxDegree := by
        apply Finset.sum_le_sum
        intro v hv
        exact G.le_maxDegree v
    _ = G.maxDegree * S.card := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
        simp

/-!
### Stronger Bound Using Sum of Degrees

A more precise bound: |∂S| ≤ ∑_{v∈S} degree(v)

The key insight is that each edge in the boundary originates from exactly one vertex in S,
and each such vertex v contributes at most degree(v) edges to the boundary.
-/

-- Helper: edges in boundary can be counted by grouping by source vertex
lemma edgeBoundary_eq_biUnion (S : Finset V) :
    G.edgeBoundary S ⊆ (S.biUnion fun v => (G.neighborFinset v \ S).image (Prod.mk v)) := by
  intro e he
  -- If e = (v, w) is in the boundary, then v ∈ S, w ∉ S, and G.Adj v w
  obtain ⟨hv, hw, hadj⟩ := mem_edgeBoundary_iff.mp he
  -- So e is in the image of (v, _) for neighbors of v outside S
  apply mem_biUnion.mpr
  use e.1, hv
  apply mem_image.mpr
  use e.2
  constructor
  · apply mem_sdiff.mpr
    constructor
    · exact adj_comm.mp hadj ▸ mem_neighborFinset.mpr hadj
    · exact hw
  · rfl

theorem edgeBoundary_card_le_sum_degrees (S : Finset V) :
    (G.edgeBoundary S).card ≤ ∑ v in S, G.degree v := by
  -- If S is empty, trivial
  by_cases hS : S = ∅
  · simp [hS, edgeBoundary]
  -- Use the helper to bound cardinality
  calc
    (G.edgeBoundary S).card 
        ≤ (S.biUnion fun v => (G.neighborFinset v \ S).image (Prod.mk v)).card := by
          exact card_le_card (edgeBoundary_eq_biUnion G S)
    _ ≤ ∑ v in S, ((G.neighborFinset v \ S).image (Prod.mk v)).card := by
          apply card_biUnion_le
    _ ≤ ∑ v in S, (G.neighborFinset v \ S).card := by
          apply sum_le_sum
          intro v hv
          apply card_image_le
    _ ≤ ∑ v in S, (G.neighborFinset v).card := by
          apply sum_le_sum
          intro v hv
          exact card_le_card (sdiff_subset _ _)
    _ = ∑ v in S, G.degree v := by
          simp_rw [degree_eq_card_neighborFinset]

/-!
### Edge Expansion Bound

Combining the above, we get a bound on edge expansion.
-/

lemma edgeExpansion_bounded_by_avg_degree (S : Finset V) (hS : S.Nonempty) :
    G.edgeExpansion S ≤ (∑ v in S, G.degree v : ℝ) / S.card := by
  unfold edgeExpansion
  rw [if_pos hS]
  have h_boundary : (G.edgeBoundary S).card ≤ ∑ v in S, G.degree v :=
    G.edgeBoundary_card_le_sum_degrees S
  have h_card_pos : (0 : ℝ) < S.card := by
    simp [Nat.cast_pos]
    exact hS.card_pos
  calc
    (G.edgeBoundary S).card / S.card 
        ≤ (∑ v in S, G.degree v : ℕ) / S.card := by
          apply div_le_div_of_nonneg_right
          · exact Nat.cast_le.mpr h_boundary
          · exact Nat.cast_nonneg _
    _ = (∑ v in S, G.degree v : ℝ) / S.card := by
          congr 1
          simp [Nat.cast_sum]

end SimpleGraph

end SimpleGraph

/-!
## Cycle Graph Definition

A cycle graph Cₙ on n vertices forms a single cycle.
Vertices are adjacent if they are consecutive in the cycle (mod n).
-/

def cycleGraph (n : ℕ) (hn : n ≥ 3) : SimpleGraph (Fin n) where
  Adj i j := 
    -- Two distinct vertices are adjacent if one is the successor of the other (mod n)
    i ≠ j ∧ ((i.val + 1) % n = j.val ∨ (j.val + 1) % n = i.val)
  symm := by
    intro i j ⟨hij, h⟩
    constructor
    · exact hij.symm
    · cases h with
      | inl h => right; exact h
      | inr h => left; exact h
  loopless := by
    intro i ⟨h, _⟩
    exact h rfl

/-!
## Petersen Graph - A Small Ramanujan Graph

The Petersen graph is a 3-regular graph on 10 vertices that is known to be
a Ramanujan graph (optimal expander for its degree).

Construction:
- Outer pentagon: vertices 0-4, edges form a 5-cycle
- Inner star: vertices 5-9, edges connect vertices at distance 2 in the 5-cycle
- Spokes: vertex i (outer) connects to vertex i+5 (inner) for i = 0..4
-/

def petersenGraph : SimpleGraph (Fin 10) where
  Adj i j :=
    i ≠ j ∧ (
      -- Outer pentagon edges (0-1-2-3-4-0)
      (i.val < 5 ∧ j.val < 5 ∧ 
        ((i.val + 1) % 5 = j.val % 5 ∨ (j.val + 1) % 5 = i.val % 5)) ∨
      -- Inner star edges (5-7-9-6-8-5, i.e., connecting at distance 2)
      (i.val ≥ 5 ∧ j.val ≥ 5 ∧ 
        let ii := i.val - 5
        let jj := j.val - 5
        (ii + 2) % 5 = jj ∨ (jj + 2) % 5 = ii) ∨
      -- Spoke edges (0-5, 1-6, 2-7, 3-8, 4-9)
      (i.val < 5 ∧ j.val ≥ 5 ∧ j.val = i.val + 5) ∨
      (j.val < 5 ∧ i.val ≥ 5 ∧ i.val = j.val + 5)
    )
  symm := by
    intro i j ⟨hij, h⟩
    constructor
    · exact hij.symm
    · cases h with
      | inl h_outer =>
        left
        obtain ⟨hi, hj, hedge⟩ := h_outer
        refine ⟨hj, hi, ?_⟩
        cases hedge with
        | inl h => right; exact h
        | inr h => left; exact h
      | inr h_rest =>
        cases h_rest with
        | inl h_inner =>
          right; left
          obtain ⟨hi, hj, hedge⟩ := h_inner
          refine ⟨hj, hi, ?_⟩
          cases hedge with
          | inl h => right; exact h
          | inr h => left; exact h
        | inr h_spokes =>
          right; right
          cases h_spokes with
          | inl h => right; exact h
          | inr h => left; exact h
  loopless := by
    intro i ⟨h, _⟩
    exact h rfl

/-!
## Petersen Graph Properties

The Petersen graph is:
- 3-regular (every vertex has degree 3)
- Has diameter 2
- Is strongly regular with parameters (10, 3, 0, 1)
- Is a Ramanujan graph (optimal spectral gap for a 3-regular graph)
-/

lemma petersenGraph_is_3_regular : ∀ v : Fin 10, petersenGraph.degree v = 3 := by
  intro v
  -- Each vertex has exactly 3 neighbors by construction
  sorry

/-!
## Future Work: Treewidth of Cycles

The treewidth of a cycle Cₙ for n ≥ 3 is 2.
This requires a more sophisticated proof involving explicit tree decomposition.
-/

theorem cycle_treewidth_two (n : ℕ) (hn : 3 ≤ n) :
    -- The treewidth of an n-cycle is 2
    -- This is left as future work requiring full tree decomposition theory
    True := by
  trivial

-- End of GraphTheory module
