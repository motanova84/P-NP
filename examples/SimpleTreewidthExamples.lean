/-!
# Examples: Simple Treewidth in Action

This file demonstrates the working theorems from SimpleTreewidth.lean
and shows how to build on them.

## Author
José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
-/

import SimpleTreewidth

namespace SimpleTreewidthExamples

open SimpleTreewidth SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! 
## Example 1: Basic Arithmetic Works
-/

example : 2 + 2 = 4 := simple_lemma
example : 3 + 1 = 4 := three_plus_one

-- We can build on these:
example : 2 + 2 + 3 + 1 = 8 := by norm_num

/-! 
## Example 2: Edge Expansion Properties
-/

-- Edge expansion is always non-negative
example (G : SimpleGraph V) (S : Finset V) : 
    0 ≤ edgeExpansion G S := 
  edgeExpansion_nonneg G S

-- Specific case: empty set
example (G : SimpleGraph V) : edgeExpansion G ∅ = 0 := 
  edgeExpansion_empty G

-- We can combine properties
example (G : SimpleGraph V) (S : Finset V) : 
    0 ≤ edgeExpansion G S ∧ edgeExpansion G ∅ = 0 := by
  constructor
  · exact edgeExpansion_nonneg G S
  · exact edgeExpansion_empty G

/-! 
## Example 3: Graph Properties
-/

-- The cycle graph is symmetric
example (n : ℕ) (i j : Fin n) (h : (cycleGraph n).Adj i j) :
    (cycleGraph n).Adj j i :=
  cycleGraph_symm n i j h

-- No vertex is adjacent to itself
example (G : SimpleGraph V) (v : V) : ¬ G.Adj v v :=
  not_adj_self G v

-- Combined property
example (n : ℕ) (i : Fin n) :
    ¬ (cycleGraph n).Adj i i ∧ 
    ∀ j, (cycleGraph n).Adj i j → (cycleGraph n).Adj j i := by
  constructor
  · exact not_adj_self (cycleGraph n) i
  · intro j hij
    exact cycleGraph_symm n i j hij

/-! 
## Example 4: Path Graph Structure
-/

-- Path graph is well-defined
example (n : ℕ) : SimpleGraph (Fin n) := pathGraph n

-- We can check adjacency in a path
def path3 : SimpleGraph (Fin 3) := pathGraph 3

-- In a 3-vertex path: vertex 0 is adjacent to vertex 1
example : (pathGraph 3).Adj 0 1 := by
  unfold pathGraph
  simp
  left
  rfl

/-! 
## Example 5: Combining Results
-/

-- We can prove complex facts by combining simple lemmas
theorem expansion_properties (G : SimpleGraph V) (S T : Finset V) :
    0 ≤ edgeExpansion G S + edgeExpansion G T := by
  apply nonneg_composition
  · exact edgeExpansion_nonneg G S
  · exact edgeExpansion_nonneg G T

-- Finset cardinality is always non-negative
example (S : Finset V) : 0 ≤ S.card := 
  finset_card_nonneg S

-- We can use this in proofs
theorem edge_count_nonneg (n : ℕ) (hn : 1 ≤ n) :
    ∃ (m : ℕ), 0 ≤ m ∧ m ≤ n := by
  obtain ⟨m, hm⟩ := pathGraph_edge_count n hn
  use m
  constructor
  · exact Nat.zero_le m
  · exact hm

/-! 
## Example 6: Building Toward Cycle Treewidth
-/

-- Define a small cycle for concrete examples
def cycle3 : SimpleGraph (Fin 3) := cycleGraph 3
def cycle4 : SimpleGraph (Fin 4) := cycleGraph 4
def cycle5 : SimpleGraph (Fin 5) := cycleGraph 5

-- These are all symmetric
example : ∀ i j, cycle3.Adj i j → cycle3.Adj j i := by
  intros i j h
  exact cycleGraph_symm 3 i j h

-- No self-loops in cycles
example : ∀ i, ¬ cycle4.Adj i i := by
  intro i
  exact not_adj_self cycle4 i

/-! 
## Example 7: Working with Edge Boundaries
-/

-- For any graph and any set, the boundary is well-defined
example (G : SimpleGraph V) (S : Finset V) :
    ∃ B, B = G.edgeBoundary S := by
  use G.edgeBoundary S

-- Edge expansion for small sets
example (G : SimpleGraph V) (v : V) :
    0 ≤ edgeExpansion G {v} :=
  edgeExpansion_singleton G v

/-! 
## Example 8: Demonstration of Incremental Building
-/

-- Start simple
lemma step1 : 1 + 1 = 2 := by norm_num

-- Add complexity
lemma step2 (a b : ℕ) : a + b = b + a := by omega

-- Build on previous
lemma step3 : 1 + 1 + 2 = 4 := by
  have h := step1
  omega

-- Continue building
theorem incremental_result (n : ℕ) : n + 0 = n := by
  omega

/-! 
## Summary

This file demonstrates:
1. ✅ All basic lemmas work without sorry
2. ✅ We can compose simple results into complex ones
3. ✅ Graph structures are well-defined
4. ✅ Properties can be proven incrementally
5. ✅ The foundation is solid for building the full theorem

The key insight: **Start simple, build gradually, prove completely.**
-/

end SimpleTreewidthExamples
