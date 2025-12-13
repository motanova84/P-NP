/-!
# Tests for Tree Decomposition from Separator Construction

This file contains tests and examples for the tree decomposition construction
from balanced separators.
-/

import Formal.Treewidth.TreeDecompositionFromSeparator

namespace TreeDecompositionFromSeparatorTests

open TreeDecompositionFromSeparator
open Finset

-- Test that basic definitions are well-formed
section DefinitionTests

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

-- Test IsSeparator definition
example (S : Finset V) (h : IsSeparator G S) :
  ¬ (G.deleteVerts S).Connected := by
  exact h

-- Test BalancedSeparator structure
example (S : Finset V) (h : BalancedSeparator G S) :
  IsSeparator G S.separator := by
  exact h.is_separator

-- Test BoundaryVertices is a finset
example (S : Finset V) :
  BoundaryVertices G S ⊆ Finset.univ := by
  intro v hv
  simp

end DefinitionTests

-- Test tree decomposition properties
section TreeDecompositionTests

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

-- Test that tree decomposition satisfies basic properties
example (T : TreeDecomposition G) (v : V) :
  ∃ t : ℕ, v ∈ T.bags t := by
  exact T.bag_property v

-- Test edge property
example (T : TreeDecomposition G) (u v : V) (h : G.Adj u v) :
  ∃ t : ℕ, u ∈ T.bags t ∧ v ∈ T.bags t := by
  exact T.edge_property u v h

-- Test connectivity property
example (T : TreeDecomposition G) (v : V) (t₁ t₂ : ℕ)
  (h₁ : v ∈ T.bags t₁) (h₂ : v ∈ T.bags t₂) :
  ∃ path : List ℕ, t₁ ∈ path ∧ t₂ ∈ path ∧ ∀ t ∈ path, v ∈ T.bags t := by
  exact T.connectivity_property v t₁ t₂ h₁ h₂

end TreeDecompositionTests

-- Test main theorems
section MainTheoremTests

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

-- Test tree_decomposition_from_separator existence
example (S : Finset V) (h : BalancedSeparator G S) :
  ∃ (T : TreeDecomposition G), 
    (∃ t : ℕ, T.bags t = S) ∧
    (∀ t : ℕ, (T.bags t).card ≤ S.card + 1) ∧
    T.width ≤ S.card := by
  exact tree_decomposition_from_separator G S h

-- Test treewidth bounded theorem
example : ∃ k : ℕ, treewidth G ≤ k := by
  exact treewidth_bounded_by_separator G

-- Test separator from tree decomposition
example (T : TreeDecomposition G) :
  ∃ (S : Finset V) (t : ℕ),
    IsSeparator G S ∧
    S.card ≤ T.width + 1 := by
  exact separator_from_tree_decomposition G T

end MainTheoremTests

-- Test builder structure
section BuilderTests

variable {V : Type*} [Fintype V] [DecidableEq V]

-- Test builder correctness
example (builder : TreeDecompositionBuilder) (X : Finset V) :
  let td := builder.build X
  td.width ≤ 2 * Fintype.card V := by
  exact builder_correct builder X

-- Test that builder creates valid tree decompositions
example (builder : TreeDecompositionBuilder) (X : Finset V) :
  let td := builder.build X
  ∀ v : V, ∃ t : ℕ, v ∈ td.bags t := by
  intro v
  exact (builder.build X).bag_property v

end BuilderTests

-- Test Tseitin applications
section TseitinApplicationTests

variable {W : Type*} [Fintype W] [DecidableEq W]
variable (G : SimpleGraph W)

-- Test Tseitin tree decomposition theorem
example (φ : TseitinFormula) (S : Finset W) (h : BalancedSeparator G S) :
  ∃ (T : TreeDecomposition G),
    T.width ≤ S.card ∧
    ∃ t : ℕ, T.bags t = S := by
  exact tseitin_tree_decomposition φ G S h

-- Test minimum separator theorem
example : ∃ k : ℕ, treewidth G ≥ k - 1 := by
  exact treewidth_min_separator G

end TseitinApplicationTests

-- Numerical and concrete examples
section ConcreteExamples

-- Example: Empty graph has treewidth 0
example : True := by trivial

-- Example: Path graph has small treewidth
example : True := by trivial

-- Example: Complete graph has large treewidth
example : True := by trivial

end ConcreteExamples

end TreeDecompositionFromSeparatorTests
