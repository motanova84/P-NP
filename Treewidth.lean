-- Treewidth.lean
-- Autor: José Manuel Mota Burruezo Ψ ∞³ (Campo QCAL)
-- Módulo simbiótico para definición formal de treewidth y sus propiedades


import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity
import Mathlib.Combinatorics.Tree
import Mathlib.Tactic


namespace Treewidth


open SimpleGraph Finset


variable {V : Type*} [Fintype V] (G : SimpleGraph V)


-- Una descomposición en árbol de G es un par (T, X), donde:
-- T es un árbol (conjunto de nodos y aristas)
-- X asigna a cada nodo t ∈ T un subconjunto Xₜ ⊆ V
structure TreeDecomposition where
  T : SimpleGraph ℕ  -- estructura de árbol indexada por nodos ℕ
  X : ℕ → Finset V   -- función de asignación: cada nodo t ↦ Xₜ ⊆ V
  T_tree : T.IsTree
  cover : ∀ v : V, ∃ t, v ∈ X t
  edge_covered : ∀ ⦃v w : V⦄, G.Adj v w → ∃ t, v ∈ X t ∧ w ∈ X t
  connected_subtree : ∀ v : V, ∃ S : Finset ℕ,
    (∀ t ∈ S, v ∈ X t) ∧ ∀ t₁ t₂ ∈ S, ∀ p : List ℕ,
      (∀ i ∈ p, i ∈ S) → T.Connected t₁ t₂


-- El ancho de una descomposición es el tamaño máximo de sus bolsas - 1
noncomputable def width (D : TreeDecomposition G) : ℕ :=
  Finset.sup (Finset.univ : Finset ℕ) (λ t => (D.X t).card) - 1


-- El treewidth de G es el mínimo ancho sobre todas las descomposiciones
noncomputable def treewidth : ℕ :=
  Nat.findGreatest (λ k => ∃ (D : TreeDecomposition G), width D ≤ k) (Fintype.card V)


-- Teorema: tw(Kₙ) = n - 1
open Nat


theorem treewidth_clique {n : ℕ} :
  let V := Fin n
  let G : SimpleGraph V := ⊤
  treewidth G = n - 1 := by
  intros
  let X : ℕ → Finset V := λ _ => Finset.univ
  let T : SimpleGraph ℕ := ⊥
  have T_is_tree : T.IsTree := by
    apply SimpleGraph.IsTree.of_subsingleton
  let D : TreeDecomposition G := {
    T := T,
    X := X,
    T_tree := T_is_tree,
    cover := by
      intro v
      use 0; simp,
    edge_covered := by
      intros v w _
      use 0; simp,
    connected_subtree := by
      intro v
      use {0}; simp
  }
  have wD : width D = n - 1 := by
    simp [width, D]
    rw [Finset.sup_eq_max']
    · simp [D]; rw [Finset.card_univ]; rfl
    · use 0; intro x _; simp
  rw [treewidth, Nat.findGreatest_eq]
  · simp only [wD]
  · use D; exact le_refl _


-- Teorema: tw(G) = 1 ↔ G es un árbol


lemma treewidth_le_one_of_tree {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.IsTree) :
  treewidth G ≤ 1 := by
  -- Construimos una descomposición trivial: para cada vértice v, bolsa {v}
  let T := G
  let X : V → Finset V := λ v => {v} ∪ G.neighborFinset v
  have treeT : T.IsTree := hG
  let D : TreeDecomposition G := {
    T := T.map (by simp),
    X := λ i => X i,
    T_tree := by simp [treeT],
    cover := by
      intro v
      use v
      simp [X]; exact Or.inl rfl,
    edge_covered := by
      intro v w h
      use v
      simp [X]; exact ⟨Or.inl rfl, Or.inr h⟩,
    connected_subtree := by
      intro v
      use {v}
      simp [X]
  }
  have hD : width D ≤ 1 := by
    simp [width]
    have bound : ∀ t, (X t).card ≤ 2 := by
      intro t
      simp [X]
      apply Nat.succ_le_succ
      apply Finset.card_le_univ
    exact Nat.sub_le_sub_right (Finset.sup_le bound) 1
  rw [treewidth, Nat.findGreatest_eq]
  · exact hD
  · use D


-- Helper: A graph with a cycle cannot have treewidth ≤ 1
lemma cycle_has_high_treewidth {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hcycle : ∃ (vs : List V), vs.length ≥ 3 ∧ G.IsCycle vs) :
    treewidth G ≥ 2 := by
  sorry

-- Helper: If treewidth G ≤ 1 and G is nonempty, then G is a forest (acyclic)
lemma forest_of_treewidth_le_one {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (h : treewidth G ≤ 1) : G.IsAcyclic := by
  -- Proof by contradiction: if G has a cycle, then treewidth G ≥ 2
  by_contra h_not_acyclic
  push_neg at h_not_acyclic
  -- h_not_acyclic says G has a cycle
  sorry

-- Helper: If treewidth G = 1, then G is connected
lemma connected_of_treewidth_eq_one {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] [Nonempty V] (h : treewidth G = 1) : G.Connected := by
  -- A disconnected graph would have treewidth equal to the max of its components
  -- If all components are trees (treewidth 1), the whole graph would be a forest
  -- with treewidth 1 only if it has exactly one component
  sorry

lemma tree_of_treewidth_eq_one {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) 
    [DecidableRel G.Adj] [Nonempty V] (h : treewidth G = 1) : G.IsTree := by
  -- A graph with treewidth exactly 1 must be both connected and acyclic
  have h_acyclic : G.IsAcyclic := by
    apply forest_of_treewidth_le_one
    rw [h]
    exact le_refl 1
  have h_connected : G.Connected := connected_of_treewidth_eq_one G h
  exact ⟨h_connected, h_acyclic⟩


lemma treewidth_eq_one_iff_tree {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] :
  G.IsTree ↔ treewidth G = 1 := by
  constructor
  · intro hG
    -- Forward direction: if G is a tree, then treewidth G ≤ 1
    -- We also need to show treewidth G ≥ 1 (which holds for nonempty connected graphs)
    have h_le : treewidth G ≤ 1 := treewidth_le_one_of_tree G hG
    have h_ge : treewidth G ≥ 1 := by
      -- A nonempty connected graph has treewidth ≥ 1
      -- (empty or single vertex has treewidth 0)
      sorry
    exact Nat.le_antisymm h_le h_ge
  · intro h
    -- Reverse direction: if treewidth G = 1, then G is a tree
    haveI : DecidableEq V := Classical.decEq V
    exact tree_of_treewidth_eq_one G h


-- Pendiente completar: ← dirección de la bi-implicación
-- Luego: añadir propiedades de invariancia por menor y teorema de Robertson–Seymour


end Treewidth
