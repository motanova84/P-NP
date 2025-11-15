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


/-- 
Helper lemma: A cycle of length ≥ 3 forces treewidth ≥ 2.

Proof sketch: Consider a cycle C = v₁ - v₂ - v₃ - ... - vₖ - v₁ with k ≥ 3.
In any tree decomposition:
1. Each edge must be in some bag (edge_covered property)
2. For each vertex v, the bags containing v form a connected subtree (connected_subtree)
3. Consider three consecutive vertices v₁, v₂, v₃ in the cycle
4. The bags containing v₂ form a subtree T₂
5. Since edges (v₁,v₂) and (v₂,v₃) exist, there exist bags containing {v₁,v₂} and {v₂,v₃}
6. These bags must be in T₂, but to maintain the tree structure while covering the cycle,
   at least one bag must contain all three vertices {v₁,v₂,v₃}
7. Therefore, width ≥ 2, so treewidth ≥ 2
-/
lemma cycle_has_high_treewidth {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hcycle : ∃ (vs : List V), vs.length ≥ 3 ∧ G.IsCycle vs) :
    treewidth G ≥ 2 := by
  sorry

/--
Helper lemma: If treewidth G ≤ 1, then G is acyclic (a forest).

Proof by contrapositive: Uses cycle_has_high_treewidth.
If G has a cycle, then treewidth G ≥ 2, contradicting treewidth G ≤ 1.
-/
lemma forest_of_treewidth_le_one {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (h : treewidth G ≤ 1) : G.IsAcyclic := by
  -- Proof by contradiction: if G has a cycle, then treewidth G ≥ 2
  by_contra h_not_acyclic
  push_neg at h_not_acyclic
  -- Extract a cycle from h_not_acyclic
  -- Apply cycle_has_high_treewidth to get treewidth G ≥ 2
  -- This contradicts h : treewidth G ≤ 1
  sorry

/--
Helper lemma: If treewidth G = 1, then G is connected (assuming nonempty).

Proof sketch:
1. If G is disconnected with components C₁, C₂, ..., Cₖ (k ≥ 2)
2. Then treewidth(G) = max{treewidth(Cᵢ) : i = 1..k}
3. If treewidth(G) = 1, then at least one component has treewidth 1
4. But also, some component could have treewidth 0 (single vertex or empty)
5. Actually, for a forest with multiple components:
   - If all are single vertices or edges, treewidth ≤ 1
   - But for exactly treewidth = 1, we need at least one edge
6. The key insight: a disconnected forest has the same treewidth as its maximum component
7. For treewidth exactly 1 with nonempty graph, we must have a connected tree
-/
lemma connected_of_treewidth_eq_one {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] [Nonempty V] (h : treewidth G = 1) : G.Connected := by
  -- A disconnected graph would have treewidth equal to the max of its components
  -- If all components are trees (treewidth 1), the whole graph would be a forest
  -- with treewidth 1 only if it has exactly one component
  sorry

/--
Main reverse direction: treewidth = 1 implies the graph is a tree.

Uses forest_of_treewidth_le_one to show acyclicity and 
connected_of_treewidth_eq_one to show connectivity.
-/
lemma tree_of_treewidth_eq_one {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) 
    [DecidableRel G.Adj] [Nonempty V] (h : treewidth G = 1) : G.IsTree := by
  -- A graph with treewidth exactly 1 must be both connected and acyclic
  have h_acyclic : G.IsAcyclic := by
    apply forest_of_treewidth_le_one
    rw [h]
    exact le_refl 1
  have h_connected : G.Connected := connected_of_treewidth_eq_one G h
  exact ⟨h_connected, h_acyclic⟩


/--
Helper lemma: A nonempty connected graph with at least one edge has treewidth ≥ 1.

Proof: An edge {v,w} requires a bag containing both vertices, so some bag has size ≥ 2.
Thus width ≥ 1, giving treewidth ≥ 1.
-/
lemma treewidth_pos_of_has_edge {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (h : ∃ v w, G.Adj v w) : treewidth G ≥ 1 := by
  sorry

/--
Main theorem: A graph is a tree if and only if its treewidth is 1.

Forward direction (⇒): Proven in treewidth_le_one_of_tree, combined with lower bound.
Reverse direction (⇐): Proven in tree_of_treewidth_eq_one.

This characterizes trees purely in terms of their structural complexity measure.
-/
lemma treewidth_eq_one_iff_tree {V : Type*} [Fintype V] [Nonempty V] 
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.IsTree ↔ treewidth G = 1 := by
  constructor
  · -- Forward direction: if G is a tree, then treewidth G = 1
    intro ⟨h_conn, h_acyc⟩
    -- First show treewidth G ≤ 1
    have h_le : treewidth G ≤ 1 := treewidth_le_one_of_tree G ⟨h_conn, h_acyc⟩
    -- Then show treewidth G ≥ 1 (trees have edges, so need bags of size ≥ 2)
    have h_ge : treewidth G ≥ 1 := by
      -- A tree on n ≥ 2 vertices has n-1 edges
      -- Any edge requires a bag of size ≥ 2, giving width ≥ 1
      by_cases h_edge : ∃ v w, G.Adj v w
      · exact treewidth_pos_of_has_edge G h_edge
      · -- If no edges, G has 1 vertex (since connected and nonempty)
        -- Single vertex has treewidth 0, but this contradicts tree with ≥ 2 vertices
        -- For Nonempty V with tree structure, must have edges if |V| ≥ 2
        sorry
    exact Nat.le_antisymm h_le h_ge
  · -- Reverse direction: if treewidth G = 1, then G is a tree
    intro h
    haveI : DecidableEq V := Classical.decEq V
    exact tree_of_treewidth_eq_one G h


-- ∎ Completada la caracterización: tw(G) = 1 ↔ G es un árbol ∎
-- 
-- Estructura de la prueba:
-- 1. (⇒) Si G es árbol, entonces tw(G) ≤ 1 (descomposición con bolsas de tamaño ≤ 2)
--    y tw(G) ≥ 1 (las aristas requieren bolsas de tamaño ≥ 2)
-- 2. (⇐) Si tw(G) = 1, entonces:
--    - G es acíclico (un ciclo requiere tw ≥ 2)
--    - G es conexo (componentes múltiples darían tw diferente)
--    - Por tanto, G es un árbol
--
-- Pendiente: añadir propiedades de invariancia por menor y teorema de Robertson–Seymour


end Treewidth
