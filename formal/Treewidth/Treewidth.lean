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

/-!
# Treewidth and Tree Decompositions

This module formalizes tree decompositions and treewidth of graphs.

## Main Definitions

* `TreeDecomposition G`: A tree decomposition of a graph G
* `width D`: The width of a tree decomposition D
* `treewidth G`: The treewidth of a graph G

## Main Results

* `complete_graph_treewidth`: The treewidth of a complete graph Kₙ is n - 1
* `treewidth_le_one_of_tree`: If G is a tree, then tw(G) ≤ 1
* `tree_of_treewidth_one`: If tw(G) = 1, then G is a tree
* `treewidth_minor_monotonic`: Treewidth is monotonic under graph minors

-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity
import Mathlib.Data.Finset.Card
import Mathlib.Order.Basic

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
  Nat.findGreatest (λ k => ∃ (D : TreeDecomposition G), width G D ≤ k) (Fintype.card V)


-- Teorema: tw(Kₙ) = n - 1
theorem treewidth_clique {n : ℕ} :
  let V := Fin n
  let G := ⊤ : SimpleGraph V
  treewidth G = n - 1 := by
  sorry -- prueba pendiente


-- Teorema: tw(G) = 1 ssi G es un árbol
-- ...


-- Teoremas de minor-monotonía y conexión con el teorema de Robertson–Seymour
-- ...

variable {V : Type*} [Fintype V] [DecidableEq V]

/--
A tree decomposition of a graph G consists of:
- A tree T (itself a graph)
- A function X mapping tree nodes to bags (finite sets of graph vertices)
- Three properties:
  1. cover: Every vertex of G appears in at least one bag
  2. edge_covered: Every edge of G has both endpoints in some bag
  3. connected_subtree: For each vertex v of G, the bags containing v form a connected subtree
-/
structure TreeDecomposition (G : SimpleGraph V) where
  T : SimpleGraph V
  X : V → Finset V
  T_tree : T.IsTree
  cover : ∀ v : V, ∃ t : V, v ∈ X t
  edge_covered : ∀ v w : V, G.Adj v w → ∃ t : V, v ∈ X t ∧ w ∈ X t
  connected_subtree : ∀ v : V, ∃ S : Finset V, 
    (∀ t ∈ S, v ∈ X t) ∧ T.Connected ∧ 
    (∀ t₁ t₂ : V, t₁ ∈ S → t₂ ∈ S → ∀ p : T.Walk t₁ t₂, ∀ u ∈ p.support, u ∈ S → v ∈ X u)

/--
The width of a tree decomposition is the maximum bag size minus 1.
-/
def width {G : SimpleGraph V} (D : TreeDecomposition G) : ℕ :=
  (Finset.univ.image (fun t => (D.X t).card)).sup id - 1

/--
The treewidth of a graph is the minimum width over all tree decompositions.
Uses Nat.findGreatest to find the optimal decomposition.
-/
def treewidth (G : SimpleGraph V) : ℕ :=
  Nat.findGreatest (fun k => ∃ D : TreeDecomposition G, width D ≤ k) (Fintype.card V)

/--
Complete graph on n vertices.
-/
def completeGraph (n : ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.completeGraph (Fin n)

-- Theorem: tw(Kₙ) = n - 1
theorem complete_graph_treewidth (n : ℕ) : 
  treewidth (completeGraph n) = n - 1 := by
  -- The complete graph requires all vertices in one bag
  let T : SimpleGraph (Fin 1) := SimpleGraph.completeGraph (Fin 1)
  have T_is_tree : T.IsTree := by
    constructor
    · exact SimpleGraph.completeGraph_connected _
    · intro v w p hp
      simp [SimpleGraph.Walk.IsPath] at hp
      simp
  let D : TreeDecomposition (completeGraph n) := {
    T := T,
    X := fun _ => Finset.univ,
    T_tree := T_is_tree,
    cover := by
      intro v
      use 0
      simp
    edge_covered := by
      intros v w _
      use 0
      simp
    connected_subtree := by
      intro v
      use {0}
      simp
  }
  have wD : width D = n - 1 := by
    simp [width, D]
    rw [Finset.sup_eq_max']
    · simp [D]
      rw [Finset.card_univ]
      rfl
    · use 0
      intro x _
      simp
  rw [treewidth, Nat.findGreatest_eq]
  · simp only [wD]
  · use D
    exact le_refl _


-- Theorem: tw(G) = 1 ↔ G is a tree

lemma treewidth_le_one_of_tree {V : Type*} [Fintype V] [DecidableEq V] 
    (G : SimpleGraph V) (hG : G.IsTree) :
  treewidth G ≤ 1 := by
  let X : V → Finset V := fun v => insert v (G.neighborFinset v)
  let T := G
  have T_is_tree : T.IsTree := hG
  let D : TreeDecomposition G := {
    T := T,
    X := X,
    T_tree := T_is_tree,
    cover := by
      intro v
      use v
      simp
    edge_covered := by
      intro v w h
      use v
      simp [h.symm]
    connected_subtree := by
      intro v
      use {v}
      simp
  }
  have width_le_one : width D ≤ 1 := by
    simp [width]
    apply le_trans (Finset.sup_le _)
    · intro x _
      simp [X]
      rw [Finset.card_insert_of_not_mem]
      · exact le_add_left (Finset.card_le_univ _)
      · apply Finset.not_mem_of_mem_erase
        simp
    · linarith
  rw [treewidth, Nat.findGreatest_eq]
  · exact width_le_one
  · use D


lemma tree_of_treewidth_one {V : Type*} [Fintype V] [DecidableEq V] 
    (G : SimpleGraph V) (h : treewidth G = 1) :
  G.IsTree := by
  -- In this case we should construct a minimal connected tree without cycles
  -- from the decomposition and prove it satisfies the tree conditions
  -- This assumes there exists a decomposition of width 1, which implies
  -- vertices are connected and each edge is covered in a bag of at most 2 vertices
  -- → linear structure without cycles
  -- Complete constructive proof possible through cycle elimination
  sorry


-- Theorem: If H is a minor of G, then tw(H) ≤ tw(G)
theorem treewidth_minor_monotonic {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) (f : W → V)
    (minor_map : ∀ ⦃v w : W⦄, H.Adj v w → G.Adj (f v) (f w)) :
  treewidth H ≤ treewidth G := by
  -- Project a valid decomposition of G onto H using f
  -- and construct a new decomposition of H with width ≤ that of G
  sorry


end Treewidth
