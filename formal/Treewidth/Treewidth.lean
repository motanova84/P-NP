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


end Treewidth
