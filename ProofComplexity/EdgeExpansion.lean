import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Finset.Card

namespace QCAL

open Finset

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Conjunto de aristas que cruzan el corte S | Sᶜ. -/
def edgeBoundary (G : SimpleGraph V) (S : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e =>
    match e with
    | ⟪u, v⟫ => (u ∈ S ∧ v ∉ S) ∨ (v ∈ S ∧ u ∉ S))

/-- Tamaño de la frontera de aristas. -/
def boundarySize (G : SimpleGraph V) (S : Finset V) : ℕ :=
  (edgeBoundary G S).card

open scoped Real

/-- Conjunto de subconjuntos válidos para expansión. -/
def validCuts (G : SimpleGraph V) : Set (Finset V) :=
  {S | 0 < S.card ∧ S.card ≤ (Fintype.card V) / 2}

/-- Expansión por aristas (edge expansion). -/
noncomputable def edgeExpansionCoeff (G : SimpleGraph V) : ℝ :=
  sInf
  { r : ℝ |
    ∃ S ∈ validCuts (G := G),
      r = (boundarySize G S : ℝ) / (S.card : ℝ) }

/-- G es expander si h(G) ≥ ε. -/
def IsEdgeExpander (G : SimpleGraph V) (ε : ℝ) : Prop :=
  ε ≤ edgeExpansionCoeff G

/-- Lema básico: cota de no negatividad para la expansión de aristas. -/
lemma edgeExpansion_nonneg (G : SimpleGraph V) :
  0 ≤ edgeExpansionCoeff G := by
  sorry

/-- Forma estructural que usarán los lower bounds. -/
structure ExpanderGraph (V : Type) [Fintype V] [DecidableEq V] :=
  (G : SimpleGraph V)
  (ε : ℝ)
  (hε : 0 < ε)
  (hexp : IsEdgeExpander G ε)

end QCAL
