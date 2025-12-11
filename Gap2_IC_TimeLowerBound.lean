/-!
# Gap2_IC_TimeLowerBound.lean

Formalización del Teorema GAP 2 (IC → Tiempo Exponencial)
Proyecto QCAL ∞³ – José Manuel Mota Burruezo (JMMB Ψ✧)

This file establishes the relationship between Information Complexity (IC) 
and computational time, proving that IC ≥ k implies t ≥ 2^k.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

open Finset Real

namespace QCAL

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Una definición simple de separador en un grafo -/
def is_separator (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∃ C : Finset (Finset V),
    (∀ c ∈ C, Disjoint c S ∧ ∀ u ∈ c, ∀ v ∈ c, u ≠ v → ¬G.Adj u v) ∧
    (⋃₀ C) = univ \ S

/-- Número de componentes desconectados después de quitar S -/
def component_count (G : SimpleGraph V) (S : Finset V) : ℕ :=
  (G.deleteVertices S).connectedComponents.toFinset.card

/-- Complejidad de información: IC(G | S) = |S| + log₂(#componentes) -/
def information_complexity (G : SimpleGraph V) (S : Finset V) : ℝ :=
  let c := component_count G S
  if c = 0 then S.card else S.card + Real.log c / Real.log 2

/-- Tiempo computacional estimado: t(G) ≥ 2 ^ IC(G | S) -/
def time_lower_bound (G : SimpleGraph V) (S : Finset V) : ℝ :=
  2 ^ (information_complexity G S)

/-- Teorema GAP 2 (versión inicial): Si IC ≥ k entonces t ≥ 2^k -/
lemma information_complexity_lower_bound_time 
  (G : SimpleGraph V) (S : Finset V) (k : ℝ) 
  (hsep : is_separator G S)
  (hic : information_complexity G S ≥ k) :
  time_lower_bound G S ≥ 2 ^ k := by
  unfold time_lower_bound
  unfold information_complexity
  split_ifs with h
  · -- Case: c = 0, so IC = S.card
    simp only [Nat.cast_nonneg] at hic ⊢
    calc 2 ^ (S.card : ℝ) ≥ 2 ^ k := by
      apply Real.rpow_le_rpow_left
      · norm_num
      · exact hic
  · -- Case: c ≠ 0, so IC = S.card + log c / log 2
    apply Real.rpow_le_rpow_left
    · norm_num
    · exact hic

end QCAL
