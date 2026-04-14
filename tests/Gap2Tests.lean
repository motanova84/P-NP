/-!
# Tests for Gap2_IC_TimeLowerBound

This file contains tests demonstrating the usage of the Gap2_IC_TimeLowerBound module
and verifying that the key theorems are accessible.
-/

import Gap2_IC_TimeLowerBound
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Card

open Classical
noncomputable section

/-! ## Example: Information Complexity is non-negative -/

example : ∀ (V : Type) [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) 
  (S : Finset V),
  IC(G, S) ≥ S.card := by
  intro V _ _ G S
  exact ic_monotone_in_components G S

/-! ## Verification that KAPPA_PI constant is defined -/

example : KAPPA_PI = 2.5773 := by rfl

/-! ## Main theorem is accessible -/

example : ∀ (V : Type) [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) 
  (S : Finset V) 
  (α : ℝ)
  (h_ic : IC(G, S) ≥ α),
  Time(G) ≥ 2 ^ α := by
  intro V _ _ G S α h_ic
  exact information_complexity_lower_bound_time G S α h_ic

/-! ## Expander property structure is accessible -/

example : ∀ (V : Type) [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) 
  (δ : ℝ),
  IsExpander G δ → 
  ∃ d : ℕ, ∀ v, G.degree v = d := by
  intro V _ _ G δ h_exp
  exact h_exp.regular

/-! ## Kappa Pi threshold theorem is accessible -/

example : ∀ (V : Type) [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) 
  (S : Finset V)
  (h_ic : IC(G, S) ≥ Fintype.card V / KAPPA_PI),
  Time(G) ≥ 2^(Fintype.card V / KAPPA_PI) := by
  intro V _ _ G S h_ic
  exact kappa_pi_threshold_theorem G S h_ic

end
