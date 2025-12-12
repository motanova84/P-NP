/-!
# Tests for Gap2 IC Time Lower Bound

This file contains tests demonstrating the usage of the Gap2_IC_TimeLowerBound module
and verifying that the key theorems are accessible.
-/

import Gap2_IC_TimeLowerBound
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Card

open QCAL

/-! ## Verification that the main lemma is well-defined -/

example : ∀ (V : Type*) [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) 
  (S : Finset V) 
  (k : ℝ)
  (hsep : is_separator G S)
  (hic : information_complexity G S ≥ k),
  time_lower_bound G S ≥ 2 ^ k := by
  intro V _ _ G S k hsep hic
  exact information_complexity_lower_bound_time G S k hsep hic

/-! ## Verification that definitions are accessible -/

example : ∀ (V : Type*) [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) 
  (S : Finset V),
  time_lower_bound G S = 2 ^ (information_complexity G S) := by
  intro V _ _ G S
  rfl

/-! ## Basic time complexity property -/

example : ∀ (V : Type*) [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) 
  (S : Finset V)
  (k : ℝ)
  (h : information_complexity G S = k),
  time_lower_bound G S = 2 ^ k := by
  intro V _ _ G S k h
  unfold time_lower_bound
  rw [h]

#check information_complexity_lower_bound_time
#check is_separator
#check component_count
#check information_complexity
#check time_lower_bound
