/-!
# Tests for Graph Information Complexity

This file contains tests demonstrating the usage of the GraphInformationComplexity module
and verifying that the key theorems are accessible.
-/

import GraphInformationComplexity
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Card

open GraphInformationComplexity

/-! ## Example: Small graph with a separator -/

-- Example with a finite vertex set
example : ∀ (V : Type) [Fintype V] [DecidableEq V] 
  (G : SimpleGraph V) 
  (S : Separator G)
  (h_sep : is_balanced_separator G S)
  (h_nonempty : Fintype.card V > 0),
  Nat.log 2 (total_configs G S) ≥ S.S.card / 2 := by
  intro V _ _ G S h_sep h_nonempty
  exact log_total_configs_lower_bound G S h_sep h_nonempty

/-! ## Verification that GraphIC is well-defined -/

example : ∀ (V : Type) [Fintype V] [DecidableEq V] 
  (G : SimpleGraph V) 
  (S : Separator G),
  GraphIC G S = Nat.log 2 (total_configs G S) := by
  intro V _ _ G S
  rfl

/-! ## Verification of the balanced separator bound -/

example : ∀ (V : Type) [Fintype V] [DecidableEq V]
  (G : SimpleGraph V)
  (S : Separator G)
  (h_sep : is_balanced_separator G S),
  S.S.card ≤ (2 * Fintype.card V) / 3 := by
  intro V _ _ G S h_sep
  exact balanced_separator_size_bound G S h_sep

/-! ## Direct proof variant -/

example : ∀ (V : Type) [Fintype V] [DecidableEq V]
  (G : SimpleGraph V)
  (S : Separator G)
  (h_sep : is_balanced_separator G S)
  (h_nonempty : Fintype.card V > 0),
  Nat.log 2 (2 ^ (Fintype.card V - S.S.card)) ≥ S.S.card / 2 := by
  intro V _ _ G S h_sep h_nonempty
  exact log_total_configs_lower_bound_direct G S h_sep h_nonempty

#check GraphIC
#check balanced_separator_size_bound
#check log_total_configs_lower_bound
#check log_total_configs_lower_bound_direct
