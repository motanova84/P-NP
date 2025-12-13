/-!
# Tests for OmegaNotation and graphic_lower_bound_case2

This file verifies that the OmegaNotation namespace and graphic_lower_bound_case2 lemma
are properly defined and can be used.
-/

import Formal.P_neq_NP

open Formal.P_neq_NP

/-! ## Test 1: OmegaNotation namespace is accessible -/

#check OmegaNotation.mul_const_pos_eq_self

-- Test that the axiom has the correct type
example {f : ℝ → ℝ} {c : ℝ} (hc : c > 0) (n : ℝ) :
    c * ω_notation f n = ω_notation f n := by
  exact OmegaNotation.mul_const_pos_eq_self hc n

/-! ## Test 2: graphic_lower_bound_case2 lemma is accessible -/

#check graphic_lower_bound_case2

/-! ## Test 3: The lemma has the expected signature -/

-- Verify the lemma takes the expected parameters
variable {V : Type*} [DecidableEq V] [Fintype V]
variable {G : SimpleGraph V} {S : Finset V} {n k : ℕ}

example 
    (h_high : (k : ℝ) = ω_notation (λ x => Real.log x) n)
    (h_κ_pos : 0 < κ_Π)
    (hS : BalancedSeparator G S)
    (h_k_eq : k = Treewidth.treewidth G) :
    (GraphIC G S : ℝ) ≥ ω_notation (λ x => Real.log x) n := by
  exact graphic_lower_bound_case2 h_high h_κ_pos hS h_k_eq

/-! ## Test 4: κ_Π is positive as required -/

example : 0 < κ_Π := by
  unfold κ_Π
  norm_num
