/-!
# Tests for Expander Separator Theory

This file contains basic tests and examples for the expander separator module.
-/

import Formal.Treewidth.ExpanderSeparators

namespace ExpanderSeparatorTests

open Treewidth.ExpanderSeparators
open Real

-- Test that constants are well-defined
example : 0 < κ_Π := κ_Π_pos

example : 1 < κ_Π := κ_Π_gt_one

example : κ_Π < 3 := κ_Π_lt_three

-- Test that α_optimal is well-defined
example : 0 < α_optimal := α_optimal_pos

example : α_optimal < 1 := α_optimal_lt_one

-- Test that α_optimal equals 1/κ_Π
example : α_optimal = 1 / κ_Π := rfl

-- Test basic properties of structures
section StructureTests

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

-- A balanced separator has the balanced property
example (S : Finset V) (h : BalancedSeparator G S) :
  ∀ C ∈ Components G S, C.card ≤ 2 * (Fintype.card V) / 3 := by
  exact h.balanced

-- An optimal separator is also balanced
example (S : Finset V) (h : OptimalSeparator G S) :
  BalancedSeparator G S := by
  exact h.toBalancedSeparator

-- An expander has positive expansion constant
example (h : IsKappaExpander G) :
  0 < h.expansion_constant := by
  rw [h.constant_eq]
  exact div_pos (by norm_num) κ_Π_pos

end StructureTests

-- Test theorem statements (without proving them fully here)
section TheoremTests

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

-- GAP 2: Expanders have large separators
example (h_exp : IsKappaExpander G) (S : Finset V) (h_bal : BalancedSeparator G S) :
  (S.card : ℝ) ≥ (Fintype.card V : ℝ) / (2 * κ_Π) := by
  exact kappa_expander_large_separator G h_exp S h_bal

-- GAP 3: Separator-treewidth relation with optimal constant
example (S : Finset V) (h_opt : OptimalSeparator G S) :
  α_optimal * (treewidth G : ℝ) ≤ (S.card : ℝ) ∧
  (S.card : ℝ) ≤ κ_Π * (treewidth G : ℝ) := by
  exact separator_treewidth_relation G S h_opt

-- GAP 4: Optimal separators minimize potential
example (S : Finset V) (h_opt : OptimalSeparator G S) :
  ∀ S' : Finset V, BalancedSeparator G S' →
    separator_potential G S ≤ separator_potential G S' := by
  exact optimal_separator_minimizes_potential G S h_opt

end TheoremTests

-- Test numerical properties
section NumericalTests

-- κ_Π properties
example : (1 : ℝ) / κ_Π < 1 := by
  calc (1 : ℝ) / κ_Π < 1 / 1 := by
      apply div_lt_div_of_pos_left
      · norm_num
      · norm_num
      · exact κ_Π_gt_one
    _ = 1 := by norm_num

-- α_optimal * κ_Π = 1
example : α_optimal * κ_Π = 1 := by
  unfold α_optimal
  field_simp
  ring

-- Relation between bounds
example (k : ℕ) (hk : 0 < k) :
  α_optimal * (k : ℝ) < κ_Π * (k : ℝ) := by
  have h1 : α_optimal < κ_Π := by
    calc α_optimal = 1 / κ_Π := rfl
      _ < κ_Π / κ_Π := by
        apply div_lt_div_of_pos_right
        · norm_num
        · exact κ_Π_pos
      _ = 1 := by field_simp
      _ < κ_Π := κ_Π_gt_one
  calc α_optimal * (k : ℝ)
    _ < κ_Π * (k : ℝ) := by
      apply mul_lt_mul_of_pos_right h1
      exact Nat.cast_pos.mpr hk

end NumericalTests

end ExpanderSeparatorTests
