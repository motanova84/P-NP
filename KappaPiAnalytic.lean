/-!
# Analytic κ_Π: Exact Proof via Monotonicity

This module defines the **analytic Millennium Constant**

  `κ_Π_analytic = ln(13) + ½ · ln(π / e)`

and proves `κ_Π_analytic > 2` using only native Mathlib real-analysis bounds —
no decimal approximations, no `sorry`.

## Key lemmas

* `exp2_lt_13`   — `Real.exp 2 < 13`
  Derived via `e < 3` (from `Real.exp_one_lt_d9`) and monotonicity:
  `e² < 3² = 9 < 13`.

* `e_lt_pi`      — `Real.exp 1 < Real.pi`
  Derived via `e < 3 < π` (using `Real.pi_gt_3141592`).

* `κ_Π_analytic_gt_two` — `2 < κ_Π_analytic`
  * `ln(13) > 2` because `13 > e²` and `ln` is monotone.
  * `½ · ln(π/e) > 0` because `π/e > 1`.
  * Sum: `ln(13) + ½ · ln(π/e) > 2 + 0 = 2`.

## Status: 0 sorries

∞³ 141.7001 Hz - JMMB Ψ
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Tactic

open Real

/-! ## 1. Definition -/

/--
`κ_Π_analytic`: the analytic Millennium Constant.

  κ_Π_analytic = ln(13) + ½ · ln(π / e)

This is the exact analytic form of the constant that appears in the spectral
entropy bound relating treewidth to information complexity.
-/
noncomputable def κ_Π_analytic : ℝ :=
  Real.log 13 + (1 / 2) * Real.log (Real.pi / Real.exp 1)

/-! ## 2. Bound: exp(2) < 13 -/

/--
`Real.exp 2 < 13`.

**Proof**: `e < 3` (from `Real.exp_one_lt_d9`), so `e² < 9 < 13`.
-/
theorem exp2_lt_13 : Real.exp 2 < 13 := by
  -- Step 1: e < 3  (Mathlib upper bound for exp 1)
  have h_e_lt_3 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  -- Step 2: exp(2) = (exp 1)²
  have h_e2 : Real.exp 2 = (Real.exp 1) ^ 2 := by
    rw [sq, ← Real.exp_add]; norm_num
  -- Step 3: (exp 1)² < 3² = 9
  have h_e2_lt_9 : Real.exp 2 < 9 := by
    rw [h_e2, sq]
    calc Real.exp 1 * Real.exp 1
        < 3 * 3 := mul_lt_mul'' h_e_lt_3 h_e_lt_3 (Real.exp_pos 1).le (Real.exp_pos 1).le
      _ = 9 := by norm_num
  -- Step 4: 9 < 13
  linarith

/-! ## 3. Bound: e < π -/

/--
`Real.exp 1 < Real.pi`.

**Proof**: `e < 3 < π`.
-/
theorem e_lt_pi : Real.exp 1 < Real.pi := by
  have h_e_lt_3 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  -- Real.pi_gt_3141592 : 3.141592 < Real.pi, so 3 < Real.pi
  have h_3_lt_pi : (3 : ℝ) < Real.pi := by linarith [Real.pi_gt_3141592]
  linarith

/-! ## 4. Main theorem: κ_Π_analytic > 2 -/

/--
**Theorem**: `2 < κ_Π_analytic`.

**Proof** (exact, via monotonicity):

1. `ln(13) > 2`:
   Because `13 > e²` (`exp2_lt_13`) and `ln` is strictly monotone on `(0, ∞)`:
   `2 = ln(e²) < ln(13)`.

2. `½ · ln(π/e) > 0`:
   Because `π/e > 1` (`e_lt_pi`) and `ln` is positive on `(1, ∞)`.

3. Combine: `2 < ln(13) < ln(13) + ½ · ln(π/e) = κ_Π_analytic`.
-/
theorem κ_Π_analytic_gt_two : 2 < κ_Π_analytic := by
  -- ① ln(13) > 2
  have h_log_13_gt_2 : 2 < Real.log 13 := by
    -- 2 = ln(e²) < ln(13) since e² < 13 and ln is monotone
    have h_log_e2 : Real.log (Real.exp 2) = 2 := Real.log_exp 2
    rw [← h_log_e2]
    exact Real.log_lt_log (Real.exp_pos 2) exp2_lt_13
  -- ② ½ · ln(π/e) > 0
  have h_spectral_pos : 0 < (1 / 2) * Real.log (Real.pi / Real.exp 1) := by
    -- π/e > 1 because e < π
    have h_div_gt_one : 1 < Real.pi / Real.exp 1 :=
      (one_lt_div (Real.exp_pos 1)).mpr e_lt_pi
    -- ln(π/e) > 0
    have h_log_pos : 0 < Real.log (Real.pi / Real.exp 1) :=
      Real.log_pos h_div_gt_one
    exact mul_pos (by norm_num) h_log_pos
  -- ③ Conclude: 2 < ln(13) < ln(13) + ½·ln(π/e) = κ_Π_analytic
  unfold κ_Π_analytic
  linarith

/--
`κ_Π_analytic` is positive.
-/
theorem κ_Π_analytic_pos : 0 < κ_Π_analytic :=
  lt_trans (by norm_num) κ_Π_analytic_gt_two

/--
`κ_Π_analytic` is greater than 1.
-/
theorem κ_Π_analytic_gt_one : 1 < κ_Π_analytic :=
  lt_trans (by norm_num) κ_Π_analytic_gt_two
