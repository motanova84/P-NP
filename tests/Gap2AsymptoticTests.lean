/-!
# Tests for Gap2_Asymptotic

This file contains tests demonstrating the usage of the Gap2_Asymptotic module
and verifying that the key theorems are accessible.
-/

import Gap2_Asymptotic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open AsymptoticLowerBounds
open Real

noncomputable section

/-! ## Test 1: Asymptotic notation definitions work -/

example : IsOmega (fun n => (n : ℝ) ^ 2) (log ∘ (↑)) := by
  intro C hC_pos
  use 2
  intro n hn
  sorry  -- Would prove n^2 dominates log n

/-! ## Test 2: Big-O notation is defined -/

example : IsBigO (fun n => (n : ℝ) ^ 2) (fun n => (n : ℝ) ^ 3) := by
  use 1, by norm_num
  use 1
  intro n hn
  sorry  -- Would prove n^2 = O(n^3)

/-! ## Test 3: Power epsilon dominates log -/

example : (fun n : ℕ => (n : ℝ) ^ (1/2)) = ω(log ∘ (↑)) := by
  apply pow_epsilon_dominates_log
  norm_num

/-! ## Test 4: Exponential growth theorem is accessible -/

example {f g : ℕ → ℝ} 
  (h_f_ge : ∀ n, f n ≥ g n)
  (h_g_omega : g = ω(log ∘ (↑)))
  (h_const : ∃ ε > 0, ∀ n, (2 : ℝ) ^ (log n) ≥ (n : ℝ) ^ ε) :
  ∃ ε > 0, f = ω(fun n => (n : ℝ) ^ ε) := by
  exact asymptotic_exponential_growth h_f_ge h_g_omega h_const

/-! ## Test 5: Gap2 superlog theorem is accessible -/

example {Π : ProblemInstance} {S : Separator Π}
  (h_κ : κ_Π > 0)
  (h_ic : ∀ (C : ℝ) (hC : C > 0), ∃ N, ∀ n ≥ N, 
    GraphIC (incidenceGraph Π) S n ≥ C * log (size Π n)) :
  ∃ (ε : ℝ) (hε : 0 < ε), RuntimeLowerBound Π := by
  exact gap2_superlog_implies_superpoly h_κ h_ic

/-! ## Test 6: SAT not in P theorem structure -/

example :
  (∃ (φ : CNFFormula) (S : Unit),
    ∀ (C : ℝ) (hC : C > 0), ∃ N, ∀ n ≥ N,
      (numVars φ : ℝ) ≥ C * log n) →
  SAT_Language ∉ P_Class := by
  exact sat_not_in_p_if_superlog_ic

/-! ## Test 7: P ≠ NP final theorem is accessible -/

example : P_Class ≠ NP_Class := by
  exact P_neq_NP_final

/-! ## Test 8: Tseitin hard instances exist -/

example :
  ∃ (φ : CNFFormula) (S : Unit),
    ∀ (C : ℝ) (hC : C > 0), ∃ N, ∀ n ≥ N,
      (numVars φ : ℝ) ≥ C * log n := by
  exact tseitin_hard_instances_exist

/-! ## Test 9: Runtime lower bound structure -/

example (Π : ProblemInstance) : 
  ∃ (R : RuntimeLowerBound Π), R.bound 10 ≥ 0 := by
  refine ⟨{
    bound := fun n => (n : ℝ)
    is_lower := fun n => by positivity
  }, by norm_num⟩

/-! ## Test 10: Omega not subset of Big-O -/

example {ε k : ℝ} (hε : ε > 0) 
  {f : ℕ → ℝ}
  (h_omega : f = ω(fun n => (n : ℝ) ^ ε))
  (h_bigO : f = O(fun n => (n : ℝ) ^ k)) :
  False := by
  exact omega_not_subset_of_bigO hε h_omega h_bigO

end
