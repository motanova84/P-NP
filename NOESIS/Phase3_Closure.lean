import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace NOESIS.Closure

/-- Lema 1: Supresión polinómica de fuga off-diagonal con ε = 1 / n^p. -/
theorem off_diagonal_suppression (n p : ℕ) (hp : p ≥ 2) (hn : n ≥ 2) :
    let ε : ℝ := 1 / (n ^ p : ℝ)
    let leakage_rate : ℝ := ε ^ 2
    leakage_rate ≤ 1 / (n ^ 4 : ℝ) := by
  intro ε leakage_rate
  dsimp [leakage_rate, ε]
  have hn_nonneg : (0 : ℝ) ≤ n := by positivity
  have hn_pos : (0 : ℝ) < n := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hpow : (n : ℝ) ^ 4 ≤ (n : ℝ) ^ (2 * p) := by
    have hExp : (4 : ℕ) ≤ 2 * p := by nlinarith
    exact pow_le_pow_of_nonneg_left hn_nonneg hExp
  have h_inv : 1 / ((n : ℝ) ^ (2 * p)) ≤ 1 / ((n : ℝ) ^ 4) := by
    have hpos4 : 0 < (n : ℝ) ^ 4 := by exact pow_pos hn_pos 4
    exact one_div_le_one_div_of_le hpos4 hpow
  have h_sq : (1 / ((n : ℝ) ^ p)) ^ 2 = 1 / ((n : ℝ) ^ (2 * p)) := by
    rw [pow_two, one_div_mul_one_div]
    have hmul : (n : ℝ) ^ p * (n : ℝ) ^ p = (n : ℝ) ^ (p + p) := by
      simpa [pow_add]
    rw [hmul]
    congr
    omega
  rw [h_sq]
  exact h_inv

/-- Lema 2: Estabilidad del gap espectral con perturbación local. -/
theorem spectral_gap_stability (n p : ℕ) (hp : p ≥ 2) (hn : n ≥ 2) :
    let ε : ℝ := 1 / (n ^ p : ℝ)
    let Δ_eff : ℝ := 1 - 2 * ε
    Δ_eff ≥ 1 / 2 := by
  intro ε Δ_eff
  dsimp [Δ_eff, ε]
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn_nonneg : (0 : ℝ) ≤ n := by positivity
  have hn_sq_ge4 : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hpow : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ p := by
    exact pow_le_pow_of_nonneg_left hn_nonneg hp
  have hnp_ge4 : (4 : ℝ) ≤ (n : ℝ) ^ p := le_trans hn_sq_ge4 hpow
  have hε : 1 / ((n : ℝ) ^ p) ≤ 1 / 4 := by
    exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) hnp_ge4
  nlinarith

/-- Lema 3: Cota polinómica simple para dimensión de Krylov. -/
theorem krylov_poly_complexity (n : ℕ) (hn : n ≥ 1) :
    let T_star : ℝ := (n : ℝ) * Real.log 2 + Real.log 2
    let krylov_dim : ℕ := 2 * (n ^ 4)
    ∃ c : ℕ, (krylov_dim : ℝ) ≤ c * (n ^ 4 : ℝ) := by
  intro T_star krylov_dim
  refine ⟨2, ?_⟩
  dsimp [krylov_dim]
  push_cast
  ring

end NOESIS.Closure
