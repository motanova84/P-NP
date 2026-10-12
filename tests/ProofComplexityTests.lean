import ProofComplexity.TseitinExpander
import ProofComplexity.EdgeExpansion

namespace ProofComplexityTests

open QCAL
open Real

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Test 1: Positivity of universal rigidity constant kappaPi. -/
example : 0 < kappaPi := kappaPi_pos

/-- Test 2: Heptagonal spectral anchor bounding fundamental harmonic mode. -/
example : Real.exp kappaPi > heptagonalFundamentalMode := kappaPi_spectral_anchor

/-- Test 3: Resolution size exponential lower bound from expander property. -/
example (φ : TseitinFormula V) {d : ℕ} {ε : ℝ} (hE : IsExpander φ.G d ε) :
    (ResSize φ : ℝ) ≥ Real.exp (kappaPi * (nVars φ)) :=
  tseitin_resolution_exp_lower_bound φ hE

/-- Test 4: Polynomial Calculus size exponential lower bound from expander property. -/
example (φ : TseitinFormula V) {d : ℕ} {ε : ℝ} (hE : IsExpander φ.G d ε) :
    (PCSize φ : ℝ) ≥ Real.exp (kappaPi * (nVars φ)) :=
  tseitin_pc_exp_lower_bound φ hE

/-- Test 5: Impossible parity lemma ensures unsatisfiability under odd charge. -/
example (φ : TseitinFormula V) (hOdd : isOddCharge φ.chi) :
    IsUnsatisfiable φ :=
  tseitin_impossible_parity_lemma φ hOdd

/-- Test 6: Unified QCAL spectral barrier theorem. -/
example (φ : TseitinFormula V) {d : ℕ} {ε : ℝ}
    (hE : IsExpander φ.G d ε) (hOdd : isOddCharge φ.chi) :
    IsUnsatisfiable φ ∧
    ((ResSize φ : ℝ) ≥ Real.exp (kappaPi * (nVars φ))) ∧
    ((PCSize φ : ℝ) ≥ Real.exp (kappaPi * (nVars φ))) :=
  qcal_spectral_barrier_unified φ hE hOdd

end ProofComplexityTests
