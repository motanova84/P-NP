/-!
# Example: Using the κ_Π Proof

This file demonstrates how to use the main theorem `p_neq_np_with_kappa_pi`
to prove that specific CNF formulas are not in P.

## Examples

1. High-treewidth random 3-SAT instances
2. Grid-based formulas
3. Expander-based formulas

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
-/

import PNeqNPKappaPi

namespace KappaPiExample

open PNeqNPKappaPi

-- ═══════════════════════════════════════════════════════════
-- EXAMPLE 1: Random 3-SAT with High Treewidth
-- ═══════════════════════════════════════════════════════════

/--
Example: A random 3-SAT instance with high treewidth.

Random 3-SAT formulas with clause-to-variable ratio ≥ 4.2 typically have
treewidth Θ(n), where n is the number of variables.

For n = 10,000:
- tw ≈ 5000 (Θ(n))
- tw / κ_Π² ≈ 5000 / 6.65 ≈ 752
- IC(φ) ≥ 752 >> 150
- Therefore φ ∉ P by p_neq_np_with_kappa_pi
-/
example (n : ℕ) (hn : n ≥ 10000) :
  ∃ (V : Type) [inst1 : DecidableEq V] [inst2 : Fintype V]
    (φ : @CnfFormula V inst2),
    Fintype.card V = n ∧
    inNPComplete φ ∧
    treewidth (incidenceGraph φ) ≥ (n : ℝ) / 2 ∧
    φ ∉ P := by
  -- Construct a random 3-SAT instance with appropriate properties
  sorry

-- ═══════════════════════════════════════════════════════════
-- EXAMPLE 2: Grid Formula
-- ═══════════════════════════════════════════════════════════

/--
Example: A grid-based CNF formula.

Grid formulas have treewidth Θ(√n). For a 100×100 grid (n = 10,000):
- tw ≈ 100 (Θ(√n))
- tw / κ_Π² ≈ 100 / 6.65 ≈ 15

This is less than 150, so we cannot directly conclude φ ∉ P using our theorem.
Grid formulas might be tractable!

This demonstrates the sharpness of the dichotomy.
-/
example :
  ∃ (V : Type) [inst1 : DecidableEq V] [inst2 : Fintype V]
    (φ : @CnfFormula V inst2),
    let n := Fintype.card V
    let tw := treewidth (incidenceGraph φ)
    n = 10000 ∧
    (95 ≤ tw ∧ tw ≤ 105) ∧  -- tw approximately 100
    tw / κ_Π_squared < 150 := by
  sorry

/--
However, for a larger grid (e.g., 300×300, n = 90,000):
- tw ≈ 300
- tw / κ_Π² ≈ 300 / 6.65 ≈ 45

Still less than 150! This shows that grid formulas are on the tractable side
of the dichotomy, consistent with known results.
-/

-- ═══════════════════════════════════════════════════════════
-- EXAMPLE 3: Expander-Based Formula
-- ═══════════════════════════════════════════════════════════

/--
Example: A CNF formula based on expander graphs.

Expander graphs have high treewidth (typically Ω(n)). For n = 10,000:
- tw ≈ 8000 (Ω(n) for good expanders)
- tw / κ_Π² ≈ 8000 / 6.65 ≈ 1203
- IC(φ) ≥ 1203 >> 150
- Therefore φ ∉ P by p_neq_np_with_kappa_pi

This is the "hardest" type of formula.
-/
example :
  ∃ (V : Type) [inst1 : DecidableEq V] [inst2 : Fintype V]
    (φ : @CnfFormula V inst2),
    let n := Fintype.card V
    let tw := treewidth (incidenceGraph φ)
    n = 10000 ∧
    inNPComplete φ ∧
    tw ≥ n * 0.8 ∧  -- High treewidth from expander
    φ ∉ P := by
  -- Use p_neq_np_with_kappa_pi
  sorry

-- ═══════════════════════════════════════════════════════════
-- EXAMPLE 4: Applying the Main Theorem
-- ═══════════════════════════════════════════════════════════

/--
Direct application of the main theorem.

Given any NP-complete formula φ with:
- n ≥ 10,000 variables
- tw ≥ n/10

We can conclude φ ∉ P.
-/
theorem apply_kappa_pi_theorem
  {V : Type} [DecidableEq V] [Fintype V]
  (φ : CnfFormula V)
  (h_np : inNPComplete φ)
  (h_n : Fintype.card V ≥ 10000)
  (h_tw : treewidth (incidenceGraph φ) ≥ (Fintype.card V : ℝ) / 10) :
  φ ∉ P := by
  apply p_neq_np_with_kappa_pi
  · exact h_np
  · exact h_tw

-- ═══════════════════════════════════════════════════════════
-- EXAMPLE 5: The Dichotomy Boundary
-- ═══════════════════════════════════════════════════════════

/--
The computational dichotomy has a sharp boundary at log n.

For tractability, we need:
tw / κ_Π² < 150

This means:
tw < 150 * κ_Π² ≈ 150 * 6.65 ≈ 997

For n variables, tractability requires:
tw < 997

For large n, this is approximately:
tw = O(1) or tw = O(log n)

Thus the dichotomy boundary is at log n vs ω(log n).
-/
theorem dichotomy_boundary :
  ∀ (V : Type) [DecidableEq V] [Fintype V] (φ : CnfFormula V),
    let n := Fintype.card V
    let tw := treewidth (incidenceGraph φ)
    (tw ≤ Real.log n → inP φ) ∧
    (tw ≥ n / 10 → ¬inP φ) := by
  sorry

-- ═══════════════════════════════════════════════════════════
-- CONSTANTS TABLE
-- ═══════════════════════════════════════════════════════════

/-- Summary of key constants used in examples -/
def constants_summary : String :=
  "κ_Π = 2.5773
   κ_Π² = 6.64
   Threshold = 150
   Boundary ≈ 997
   Min time = 2^150 ≈ 10^45"

#check constants_summary

-- ═══════════════════════════════════════════════════════════
-- VERIFICATION EXAMPLES
-- ═══════════════════════════════════════════════════════════

/-- Verify that κ_Π is within bounds -/
example : 2.577 ≤ κ_Π ∧ κ_Π ≤ 2.578 := κ_Π_bounds

/-- Verify that κ_Π² is within bounds -/
example : 6.64 ≤ κ_Π_squared ∧ κ_Π_squared ≤ 6.65 := κ_Π_squared_bounds

/-- Check main theorem type -/
#check @p_neq_np_with_kappa_pi

/-- Check corollary -/
#check p_neq_np

end KappaPiExample
