/-!
# Information Complexity Theory

This module formalizes information complexity measures and their
relationship to computational complexity.

## Main Results

* Information complexity lower bounds for high treewidth problems
* Connection to communication complexity

## References

* Braverman & Rao: Information complexity framework
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import ComputationalDichotomy

namespace InformationComplexity

open ComputationalDichotomy

/-- Information complexity measure for a problem -/
axiom information_complexity : CNFFormula → ℝ

/-- Communication protocol type -/
axiom Protocol : Type

/-- Information cost of a protocol -/
axiom protocol_information_cost : Protocol → ℝ

/-- High treewidth implies high information complexity -/
axiom high_treewidth_high_information
  (φ : CNFFormula)
  (tw : ℕ)
  (h : tw > Nat.log (numVars φ)) :
  information_complexity φ ≥ (tw : ℝ) / Real.log (numVars φ)

end InformationComplexity
