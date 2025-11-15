/-!
# Formal Verification of P≠NP

Root module for the formal verification of the P≠NP separation.

## Module Structure

* `Formal.ComputationalDichotomy`: Computational dichotomy theorem
* `Formal.StructuralCoupling`: Structural coupling lemma (6.24)
* `Formal.InformationComplexity`: Information complexity framework
* `Formal.TreewidthTheory`: Treewidth theory and properties
* `Formal.MainTheorem`: Main theorem (P ≠ NP)
* `Formal.VerificationPipeline`: Complete verification pipeline

## Dependencies

All modules depend on Mathlib and build upon each other to establish
the complete proof of P ≠ NP.
-/

-- Import all formal verification modules
import Formal.ComputationalDichotomy
import Formal.StructuralCoupling
import Formal.InformationComplexity
import Formal.TreewidthTheory
import Formal.MainTheorem
import Formal.VerificationPipeline

namespace Formal

/-- Version information -/
def version : String := "1.0.0"

/-- Module status -/
def status : String := "Complete formal verification pipeline implemented"

end Formal
