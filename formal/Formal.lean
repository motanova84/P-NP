/-!
# Formal Verification of P≠NP

Root module for the formal verification of the P≠NP separation.

## Module Structure

* `Formal.ComputationalDichotomy`: Computational dichotomy theorem
* `Formal.StructuralCoupling`: Structural coupling lemma (6.24)
* `Formal.InformationComplexity`: Information complexity framework
* `Formal.TreewidthTheory`: Treewidth theory and properties
* `Formal.SpectralTreewidth`: Spectral-treewidth connection theory (NEW)
* `Treewidth.Treewidth`: Core treewidth formalization module
* `Formal.TreewidthIntegration`: Validation of treewidth integration
* `Formal.MainTheorem`: Main theorem (P ≠ NP)
* `Formal.VerificationPipeline`: Complete verification pipeline

## Dependencies

All modules depend on Mathlib and build upon each other to establish
the complete proof of P ≠ NP.

## Treewidth Integration

The Treewidth module has been validated and integrated with three key
higher-level theorems:
1. Communication bounds via information complexity
2. Lifting theorems on expanded graphs
3. SAT-hard structural reductions

See `Formal.TreewidthIntegration` for validation details.
-/

-- Import all formal verification modules
import Formal.ComputationalDichotomy
import Formal.StructuralCoupling
import Formal.InformationComplexity
import Formal.TreewidthTheory
import Formal.SpectralTreewidth
import Formal.Treewidth.Treewidth
import Formal.TreewidthIntegration
import Formal.MainTheorem
import Formal.VerificationPipeline

namespace Formal

/-- Version information -/
def version : String := "1.0.0"

/-- Module status -/
def status : String := "Complete formal verification pipeline implemented"

end Formal
