import Lake
open Lake DSL

package PNP

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.12.0"

lean_lib ComputationalDichotomy where
  roots := #[`ComputationalDichotomy]

lean_lib StructuralCoupling where
  roots := #[`StructuralCoupling]

lean_lib InformationComplexity where
  roots := #[`InformationComplexity]

lean_lib TreewidthTheory where
  roots := #[`TreewidthTheory]

lean_lib MainTheorem where
  roots := #[`MainTheorem]

lean_lib FormalVerification where
  roots := #[`FormalVerification]
  globs := #[.submodules `Treewidth, .submodules `Lifting, .submodules `LowerBounds]

lean_lib VerificationPipeline where
  roots := #[`VerificationPipeline]
lean_lib Formal where
  roots := #[`Formal]

@[default_target]
lean_exe pnp where
  root := `Director
