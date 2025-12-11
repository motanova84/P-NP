import Lake
open Lake DSL

package PNP

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.20.0"

lean_lib ComputationalDichotomy where
  roots := #[`ComputationalDichotomy]

lean_lib InformationComplexity where
  roots := #[`InformationComplexity]

lean_lib TreewidthTheory where
  roots := #[`TreewidthTheory]

lean_lib FormalVerification where
  roots := #[`FormalVerification]
  globs := #[.submodules `Treewidth, .submodules `Lifting, .submodules `LowerBounds, .submodules `StructuralCoupling]

lean_lib Treewidth where
  roots := #[`Treewidth]

lean_lib Formal where
  roots := #[`Formal]

lean_lib GraphInformationComplexity where
  roots := #[`GraphInformationComplexity]

lean_lib EmpiricalEvidence where
  roots := #[`empirical_evidence]

lean_lib UltimateUnification where
  roots := #[`Ultimate_Unification]

@[default_target]
lean_exe pnp where
  root := `Director
