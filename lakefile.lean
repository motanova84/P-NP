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

lean_lib SpectralTheory where
  roots := #[`SpectralTheory]

lean_lib PNPSpectral where
  roots := #[`P_neq_NP_Spectral]
lean_lib GraphInformationComplexity where
  roots := #[`GraphInformationComplexity]

lean_lib HolographicComplexity where
  roots := #[`HolographicComplexity]
lean_lib HigherDimension where
  roots := #[`HigherDimension]

@[default_target]
lean_exe pnp where
  root := `Director
