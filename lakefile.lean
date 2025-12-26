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

lean_lib TseitinHardFamily where
  roots := #[`TseitinHardFamily]

lean_lib HolographicDuality where
  roots := #[`HolographicDuality]
lean_lib VolumeIntegral where
  roots := #[`VolumeIntegral]
lean_lib PnPNeholographic where
  roots := #[`PnPNeholographic]
lean_lib FinalAxiom where
  roots := #[`FinalAxiom]
lean_lib UltimateUnification where
  roots := #[`UltimateUnification]
lean_lib Gap2_IC_TimeLowerBound where
  roots := #[`Gap2_IC_TimeLowerBound]
lean_lib GAP2 where
  roots := #[`GAP2_Complete]
lean_lib Gap2Asymptotic where
lean_lib GAP2Asymptotic where
  roots := #[`Gap2_Asymptotic]
lean_lib TuringMachine where
  roots := #[`TuringMachine]

lean_lib TEOREMAJMMB where
  roots := #[`TEOREMAJMMB]

lean_lib ComplexityClasses where
  roots := #[`ComplexityClasses]
lean_lib SAT where
  roots := #[`SAT]

lean_lib TseitinExpander where
  roots := #[`TseitinExpander]
lean_lib TreewidthToIC where
  roots := #[`TreewidthToIC]

lean_lib KappaSmallForIncidence where
  roots := #[`KappaSmallForIncidence]
lean_lib HolographicComplexity where
  roots := #[`HolographicComplexity]
lean_lib HigherDimension where
  roots := #[`HigherDimension]

lean_lib PhysicalConsistency where
  roots := #[`PhysicalConsistency]

lean_lib Gap2_Asymptotic where
  roots := #[`Gap2_Asymptotic]
lean_lib SevenStairs where
  roots := #[`SevenStairs]

@[default_target]
lean_exe pnp where
  root := `Director
