import Lake
open Lake DSL

package PNP

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.20.0"

lean_lib ComputationalDichotomy where
  roots := #[`ComputationalDichotomy]

lean_lib StructuralCoupling where
  roots := #[`StructuralCoupling]

lean_lib InformationComplexity where
  roots := #[`InformationComplexity]

lean_lib TreewidthTheory where
  roots := #[`TreewidthTheory]

lean_lib FormalVerification where
  roots := #[`FormalVerification]
  globs := #[.submodules `Treewidth, .submodules `Lifting, .submodules `LowerBounds, .submodules `StructuralCoupling]

lean_lib Treewidth where
  roots := #[`Treewidth]

lean_lib SimpleTreewidth where
  roots := #[`SimpleTreewidth]
lean_lib GraphTheory where
  roots := #[`GraphTheory]

lean_lib SpectralExpansion where
  roots := #[`SpectralExpansion]

lean_lib CycleTreeDecomposition where
  roots := #[`CycleTreeDecomposition]

lean_lib MainTheorem where
  roots := #[`PvsNP]
  globs := #[.submodules `formal]
lean_lib Formal where
  roots := #[`Formal]

lean_lib PNeqNPKappaPi where
  roots := #[`PNeqNPKappaPi]
lean_lib P_neq_NP where
  roots := #[`P_neq_NP]
lean_lib SpectralTheory where
  roots := #[`SpectralTheory]

lean_lib SpectralEntropy where
  roots := #[`SpectralEntropy]

lean_lib PNPSpectral where
  roots := #[`P_neq_NP_Spectral]
lean_lib GraphInformationComplexity where
  roots := #[`GraphInformationComplexity]

lean_lib EmpiricalEvidence where
  roots := #[`empirical_evidence]

lean_lib UltimateUnification where
  roots := #[`Ultimate_Unification]
lean_lib HolographicPnP where
  roots := #[`HolographicPnP]
lean_lib HolographicVolume where
  roots := #[`HolographicVolume]
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

lean_lib RuntimeLowerBounds where
  roots := #[`RuntimeLowerBounds]
lean_lib Gap2_Asymptotic where
  roots := #[`Gap2_Asymptotic]
lean_lib SevenStairs where
  roots := #[`SevenStairs]

lean_lib QCALPiTheorem where
  roots := #[`QCALPiTheorem]

lean_lib CY_RF_Construct where
  roots := #[`CY_RF_Construct]

lean_lib KappaPhiTheorem where
  roots := #[`KappaPhiTheorem]

lean_lib HolographicProofUnified where
  roots := #[`HolographicProofUnified]

lean_lib ExpanderTreewidth where
  roots := #[`ExpanderTreewidth]

lean_lib RamanujanGraphs where
  roots := #[`RamanujanGraphs]

lean_lib KappaPiExpander where
  roots := #[`KappaPiExpander]

lean_lib PetersenGraphDemo where
  roots := #[`PetersenGraphDemo]

lean_lib QCAL where
  roots := #[`QCAL.Core, `QCAL.Theorem]
lean_lib RamanujanGraph where
  roots := #[`RamanujanGraph]

lean_lib KappaExpander where
  roots := #[`KappaExpander]

lean_lib CompilationTests where
  roots := #[`CompilationTests]

lean_lib QCALDemonstration where
  roots := #[`QCAL_Demonstration]

lean_lib QCALUnifiedTheory where
  roots := #[`QCAL_Unified_Theory]

lean_lib CoherenceEconomy where
  roots := #[`CoherenceEconomy]

lean_lib TransitionAxioms where
  roots := #[`TransitionAxioms]

lean_lib PiCode1417ECON where
  roots := #[`PiCode1417ECON]

lean_lib PNPImpliesCS where
  roots := #[`PNPImpliesCS]

lean_lib CoherenceEconomyMain where
lean_lib PNPImpliesCS where
  roots := #[`PNPImpliesCS]

lean_lib CSMain where
  roots := #[`Main]

lean_lib ProofComplexity where
  roots := #[`ProofComplexity.Complexity]

@[default_target]
lean_exe pnp where
  root := `Principal
  root := `Director
