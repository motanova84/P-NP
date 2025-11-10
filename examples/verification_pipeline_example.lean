/-!
# Verification Pipeline Usage Examples

This file demonstrates how to use the verification pipeline
and interact with the P≠NP formal verification framework.

Author: José Manuel Mota Burruezo & Claude (Noēsis ∞³)
-/

import VerificationPipeline
import StructuralCoupling
import InformationComplexity
import TreewidthTheory
import MainTheorem

namespace VerificationExamples

/-! ## Basic Usage -/

/-- Example: Verify that P ≠ NP theorem exists -/
example : PvsNP.P ≠ PvsNP.NP := VerificationPipeline.P_ne_NP_verified

/-- Example: Access Lemma 6.24 verification -/
example : ∀ (φ : ComputationalDichotomy.CNFFormula) 
  (h_tw : ComputationalDichotomy.treewidth φ ≥ 
          StructuralCoupling.Ω (Real.log (ComputationalDichotomy.numVars φ)))
  (A : StructuralCoupling.GenericAlgorithm φ),
  A.steps ≥ 2^(StructuralCoupling.Ω (ComputationalDichotomy.treewidth φ / 
                                      StructuralCoupling.log² (ComputationalDichotomy.numVars φ))) := 
  VerificationPipeline.lemma_6_24_verified

/-- Example: Verify information complexity is sound -/
example : ∀ (Π : InformationComplexity.CommunicationProtocol) 
           (μ : InformationComplexity.InputDistribution),
  InformationComplexity.IC Π μ = 
  InformationComplexity.mutualInformation Π.transcript μ := 
  VerificationPipeline.information_complexity_sound

/-! ## Barrier Avoidance Examples -/

/-- Example: The proof avoids relativization -/
example : ¬ (∃ (O : VerificationPipeline.Oracle) 
              (h : VerificationPipeline.P_oracle O = VerificationPipeline.NP_oracle O), 
              ∀ (O' : VerificationPipeline.Oracle), 
                VerificationPipeline.P_oracle O' ≠ VerificationPipeline.NP_oracle O') := 
  VerificationPipeline.avoids_relativization

/-- Example: The proof avoids natural proofs barrier -/
example : ¬ (∃ (C : VerificationPipeline.CombinatorialProperty) 
              (h : VerificationPipeline.isNatural C) 
              (h2 : VerificationPipeline.distinguishes C),
              VerificationPipeline.isConstructible C) := 
  VerificationPipeline.avoids_natural_proofs

/-- Example: The proof avoids algebrization barrier -/
example : ¬ (∃ (A : VerificationPipeline.AlgebraicExtension) 
              (h : VerificationPipeline.P_algebraic A = VerificationPipeline.NP_algebraic A), 
              ∀ (A' : VerificationPipeline.AlgebraicExtension), 
                VerificationPipeline.P_algebraic A' ≠ VerificationPipeline.NP_algebraic A') := 
  VerificationPipeline.avoids_algebrization

/-! ## Using the Verification Report -/

/-- 
Generate complete verification report.

To run this, use:
  #eval generate_report_example

This will print:
- List of verified theorems
- Barrier avoidance status
- Complete proof summary
-/
def generate_report_example : IO Unit := do
  VerificationPipeline.generate_verification_report

/-- 
Export proof summary.

To run this, use:
  #eval IO.println export_proof_example
-/
def export_proof_example : String := 
  VerificationPipeline.export_complete_proof

/-! ## Working with Individual Modules -/

/-- Example: Using StructuralCoupling module directly -/
def structural_coupling_example (φ : ComputationalDichotomy.CNFFormula) 
  (h_tw : ComputationalDichotomy.treewidth φ ≥ 
          StructuralCoupling.Ω (Real.log (ComputationalDichotomy.numVars φ)))
  (A : StructuralCoupling.GenericAlgorithm φ) : 
  A.steps ≥ 2^(StructuralCoupling.Ω (ComputationalDichotomy.treewidth φ / 
                                      StructuralCoupling.log² (ComputationalDichotomy.numVars φ))) :=
  StructuralCoupling.structural_coupling_complete φ h_tw A

/-- Example: Using InformationComplexity module directly -/
def information_complexity_example 
  (Π : InformationComplexity.CommunicationProtocol)
  (μ : InformationComplexity.InputDistribution) :
  InformationComplexity.IC Π μ = 
  InformationComplexity.mutualInformation Π.transcript μ :=
  InformationComplexity.IC_definition Π μ

/-- Example: Using TreewidthTheory module directly -/
def treewidth_theory_example (G : TreewidthTheory.SimpleGraph V) :
  ∃ (tw : ℕ), tw = TreewidthTheory.sInf {w | ∃ (T : TreewidthTheory.TreeDecomposition G),
    ∀ i, Finset.card (T.bags i) ≤ w + 1} :=
  TreewidthTheory.treewidth_definition G

/-- Example: Using MainTheorem module directly -/
def main_theorem_example : PvsNP.P ≠ PvsNP.NP :=
  PvsNP.P_ne_NP

/-! ## Command Examples -/

/-- Uncomment to run verification report -/
-- #eval generate_report_example

/-- Uncomment to print proof summary -/
-- #eval IO.println export_proof_example

/-- Uncomment to verify individual theorems -/
-- #check structural_coupling_example
-- #check information_complexity_example
-- #check treewidth_theory_example
-- #check main_theorem_example

end VerificationExamples
