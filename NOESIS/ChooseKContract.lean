import Mathlib.Data.Nat.Basic

namespace NOESIS.Oracle

/-- A deterministic candidate selector for the oracle index. -/
def ChooseK := ℕ → ℕ

/-- The semantic decision obligation attached to a selector. -/
def CorrectChooseK (M : QCALModel) (isSAT : ℕ → Prop) (chooseK : ChooseK) : Prop :=
  ∀ N : ℕ, oracleAccepts M N (chooseK N) ↔ isSAT N

/-- Abstract cost model for executing a selector on an encoded input size. -/
structure CostModel where
  cost : ChooseK → ℕ → ℕ

/--
A polynomial-time certificate is a proof relative to an explicit cost model.
The predicate `IsPolynomial` is deliberately left as part of the contract so
that the eventual theorem cannot hide its representation or machine model.
-/
structure PolyTimeCertificate (C : CostModel) (chooseK : ChooseK) where
  polynomial : ℕ → ℕ
  isPolynomial : Prop
  bound : ∀ n, C.cost chooseK n ≤ polynomial n

/--
The P-NP oracle gap is closed only when the same selector has both semantic
correctness and an explicit, proved complexity certificate.
-/
structure VerifiedChooseK (M : QCALModel) (isSAT : ℕ → Prop) (C : CostModel) where
  chooseK : ChooseK
  correctness : CorrectChooseK M isSAT chooseK
  complexity : PolyTimeCertificate C chooseK

end NOESIS.Oracle
