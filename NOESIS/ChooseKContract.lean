import Mathlib.Data.Nat.Basic

namespace NOESIS.Oracle

/-- A deterministic candidate selector for the oracle index. -/
def ChooseK := ℕ → ℕ

/-- The semantic decision obligation attached to a selector. -/
def CorrectChooseK (M : QCALModel) (isSAT : ℕ → Prop) (chooseK : ChooseK) : Prop :=
  ∀ N : ℕ, oracleAccepts M N (chooseK N) ↔ isSAT N

/--
A complexity certificate is intentionally an abstract contract.
It does not assert that an implementation is polynomial; a concrete
certificate must provide the bound and its proof in the chosen cost model.
-/
structure PolyTimeCertificate (chooseK : ChooseK) where
  polynomial : ℕ → ℕ
  polynomial_nonnegative : ∀ n, 0 ≤ polynomial n
  bound : Prop

/--
The P-NP oracle gap is closed only when both semantic correctness and a
machine-checked complexity certificate are supplied for the same selector.
-/
structure VerifiedChooseK (M : QCALModel) (isSAT : ℕ → Prop) where
  chooseK : ChooseK
  correctness : CorrectChooseK M isSAT chooseK
  complexity : PolyTimeCertificate chooseK

end NOESIS.Oracle
