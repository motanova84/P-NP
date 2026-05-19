import Mathlib.Data.Real.Basic
import QCAL.Resonance.Bridge
namespace QCAL.Protocol.A2A
open QCAL.Resonance
structure Task where description : String; hash : String
structure A2AEscrow where buyer : String; seller : String; task : Task; btcAmount : ℕ; psi : ℝ
def IsReleaseable (escrow : A2AEscrow) (outcome : Bool) : Prop := outcome = true ∧ escrow.psi ≥ 0.999999
end QCAL.Protocol.A2A
