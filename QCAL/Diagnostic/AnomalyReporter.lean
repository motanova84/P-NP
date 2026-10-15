import Mathlib.Data.Real.Basic
import Mathlib.Data.UInt
import QCAL.Gravity.Shield
namespace QCAL.Diagnostic.AnomalyReporter
open QCAL.Gravity.Shield
inductive AnomalyType | PassportLock : String → AnomalyType | CoherenceDrop : ℝ → AnomalyType | MassDivergence : ℝ → AnomalyType
structure AnomalyEvent where event_id : Nat; timestamp : UInt64; block_id : Nat; payload : AnomalyType
end QCAL.Diagnostic.AnomalyReporter
