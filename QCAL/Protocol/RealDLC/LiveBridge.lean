import Mathlib.Data.Real.Basic
import Mathlib.Data.UInt
namespace QCAL.Protocol.RealDLC
inductive DlcOutcome | buyerWins | sellerWins
structure RealDlcContract where buyerAddr : String; sellerAddr : String; fundingTxId : String; maxTimeout : UInt32
end QCAL.Protocol.RealDLC
