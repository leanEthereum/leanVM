import Sphincs.SecurityHiddenCost
import Sphincs.SecuritySeedGuess

/-! `StopOr bad` holds of a stopped run, or of a finished run whose result is bad. -/

open OracleComp OracleSpec ENNReal
namespace Sphincs.Security.HiddenReveal
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 100000
attribute [local instance] Classical.propDecidable
variable {ι : Type} [Fintype ι]
noncomputable local instance : DecidableEq ι := Classical.decEq _

def StopOr {α : Type} (bad : α → Prop) : Option α → Prop
  | none => True
  | some value => bad value

end Sphincs.Security.HiddenReveal
