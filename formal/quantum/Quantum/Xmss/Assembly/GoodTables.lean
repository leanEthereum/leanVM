module

public import Quantum.Xmss.Assembly.EndReads
public import Quantum.Xmss.Assembly.TrialsOff

@[expose] public section

/-!
# The good tables of the event side

`GoodL`: EndReads' `TableGood` (`PermGood π 18`, honest paths sharing no cell) and no top-layer
trial block a programmable `k`-cell (`TrialsOff`). Security averages its per-table bounds over
`GoodL` and pays the fraction off it once.
-/

namespace Quantum.Xmss.Assembly

open Quantum.Xmss

/-- **The good tables of the event side**: EndReads' `TableGood` (`PermGood π 18`, honest paths
sharing no cell) and no top-layer trial block a programmable `k`-cell (`TrialsOff`). -/
def GoodL (L : HonestTable) : Prop :=
  TableGood L ∧ TrialsOff L

/-- The good tables, decided classically. -/
noncomputable instance instDecidablePredGoodL : DecidablePred GoodL :=
  Classical.decPred _

end Quantum.Xmss.Assembly

end
