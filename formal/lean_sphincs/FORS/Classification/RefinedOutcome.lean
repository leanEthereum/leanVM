module

public import FORS.Classification.WinRefined

@[expose] public section

/-! The refined classification keeps the finished, valid outcome of a winning run, as the bounds
on FORS contacts require. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.HiddenBridge

variable [Params]

open Concrete HiddenGraph

/-- The refined bad event of a finished run with a valid transcript. -/
def badAV (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (results : OtsKey → Option (Counter × Encoding)) (table : Coordinate → Digest)
    (v : ((Option HiddenBridge.Outcome × List Coordinate) × List (HiddenCost.Entry HashInput)) × QueryCache HashSpec) :
    Prop :=
  badA parameterOutput fixed highs remaining results table v ∧
    ∃ outcome, v.1.1.1 = some outcome ∧ SigningTranscript.Valid outcome.2.1

end FORS.Security.HiddenBridge
