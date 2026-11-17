module

public import LeanVM.Cost.AS.Newton
public import LeanVM.Protocol.Whir.Sound.DescentC
import all LeanVM.Protocol.Whir.Sound.DescentC
import all LeanVM.Protocol.Whir.Sound.DescentT
import all LeanVM.Protocol.Whir.Sound.DescentA
import all LeanVM.Protocol.Whir.Sound.StackA
import all LeanVM.Protocol.Whir.Sound.LowMsgC
import all Statement.Prover.Ntt

/-!
# The agreement-set extractor's descent, compiled

The descent in its compiled form (`Whir.Sound.DescentC`): the folds, the agreement sets, one-error
decoding over arrays, the descent within a level (`descRevC`) and across levels (`descendTraceC`,
with the step up a level by the additive NTT, `upAtA`), and level 0's stack (`stackA`). The
encodings of a fold round and of a WHIR trace, constructor by constructor.
-/

namespace LeanVM.Cost.AS

open LeanVM.Cost LeanVM.Parameters LeanVM.Protocol.Whir.Sound LeanVM.Protocol.Whir.Sound.Newton

public section

cost_enc LeanVM.Protocol.Verifier.FoldRound

/-- A trace's encoding, constructor by constructor. -/
@[expose] def encTrace : WhirTrace → MachineValue
  | .final rounds folded => .constructor 0 [encodeValue rounds, encodeValue folded]
  | .mid rounds high rest => .constructor 1 [encodeValue rounds, encodeValue high, encTrace rest]

@[instance_reducible] instance : MachineEncoding WhirTrace := ⟨encTrace⟩

cost_compile foldCAC := foldCA

cost_compile foldsCAC := foldsCA

cost_compile foldsACC := foldsAC

cost_compile agreeCC := agreeC

cost_compile winPtsCC := @winPtsC

cost_compile decFsC := @decFs

cost_compile valsOfC := valsOf

cost_compile badColsC := @badCols

cost_compile checkStageC := @checkStage

cost_compile decStageC := decStage

cost_compile newtonDecCC := newtonDecC

cost_compile descRevCC := descRevC

cost_compile novelAtHC := novelAtH

cost_compile polyOfAtHC := polyOfAtH

cost_compile msgAC := msgA

cost_compile upAtAC := upAtA

cost_compile descendTraceCC := descendTraceC

cost_compile stackAC := stackA

end

end LeanVM.Cost.AS
