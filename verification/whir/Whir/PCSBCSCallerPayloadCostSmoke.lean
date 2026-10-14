import Whir.PCSBCSCallerPayloadCost

/-! Actual source-token execution tests. Zero-valued arithmetic messages are
claim-projection fixtures, not honest verified proofs or a security endpoint. -/
namespace Whir.PCSBCSCallerPayloadCostSmoke
open Concrete FiatShamirGame AnchoredHeaderCodec
open WHIRCallerClaims hiding recPayload settledClaims
open PCSBCSCallerPayloadCost

local instance : Add E := ⟨E.add⟩
local instance : Mul E := ⟨E.mul⟩
local instance : Zero E := ⟨E.zero⟩
local instance : One E := ⟨E.one⟩
local instance (n : Nat) : OfNat E n := ⟨FieldModel.instCommRingE.natCast n⟩

private def require (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError label)

private def zeroToken : WHIRCallerShape.EventShape → CallerToken
  | .absorb _ => .sent 0
  | .squeeze _ => .draw 0
  | .nonce bits => .nonce bits (ByteCodec.encodeNat 24 0)

private def zeroCosts : OutputCosts := ⟨(fun _ => 0),(fun _ => 0),(fun _ => 0),(fun _ => 0)⟩
private def getterCosts : OutputCosts := ⟨(fun i => i.val + 3),(fun _ => 0),(fun _ => 0),(fun _ => 0)⟩

private def recLayout : RecLayout :=
  ⟨⟨[],[],[],0⟩,[],#[.committed 0 13],⟨0,6,7⟩,1⟩

private def cpuLayout : CpuLayout :=
  ⟨⟨[],[],[],0⟩,List.replicate 11 ⟨0,0,0,false,[],[]⟩,
    #[.committed 0 6],[⟨0,6,7⟩],[],0,(fun i => UInt64.ofNat i.val),1⟩

private def fixture (layout : CallerLayout) : List CallerToken :=
  ((WHIRCallerClaims.callerShape layout).drop (rootScalarCount layout)).map zeroToken

private def saved (layout : CallerLayout) : Record :=
  ⟨AnchoredSourceCaller.shape layout,ByteCodec.encodeNat 32 17,
    ⟨ByteCodec.encodeNat 32 19,(fun _ => none),0,true,0,0⟩,
    List.replicate (AnchoredSourceCaller.shape layout).logN 0,23⟩

def smoke : IO Unit := do
  let recTokens := fixture (.recursion recLayout)
  let rr := recPayload recLayout (recTokens ++ [.sent 29])
  require "recursion payload accepted and retains exact suffix" (match rr.result with
    | some ((families,points),rest) => families.length == 1 && points.size == 0 && rest == [.sent 29]
    | none => false)
  require "recursion source accepts same token execution" (WHIRCallerClaims.recPayload recLayout recTokens).isSome
  require "malformed recursion token rejected with positive reached work"
    ((recPayload recLayout [.sent 0]).result.isNone && (recPayload recLayout [.sent 0]).work > 0)
  let recSaved := saved (.recursion recLayout)
  let recFresh := recTokens ++ (openingScalars recSaved).map CallerToken.sent
  require "fresh recursion binding and exact schedule accepted"
    (freshInterpret (.recursion recLayout) recSaved getterCosts recFresh).value.isSome
  require "recursion has no opaque CPU getters"
    ((freshSourceClaims (.recursion recLayout) recSaved getterCosts recFresh).work ==
      (freshSourceClaims (.recursion recLayout) recSaved zeroCosts recFresh).work)
  let recOriginal := (headerScalars recSaved.shape recSaved.root).map CallerToken.sent ++
    recSaved.point.map CallerToken.draw ++ [.sent recSaved.value] ++ recFresh
  require "original anchored recursion receive and binding accepted" (match
    (sourceClaims (.recursion recLayout) recSaved.context getterCosts recOriginal).result with
    | some (claims,rest) => decide (claims.record = recSaved) && rest.isEmpty
    | none => false)
  let cpuTokens := fixture (.cpu cpuLayout)
  let cr := cpuPayload cpuLayout getterCosts (cpuTokens ++ [.sent 29])
  require "CPU payload accepted and emits five exit points" (match cr.result with
    | some ((families,points),rest) => families.length == 1 && points.size == 5 && rest == [.sent 29]
    | none => false)
  require "CPU fourth output is placed at register thirteen with original value" (match cr.result with
    | some ((_,points),_) => match points[4]? with
      | some (RingPCSGame.PointClaim.point _ point value) =>
        point.toList == [1,0,1,1,0,0] && value == E.ofK 3
      | _ => false
    | none => false)
  require "CPU source accepts same token execution" (WHIRCallerClaims.cpuPayload cpuLayout cpuTokens).isSome
  let base := cpuPayload cpuLayout zeroCosts cpuTokens
  let paid := cpuPayload cpuLayout getterCosts cpuTokens
  require "exactly four reached output getter invocations" (paid.work == base.work + 18)
  require "trace contains exactly the four output indices" (outputGetterTrace cpuLayout cpuTokens == List.finRange 4)
  let early := cpuPayload cpuLayout getterCosts [.sent 0]
  let earlyBase := cpuPayload cpuLayout zeroCosts [.sent 0]
  require "early CPU rejection does not invoke getters" (early.result.isNone && early.work == earlyBase.work)
  require "early failure getter trace is empty" (outputGetterTrace cpuLayout [.sent 0]).isEmpty
  let record := saved (.cpu cpuLayout)
  let freshTokens := cpuTokens ++ (openingScalars record).map CallerToken.sent
  let fresh := freshSourceClaims (.cpu cpuLayout) record getterCosts (freshTokens ++ [.sent 31])
  require "fresh source retains immutable record and suffix" (match fresh.result with
    | some (claims,rest) => decide (claims.record = record) && rest == [.sent 31]
    | none => false)
  require "fresh exact interpreter accepts complete source token form"
    (freshInterpret (.cpu cpuLayout) record getterCosts freshTokens).value.isSome
  require "fresh exact interpreter rejects leftover tokens"
    (freshInterpret (.cpu cpuLayout) record getterCosts (freshTokens ++ [.sent 31])).value.isNone
  require "fresh exact interpreter rejects inserted original header"
    (freshInterpret (.cpu cpuLayout) record getterCosts
      ((headerScalars record.shape record.root).map CallerToken.sent ++ freshTokens)).value.isNone
  require "fresh exact interpreter rejects resampled anchor"
    (freshInterpret (.cpu cpuLayout) record getterCosts
      (cpuTokens ++ record.point.map CallerToken.draw ++ (openingScalars record).map CallerToken.sent)).value.isNone
  let changed := {record with value := record.value + 1}
  let rejected := cpuTokens ++ (openingScalars changed).map CallerToken.sent
  let failPaid := freshSourceClaims (.cpu cpuLayout) record getterCosts rejected
  let failBase := freshSourceClaims (.cpu cpuLayout) record zeroCosts rejected
  require "binding rejection still charges four already reached getters"
    (failPaid.result.isNone && failPaid.work == failBase.work + 18)
  require "duplicate settled columns rejected" ((settledClaims
    [⟨0,0,2,true,[0,0],[]⟩] [] []).result.isNone)
  require "out of range settled column rejected" ((settledClaims
    [⟨0,0,1,true,[1],[]⟩] [] []).result.isNone)
  let settled := settledClaims [⟨0,0,3,true,[1],[]⟩] [] [.sent 7,.sent 9,.draw 11]
  require "settled ordinary and summed columns preserve order and rest" (match settled.result with
    | some ([claim],rest) => claim.evals == [7,0,9] && rest == [.draw 11]
    | _ => false)
  require "missing settled ordinary scalar rejected"
    ((settledClaims [⟨0,0,3,true,[1],[]⟩] [] [.sent 7]).result.isNone)
  let registered := {cpuLayout with registers := [⟨0,[0,1]⟩]}
  let registerRun := cpuPayload registered getterCosts cpuTokens
  require "real register slice traversal constructs its padded ring" (match registerRun.result with
    | some ((rings,points),rest) => rings.length == 2 && points.size == 5 && rest.isEmpty
    | _ => false)
  require "real source register interpreter agrees on acceptance"
    (WHIRCallerClaims.cpuPayload registered cpuTokens).isSome
  require "register success reaches all four output getters"
    ((outputGetterTrace registered cpuTokens).length == 4)
  require "empty register table list rejects before getters"
    ((cpuPayload {cpuLayout with registers := [⟨0,[]⟩]} getterCosts cpuTokens).result.isNone)
  require "out of range register table index rejected"
    ((cpuPayload {cpuLayout with registers := [⟨0,[20]⟩]} getterCosts cpuTokens).result.isNone)
  let mixed := {cpuLayout with tables :=
    [⟨0,0,0,false,[],[]⟩,⟨0,0,0,true,[],[]⟩] ++ List.replicate 9 ⟨0,0,0,false,[],[]⟩}
  require "non-prefix settled layout rejected after real table execution"
    ((cpuPayload mixed getterCosts (fixture (.cpu mixed))).result.isNone)
  let ground := {cpuLayout with bus := {cpuLayout.bus with grinding := 7}}
  require "wrong proof of work nonce rejected"
    ((cpuPayload ground getterCosts [.nonce 8 (ByteCodec.encodeNat 24 0)]).result.isNone)
  let preludeTokens := (List.replicate 11 (CallerToken.sent 0)) ++
    [.sent (E.ofK 1),.sent (E.ofK (UInt64.ofNat (2^40)))]
  let originalTokens := preludeTokens ++
    (headerScalars record.shape record.root).map CallerToken.sent ++ record.point.map CallerToken.draw ++
    [.sent record.value] ++ freshTokens
  let original := sourceClaims (.cpu cpuLayout) record.context getterCosts originalTokens
  require "original anchored CPU source accepts prelude header anchor payload and binding" (match original.result with
    | some (claims,rest) => decide (claims.record = record) && rest.isEmpty
    | none => false)
  require "bad CPU prelude clock rejected" ((prelude (.cpu cpuLayout)
    ((List.replicate 11 (CallerToken.sent 0)) ++ [.sent 1,.sent 0])).result.isNone)
  let pendingContext := {record.context with
    pendingBytes := 17
    pending := fun i => if i.val < 3 then some (UInt64.ofNat (i.val+1)) else none}
  let pendingRecord := {record with context := pendingContext}
  let metadataCosts := {getterCosts with
    pending := fun _ => 7
    rootByte := fun _ => 3
    contextByte := fun _ => 5}
  let pendingFrame := (openingScalars pendingRecord).map CallerToken.sent
  require "pending pack has exactly three reached word getters"
    ((pendingGetterTrace pendingContext).length == 3)
  require "one opening evaluates both digest projections and live pending words"
    (openingGetterWork pendingRecord metadataCosts == 533)
  let fullBinding := binding pendingRecord metadataCosts pendingFrame
  let fullBindingBase := binding pendingRecord getterCosts pendingFrame
  require "complete binding charges both reached metadata encodings"
    (fullBinding.result.isSome && fullBinding.work == fullBindingBase.work + 1066)
  let shortBinding := binding pendingRecord metadataCosts []
  let shortBindingBase := binding pendingRecord getterCosts []
  require "truncated binding charges only its reached first metadata encoding"
    (shortBinding.result.isNone && shortBinding.work == shortBindingBase.work + 533)
  let pendingFreshTokens := cpuTokens ++ pendingFrame
  let pendingFull := freshInterpret (.cpu cpuLayout) pendingRecord metadataCosts pendingFreshTokens
  let pendingBase := freshInterpret (.cpu cpuLayout) pendingRecord getterCosts pendingFreshTokens
  require "fresh full interpretation charges shape plus two binding encodings"
    (pendingFull.value.isSome && pendingFull.work == pendingBase.work + 1599)
  let rejectedShape := freshInterpret (.cpu cpuLayout) pendingRecord metadataCosts []
  let rejectedShapeBase := freshInterpret (.cpu cpuLayout) pendingRecord getterCosts []
  require "shape rejection still charges expected shape metadata but no CPU getter"
    (rejectedShape.value.isNone && rejectedShape.work == rejectedShapeBase.work + 533)
  let trace := freshInterpretGetterTrace (.cpu cpuLayout) pendingRecord pendingFreshTokens
  require "full interpretation traces exact reached accessor multiplicities"
    (trace.outputs.length == 4 && trace.pendingWords.length == 9 &&
      trace.rootBytes.length == 192 && trace.contextBytes.length == 192)
  require "weighted reached trace is exactly the full primitive fee delta"
    (trace.price metadataCosts == 1617 &&
      pendingFull.work ==
        (freshInterpret (.cpu cpuLayout) pendingRecord zeroCosts pendingFreshTokens).work +
          trace.price metadataCosts)
  let failedTrace := freshInterpretGetterTrace (.cpu cpuLayout) pendingRecord []
  require "shape rejection trace omits all unreached payload and binding accesses"
    (failedTrace.outputs.isEmpty && failedTrace.pendingWords.length == 3 &&
      failedTrace.rootBytes.length == 64 && failedTrace.contextBytes.length == 64)
  IO.println "counted caller payload: CPU, recursion, malformed forms, binding, suffixes, and four getter charges passed"

end Whir.PCSBCSCallerPayloadCostSmoke

def main : IO Unit := Whir.PCSBCSCallerPayloadCostSmoke.smoke
