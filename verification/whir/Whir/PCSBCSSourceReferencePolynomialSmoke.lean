import Whir.PCSBCSSourceReferencePolynomialBound

namespace Whir.PCSBCSSourceReferencePolynomialSmoke
open Concrete Protocol FiatShamirGame DuplexRefinement WHIRHistory WHIRHistoryKey
open PCSBCSPublicLogParserCost PCSBCSSourceReferenceParserCost
open PCSBCSSourceReferencePolynomialBound

private def require (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)

 def smoke : IO Unit := do
  let p : ParameterBounds.Profile := (⟨0,by decide⟩,⟨0,by decide⟩)
  let c := ParameterBounds.config p
  let entry : FramedHistory := ⟨zeroDigest,zeroDigest,[]⟩
  let initial := outputKeyCount c entry [initialPending] 0
  let accepted := parsePendingKeyCount p entry initial.1
  require (accepted.1.isSome && initial.2 == 17 && accepted.2 > initial.2)
    "initial scheduled key did not succeed with its exact reconstruction charge"
  let rejected := parsePendingKeyCount p entry { initial.1 with terminal := .commitment 0 }
  require (rejected.1.isNone && rejected.2 == 5 && rejected.2 < accepted.2)
    "terminal rejection did not stop before scheduled reconstruction"
  let malformed : Coordinate := ⟨{entry with frames := [.nonce 0 1 (ByteCodec.encodeE (E.ofK 0))]},.output 0⟩
  let bad := parsePendingKeyCount p entry malformed
  require (bad.1.isNone && bad.2 > 0) "nonce-only rejection lost its parser charge"
  let packets : List Pending :=
    [⟨[E.ofK 0,E.ofK 1],some (3,E.ofK 2)⟩,⟨[E.ofK 3],none⟩,initialPending]
  let built := completedModelCount c zeroDigest zeroDigest packets
  let before := beforeModelCount c zeroDigest zeroDigest packets
  let output := outputKeyCount c entry packets 0
  require (pendingMass packets == 6 && built.2 > before.2 && output.2 > before.2)
    "scalar packets, nonce, or final framing were omitted"
  require (modelWireSize built.1 ≥ framesSize built.1.history.frames && built.2 > 2700)
    "literal scalar encoding or model byte/cursor mass was not charged"
  let costs : PCSBCSCallerPayloadCost.OutputCosts :=
    { call := fun _ => 0, pending := fun i => i.val+10,
      rootByte := fun _ => 0, contextByte := fun _ => 0 }
  let saved : AnchoredHeaderCodec.Record :=
    ⟨⟨2,1,1,1⟩,zeroDigest,⟨zeroDigest,fun _ => none,0,true,0,0⟩,[E.ofK 0,E.ofK 0],E.ofK 0⟩
  let valid := recordValidityCount saved costs
  require (valid.1 && valid.2.1.length == 8 && valid.2.2 == 210)
    "successful validity check omitted pending getter calls"
  let invalid := recordValidityCount {saved with context := {saved.context with pending := fun _ => some 0}} costs
  require (!invalid.1 && invalid.2.1.length == 1 && invalid.2.2 == 55)
    "pending validity rejection did not short-circuit"
  IO.println "source reference polynomial recurrence smoke PASS (success/rejection, scalar packets, nonce, frame/cursor volumes, explicit pending getters)"
end Whir.PCSBCSSourceReferencePolynomialSmoke

def main : IO Unit := Whir.PCSBCSSourceReferencePolynomialSmoke.smoke
