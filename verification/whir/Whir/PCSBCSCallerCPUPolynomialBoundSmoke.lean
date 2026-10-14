import Whir.PCSBCSCallerCPUPolynomialBound

/-! Finite executable checks of the actual counted CPU path and source erasure.
The zero arithmetic fixtures are projections, not security or honest-proof claims. -/
set_option autoImplicit false
namespace Whir.PCSBCSCallerCPUPolynomialBoundSmoke
open Concrete FiatShamirGame AnchoredHeaderCodec
open WHIRCallerClaims hiding cpuPayload
open PCSBCSCallerPayloadCost

local instance : Zero E := ⟨E.zero⟩
local instance (n : Nat) : OfNat E n := ⟨FieldModel.instCommRingE.natCast n⟩

private def require (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError label)

private def layout : CpuLayout :=
  ⟨⟨[],[],[⟨0,1,0⟩],0⟩,List.replicate 11 ⟨0,0,0,false,[],[]⟩,
    #[.committed 0 6],[⟨0,6,7⟩],[⟨0,[0,1]⟩],0,(fun i => UInt64.ofNat i.val),1⟩

private def tokens (l : CpuLayout) : List CallerToken :=
  ((WHIRCallerClaims.callerShape (.cpu l)).drop (rootScalarCount (.cpu l))).map fun event =>
    match event with
    | .absorb _ => .sent 0
    | .squeeze _ => .draw 0
    | .nonce bits => .nonce bits (ByteCodec.encodeNat 24 0)

private def costs : OutputCosts :=
  ⟨(fun i => i.val*i.val+3),(fun _ => 0),(fun _ => 0),(fun _ => 0)⟩

private def familyShape (rs : List RingPCSGame.FamilyClaim) : List (Nat × Array E) :=
  rs.map fun r => (r.offset,r.point)

private def pointShape : RingPCSGame.PointClaim → Nat × Nat × Nat × Nat × Array E × E
  | .point offset point value => (0,offset,0,0,point,value)
  | .strided offset slot stride point value => (1,offset,slot,stride,point,value)

private def checkFixture (label : String) (l : CpuLayout) (ts : List CallerToken)
    (beforeAccept payloadAccept : Bool) : IO Unit := do
  let before := cpuPayloadBeforeExit l ts
  let paid := cpuPayload l costs ts
  let base := cpuPayload l OutputCosts.zero ts
  let source := WHIRCallerClaims.cpuPayload l ts
  let volume := cpuLayoutVolume l
  require (label ++ ": before-exit outcome") (before.result.isSome == beforeAccept)
  require (label ++ ": payload outcome") (paid.result.isSome == payloadAccept)
  require (label ++ ": actual before-exit polynomial") (decide (before.work ≤ cpuBeforeExitWork volume))
  let getterWork := ((outputGetterTrace l ts).map costs.call).sum
  require (label ++ ": actual payload polynomial")
    (decide (paid.work ≤ cpuPayloadWorkPolynomial volume+getterWork))
  require (label ++ ": reached arbitrary output prices") (paid.work == base.work+getterWork)
  require (label ++ ": erasure outcome") (source.isSome == paid.result.isSome)
  match paid.result,source with
  | some ((rings,points),rest),some ((sourceRings,sourcePoints),sourceRest) =>
    require (label ++ ": erasure cursor and concrete claims")
      (rest == sourceRest && familyShape rings == familyShape sourceRings &&
        points.toList.map pointShape == sourcePoints.toList.map pointShape)
    require (label ++ ": exact actual family count")
      (rings.length == l.flock.length+l.bus.producers.length+l.registers.length)
    require (label ++ ": actual dimensions and cardinality")
      ((rings.all fun r => decide (r.point.size ≤ volume)) &&
        decide (points.size ≤ 3*volume*volume+5) &&
        (points.toList.all fun p => decide (cpuPointDimension p ≤ volume+6)))
  | none,none => pure ()
  | _,_ => throw (IO.userError (label ++ ": source/counter disagreement"))

def smoke : IO Unit := do
  let ts := tokens layout
  checkFixture "valid producer and nested register" layout ts true true
  checkFixture "valid retained suffix" layout (ts ++ [.sent 37]) true true
  checkFixture "early invalid token" layout [] false false
  checkFixture "mid invalid token" layout (ts.take (ts.length/2)) false false
  checkFixture "late invalid token" layout (ts.take (ts.length-1)) false false
  checkFixture "empty register early-return carrier" {layout with registers := [⟨0,[]⟩]} ts false false
  checkFixture "nested register missing lookup" {layout with registers := [⟨0,[0,50]⟩]} ts false false
  checkFixture "late placement rejection charges getters" {layout with placements := #[]} ts true false
  let settledBad := {layout with tables := [⟨0,0,1,true,[0,0],[]⟩] ++ layout.tables.drop 1}
  checkFixture "invalid settled layout" settledBad (tokens settledBad) false false
  let producerBad := {layout with bus := {layout.bus with producers := [⟨0,65,0⟩]}}
  checkFixture "producer padding rejects oversized evaluation" producerBad (tokens producerBad) false false
  IO.println "CPU polynomial smoke: valid producer/register; early/mid/late token/layout rejection; both actual counters, source erasure, dimensions, exact family count and reached arbitrary output prices checked"

end Whir.PCSBCSCallerCPUPolynomialBoundSmoke

def main : IO Unit := Whir.PCSBCSCallerCPUPolynomialBoundSmoke.smoke
