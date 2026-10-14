import Whir.PCSBCSCallerSchedulePolynomialBound

/-! Executable checks of actual CPU/recursive schedule construction and reached
parser rejection. Zero messages are projection fixtures, not valid proofs. -/
namespace Whir.PCSBCSCallerSchedulePolynomialBoundSmoke
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

private def baseRec : RecLayout :=
  ⟨⟨[],[],[],0⟩,[],#[.committed 0 13],⟨0,6,7⟩,1⟩
private def baseCpu : CpuLayout :=
  ⟨⟨[],[],[],0⟩,List.replicate 11 ⟨0,0,0,false,[],[]⟩,
    #[.committed 0 6],[⟨0,6,7⟩],[⟨0,[0,1]⟩],0,(fun i => UInt64.ofNat i.val),1⟩
private def zeroCosts : OutputCosts := ⟨(fun _ => 0),(fun _ => 0),(fun _ => 0),(fun _ => 0)⟩
private def prices : OutputCosts := ⟨(fun i => i.val+3),(fun _ => 7),(fun _ => 3),(fun _ => 5)⟩
private def saved (layout : CallerLayout) : Record :=
  ⟨AnchoredSourceCaller.shape layout,ByteCodec.encodeNat 32 17,
    ⟨ByteCodec.encodeNat 32 19,(fun _ => none),0,true,0,0⟩,
    List.replicate (AnchoredSourceCaller.shape layout).logN 0,23⟩

private def checkLayout (layout : CallerLayout) : IO Unit := do
  let shape := PCSBCSCallerPayloadCost.callerShape layout
  let n := layoutVolume layout
  require "actual caller schedule equals source" (shape.value == WHIRCallerClaims.callerShape layout)
  require "actual caller constructor work bound" (shape.work <= 10000*(n+1)^4)
  require "actual caller schedule length bound" (shape.value.length <= 10000*(n+1)^4)
  let r := saved layout
  let fresh := PCSBCSCallerPayloadCost.freshCallerShape layout r prices
  require "actual fresh schedule equals source"
    (fresh.value == AnchoredSourceFreshCaller.callerShape layout r)
  require "fresh mandatory accessor prices retained"
    (fresh.work == (PCSBCSCallerPayloadCost.freshCallerShape layout r zeroCosts).work+
      openingGetterWork r prices)
  let size := n+r.context.pendingBytes+r.point.length+1
  require "actual fresh work polynomial" (fresh.work <=
    30000*(size+1)^4+46*size+647+openingGetterWork r prices)
  require "actual fresh length polynomial" (fresh.value.length <= 10000*(size+1)^4+size+10)

def smoke : IO Unit := do
  for mu in [0,1,2,3,4,7,12] do
    let g := PCSBCSCallerPayloadCost.gkrShape mu
    require "zero odd even nested GKR source equality" (g.value == WHIRCallerClaims.gkrShape mu)
    require "actual GKR construction polynomial" (g.work <= 300*(mu+1)^2)
    require "actual nested GKR length polynomial" (g.value.length <= 300*(mu+1)^2)
  IO.println "actual zero/odd/even/nested GKR schedule checks passed"
  let unique : BusLayout := ⟨[⟨3,false,[.column 1,.column 2,.publicValue]⟩],[],[],7⟩
  let duplicate : BusLayout :=
    ⟨[⟨3,false,[.column 1,.column 2,.publicValue,.column 1]⟩],
      [⟨3,false,[.column 2,.tableExpression]⟩,⟨9,true,[.column 8]⟩],
      [⟨2,3,5⟩],7⟩
  require "framework dedup preserves first mention order"
    ((PCSBCSCallerPayloadCost.frameworkKeys duplicate).value == [(1,3),(2,3)])
  require "actual duplicate traversal is priced"
    ((PCSBCSCallerPayloadCost.frameworkKeys duplicate).work >
      (PCSBCSCallerPayloadCost.frameworkKeys unique).work)
  for bus in [unique,duplicate,⟨[],[],[],0⟩] do
    let n := PCSBCSCallerParserCost.busLayoutSize bus
    let keys := PCSBCSCallerPayloadCost.frameworkKeys bus
    require "actual dedup source equality" (keys.value == WHIRCallerClaims.frameworkKeys bus)
    require "actual dedup work polynomial" (keys.work <= 30*(n+1)^4)
    require "actual dedup length polynomial" (keys.value.length <= n^2)
    let shape := PCSBCSCallerPayloadCost.busShape bus
    require "actual bus source equality" (shape.value == WHIRCallerClaims.busShape bus)
    require "actual bus work polynomial" (shape.work <= 1500*(n+1)^4)
    require "actual bus length polynomial" (shape.value.length <= 1500*(n+1)^4)
  let airs : List AirLayout := [⟨4,7,1,[⟨1,3⟩,⟨5,2⟩]⟩,⟨2,0,9,[⟨12,0⟩]⟩]
  let cn := PCSBCSCallerParserCost.airLayoutsSize airs
  let constraints := PCSBCSCallerPayloadCost.constraintsShape airs
  require "fields and saturating malformed AIR source equality"
    (constraints.value == WHIRCallerClaims.constraintsShape airs)
  require "actual field schedule work polynomial" (constraints.work <= 200*(cn+1)^2)
  require "actual field schedule length polynomial" (constraints.value.length <= 200*(cn+1)^2)
  for flocks in [[],[⟨0,0,0⟩],[⟨0,6,7⟩,⟨3,9,8⟩],[⟨0,5,2⟩,⟨3,9,8⟩]] do
    let n := PCSBCSCallerParserCost.flockConfigurationSize flocks
    let shape := PCSBCSCallerPayloadCost.flockProgramShape flocks
    require "empty invalid and mixed flock schedule equality"
      (shape.value == WHIRCallerClaims.flockProgramShape flocks)
    require "actual flock construction work polynomial" (shape.work <= 2000*(n+1))
    require "actual flock construction length polynomial" (shape.value.length <= 2000*(n+1))
  IO.println "actual dedup, AIR fields, and mixed/invalid flock schedule checks passed"
  let complexRec := {baseRec with bus := duplicate, tables := [(3,⟨4,7,1,[⟨1,3⟩,⟨5,2⟩]⟩)]}
  let complexCpu := {baseCpu with
    bus := duplicate
    tables := [⟨1,4,7,true,[1,3],[⟨1,2⟩]⟩,⟨3,2,1,false,[9,9],[⟨9,0⟩]⟩]
    flock := [⟨0,6,7⟩,⟨3,9,8⟩]}
  for layout in [CallerLayout.recursion baseRec,.cpu baseCpu,.recursion complexRec,.cpu complexCpu,
      .recursion {complexRec with hash := ⟨0,0,0⟩},.cpu {complexCpu with flock := []}] do
    checkLayout layout
  IO.println "actual CPU/recursive and fresh schedule bounds passed"
  let recTokens := ((WHIRCallerClaims.callerShape (.recursion baseRec)).drop
    (rootScalarCount (.recursion baseRec))).map zeroToken
  let cpuTokens := ((WHIRCallerClaims.callerShape (.cpu baseCpu)).drop
    (rootScalarCount (.cpu baseCpu))).map zeroToken
  require "recursive actual payload accepts positive fixture" (recPayload baseRec recTokens).result.isSome
  require "recursive source accepts same fixture" (WHIRCallerClaims.recPayload baseRec recTokens).isSome
  require "CPU actual register traversal accepts positive fixture" (cpuPayload baseCpu prices cpuTokens).result.isSome
  require "CPU source accepts same register fixture" (WHIRCallerClaims.cpuPayload baseCpu cpuTokens).isSome
  let recSaved := saved (.recursion baseRec)
  let fresh := recTokens ++ (openingScalars recSaved).map CallerToken.sent
  require "exact fresh recursive interpreter accepts actual schedule"
    (freshInterpret (.recursion baseRec) recSaved prices fresh).value.isSome
  require "exact fresh interpreter rejects trailing scalar"
    (freshInterpret (.recursion baseRec) recSaved prices (fresh++[.sent 0])).value.isNone
  require "actual recursive truncation rejects with reached work"
    ((recPayload baseRec [.sent 0]).result.isNone && (recPayload baseRec [.sent 0]).work > 0)
  require "actual malformed duplicate settled columns reject"
    ((settledClaims [⟨0,0,2,true,[0,0],[]⟩] [] []).result.isNone)
  require "actual invalid flock boundary rejects"
    ((PCSBCSCallerParserCost.flockClaims [⟨0,5,2⟩] []).result.isNone)
  IO.println "actual source payload acceptance and malformed boundary rejection checks passed"
  let pendingContext := {recSaved.context with
    pendingBytes := 49
    pending := fun i => if i.val < 7 then some (UInt64.ofNat (i.val+1)) else none}
  let pending := {recSaved with context := pendingContext}
  let paid := PCSBCSCallerPayloadCost.freshCallerShape (.recursion complexRec) pending prices
  let free := PCSBCSCallerPayloadCost.freshCallerShape (.recursion complexRec) pending zeroCosts
  require "pending root and context accessors are mandatory exact prices"
    (paid.work == free.work+openingGetterWork pending prices && openingGetterWork pending prices > 0)
  let pendingSize := layoutVolume (.recursion complexRec)+pending.context.pendingBytes+
    pending.point.length+1
  require "actual saved pending point and frame volume work bound"
    (paid.work <= 30000*(pendingSize+1)^4+46*pendingSize+647+openingGetterWork pending prices)
  require "actual saved pending point and frame volume length bound"
    (paid.value.length <= 10000*(pendingSize+1)^4+pendingSize+10)
  IO.println "PCSBCSCallerSchedulePolynomialBoundSmoke: all actual schedule and boundary checks passed"

end Whir.PCSBCSCallerSchedulePolynomialBoundSmoke

def main : IO Unit := Whir.PCSBCSCallerSchedulePolynomialBoundSmoke.smoke
