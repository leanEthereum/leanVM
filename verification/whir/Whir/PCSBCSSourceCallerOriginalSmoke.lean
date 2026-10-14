import Whir.PCSBCSSourceCallerOriginal

/-! Executable tests of the real source decoder and original preparation on the
lowest production profile. Zero prior-output bytes are explicit parser fixture
coins, not a claim of honest algebraic acceptance or deployed hash outputs.
Public fixture definitions also support the captured-source integration smoke. -/
namespace Whir.PCSBCSSourceCallerOriginalSmoke
open Concrete FiatShamirGame WHIRCallerClaims AnchoredHeaderCodec
open PCSBCSSourceCallerOriginal

-- Keep the executable canonical E dictionary used by caller payload smokes.
local instance : Add E := ⟨E.add⟩
local instance : Mul E := ⟨E.mul⟩
local instance : Zero E := ⟨E.zero⟩
local instance : One E := ⟨E.one⟩
local instance (n : Nat) : OfNat E n := ⟨FieldModel.instCommRingE.natCast n⟩

/-- logN=15, rate=1, read through the real production configuration. -/
def p : ParameterBounds.Profile := ⟨⟨0,by decide⟩,⟨0,by decide⟩⟩

def layout : CallerLayout :=
  .recursion ⟨⟨[],[],[],0⟩,[],#[.committed 0 13],⟨0,6,7⟩,1⟩

private def digest (n : Nat) : Digest32 :=
  fun i => ⟨(n / 256^i.val) % 256,Nat.mod_lt _ (by decide)⟩

/-- The saved anchor is independent of the fresh all-zero payload draws. -/
def saved : Record :=
  ⟨AnchoredSourceCaller.shape layout,digest 17,
    ⟨digest 19,(fun _ => none),0,true,0,0⟩,
    E.ofK 3 :: List.replicate 14 0,E.ofK 23⟩

private def zeroToken : WHIRCallerShape.EventShape → CallerToken
  | .absorb _ => .sent 0
  | .squeeze _ => .draw 0
  | .nonce bits => .nonce bits (ByteCodec.encodeNat 24 0)

def payloadTokens : List CallerToken :=
  ((WHIRCallerClaims.callerShape layout).drop (rootScalarCount layout)).map zeroToken

def tokens : List CallerToken :=
  payloadTokens ++ (openingScalars saved).map CallerToken.sent

def entry : FramedHistory := tokenHistory (digest 11) (digest 13) tokens

def answers : Coordinate → Digest32 := fun _ => digest 0

def originalInput : Option (PCSBCSCallerBinding.CallerInput p) :=
  original p layout saved entry answers

private def require (label : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"source-original smoke failed: {label}")
  IO.println s!"source-original: {label}"

/-- A two-word family at the last aligned occupied region. -/
def boundaryFamily : Fin 1 → RingPCSGame.FamilyClaim :=
  fun _ => ⟨8190,#[0],fun bit => E.ofK (UInt64.ofNat (bit.val + 1))⟩

def boundaryPoints : Array RingPCSGame.PointClaim :=
  #[.point 8190 #[0] (E.ofK 31),.strided 8188 1 1 #[0] (E.ofK 37)]

/-- Exercise preparation, not a source copy or a proof-only prepared value. -/
def smoke : IO Unit := do
  require "lowest real production profile and saved occupied prefix"
    ((ParameterBounds.config p).logN == 15 && (ParameterBounds.config p).folds[0]! == 6 &&
      (ParameterBounds.config p).rates[0]! == 1 && saved.shape.lanes == 16 && decide saved.Valid)
  let decoded ← match AnchoredSourceFreshCaller.decode layout saved entry answers with
    | none => throw (IO.userError "actual framed source decode rejected")
    | some claims => pure claims
  require "actual decoder retains saved record/root and emits original family"
    (decide (decoded.record = saved ∧ decoded.caller.root = saved.root) &&
      decoded.caller.families.length == 1 && decoded.caller.points.size == 0)
  let input ← match originalInput with
    | none => throw (IO.userError "actual source original preparation rejected")
    | some input => pure input
  require "returned caller has exact saved lanes and independent literal anchor"
    (input.lanes == 16 && input.m == 1 && input.points.size == 0 &&
      input.anchorPoint == saved.point.toArray && input.anchorValue == saved.value &&
      (if h : 0 < input.m then
        input.anchorPoint[0]! != (input.family ⟨0,h⟩).point[0]! else false))
  require "actual preparation materializes source family and saved anchor tables"
    (input.prepared.familyWeights.size == 1 && input.prepared.familyWeights[0]!.size == 32768 &&
      input.prepared.familyTargets[0]!.size == 64 && input.prepared.anchorTable.size == 32768 &&
      input.prepared.anchorClaim.weight.size == 32768 &&
      input.prepared.anchorClaim.value == saved.value && input.prepared.basisCache.size == 64 &&
      input.prepared.anchorTable[1]! == E.ofK 3 && input.prepared.anchorClaim.weight[8192]! == 0)
  let prepared ← match OriginalClaimsChecker.prepare (ParameterBounds.config p) saved.shape.lanes
      boundaryFamily boundaryPoints saved.point.toArray saved.value with
    | none => throw (IO.userError "valid plain/strided end-boundary original preparation rejected")
    | some prepared => pure prepared
  require "plain and strided last-region boundaries accepted and targets preserved"
    ((prepared.familyWeights[0]!)[8190]! == 1 && (prepared.familyWeights[0]!)[8192]! == 0 &&
      (prepared.familyTargets[0]!)[63]! == E.ofK 64 && prepared.pointClaims.size == 2 &&
      prepared.pointClaims[0]!.weight[8190]! == 1 &&
      prepared.pointClaims[1]!.weight[8189]! == 1 &&
      prepared.pointClaims[1]!.weight[8188]! == 0 &&
      prepared.pointClaims[0]!.value == E.ofK 31 && prepared.pointClaims[1]!.value == E.ofK 37)
  let badFamily : Fin 1 → RingPCSGame.FamilyClaim :=
    fun j => {boundaryFamily j with offset := 8191}
  require "misaligned original family rejected by existing prepare"
    (OriginalClaimsChecker.prepare (ParameterBounds.config p) 16 badFamily boundaryPoints
      saved.point.toArray saved.value).isNone
  let badPoints : List RingPCSGame.PointClaim :=
    [.point 8191 #[0] 0,.point 8192 #[0] 0,
      .point 0 (Array.replicate 16 0) 0,
      .strided 8188 2 1 #[0] 0,.strided 8190 1 1 #[0] 0,
      .strided 8192 1 1 #[0] 0,.strided 0 0 15 #[0] 0]
  for claim in badPoints do
    require "invalid plain/strided alignment, span, slot or dimension rejected"
      (OriginalClaimsChecker.prepare (ParameterBounds.config p) 16 boundaryFamily #[claim]
        saved.point.toArray saved.value).isNone
  require "saved anchor dimension checked independently"
    (OriginalClaimsChecker.prepare (ParameterBounds.config p) 16 boundaryFamily boundaryPoints
      #[E.ofK 3] saved.value).isNone
  require "zero and excess lanes rejected"
    ((OriginalClaimsChecker.prepare (ParameterBounds.config p) 0 boundaryFamily boundaryPoints
      saved.point.toArray saved.value).isNone &&
      (OriginalClaimsChecker.prepare (ParameterBounds.config p) 65 boundaryFamily boundaryPoints
        saved.point.toArray saved.value).isNone)
  let changed := {saved with value := E.ofK 24}
  let changedEntry := tokenHistory (digest 11) (digest 13)
    (payloadTokens ++ (openingScalars changed).map CallerToken.sent)
  require "actual constructor rejects changed saved binding frame"
    (original p layout saved changedEntry answers).isNone
  IO.println "source-original: actual decode/prepare and original guard regressions passed"

end Whir.PCSBCSSourceCallerOriginalSmoke

def main : IO Unit := Whir.PCSBCSSourceCallerOriginalSmoke.smoke
