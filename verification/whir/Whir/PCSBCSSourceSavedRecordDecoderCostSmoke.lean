import Whir.PCSBCSSourceSavedRecordDecoderCost

/-! Deterministic executable fixtures for exact decoder erasure and reached
structural charges. Native execution is separate from the kernel proofs. -/
namespace Whir.PCSBCSSourceSavedRecordDecoderCostSmoke
open Concrete FiatShamirGame AnchoredHeaderCodec PCSBCSSourceSavedRecordDecoder
open PCSBCSSourceSavedRecordDecoderCost

private def profile : ParameterBounds.Profile := (⟨0,by decide⟩,⟨0,by decide⟩)
private def digest (n : Nat) : Digest32 := fun i =>
  ⟨(n+i.val)%256,Nat.mod_lt _ (by decide)⟩
private def saved (n : Nat) : Record :=
  let c := ParameterBounds.config profile
  { shape := ⟨c.logN,c.folds[0]!,c.rates[0]!,1⟩
    root := digest 17
    context := { cv := digest 33
                 pending := fun i => if i.val < (n+7)/8 then
                   some (UInt64.ofNat (101+i.val)) else none
                 pendingBytes := n
                 first := true
                 previous := 7
                 squeezed := 11 }
    point := (List.range c.logN).map (fun i => E.ofK (UInt64.ofNat i))
    value := E.ofK 313 }
private def entry (xs : List E) : FramedHistory :=
  WHIRHistory.encodeHistory ⟨digest 5,digest 9,
    [.absorb 0 [E.ofK 88],.nonce 24 0 0,.absorb 24 [E.ofK 90],
      .absorb 0 ([E.ofK 91,E.ofK 92] ++ xs),.absorb 0 []]⟩
private def require (label : String) (passed : Bool) : IO Unit := do
  unless passed do throw (IO.userError s!"saved-record cost smoke failed: {label}")
  IO.println s!"saved-record cost: {label}"
private def check (label : String) (h : FramedHistory) : IO Unit := do
  let counted := decodeCount profile h
  require s!"{label}: exact byte decoder erasure"
    (decide (counted.1 = decode profile h))
  require s!"{label}: physical polynomial"
    (counted.2 ≤ physicalPolynomial (physicalSize h))
  IO.println s!"saved-record cost: {label} physical={physicalSize h} charge={counted.2}"

/-- Charge for the reached metadata and profile guards, before opening work. -/
private def beforeOpening (xs : List E) (r : Record) : Nat :=
  reconstructCharge xs + validCharge r (xs.length-9) + 1 +
    compatibleCharge profile r + 1

def smoke : IO Unit := do
  for n in [0,1,8,9,24,25,48,49,64] do
    let r := saved n
    let xs := openingScalars r
    let h := entry xs
    check s!"positive pending bytes={n}" h
    require s!"positive full record bytes={n}" (decide ((decodeCount profile h).1 = some r))
    let parsed := parseCount profile xs
    require s!"positive exact parse charge bytes={n}"
      (parsed.2 == beforeOpening xs r + openingCharge r (xs.length-9) + 2*xs.length+2)
    require s!"positive pending caps bytes={n}"
      ((pendingPacks r.context).length ≤ 3 && (r.context.pendingBytes+7)/8 ≤ 8)
  let malformed : Frame := .absorb 0 [⟨1,by decide⟩]
  let early : FramedHistory := ⟨digest 5,digest 9,[malformed]⟩
  check "early malformed bytes" early
  require "early error charge is exactly six" ((decodeCount profile early).1.isNone && (decodeCount profile early).2 == 6)
  let ignored : Frame := WHIRHistory.encodeFrame (.absorb 0 (openingScalars (saved 64)))
  let earlyWithIgnored := {early with frames := [malformed,ignored]}
  check "early error skips later large frame" earlyWithIgnored
  require "unreached frame costs nothing" ((decodeCount profile earlyWithIgnored).2 == 6)
  let empty : FramedHistory := ⟨digest 5,digest 9,[]⟩
  check "short reconstruction all four candidates" empty
  require "empty entry exact four-candidate charge" ((decodeCount profile empty).1.isNone && (decodeCount profile empty).2 == 33)
  let earlier := WHIRHistory.encodeFrame (.absorb 0 [E.ofK 88])
  let afterPrefix := {early with frames := [earlier,malformed,ignored]}
  check "frame error after successful prefix" afterPrefix
  require "successful prefix and reached malformed frame exact charge"
    ((decodeCount profile afterPrefix).1.isNone && (decodeCount profile afterPrefix).2 == 1082)
  let remainder := {early with frames :=
    [.absorb 0 (WHIRHistory.scalarBytes [E.ofK 88] ++ [⟨1,by decide⟩]),ignored]}
  check "scalar decoded before nonempty remainder error" remainder
  require "nonempty byte remainder exact reached charge"
    ((decodeCount profile remainder).1.isNone && (decodeCount profile remainder).2 == 1079)
  let xs := openingScalars (saved 25)
  let mid := xs.mapIdx (fun i x => if i = 7 then ⟨65,x.c1,x.c2⟩ else x)
  check "mid invalid pending metadata" (entry mid)
  require "mid metadata rejects" (parseCount profile mid).1.isNone
  match reconstruct mid with
  | none => throw (IO.userError "mid reconstruction unexpectedly absent")
  | some r =>
    require "mid stops before profile/opening/equality"
      ((parseCount profile mid).2 == reconstructCharge mid + validCharge r (mid.length-9)+1)
  let mismatch := xs.mapIdx (fun i x => if i = 0 then 0 else x)
  check "late exact-opening marker mismatch" (entry mismatch)
  require "late mismatch rejects" (parseCount profile mismatch).1.isNone
  match reconstruct mismatch with
  | none => throw (IO.userError "late reconstruction unexpectedly absent")
  | some r =>
    require "late first scalar mismatch costs exactly two"
      ((equalCount (openingScalars r) mismatch).2 == 2)
    require "late reached opening and prefix comparison charge"
      ((parseCount profile mismatch).2 == beforeOpening mismatch r + openingCharge r (mismatch.length-9)+3)
  let tailMismatch := xs.mapIdx (fun i x => if i = 8 then ⟨x.c0,1,x.c2⟩ else x)
  check "late ninth scalar padding mismatch" (entry tailMismatch)
  match reconstruct tailMismatch with
  | none => throw (IO.userError "padding reconstruction unexpectedly absent")
  | some r =>
    require "ninth scalar mismatch charges reached nine cells"
      ((equalCount (openingScalars r) tailMismatch).2 == 18)
    require "ninth scalar mismatch exact full reached charge"
      ((parseCount profile tailMismatch).1.isNone &&
        (parseCount profile tailMismatch).2 == beforeOpening tailMismatch r + openingCharge r (tailMismatch.length-9)+19)
  let wrongProfile := xs.mapIdx (fun i x => if i = 1 then ⟨x.c0,x.c1,2⟩ else x)
  check "mid supported profile comparison mismatch" (entry wrongProfile)
  match reconstruct wrongProfile with
  | none => throw (IO.userError "profile reconstruction unexpectedly absent")
  | some r =>
    require "profile mismatch stops before exact opening"
      ((parseCount profile wrongProfile).1.isNone &&
        (parseCount profile wrongProfile).2 == beforeOpening wrongProfile r)
  let interrupted := {entry xs with frames := (entry xs).frames ++
    [WHIRHistory.encodeFrame (.nonce 0 0 0)]}
  check "nonce clears literal final run" interrupted
  require "nonce separator rejects saved suffix" (decodeCount profile interrupted).1.isNone

end Whir.PCSBCSSourceSavedRecordDecoderCostSmoke

def main : IO Unit := Whir.PCSBCSSourceSavedRecordDecoderCostSmoke.smoke
