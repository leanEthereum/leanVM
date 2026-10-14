import Whir.PCSBCSSourceSavedRecordDecoder

/-! Executable fixtures exercise actual source frame bytes. These are decoder
fixtures, not valid algebraic WHIR proofs or a native-verifier refinement. -/
namespace Whir.PCSBCSSourceSavedRecordDecoderSmoke
open Concrete FiatShamirGame AnchoredHeaderCodec PCSBCSSourceSavedRecordDecoder

private def profile : ParameterBounds.Profile := (⟨0,by decide⟩,⟨0,by decide⟩)
private def digest (n : Nat) : Digest32 := fun i =>
  ⟨(n+i.val)%256,Nat.mod_lt _ (by decide)⟩
private def saved (n lanes : Nat) : Record :=
  let c := ParameterBounds.config profile
  { shape := ⟨c.logN,c.folds[0]!,c.rates[0]!,lanes⟩
    root := digest (n+17)
    context := { cv := digest (n+33)
                 pending := fun i => if i.val < (n+7)/8 then
                   some (UInt64.ofNat (101+i.val)) else none
                 pendingBytes := n
                 first := n%2 == 0
                 previous := UInt64.ofNat (n+7)
                 squeezed := UInt64.ofNat (n+11) }
    point := (List.range c.logN).map (fun i => E.ofK (UInt64.ofNat (i+n)))
    value := E.ofK (UInt64.ofNat (n+313)) }
private def entry (xs : List E) : FramedHistory :=
  WHIRHistory.encodeHistory ⟨digest 5,digest 9,
    [.absorb 0 [E.ofK 88],.nonce 24 0 0,.absorb 24 [E.ofK 90],
      .absorb 0 ([E.ofK 91,E.ofK 92] ++ xs)]⟩
private def require (label : String) (passed : Bool) : IO Unit := do
  unless passed do throw (IO.userError s!"saved-record decoder smoke failed: {label}")
  IO.println s!"saved-record decoder: {label}"

def smoke : IO Unit := do
  for n in [0,1,8,9,24,25,48,49,64] do
    for lanes in [1,2] do
      let r := saved n lanes
      require s!"valid adaptive metadata bytes={n} lanes={lanes}" (decide r.Valid)
      require s!"profile compatibility bytes={n} lanes={lanes}" (decide (Compatible profile r))
      require s!"full record byte recovery bytes={n} lanes={lanes}"
        (decide (decode profile (entry (openingScalars r)) = some r))
  let r := saved 25 2
  let xs := openingScalars r
  require "wrong marker rejected" (parse profile (xs.mapIdx (fun i x => if i = 0 then 0 else x))).isNone
  require "wrong shape rejected" (parse profile (xs.mapIdx (fun i x => if i = 1 then 0 else x))).isNone
  require "zero lanes rejected" (parse profile (xs.mapIdx (fun i x => if i = 2 then 0 else x))).isNone
  require "root padding rejected" (parse profile (xs.mapIdx (fun i x =>
    if i = 4 then ⟨x.c0,x.c1,1⟩ else x))).isNone
  require "metadata boolean rejected" (parse profile (xs.mapIdx (fun i x =>
    if i = 7 then ⟨x.c0,2,x.c2⟩ else x))).isNone
  require "pending padding rejected" (parse profile (xs.mapIdx (fun i x =>
    if i = 10 then ⟨x.c0,x.c1,1⟩ else x))).isNone
  require "truncated suffix rejected" (parse profile xs.dropLast).isNone
  require "extra suffix rejected" (parse profile (xs ++ [0])).isNone
  for d in [1,2,3] do
    require s!"suffix shift {d} cannot be another saved opening" (parse profile (xs.drop d)).isNone
  let malformed : FramedHistory := ⟨digest 5,digest 9,[.absorb 0 [⟨1,by decide⟩]]⟩
  require "non-scalar-aligned byte frame rejected" (decode profile malformed).isNone
  let emptyTail := {entry xs with frames := (entry xs).frames ++ [.absorb 0 []]}
  require "empty zero-consumption tail retains literal run"
    (decide (decode profile emptyTail = some r))

end Whir.PCSBCSSourceSavedRecordDecoderSmoke

def main : IO Unit := Whir.PCSBCSSourceSavedRecordDecoderSmoke.smoke
