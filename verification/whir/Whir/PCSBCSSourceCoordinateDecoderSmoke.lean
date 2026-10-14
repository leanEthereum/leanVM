import Whir.PCSBCSSourceCoordinateDecoder

namespace Whir.PCSBCSSourceCoordinateDecoderSmoke
open Whir FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame DuplexPublicSimulator
open PCSBCSSourceCoordinateDecoder

local instance : DecidableEq Terminal := by
  intro a b
  cases a <;> cases b <;> simp <;> infer_instance

local instance : DecidableEq Coordinate := by
  intro a b
  cases a
  cases b
  simp only [Coordinate.mk.injEq]
  infer_instance

private def bytes (n salt : Nat) : List Byte :=
  (List.range n).map fun i => ⟨(i*17+salt)%256, Nat.mod_lt _ (by decide)⟩

private def digest (salt : Nat) : Digest32 := fun i =>
  ⟨(i.val*13+salt)%256, Nat.mod_lt _ (by decide)⟩

/-- Store compression replies as data before taking the next step. The log
contains real primitive inputs/replies only, never semantic recovery hints. -/
private def publicPath (cv : Digest32) (log : PublicLog) :
    List DuplexEncoding.Instruction → Option (PublicLog × Node)
  | [] => none
  | [(block,tweak)] => some (log,⟨cv,block,tweak,true⟩)
  | (block,tweak) :: next :: rest =>
    let node : Node := ⟨cv,block,tweak,true⟩
    let stored := Array.ofFn (blake2sOracle node)
    let answer : Digest32 := fun i => stored[i.val]'(by simp [stored])
    publicPath answer (observe log node answer) (next::rest)

private def key? (e : Extracted) : Option (RawKey 32) :=
  if hm : e.message.length ≤ 32 then
    if ht : e.template.length ≤ 32 then some (restrictKey 32 e hm ht) else none
  else none

private def rejects (e : Extracted) : Bool :=
  match key? e with
  | none => false
  | some key => (decode seedIV key).isNone

private def check (label : String) (passed : Bool) : IO Unit := do
  unless passed do throw (IO.userError (label ++ ": FAILED"))
  IO.println (label ++ ": ok")

private def coordinate (salt : Nat) (terminal : Terminal) : Coordinate :=
  ⟨⟨digest salt,digest (salt+11),
    [.absorb 7 (bytes 65 salt), .nonce 35 3 (fun i => ⟨(i.val+salt)%256, Nat.mod_lt _ (by decide)⟩),
      .absorb 0 (bytes 3 (salt+1))]⟩,terminal⟩

private def exercise (salt : Nat) (terminal : Terminal) : IO Unit := do
  let q := coordinate salt terminal
  let some (log,input) := publicPath seedIV [] (DuplexEncoding.plan q)
    | throw (IO.userError "empty public compression path")
  check "real-BLAKE2s public log coordinate recovery" (decide (recover 32 seedIV log input = some q))
  let some key := privateKey 32 log input
    | throw (IO.userError "missing public-log raw key")
  let e := expandKey key
  check "all coordinate data retained" (decide (decode seedIV key = some q))
  check "foreign seed IV rejected" ((decode (digest 199) key).isNone)
  let foreignTemplate := { e with template := e.template.map fun (_,last) => (UInt64.ofNat (10*2^56),last) }
  check "foreign template rejected" (rejects foreignTemplate)
  let badCounter := { e with template := e.template.modify 0 fun (t,last) => (t+1,last) }
  check "noncanonical counter rejected" (rejects badCounter)
  let badFlag := { e with template := e.template.modify 0 fun (t,_) => (t,false) }
  check "compression final flag rejected" (rejects badFlag)
  let badSeed := { e with message := e.message.map fun (cv,b) =>
    (cv.map (fun _ => digest 177),b) }
  check "foreign seed CV payload rejected" (rejects badSeed)
  check "truncated message rejected" (rejects { e with message := e.message.dropLast })
  check "truncated template rejected" (rejects { e with template := e.template.dropLast })
  check "truncated complete key rejected" (rejects
    { message := e.message.dropLast, template := e.template.dropLast })
  check "truncated public compression log rejected" ((recover 32 seedIV log.dropLast input).isNone)
  check "foreign public terminal flag rejected" ((recover 32 seedIV log { input with last := false }).isNone)
  check "foreign public terminal counter rejected" ((recover 32 seedIV log { input with tweak := input.tweak+1 }).isNone)
  IO.println ("actual terminal digest: " ++ DuplexCompression.hex (List.ofFn (blake2sOracle input)))

end Whir.PCSBCSSourceCoordinateDecoderSmoke

def main : IO Unit := do
  Whir.PCSBCSSourceCoordinateDecoderSmoke.exercise 19 (.output 3)
  Whir.PCSBCSSourceCoordinateDecoderSmoke.exercise 71 (.commitment 35)
  Whir.PCSBCSSourceCoordinateDecoderSmoke.exercise 121 (.powBase 47 5)
