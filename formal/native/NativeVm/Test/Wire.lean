import Native.Test.Run
import NativeVm.Wire.Code
import Statement.Fast.Keccak

/-!
# The wire decoder against `Proof.fromBytes`

`NativeVm.Wire.decode`, run on a proof's wire bytes, ends normally exactly when `Proof.fromBytes`
decodes them, and then holds what `Decoded` says of the decoded proof; `check` runs it on the bytes
and on truncated, extended and mutated copies (`cli/WireTest.lean`, on the fixtures
`export-verifier-fixtures-rust.sh` writes).
-/

namespace NativeVm.Test.WireTest

open Native Native.Test LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
open NativeVm NativeVm.Wire

/-- The context's address. -/
def ctxA : UInt64 := 0x10000
/-- The wire bytes' address. -/
def wireA : UInt64 := 0x100000
/-- The decoded area's address. -/
def decA : UInt64 := 0x1000000
/-- The working area's address. -/
def workA : UInt64 := 0x8000000

/-- The bytes packed little-endian into words, the last one zero-padded. -/
def packWords (bytes : ByteArray) : Array UInt64 := Id.run do
  let n := (bytes.size + 7) / 8
  let mut ws : Array UInt64 := Array.replicate n 0
  for i in [0:bytes.size] do
    ws := ws.modify (i / 8) fun w ↦ w ||| (bytes[i]!.toUInt64 <<< (8 * (i % 8)).toUInt64)
  ws

/-- The decoder's final memory, or `none` if it ended at the failure exit (`some none` if it got
stuck or ran out of fuel). -/
def runDecode (bytes : ByteArray) : Option (Option RState) := Id.run do
  let L := bytes.size
  let dn := decodedWords L
  let ws := packWords bytes
  let mut mem : Std.HashMap UInt64 UInt64 := {}
  for k in [0:128] do
    mem := mem.insert (ctxA + (8 * k).toUInt64) 0
  mem := mem.insert ctxA wireA
  mem := mem.insert (ctxA + 8) L.toUInt64
  mem := mem.insert (ctxA + 64) decA
  mem := mem.insert (ctxA + 72) dn.toUInt64
  mem := mem.insert (ctxA + 80) workA
  mem := mem.insert (ctxA + 88) workWords.toUInt64
  for i in [0:ws.size] do
    mem := mem.insert (wireA + (8 * i).toUInt64) ws[i]!
  for i in [0:dn] do
    mem := mem.insert (decA + (8 * i).toUInt64) 0xdeadbeef
  for i in [0:workWords] do
    mem := mem.insert (workA + (8 * i).toUInt64) 0
  let s : RState := ⟨(allRegs.map fun r ↦ if r = .rdi then ctxA else 0).toArray, mem⟩
  match run (2 ^ 40) decode s with
  | some (.ok s, _) => some (some s)
  | some (.err _, _) => some none
  | none => none

/-- The words `Decoded` fixes, by their index in the decoded area. -/
def expected (L : Nat) (π : Proof) : List (Nat × UInt64) :=
  [(0, π.stream.length.toUInt64)] ++
  (List.range π.stream.length).flatMap (fun i ↦
    [(1 + 2 * i, (eWords π.stream[i]!).getD 0 0), (2 + 2 * i, (eWords π.stream[i]!).getD 1 0)]) ++
  [(streamEnd L, π.openings.length.toUInt64)] ++
  (List.range π.openings.length).flatMap fun k ↦
    let phase := π.openings[k]!
    let base := phaseBase L k
    let h := (phase.head?.map fun o ↦ o.path.length).getD 0
    let width := (phase.head?.map fun o ↦ o.leaf.length).getD 0
    [(base, phase.length.toUInt64), (base + 1, h.toUInt64), (base + 2, width.toUInt64)] ++
    (List.range phase.length).flatMap fun j ↦
      let o := phase.getD j ⟨0, [], []⟩
      let ob := base + 3 + j * openingWords
      [(ob, o.leafIndex.toUInt64)] ++
      (List.range width).map (fun t ↦ (ob + 1 + t, (o.leaf.getD t 0).lane)) ++
      (List.range h).flatMap fun d ↦ (List.range 4).map fun l ↦
        (ob + 1 + LeanVM.Protocol.Compile.wireMaxLeafWords + 4 * d + l,
          (o.path.getD d default).toList.getD l 0)

/-- The decoder agrees with `Proof.fromBytes` on `bytes`: `none` if it does, else what differs. -/
def compare (bytes : ByteArray) : Option String :=
  let spec := Id.run (Proof.fromBytes (m := Id) keccakF1600 bytes.toList)
  match spec, runDecode bytes with
  | _, none => some "stuck or out of fuel"
  | none, some none => none
  | some _, some none => some "the code fails where fromBytes decodes"
  | none, some (some _) => some "the code decodes where fromBytes refuses"
  | some π, some (some s) =>
    let bad := (expected bytes.size π).filter fun (i, w) ↦ s.word (decA + (8 * i).toUInt64) != w
    if bad.isEmpty then none
    else some s!"{bad.length} decoded words differ, the first at word {bad.head!.1}"

/-- Whether `Proof.fromBytes` decodes `bytes`. -/
def decodes (bytes : ByteArray) : Bool :=
  (Id.run (Proof.fromBytes (m := Id) keccakF1600 bytes.toList)).isSome

/-- The copies of `bytes` the decoder is checked on: the bytes, truncated, extended, and with one
byte changed at positions spread over them. -/
def variants (bytes : ByteArray) : List (String × ByteArray) :=
  let L := bytes.size
  let flip (p : Nat) (x : UInt8) : ByteArray := bytes.set! p (bytes[p]! ^^^ x)
  [("as is", bytes), ("one byte short", bytes.extract 0 (L - 1)),
    ("half", bytes.extract 0 (L / 2)), ("three bytes", bytes.extract 0 3),
    ("one byte more", bytes.push 0)] ++
  ([0, 1, 3, 4, 16, 17].map fun p ↦ (s!"byte {p} changed", flip p 1)) ++
  ((List.range 16).map fun i ↦ let p := L * i / 16 + 7
    (s!"byte {p} changed", flip (min p (L - 1)) 0x10))

end NativeVm.Test.WireTest
