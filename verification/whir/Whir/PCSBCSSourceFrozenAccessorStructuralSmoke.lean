import Whir.PCSBCSSourceFrozenAccessorStructural

/-! Real BLAKE2s records are frozen unchanged. Invalid padding is produced by
hashed source images, never by mutating the frozen registry after extraction. -/
set_option autoImplicit false
namespace Whir.PCSBCSSourceFrozenAccessorStructuralSmoke
open Concrete Protocol CausalGame FiatShamirGame PCSBCSMerkleRootCache
open PCSBCSMerkleLeafImages PCSBCSSourceRootReferences PCSBCSSourceFrozenAccessor
open DuplexModeGame PublicMerkleLog

private def recordedTree (extension : Bool) (missing badPadding malformed : Option Nat) :
    Nat → Nat → Digest32 × DuplexPublicSimulator.PublicLog
  | 0, start =>
    let padding : K := if badPadding == some start then 9 else 0
    let live : K := UInt64.ofNat (10+start)
    let words : List K := if malformed == some start then [44] else
      if extension then [padding,live,20,30] else [padding,live]
    let bytes := ByteCodec.wordsBytes words
    (hashBlake2s bytes,if missing == some start then [] else plan blake2sOracle bytes)
  | height+1, start =>
    let left := recordedTree extension missing badPadding malformed height start
    let right := recordedTree extension missing badPadding malformed height (start+2^height)
    let bytes := List.ofFn (ByteCodec.pairBytes (left.1,right.1))
    (hashBlake2s bytes,left.2 ++ right.2 ++ plan blake2sOracle bytes)

private def check (label : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"source freeze structural: {label}")
  IO.println s!"source freeze structural PASS: {label}"

private def inspect (f : Frozen) (index : Nat) : Option Status := f.cells[index]?.map status

private def requireSelection (phase : Nat) (f : Frozen) (qs : Array Nat) : IO Selected :=
  match selectPhase phase f qs with
  | none => throw (IO.userError "source freeze structural: selection unexpectedly rejected")
  | some result => pure result

def smoke : IO Unit := do
  let s : Shape := ⟨1,2,1⟩
  let padded := recordedTree false none none none 1 0
  let ref : Reference := ⟨padded.1,s⟩
  let f := freeze padded.2 ref.root ref.shape
  check "actual padded source freeze passes structural and registry lookup checks"
    (structurallyValid ref f && (PCSBCSSourceFrozenAccessor.lookup (fun _ => some f) ref).isSome)
  check "source compact images preserve literal suffixes and rectangular sizes"
    (f.cells.size == 2 && f.raw == #[#[10],#[11]] &&
      f.raw == compactTable f.cells && f.raw.all (fun row => row.size == 1))
  let selected ← requireSelection 0 f #[1,0,1]
  check "padded repeated query traversal retains source order and flags"
    (selected.rows == #[#[E.ofK 11],#[E.ofK 10],#[E.ofK 11]] &&
      selected.cells.map status == #[⟨true,true⟩,⟨true,true⟩,⟨true,true⟩])
  let partialTree := recordedTree false (some 1) none none 1 0
  let partialRef : Reference := ⟨partialTree.1,s⟩
  let partialFrozen := freeze partialTree.2 partialRef.root s
  check "actual missing leaf passes structural lookup without upgrading ghost status"
    (structurallyValid partialRef partialFrozen &&
      (PCSBCSSourceFrozenAccessor.lookup (fun _ => some partialFrozen) partialRef).isSome &&
      inspect partialFrozen 1 == some ⟨false,false⟩ && partialFrozen.raw[1]! == #[0])
  let ghost ← requireSelection 0 partialFrozen #[1,0,1]
  check "selected unavailable duplicates remain zero and explicitly unauthenticated"
    (ghost.rows == #[#[0],#[E.ofK 10],#[0]] &&
      ghost.cells.map status == #[⟨false,false⟩,⟨true,true⟩,⟨false,false⟩])
  let bad := recordedTree false none (some 0) none 1 0
  let badRef : Reference := ⟨bad.1,s⟩
  let badFrozen := freeze bad.2 badRef.root s
  check "real hashed invalid padding remains structurally valid source storage"
    (structurallyValid badRef badFrozen &&
      (PCSBCSSourceFrozenAccessor.lookup (fun _ => some badFrozen) badRef).isSome &&
      inspect badFrozen 0 == some ⟨true,false⟩ && badFrozen.raw[0]! == #[10])
  check "only selected available bad padding rejects"
    ((selectPhase 0 badFrozen #[1,0,1]).isNone && (selectPhase 0 badFrozen #[1,1]).isSome)
  let malformed := recordedTree false none none (some 0) 1 0
  let malformedRef : Reference := ⟨malformed.1,s⟩
  let malformedFrozen := freeze malformed.2 malformedRef.root s
  check "real wrong-width source leaf becomes rectangular explicitly unavailable default"
    (structurallyValid malformedRef malformedFrozen &&
      inspect malformedFrozen 0 == some ⟨false,false⟩ && malformedFrozen.raw[0]! == #[0] &&
      (selectPhase 0 malformedFrozen #[0,1]).isSome)
  let absent := freeze [] padded.1 s
  check "wholly absent root is structural ghost storage rather than authenticated data"
    (structurallyValid ref absent && absent.raw == #[#[0],#[0]] &&
      inspect absent 0 == some ⟨false,false⟩ && inspect absent 1 == some ⟨false,false⟩ &&
      (selectPhase 0 absent #[0,1]).isSome)
  check "queried out-of-range index rejects" (selectPhase 0 f #[2]).isNone
  let extension := recordedTree true (some 1) (some 0) none 1 0
  let extensionShape : Shape := ⟨1,4,3⟩
  let extensionRef : Reference := ⟨extension.1,extensionShape⟩
  let extensionFrozen := freeze extension.2 extensionRef.root extensionShape
  check "extension source freeze accepts coexistence of invalid padding and missing cells"
    (structurallyValid extensionRef extensionFrozen && extensionFrozen.raw == #[#[10,20,30],#[0,0,0]])
  let extensionGhost ← requireSelection 1 extensionFrozen #[1,1]
  check "extension unavailable words decode into zero E with explicit ghost flags"
    (extensionGhost.rows == #[#[0],#[0]] &&
      extensionGhost.cells.map status == #[⟨false,false⟩,⟨false,false⟩] &&
      (selectPhase 1 extensionFrozen #[0]).isNone)
  let unfit : Reference := ⟨padded.1,⟨1,2,3⟩⟩
  check "occupied width exceeding image width is genuinely rejected"
    (!structurallyValid unfit (freeze padded.2 unfit.root unfit.shape))
  let noPadding : Reference := ⟨padded.1,⟨1,2,2⟩⟩
  check "zero-length padding and fully occupied source image pass construction checks"
    (structurallyValid noPadding (freeze padded.2 noPadding.root noPadding.shape))

end Whir.PCSBCSSourceFrozenAccessorStructuralSmoke

def main : IO Unit := Whir.PCSBCSSourceFrozenAccessorStructuralSmoke.smoke
