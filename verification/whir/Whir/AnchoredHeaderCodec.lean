import Whir.ByteCodec
import Whir.DuplexRefinement
import Whir.WHIRHistory

/-! Source hand-port of `pcs/src/whir/commit.rs` at 32c62977136d02cfaac106c1e363c922c1a50109. Context capture is read-only. The output cache is not a record field and cannot be installed through this interface. Digest halves use the deployed two-word/two-word packing. -/
namespace Whir.AnchoredHeaderCodec
open Concrete FiatShamirGame

structure Shape where
  logN : Nat
  logBatch : Nat
  logRate : Nat
  lanes : Nat
  deriving DecidableEq, Repr

def Shape.Valid (s : Shape) : Prop :=
  s.logBatch < s.logN ∧ s.logN < 64 ∧ 1 ≤ s.logRate ∧
    s.logN - s.logBatch + s.logRate < 64 ∧ 1 ≤ s.lanes ∧ s.lanes ≤ 2^s.logBatch

instance (s : Shape) : Decidable s.Valid := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

structure Context where
  cv : Digest32
  pending : Fin 8 → Option K
  pendingBytes : Nat
  first : Bool
  previous : UInt64
  squeezed : UInt64
  deriving DecidableEq

/-- This is exactly the native record metadata guard, not an arbitrary output-cache certificate. Reachable snapshots additionally have normalized partial words by construction. -/
def Context.Valid (c : Context) : Prop :=
  c.pendingBytes ≤ 64 ∧ ∀ i : Fin 8, (c.pending i).isSome = decide (i.val < (c.pendingBytes+7)/8)

instance (c : Context) : Decidable c.Valid := inferInstanceAs (Decidable (_ ∧ _))

/-- Missing bytes in the last live word are literal zero. No compression, finalization, sampler, or transcript mutation occurs. -/
def capture (s : DuplexRefinement.State) : Context :=
  { cv := s.cv
    pending := fun i => if i.val < (s.pending.size+7)/8 then
      some (ByteCodec.decodeK (fun j => s.pending[8*i.val+j.val]?.getD 0)) else none
    pendingBytes := s.pending.size
    first := s.first
    previous := UInt64.ofNat s.previous
    squeezed := UInt64.ofNat s.consumed }

theorem capture_valid (s : DuplexRefinement.State) (bounded : s.pending.size ≤ 64) :
    (capture s).Valid := by
  refine ⟨bounded,?_⟩
  intro i
  simp only [capture]
  by_cases h : i.val < (s.pending.size+7)/8 <;> simp [h]

theorem capture_cache_irrelevant (s : DuplexRefinement.State) (out : Digest32) :
    capture {s with output := out} = capture s := rfl

def anchorMarker : E := ⟨0x636e612d72696877,0x000031762d726f68,0⟩
def openingMarker : E := ⟨0x65706f2d72696877,0x0031762d676e696e,0⟩
def shapeScalar (s : Shape) : E :=
  ⟨UInt64.ofNat s.logN,UInt64.ofNat s.logBatch,UInt64.ofNat s.logRate⟩
def lanesScalar (s : Shape) : E := ⟨UInt64.ofNat s.lanes,0,0⟩

def headerScalars (s : Shape) (root : Digest32) : List E :=
  [anchorMarker,shapeScalar s,lanesScalar s,(ByteCodec.hashToScalars root).1,
    (ByteCodec.hashToScalars root).2]

@[simp] theorem headerScalars_length (s : Shape) (root : Digest32) :
    (headerScalars s root).length = 5 := rfl

theorem originalTransport_length (s : Shape) (root : Digest32) (value : E) :
    (headerScalars s root ++ [value]).length = 6 := rfl

def parseHeader (s : Shape) : List E → Option Digest32
  | [marker,shape,lanes,a,b] =>
      if marker = anchorMarker ∧ shape = shapeScalar s ∧ lanes = lanesScalar s then
        ByteCodec.scalarsToHash (a,b)
      else none
  | _ => none

@[simp] theorem parseHeader_header (s : Shape) (root : Digest32) :
    parseHeader s (headerScalars s root) = some root := by
  simp [parseHeader,headerScalars,ByteCodec.scalarsToHash_hashToScalars]

theorem parseHeader_sound (s : Shape) (values : List E) (root : Digest32)
    (parsed : parseHeader s values = some root) : values = headerScalars s root := by
  unfold parseHeader at parsed
  split at parsed
  next marker shape lanes a b =>
    split at parsed
    next matched =>
      obtain ⟨rfl,rfl,rfl⟩ := matched
      have exactRoot := ByteCodec.hashToScalars_scalarsToHash (a,b) root parsed
      have first := congrArg Prod.fst exactRoot
      have second := congrArg Prod.snd exactRoot
      simp only [headerScalars,first,second]
    next => contradiction
  next => contradiction

structure Record where
  shape : Shape
  root : Digest32
  context : Context
  point : List E
  value : E
  deriving DecidableEq

def Record.Valid (r : Record) : Prop := r.shape.Valid ∧ r.context.Valid ∧ r.point.length = r.shape.logN
instance (r : Record) : Decidable r.Valid := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Three consecutive live words per scalar, with K zero padding in the final partial pack. -/
def pendingPacks (c : Context) : List E :=
  (List.range ((c.pendingBytes+23)/24)).map fun i =>
    ⟨(c.pending ⟨3*i % 8,Nat.mod_lt _ (by decide)⟩).getD 0,
      if 3*i+1 < (c.pendingBytes+7)/8 then
        (c.pending ⟨(3*i+1)%8,Nat.mod_lt _ (by decide)⟩).getD 0 else 0,
      if 3*i+2 < (c.pendingBytes+7)/8 then
        (c.pending ⟨(3*i+2)%8,Nat.mod_lt _ (by decide)⟩).getD 0 else 0⟩

def openingScalars (r : Record) : List E :=
  [openingMarker,shapeScalar r.shape,lanesScalar r.shape,
    (ByteCodec.hashToScalars r.root).1,(ByteCodec.hashToScalars r.root).2,
    (ByteCodec.hashToScalars r.context.cv).1,(ByteCodec.hashToScalars r.context.cv).2,
    ⟨UInt64.ofNat r.context.pendingBytes,if r.context.first then 1 else 0,r.context.previous⟩,
    ⟨r.context.squeezed,0,0⟩] ++ pendingPacks r.context ++ r.point ++ [r.value]

theorem openingScalars_length (r : Record) :
    (openingScalars r).length = 10 + r.point.length + (r.context.pendingBytes+23)/24 := by
  simp only [openingScalars,List.length_append,List.length_cons,List.length_nil,
    pendingPacks,List.length_map,List.length_range]
  omega

theorem openingScalars_valid_length (r : Record) (valid : r.Valid) :
    (openingScalars r).length = 10 + r.shape.logN + (r.context.pendingBytes+23)/24 := by
  rw [openingScalars_length,valid.2.2]

inductive Error where
  | commitmentMismatch
  | malformedTranscript
  | cursorExhausted
  deriving DecidableEq, Repr

/-- Native read order: validate metadata and point/configuration before reading the frame. Missing transport is an error, not a zero-filled scalar; mismatch rejects before any batching challenge. -/
def verifyBinding (expected : Shape) (r : Record) (transport : List E) : Except Error (List E) :=
  if r.Valid ∧ r.shape = expected then
    let frame := openingScalars r
    if transport.length < frame.length then .error .malformedTranscript
    else if transport.take frame.length = frame then .ok (transport.drop frame.length)
    else .error .commitmentMismatch
  else .error .commitmentMismatch

theorem verifyBinding_honest (r : Record) (valid : r.Valid) (suffix : List E) :
    verifyBinding r.shape r (openingScalars r ++ suffix) = .ok suffix := by
  simp [verifyBinding,valid]

theorem verifyBinding_sound (expected : Shape) (r : Record) (transport rest : List E)
    (accepted : verifyBinding expected r transport = .ok rest) :
    r.Valid ∧ r.shape = expected ∧ transport = openingScalars r ++ rest := by
  unfold verifyBinding at accepted
  split at accepted
  next metadata =>
    dsimp only at accepted
    split at accepted
    next => contradiction
    next length =>
      split at accepted
      next same =>
        cases accepted
        refine ⟨metadata.1,metadata.2,?_⟩
        calc
          transport = transport.take (openingScalars r).length ++ transport.drop (openingScalars r).length :=
            (List.take_append_drop _ _).symm
          _ = openingScalars r ++ transport.drop (openingScalars r).length := by rw [same]
      next => contradiction
  next => contradiction

theorem verifyBinding_reject (expected : Shape) (r : Record) (transport : List E)
    (tampered : transport.take (openingScalars r).length ≠ openingScalars r) :
    ∀ rest, verifyBinding expected r transport ≠ .ok rest := by
  intro rest accepted
  have complete := (verifyBinding_sound expected r transport rest accepted).2.2
  rw [complete,List.take_left] at tampered
  exact tampered rfl

end Whir.AnchoredHeaderCodec
