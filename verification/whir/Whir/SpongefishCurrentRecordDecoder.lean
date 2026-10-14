import Whir.SpongefishRecordBindingParser
import Mathlib.Data.List.OfFn

/-! Literal raw32 saved-record recovery for the current opening grammar.
This is a public-byte parser, not Rust acceptance or failed-read poisoning. -/
namespace Whir.SpongefishCurrentRecordDecoder
open Concrete FiatShamirGame SpongefishSessionAdapter SpongefishPCSRoundFrames
set_option autoImplicit false

/-- Exactly the normalized byte image, including all padding after the live suffix. -/
theorem pending_image (ctx : Context) :
    scalarsBytes (pendingPacks ctx) =
      List.ofFn (fun i : Fin (((ctx.pending.length+23)/24)*24) => ctx.pending[i.val]?.getD 0) := by
  have chunks := List.ofFn_mul
    (fun i : Fin (((ctx.pending.length+23)/24)*24) => ctx.pending[i.val]?.getD 0)
  unfold scalarsBytes pendingPacks
  rw [List.flatMap_def,List.map_ofFn]
  change (List.ofFn (fun i : Fin ((ctx.pending.length+23)/24) =>
    scalarBytes (ByteCodec.decodeE (fun j => ctx.pending[24*i.val+j.val]?.getD 0)))).flatten = _
  simp only [scalarBytes,ByteCodec.encodeE_decodeE]
  simpa only [Nat.mul_comm] using chunks.symm

theorem pending_recovery (ctx : Context) :
    (scalarsBytes (pendingPacks ctx)).take ctx.pending.length = ctx.pending := by
  rw [pending_image]
  have ample : ctx.pending.length ≤ ((ctx.pending.length+23)/24)*24 := by omega
  apply List.ext_getElem
  · simp only [List.length_take,List.length_ofFn,Nat.min_eq_left ample]
  · intro i _ within
    simp only [List.getElem_take,List.getElem_ofFn,List.getElem?_eq_getElem within,Option.getD_some]

def scalars : Nat → List Byte → Option (List E × List Byte)
  | 0,bytes => some ([],bytes)
  | n+1,bytes => do
    let (value,bytes) ← scalarCodec.parse bytes
    let (tail,rest) ← scalars n bytes
    pure (value::tail,rest)

theorem scalars_source (n : Nat) (source rest : List Byte) (values : List E)
    (accepted : scalars n source = some (values,rest)) :
    values.length = n ∧ source = scalarsBytes values ++ rest := by
  induction n generalizing source rest values with
  | zero =>
    simp only [scalars,Option.some.injEq,Prod.mk.injEq] at accepted
    obtain ⟨rfl,rfl⟩ := accepted
    exact ⟨rfl,rfl⟩
  | succ n ih =>
    simp only [scalars] at accepted
    obtain ⟨⟨value,bytes⟩,readValue,accepted⟩ := Option.bind_eq_some_iff.mp accepted
    dsimp only at accepted
    obtain ⟨⟨tail,after⟩,readTail,accepted⟩ := Option.bind_eq_some_iff.mp accepted
    dsimp only at accepted
    have tailResult := ih bytes after tail readTail
    have equal := Option.some.inj accepted
    cases equal
    obtain ⟨length,remaining⟩ := tailResult
    have before := Codec.canonical_read scalarCodec source bytes value readValue
    rw [remaining] at before
    exact ⟨by simpa only [List.length_cons] using congrArg Nat.succ length,
      by simpa only [scalarsBytes,List.flatMap_cons,List.append_assoc,Codec.bytes,
        scalarCodec,scalarBytes] using before⟩

theorem scalars_encoded (values : List E) (rest : List Byte) :
    scalars values.length (scalarsBytes values ++ rest) = some (values,rest) := by
  induction values with
  | nil => rfl
  | cons value values ih =>
    simp only [List.length_cons,scalars,scalarsBytes,List.flatMap_cons,List.append_assoc]
    change (do
      let (value',bytes) ← scalarCodec.parse (scalarCodec.bytes value ++ (scalarsBytes values ++ rest))
      let (tail,rest') ← scalars values.length bytes
      pure (value'::tail,rest')) = some (value::values,rest)
    rw [Codec.parse_append]
    simp [ih]

/-- The shape is public caller/configuration metadata. Metadata normalization is
checked by exact re-encoding, not by silently discarding malformed high fields. -/
def decode (shape : AnchoredHeaderCodec.Shape) (source : List Byte) :
    Option (Record × List Byte) := do
  if ¬ shape.Valid then none else do
    let (header,bytes) ← scalars 3 source
    if header ≠ constants AnchoredHeaderCodec.openingMarker shape then none else do
      let (root,bytes) ← rootCodec.parse bytes
      let (cv,bytes) ← rootCodec.parse bytes
      let (metadata,bytes) ← scalarCodec.parse bytes
      let (squeezed,bytes) ← scalarCodec.parse bytes
      let n := metadata.c0.toNat
      if 64 < n then none else do
        let (packs,bytes) ← scalars ((n+23)/24) bytes
        let (point,bytes) ← scalars shape.logN bytes
        let (value,rest) ← scalarCodec.parse bytes
        let record : Record := {
          shape,root,context := ⟨cv,(scalarsBytes packs).take n,metadata.c1 == 1,
            metadata.c2,squeezed.c0⟩,point,value }
        if source = openingBytes record ++ rest then some (record,rest) else none

theorem decode_source (shape : AnchoredHeaderCodec.Shape) (source rest : List Byte)
    (record : Record) (accepted : decode shape source = some (record,rest)) :
    source = openingBytes record ++ rest := by
  unfold decode at accepted
  split at accepted
  · contradiction
  · obtain ⟨⟨header,bytes⟩,readHeader,accepted⟩ := Option.bind_eq_some_iff.mp accepted
    dsimp only at accepted
    split at accepted
    · contradiction
    · obtain ⟨⟨root,bytes⟩,readRoot,accepted⟩ := Option.bind_eq_some_iff.mp accepted
      dsimp only at accepted
      obtain ⟨⟨cv,bytes⟩,readCV,accepted⟩ := Option.bind_eq_some_iff.mp accepted
      dsimp only at accepted
      obtain ⟨⟨metadata,bytes⟩,readMetadata,accepted⟩ := Option.bind_eq_some_iff.mp accepted
      dsimp only at accepted
      obtain ⟨⟨squeezed,bytes⟩,readSqueezed,accepted⟩ := Option.bind_eq_some_iff.mp accepted
      dsimp only at accepted
      split at accepted
      · contradiction
      · obtain ⟨⟨packs,bytes⟩,readPacks,accepted⟩ := Option.bind_eq_some_iff.mp accepted
        dsimp only at accepted
        obtain ⟨⟨point,bytes⟩,readPoint,accepted⟩ := Option.bind_eq_some_iff.mp accepted
        dsimp only at accepted
        obtain ⟨⟨value,rest⟩,readValue,accepted⟩ := Option.bind_eq_some_iff.mp accepted
        dsimp only at accepted
        split at accepted
        · rename_i exactSource
          have equality := Option.some.inj accepted
          cases equality
          exact exactSource
        · contradiction

theorem decode_encoded (r : Record) (valid : r.shape.Valid)
    (pendingBound : r.context.pending.length ≤ 64) (pointLength : r.point.length = r.shape.logN)
    (rest : List Byte) : decode r.shape (openingBytes r ++ rest) = some (r,rest) := by
  have pending64 : r.context.pending.length < 2^64 := by omega
  have size : (UInt64.ofNat r.context.pending.length).toNat = r.context.pending.length := by
    simp only [UInt64.toNat_ofNat',Nat.mod_eq_of_lt pending64]
  have packsLength : (pendingPacks r.context).length = (r.context.pending.length+23)/24 := by
    simp only [pendingPacks,List.length_ofFn]
  have ample : r.context.pending.length ≤ (pendingPacks r.context).length*24 := by
    rw [packsLength]
    omega
  have first : (((if r.context.first then 1 else 0) : K) == 1) = r.context.first := by
    cases r.context.first <;> decide
  have scalarRead (x : E) (tail : List Byte) :
      scalarCodec.parse (scalarBytes x ++ tail) = some (x,tail) :=
    Codec.parse_append scalarCodec x tail
  have rootRead (x : Digest32) (tail : List Byte) :
      rootCodec.parse (rawRoot x ++ tail) = some (x,tail) :=
    Codec.parse_append rootCodec x tail
  simp [decode,valid,openingBytes,constants,contextScalars,scalarsBytes,
    List.append_assoc,scalars,scalarRead,rootRead,
    size,show ¬64 < r.context.pending.length by omega]
  have packsRead := scalars_encoded (pendingPacks r.context)
    (scalarsBytes r.point ++ (scalarBytes r.value ++ rest))
  simp only [scalarsBytes] at packsRead
  rw [← packsLength,packsRead]
  simp only [Option.bind_some]
  have pointRead := scalars_encoded r.point (scalarBytes r.value ++ rest)
  simp only [scalarsBytes] at pointRead
  rw [← pointLength,pointRead]
  simp only [Option.bind_some]
  rw [scalarRead]
  simp only [Option.bind_some,Nat.min_eq_left ample]
  have pending := pending_recovery r.context
  simp only [scalarsBytes] at pending
  rw [pending,first]
  simp

/-- Canonical raw32 framing is injective at the fixed public source shape.
This is frame identity, not a cryptographic PCS binding theorem. -/
theorem opening_injective (r s : Record) (rValid : r.shape.Valid) (sValid : s.shape.Valid)
    (rPending : r.context.pending.length ≤ 64) (sPending : s.context.pending.length ≤ 64)
    (rPoint : r.point.length = r.shape.logN) (sPoint : s.point.length = s.shape.logN)
    (shape : r.shape = s.shape) (image : openingBytes r = openingBytes s) : r = s := by
  have left := decode_encoded r rValid rPending rPoint []
  have right := decode_encoded s sValid sPending sPoint []
  simp only [List.append_nil] at left right
  rw [shape,image] at left
  exact congrArg Prod.fst (Option.some.inj (left.symm.trans right))

/-- All four possible pending-pack widths are inspected. Returning candidates
does not assume suffix uniqueness or choose an unproved first match. -/
def suffixAt (shape : Shape) (source : List Byte) (packs : Nat) : Option Record := do
  let (r,rest) ← decode shape (source.drop (source.length-(208+24*(packs+shape.logN))))
  if rest = [] then some r else none

def suffixCandidates (shape : Shape) (source : List Byte) : List Record :=
  (List.range 4).filterMap (suffixAt shape source)

theorem suffixCandidates_length (shape : Shape) (source : List Byte) :
    (suffixCandidates shape source).length ≤ 4 := by
  exact (List.length_filterMap_le _ _).trans (by simp)

theorem suffixAt_source (shape : Shape) (source : List Byte) (packs : Nat) (r : Record)
    (accepted : suffixAt shape source packs = some r) :
    List.IsSuffix (openingBytes r) source := by
  unfold suffixAt at accepted
  cases read : decode shape (source.drop (source.length-(208+24*(packs+shape.logN)))) with
  | none => simp [read] at accepted
  | some pair =>
    obtain ⟨s,rest⟩ := pair
    simp only [read] at accepted
    change (if rest = [] then some s else none) = some r at accepted
    split at accepted
    · rename_i empty
      have canonical := decode_source shape _ rest s read
      cases accepted
      rw [empty,List.append_nil] at canonical
      exact ⟨source.take (source.length-(208+24*(packs+shape.logN))),
        by rw [← canonical]; exact List.take_append_drop _ source⟩
    · contradiction

theorem suffixCandidates_source (shape : Shape) (source : List Byte) (r : Record)
    (member : r ∈ suffixCandidates shape source) : List.IsSuffix (openingBytes r) source := by
  obtain ⟨packs,_,accepted⟩ := List.mem_filterMap.mp member
  exact suffixAt_source shape source packs r accepted

theorem suffixCandidates_recovery (r : Record) (valid : r.shape.Valid)
    (pending : r.context.pending.length ≤ 64) (point : r.point.length = r.shape.logN)
    (pre : List Byte) : r ∈ suffixCandidates r.shape (pre ++ openingBytes r) := by
  let packs := (r.context.pending.length+23)/24
  have bound : packs < 4 := by dsimp [packs]; omega
  have size : (openingBytes r).length = 208+24*(packs+r.shape.logN) := by
    rw [openingBytes_length,point]
  apply List.mem_filterMap.mpr
  refine ⟨packs,List.mem_range.mpr bound,?_⟩
  unfold suffixAt
  simp only [List.length_append,← size,Nat.add_sub_cancel_right,List.drop_left]
  have parsed := decode_encoded r valid pending point []
  simp only [List.append_nil] at parsed
  rw [parsed]
  rfl

#print axioms suffixCandidates_length
#print axioms suffixAt_source
#print axioms suffixCandidates_source
#print axioms suffixCandidates_recovery

#print axioms scalars_source
#print axioms opening_injective

#print axioms decode_encoded

#print axioms pending_image
#print axioms pending_recovery
#print axioms scalars_encoded
#print axioms decode_source
end Whir.SpongefishCurrentRecordDecoder
