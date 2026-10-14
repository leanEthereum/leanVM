import Whir.AnchoredSourceFreshCaller

/-! Literal saved-record recovery for the frozen PR600 source at `12eea88c`,
through the existing hand-port `AnchoredHeaderCodec`. The only external selection
input is a supported production profile; roots, contexts, lanes, points and
values are decoded, not supplied. The byte boundary is the existing
`WHIRHistory.parseFrames`, not a new token serialization. Native caller success
must establish that its literal final sent run ends in the saved opening; this
module proves byte-parser and complete record recovery, not that native-refinement
obligation or deployed universal observer refinement. -/
namespace Whir.PCSBCSSourceSavedRecordDecoder
open Concrete FiatShamirGame AnchoredHeaderCodec

set_option maxHeartbeats 0
set_option maxRecDepth 10000

def Compatible (p : ParameterBounds.Profile) (r : Record) : Prop :=
  r.shape.logN = (ParameterBounds.config p).logN ∧
  r.shape.logBatch = (ParameterBounds.config p).folds[0]! ∧
  r.shape.logRate = (ParameterBounds.config p).rates[0]!

instance (p : ParameterBounds.Profile) (r : Record) : Decidable (Compatible p r) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def words (packs : List E) : List K := packs.flatMap fun x => [x.c0,x.c1,x.c2]

theorem words_length (packs : List E) : (words packs).length = 3*packs.length := by
  induction packs with
  | nil => rfl
  | cons x xs ih =>
    simp only [words,List.flatMap_cons,List.length_append,List.length_cons,
      List.length_nil] at *
    omega

def pending (n : Nat) (packs : List E) : Fin 8 → Option K := fun i =>
  if i.val < (n+7)/8 then some ((words packs)[i.val]?.getD 0) else none

theorem pending_recovery (c : Context) (h : c.Valid) :
    pending c.pendingBytes (pendingPacks c) = c.pending := by
  funext i
  have hn := h.1
  have hi := h.2 i
  generalize he : c.pendingBytes = n at *
  interval_cases n <;> fin_cases i <;>
    simp_all [pending,words,pendingPacks,List.range_succ] <;>
    cases hx : c.pending _ <;> simp_all

theorem halves_recovery (d : Digest32) :
    ByteCodec.scalarHalves ((ByteCodec.hashToScalars d).1,
      (ByteCodec.hashToScalars d).2) = d := by
  have h := ByteCodec.scalarsToHash_hashToScalars d
  simpa [ByteCodec.scalarsToHash,ByteCodec.hashToScalars] using h

theorem first_recovery (b : Bool) : ((if b then (1 : K) else 0) == 1) = b := by
  cases b <;> decide

def reconstruct : List E → Option Record
  | _marker :: shape :: lanes :: a :: b :: cv0 :: cv1 :: metadata :: squeezed :: tail =>
    let n := metadata.c0.toNat
    some { shape := ⟨shape.c0.toNat,shape.c1.toNat,shape.c2.toNat,lanes.c0.toNat⟩
           root := ByteCodec.scalarHalves (a,b)
           context := { cv := ByteCodec.scalarHalves (cv0,cv1)
                        pending := pending n tail
                        pendingBytes := n
                        first := metadata.c1 == 1
                        previous := metadata.c2
                        squeezed := squeezed.c0 }
           point := (tail.drop ((n+23)/24)).dropLast
           value := tail.getLast?.getD 0 }
  | _ => none

theorem pending_prefix (n : Nat) (packs rest : List E)
    (h : (n+7)/8 ≤ 3*packs.length) :
    pending n (packs ++ rest) = pending n packs := by
  funext i
  unfold pending
  split
  · rename_i hi
    have hw := words_length packs
    have bound : i.val < (words packs).length := by rw [hw]; omega
    simp only [words,List.flatMap_append] at *
    rw [List.getElem?_append_left bound]
  · rfl

theorem reconstruct_opening (r : Record) (h : r.Valid) :
    reconstruct (openingScalars r) = some r := by
  have hs := h.1
  have hb : r.context.pendingBytes < 2^64 := by have := h.2.1.1; omega
  have hn : r.shape.logN < 2^64 := by have := hs.2.1; omega
  have ht : r.shape.logBatch < 2^64 := by have := hs.1; have := hs.2.1; omega
  have hr : r.shape.logRate < 2^64 := by have := hs.2.2.2.1; omega
  have hl : r.shape.lanes < 2^64 := by
    have batchBound : r.shape.logBatch < 64 := Nat.lt_trans hs.1 hs.2.1
    have hp : 2^r.shape.logBatch < 2^64 := Nat.pow_lt_pow_right (by decide) batchBound
    have := hs.2.2.2.2.2
    omega
  have lengths : (pendingPacks r.context).length = (r.context.pendingBytes+23)/24 := by
    simp [pendingPacks]
  have cap : (r.context.pendingBytes+7)/8 ≤ 3*(pendingPacks r.context).length := by
    rw [lengths]; omega
  simp only [openingScalars,List.cons_append,List.nil_append,reconstruct,
    shapeScalar,lanesScalar,UInt64.toNat_ofNat',Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt ht,Nat.mod_eq_of_lt hr,Nat.mod_eq_of_lt hl,Nat.mod_eq_of_lt hb,
    List.append_assoc]
  rw [pending_prefix _ _ _ cap,pending_recovery _ h.2.1]
  rw [← lengths,List.drop_left]
  simp only [List.dropLast_concat,List.getLast?_append,List.getLast?_singleton,
    Option.some_or,Option.getD_some,halves_recovery]
  rw [first_recovery]

def parse (p : ParameterBounds.Profile) (xs : List E) : Option Record :=
  (reconstruct xs).bind fun r =>
    if r.Valid ∧ Compatible p r ∧ openingScalars r = xs then some r else none

theorem parse_opening (p : ParameterBounds.Profile) (r : Record)
    (h : r.Valid) (hp : Compatible p r) : parse p (openingScalars r) = some r := by
  simp [parse,reconstruct_opening r h,h,hp]

theorem parse_sound (p : ParameterBounds.Profile) (xs : List E) (r : Record)
    (h : parse p xs = some r) : r.Valid ∧ Compatible p r ∧ openingScalars r = xs := by
  unfold parse at h
  cases he : reconstruct xs with
  | none => simp [he] at h
  | some s =>
    simp only [he,Option.bind_some] at h
    split at h
    · rename_i guard; cases h; exact guard
    · contradiction

theorem opening_injective (r s : Record) (hr : r.Valid) (hs : s.Valid)
    (h : openingScalars r = openingScalars s) : r = s := by
  have := congrArg reconstruct h
  simpa [reconstruct_opening r hr,reconstruct_opening s hs] using this

theorem shape_not_marker (s : Shape) (h : s.Valid) : shapeScalar s ≠ openingMarker := by
  intro he
  have hh := congrArg E.c0 he
  have hn : (UInt64.ofNat s.logN).toNat = s.logN := by
    rw [UInt64.toNat_ofNat',Nat.mod_eq_of_lt (by have := h.2.1; omega)]
  have := congrArg UInt64.toNat hh
  simp only [shapeScalar,openingMarker] at this
  rw [hn] at this
  have := h.2.1
  norm_num at *
  omega

theorem lanes_not_marker (s : Shape) : lanesScalar s ≠ openingMarker := by
  intro he
  have := congrArg E.c1 he
  norm_num [lanesScalar,openingMarker] at this

theorem rate_nonzero (s : Shape) (h : s.Valid) : (shapeScalar s).c2 ≠ 0 := by
  intro he
  have hn : (UInt64.ofNat s.logRate).toNat = s.logRate := by
    rw [UInt64.toNat_ofNat',Nat.mod_eq_of_lt (by have := h.2.2.2.1; omega)]
  have := congrArg UInt64.toNat he
  simp only [shapeScalar] at this
  rw [hn] at this
  have := h.2.2.1
  norm_num at *
  omega

/-- There is no valid opening starting one, two or three scalars into another.
At offset three the root's second half, not its first, rules out the shape. -/
theorem shifted_opening_impossible (r s : Record) (hr : r.Valid) (hs : s.Valid)
    (d : Nat) (hd : 1 ≤ d ∧ d ≤ 3) :
    (openingScalars r).drop d ≠ openingScalars s := by
  obtain ⟨hd0,hd1⟩ := hd
  interval_cases d
  · intro he
    have hh := congrArg List.head? he
    simp [openingScalars] at hh
    exact shape_not_marker r.shape hr.1 hh
  · intro he
    have hh := congrArg List.head? he
    simp [openingScalars] at hh
    exact lanes_not_marker r.shape hh
  · intro he
    have hh := congrArg (fun xs : List E => xs[1]?) he
    simp [openingScalars] at hh
    have hc := congrArg E.c2 hh
    simp [ByteCodec.hashToScalars] at hc
    exact rate_nonzero s.shape hs.1 hc.symm

/-- Supported-profile openings have lengths in a four-element interval. -/
theorem opening_length_band (p : ParameterBounds.Profile) (r : Record)
    (h : r.Valid) (hp : Compatible p r) :
    10+(ParameterBounds.config p).logN ≤ (openingScalars r).length ∧
    (openingScalars r).length ≤ 13+(ParameterBounds.config p).logN := by
  rw [openingScalars_valid_length r h,hp.1]
  have := h.2.1.1
  omega

theorem suffix_unique (p : ParameterBounds.Profile) (xs : List E) (r s : Record)
    (hr : r.Valid) (hs : s.Valid) (pr : Compatible p r) (ps : Compatible p s)
    (ar : List.IsSuffix (openingScalars r) xs)
    (as' : List.IsSuffix (openingScalars s) xs) : r = s := by
  have br := opening_length_band p r hr pr
  have bs := opening_length_band p s hs ps
  have comparable := List.suffix_or_suffix_of_suffix ar as'
  rcases comparable with h | h
  · obtain ⟨pre,he⟩ := h
    have hl := congrArg List.length he
    simp only [List.length_append] at hl
    have hd : pre.length ≤ 3 := by omega
    have drop : (openingScalars s).drop pre.length = openingScalars r := by
      rw [← he,List.drop_left]
    by_cases hz : pre.length = 0
    · simp only [hz,List.drop_zero] at drop
      exact opening_injective r s hr hs drop.symm
    · exact False.elim (shifted_opening_impossible s r hs hr pre.length ⟨by omega,hd⟩ drop)
  · obtain ⟨pre,he⟩ := h
    have hl := congrArg List.length he
    simp only [List.length_append] at hl
    have hd : pre.length ≤ 3 := by omega
    have drop : (openingScalars r).drop pre.length = openingScalars s := by
      rw [← he,List.drop_left]
    by_cases hz : pre.length = 0
    · simp only [hz,List.drop_zero] at drop
      exact opening_injective r s hr hs drop
    · exact False.elim (shifted_opening_impossible r s hr hs pre.length ⟨by omega,hd⟩ drop)

def decodeScalars (p : ParameterBounds.Profile) (xs : List E) : Option Record :=
  (List.range 4).findSome? fun n =>
    parse p (xs.drop (xs.length-(10+(ParameterBounds.config p).logN+n)))

theorem decodeScalars_recovery (p : ParameterBounds.Profile) (r : Record)
    (h : r.Valid) (hp : Compatible p r) (pre : List E) :
    decodeScalars p (pre ++ openingScalars r) = some r := by
  let n := (r.context.pendingBytes+23)/24
  have hn : n < 4 := by dsimp [n]; have := h.2.1.1; omega
  have len : (openingScalars r).length = 10+(ParameterBounds.config p).logN+n := by
    rw [openingScalars_valid_length r h,hp.1]
  have hit : parse p ((pre ++ openingScalars r).drop
      ((pre ++ openingScalars r).length-(10+(ParameterBounds.config p).logN+n))) = some r := by
    simp only [List.length_append,← len,Nat.add_sub_cancel_right,List.drop_left]
    exact parse_opening p r h hp
  have nonempty : (decodeScalars p (pre ++ openingScalars r)).isSome := by
    unfold decodeScalars
    rw [List.findSome?_isSome_iff]
    exact ⟨n,List.mem_range.mpr hn,by rw [hit]; rfl⟩
  cases he : decodeScalars p (pre ++ openingScalars r) with
  | none => simp [he] at nonempty
  | some s =>
    obtain ⟨i,hi,accepted⟩ := List.exists_of_findSome?_eq_some he
    have sound := parse_sound p _ s accepted
    have suffix : List.IsSuffix (openingScalars s) (pre ++ openingScalars r) := by
      rw [sound.2.2]
      exact List.drop_suffix _ _
    have same := suffix_unique p _ r s h sound.1 hp sound.2.1 ⟨pre,rfl⟩ suffix
    rw [same]

/-- Literal contiguous sent run. A consumed squeeze or nonce separates runs;
zero-consumption empty absorb frames do not hide the preceding saved header. -/
def extendRun (run : List E) : WHIRHistory.SemanticFrame → List E
  | .absorb previous xs => if previous = 0 then run ++ xs else xs
  | .nonce _ _ _ => []

def literalRun (entry : FramedHistory) : Option (List E) :=
  (WHIRHistory.parseFrames entry.frames).map (fun frames => frames.foldl extendRun [])

def decode (p : ParameterBounds.Profile) (entry : FramedHistory) : Option Record :=
  (literalRun entry).bind (decodeScalars p)

theorem decode_literal_run (p : ParameterBounds.Profile) (entry : FramedHistory)
    (r : Record) (h : r.Valid) (hp : Compatible p r) (pre : List E)
    (literal : literalRun entry = some (pre ++ openingScalars r)) :
    decode p entry = some r := by
  simp only [decode,literal,Option.bind_some]
  exact decodeScalars_recovery p r h hp pre

theorem decode_sound (p : ParameterBounds.Profile) (entry : FramedHistory) (r : Record)
    (accepted : decode p entry = some r) :
    r.Valid ∧ Compatible p r ∧
      ∃ run, literalRun entry = some run ∧ List.IsSuffix (openingScalars r) run := by
  unfold decode at accepted
  cases he : literalRun entry with
  | none => simp [he] at accepted
  | some run =>
    simp only [he,Option.bind_some] at accepted
    obtain ⟨i,hi,parsed⟩ := List.exists_of_findSome?_eq_some accepted
    have sound := parse_sound p _ r parsed
    refine ⟨sound.1,sound.2.1,run,rfl,?_⟩
    rw [sound.2.2]
    exact List.drop_suffix _ _


/-- Exact byte-framing provenance, allowing arbitrary earlier real frames and
arbitrary adaptive sent scalars preceding the saved header in the final run. -/
theorem decode_source_entry (p : ParameterBounds.Profile) (r : Record)
    (h : r.Valid) (hp : Compatible p r) (domain statement : Digest32)
    (frames : List WHIRHistory.SemanticFrame) (previous : Nat) (pre : List E) :
    decode p (WHIRHistory.encodeHistory ⟨domain,statement,
      frames ++ [.absorb previous (pre ++ openingScalars r)]⟩) = some r := by
  simp only [decode,literalRun,WHIRHistory.encodeHistory,WHIRHistory.frames_roundtrip,
    Option.map_some,Option.bind_some,List.foldl_append,List.foldl_cons,List.foldl_nil,
    extendRun]
  by_cases hz : previous = 0
  · simp only [hz,↓reduceIte]
    rw [← List.append_assoc]
    exact decodeScalars_recovery p r h hp _
  · simp only [hz,↓reduceIte]
    exact decodeScalars_recovery p r h hp _

#print axioms decode_source_entry
#print axioms suffix_unique
end Whir.PCSBCSSourceSavedRecordDecoder
