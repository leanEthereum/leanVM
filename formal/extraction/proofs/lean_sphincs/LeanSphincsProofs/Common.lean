import LeanSphincsProofs.Defs

/-!
# What the proofs share

The library models the extraction calls (slices, arrays, ranges, `to_be_bytes`) as equations and
triples, the arithmetic of bytes read as numbers, and `th` at an address.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM Std.Do
open HashSig HashSig.OverPermutation Sphincs
open LeanVM.Semantics (KeccakState)
open LeanVM.Protocol.KeccakHash (digestBytes keccak256With)
open lean_sphincs

namespace LeanSphincsProofs

/-- A `mapM` of a function that returns its argument returns the list. -/
theorem mapM_ok_id {α : Type} (f : α → RustM α) (hf : ∀ x, f x = ok x) (l : List α) :
    List.mapM f l = ok l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.mapM_cons, hf, ih]
    simp [Functor.map]

/-- `copy_from_slice` on bytes of equal lengths gives the source. -/
theorem copy_from_slice_u8 (d s : Slice Std.U8) (h : d.length = s.length) :
    core.slice.Slice.copy_from_slice core.U8.Insts.CoreMarkerCopy d s = ok s := by
  have hm : List.mapM core.U8.Insts.CoreCloneClone.clone s.val = ok s.val :=
    mapM_ok_id _ (fun _ => rfl) _
  simp only [core.slice.Slice.copy_from_slice, rust_primitives.slice.slice_clone_from_slice, h,
    ite_true]
  split
  · rename_i cloned heq
    rw [hm, RustM.match.ok] at heq
    cases heq
    exact congrArg ok (Slice.ext _ _ (Slice.from_val _ _))
  · rename_i heq; rw [hm, RustM.match.ok] at heq; cases heq
  · rename_i heq; rw [hm, RustM.match.ok] at heq; cases heq

/-- `&mut a[b..e]`: the bytes from `b` to `e`, and writing them back. -/
theorem array_index_mut_range {α : Type} {N : Std.Usize} (a : Array α N) (b e : Std.Usize)
    (h : b.val ≤ e.val) (he : e.val ≤ N.val) :
    ∃ s back, core.Array.Insts.CoreOpsIndexIndexMut.index_mut
      (core.Slice.Insts.CoreOpsIndexIndexMut
        (core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice α))
      a { start := b, «end» := e } = ok (s, back) ∧
      s.val = List.slice b.val e.val a.val ∧ ∀ t : Slice α, (back t).val = a.val.setSlice! b.val t.val := by
  simp [core.Array.Insts.CoreOpsIndexIndexMut.index_mut, core.array.Array.as_mut_slice,
    rust_primitives.slice.array_as_mut_slice, core.Slice.Insts.CoreOpsIndexIndexMut.index_mut,
    core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
    rust_primitives.slice.slice_slice_mut, Slice.subslice, Array.to_slice_mut]
  refine ⟨_, _, by simp only [h, he, and_self, ↓reduceIte]; exact Aeneas.Std.bind_ok _ _, by simp, fun t => ?_⟩
  rw [Array.from_slice_val _ _ (by simp)]
  simp

/-- `a.as_slice()`. -/
theorem array_as_slice {α : Type} {N : Std.Usize} (a : Array α N) :
    ∃ s, core.array.Array.as_slice a = ok s ∧ s.val = a.val :=
  ⟨a.to_slice, rfl, by simp⟩

/-- A slice of `n` values, each a removal from the front of a sequence: the closure of
`array::repeat`. -/
theorem repeat_go {α : Type} (N : Std.Usize) (inst : core.clone.Clone α) :
    ∀ (n : ℕ) (c : Slice α), n ≤ c.length →
      rust_primitives.slice.array_from_fn_go
        (core.array.repeat.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT N inst) c n =
        ok (c.val.take n, Slice.from (c.val.drop n) (by have := c.property; simp; scalar_tac)) := by
  intro n
  induction n with
  | zero =>
    intro c _
    simp only [rust_primitives.slice.array_from_fn_go, List.take_zero, List.drop_zero]
    exact congrArg ok (Prod.ext rfl (Slice.ext _ _ (by simp)))
  | succ n ih =>
    intro c hn
    have hn' : n < c.val.length := hn
    simp only [rust_primitives.slice.array_from_fn_go]
    erw [ih c (by omega)]
    erw [Aeneas.Std.bind_ok]
    simp [core.array.repeat.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT.call_mut,
      rust_primitives.sequence.seq_remove, hn']
    erw [Aeneas.Std.bind_ok]
    rw [List.take_succ_eq_append_getElem hn']
    rfl

/-- `[x; N]` for a type whose `clone` returns its argument. -/
theorem array_repeat {α : Type} (N : Std.Usize) (inst : core.clone.Clone α)
    (hclone : ∀ y, inst.clone y = ok y) (x : α) :
    ∃ a, core.array.repeat N inst x = ok a ∧ a.val = List.replicate N.val x := by
  have hm : ∀ l : List α, List.mapM inst.clone l = ok l := mapM_ok_id _ hclone
  have hseq : ∃ s, rust_primitives.sequence.seq_create inst x N = ok s ∧
      s.val = List.replicate N.val x := by
    simp only [rust_primitives.sequence.seq_create]
    split_ifs with h0
    · exact ⟨_, rfl, by simp [h0]⟩
    · rw [hm, RustM.match.ok]
      have hn : List.replicate (N.val - 1) x ++ [x] = List.replicate N.val x := by
        rw [← List.replicate_succ', Nat.sub_add_cancel (by omega)]
      have hb : (List.replicate (N.val - 1) x ++ [x]).length ≤ Usize.max := by
        rw [hn, List.length_replicate]; scalar_tac
      simp only [dite_eq_left hb]
      exact ⟨_, rfl, by simp [hn]⟩
  obtain ⟨s, hs, hsv⟩ := hseq
  simp only [core.array.repeat, hs]
  erw [Aeneas.Std.bind_ok]
  simp only [rust_primitives.slice.array_from_fn]
  rw [repeat_go N inst N.val s (by simp [Slice.length, hsv])]
  erw [Aeneas.Std.bind_ok]
  have hl : (List.take N.val s.val).length = N.val := by simp [hsv]
  exact ⟨Array.from _ hl, by simp only [hl, ↓reduceDIte], by simp [hsv]⟩

/-- `x.to_be_bytes()` for a `u32`: the model is Aeneas's. -/
theorem u32_to_be_bytes (x : Std.U32) :
    core.num.U32.to_be_bytes x = ok (Aeneas.Std.core.num.U32.to_be_bytes x) := rfl

@[simp] theorem holds_ok (P : Prop) : (ok P : RustM Prop).holds ↔ P := by
  simp [RustM.holds, Triple, WP.wp, PredTrans.apply]

@[simp] theorem bytes_length (l : List Std.U8) : (bytes l).length = l.length := by simp [bytes]

theorem leNat_lt (l : List UInt8) : leNat l < 256 ^ l.length := by
  induction l with
  | nil => simp [leNat]
  | cons b bs ih =>
    have hb : b.toNat < 256 := b.toNat_lt
    simp only [leNat, List.foldr_cons, List.length_cons] at ih ⊢
    rw [Nat.pow_succ]
    omega

theorem leNat_byte (l : List UInt8) (i : ℕ) (hi : i < l.length) :
    leNat l / 256 ^ i % 256 = l[i].toNat := by
  induction l generalizing i with
  | nil => simp at hi
  | cons b bs ih =>
    have hb : b.toNat < 256 := b.toNat_lt
    cases i with
    | zero => simp only [leNat, List.foldr_cons, pow_zero, Nat.div_one, List.getElem_cons_zero]; omega
    | succ i =>
      simp only [leNat, List.foldr_cons, List.getElem_cons_succ] at ih ⊢
      have hi' : i < bs.length := by simpa using hi
      have key := ih i hi'
      generalize List.foldr (fun b acc ↦ b.toNat + 256 * acc) 0 bs = X at key ⊢
      rw [Nat.pow_succ', ← Nat.div_div_eq_div_mul, show (b.toNat + 256 * X) / 256 = X by omega]
      exact key

/-- The little-endian bytes of the number a byte string spells are the string. -/
theorem littleEndianBytes_leNat (n : ℕ) (l : List UInt8) (hl : l.length = n) :
    littleEndianBytes n (BitVec.ofNat (8 * n) (leNat l)) = l := by
  apply List.ext_getElem
  · simp [littleEndianBytes, hl]
  · intro i h1 h2
    simp only [littleEndianBytes, List.getElem_ofFn]
    apply UInt8.toNat_inj.mp
    have hlt : leNat l < 2 ^ (8 * n) := by
      have := leNat_lt l
      rwa [hl, show (256 : ℕ) = 2 ^ 8 by rfl, ← Nat.pow_mul] at this
    simp only [UInt8.toNat_ofBitVec, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hlt, Nat.shiftRight_eq_div_pow]
    rw [Nat.pow_mul]
    exact leNat_byte l i h2

/-- **A Rust digest's bytes are the little-endian bytes of the statement's digest.** -/
theorem littleEndianBytes_toDigest (a : Array Std.U8 16#usize) :
    littleEndianBytes 16 (toDigest a) = bytes a.val :=
  littleEndianBytes_leNat 16 _ (by simp)

/-- **A Rust message's bytes are the little-endian bytes of the statement's message.** -/
theorem littleEndianBytes_toMessage (a : Array Std.U8 32#usize) :
    littleEndianBytes 32 (toMessage a) = bytes a.val :=
  littleEndianBytes_leNat 32 _ (by simp)

/-- An equality of bit vectors built from shifts and truncations, bit by bit: checked by the
kernel, with no SAT certificate to trust. -/
macro "bv_bits" : tactic => `(tactic|
  (apply BitVec.eq_of_getLsbD_eq; intro i hi
   simp +arith [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hi] <;>
     omega))

/-- **`u32::to_be_bytes` is the statement's `bigEndianBytes 4`.** -/
theorem bytes_u32_to_be_bytes (x : Std.U32) :
    bytes (Aeneas.Std.core.num.U32.to_be_bytes x).val = bigEndianBytes 4 x.bv := by
  have h : x.bv.toBEBytes = [x.bv.extractLsb' 24 8, x.bv.extractLsb' 16 8, x.bv.extractLsb' 8 8,
      x.bv.extractLsb' 0 8] := by
    simp [BitVec.toBEBytes, BitVec.toLEBytes]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> bv_bits
  simp only [Aeneas.Std.core.num.U32.to_be_bytes, Array.from_val, h, bytes, List.map_cons,
    List.map_nil, b8]
  rfl

theorem u32_bv_eq_ofNat (x : Std.U32) : x.bv = BitVec.ofNat 32 x.val := by
  apply BitVec.eq_of_toNat_eq
  simp

/-- A computation proved to return, as its value. -/
theorem ok_of_triple {α : Type} {x : RustM α} {P : α → Prop}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) : ∃ v, x = ok v ∧ P v := by
  obtain ⟨v, hv⟩ := Hax.triple_noThrow_exists_ok h
  exact ⟨v, hv, by simpa using Hax.triple_noThrow_elim h hv⟩

/-- A range that is not exhausted gives its start and moves on. -/
theorem range_next_lt (i e : Std.Usize) (h : i.val < e.val) :
    ∃ s : Std.Usize, s.val = i.val + 1 ∧
      core.IteratorRange.next core.Usize.Insts.CoreIterRangeStep { start := i, «end» := e } =
        ok (some i, { start := s, «end» := e }) := by
  have := ok_of_triple (P := fun r => ∃ s : Std.Usize, s.val = i.val + 1 ∧
      r = (some i, ({ start := s, «end» := e } : core.ops.range.Range Std.Usize)))
    (Hax.IteratorRange_next_spec_usize i e (fun _ s hs => by simpa using hs)
      (fun hge => absurd h (by omega)))
  obtain ⟨v, hv, s, hs, rfl⟩ := this
  exact ⟨s, hs, hv⟩

/-- An exhausted range gives nothing. -/
theorem range_next_ge (i e : Std.Usize) (h : e.val ≤ i.val) :
    core.IteratorRange.next core.Usize.Insts.CoreIterRangeStep { start := i, «end» := e } =
      ok (none, { start := i, «end» := e }) := by
  have := ok_of_triple (P := fun r =>
      r = (none, ({ start := i, «end» := e } : core.ops.range.Range Std.Usize)))
    (Hax.IteratorRange_next_spec_usize i e (fun hlt => absurd hlt (by omega))
      (fun _ => by simp))
  obtain ⟨v, hv, rfl⟩ := this
  exact hv

theorem numBits_ge : 32 ≤ System.Platform.numBits := by
  cases System.Platform.numBits_eq <;> omega

theorem leNat_append (a b : List UInt8) : leNat (a ++ b) = leNat a + 256 ^ a.length * leNat b := by
  induction a with
  | nil => simp [leNat]
  | cons x xs ih =>
    simp only [leNat, List.cons_append, List.foldr_cons, List.length_cons] at ih ⊢
    rw [ih, Nat.pow_succ]
    ring

/-- The statement's hash, in `Id`, as the number its digest bytes spell. -/
theorem keccakHash_inId (π : KeccakState → KeccakState) (l : List UInt8) :
    Id.run (keccakHash (inId π) l) = BitVec.ofNat 256 (leNat (hashBytes π l)) := rfl

theorem sequenceFin_id {α : Type} : ∀ {n : ℕ} (f : Fin n → Id α),
    Id.run (sequenceFin f) = fun i ↦ Id.run (f i)
  | 0, _ => funext fun i ↦ i.elim0
  | n + 1, f => by
    funext i
    have ih := sequenceFin_id fun j : Fin n ↦ f j.succ
    simp only [sequenceFin, Id.run_bind, Id.run_pure] at ih ⊢
    by_cases h : i.val = 0
    · have : i = 0 := Fin.ext h
      simp [this]
    · simp only [h, ↓reduceDIte]
      have := congrFun ih ⟨i.val - 1, by omega⟩
      rw [this]
      congr 2
      exact Fin.ext (by simp; omega)

/-- A program that returns a value satisfying `P` meets the specification `P`. -/
theorem spec_of_exists {α : Type} {m : RustM α} {P : α → Prop} (h : ∃ y, m = ok y ∧ P y) :
    m ⦃ y => P y ⦄ := by
  obtain ⟨y, rfl, hy⟩ := h
  exact (WP.spec_ok y).2 hy

/-- `th` at a Rust address that holds the statement's `A`: the statement's addressed hash. -/
theorem th_adrs {π : KeccakState → KeccakState} (hth : ThSpec π) (seed : Array Std.U8 16#usize)
    (adrs : hash.Adrs) (A : Sphincs.Address) (m : Slice Std.U8) (hA : AdrsIs adrs A) :
    ∃ d, hash.th seed adrs m = ok d ∧
      toDigest d = Id.run (Verification.addressedHash (inId π) (toDigest seed) A (bytes m.val)) := by
  obtain ⟨d, hd, hdig⟩ := hth seed adrs m
  refine ⟨d, hd, ?_⟩
  rw [hdig, hA, ← littleEndianBytes_toDigest seed]
  rfl

/-- A cast to `u32` of a number below `2^32`, as bits. -/
theorem cast_u32_bv {ty : UScalarTy} (x : UScalar ty) :
    (UScalar.cast .U32 x).bv = BitVec.ofNat 32 x.val := by
  apply BitVec.eq_of_toNat_eq
  show (BitVec.setWidth 32 x.bv).toNat = (BitVec.ofNat 32 x.bv.toNat).toNat
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

/-- A slice made from a list holds that list. -/
theorem slice_from_val {α : Type} (l : List α) (h : l.length ≤ Usize.max) :
    (Slice.from l h).val = l := Data.ListN.ListN.from_to_inverse

theorem flat_length (l : List (Array Std.U8 16#usize)) :
    ((l.map Array.val).flatten).length = 16 * l.length := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    have hx : x.val.length = 16 := x.property
    simp only [List.map_cons, List.flatten_cons, List.length_append, ih, List.length_cons, hx]
    omega

/-- `th_digests`: the addressed hash of the digests' bytes, one after the other. -/
theorem th_digests_adrs {π : KeccakState → KeccakState} (hth : ThSpec π)
    (seed : Array Std.U8 16#usize) (a : hash.Adrs) (A : Sphincs.Address)
    (values : Slice (Array Std.U8 16#usize)) (hA : AdrsIs a A)
    (hlen : 16 * values.length ≤ Usize.max) :
    ∃ d, hash.th_digests seed a values = ok d ∧
      toDigest d = Id.run (Verification.addressedHash (inId π) (toDigest seed) A
        (bytes ((values.val.map Array.val).flatten))) := by
  have hflat : ((values.val.map Array.val).flatten).length ≤ Usize.max := by
    rw [flat_length]; exact hlen
  obtain ⟨d, hd, hval⟩ := th_adrs hth seed a A (Slice.from _ hflat) hA
  refine ⟨d, ?_, ?_⟩
  · unfold hash.th_digests core.slice.SliceArray.as_flattened
    simp only [hflat, ↓reduceDIte, Aeneas.Std.bind_ok]
    exact hd
  · rw [hval, slice_from_val]

theorem bytes_flatten (l : List (Array Std.U8 16#usize)) :
    bytes ((l.map Array.val).flatten) = l.flatMap (fun a => littleEndianBytes 16 (toDigest a)) := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    rw [List.map_cons, List.flatten_cons, List.flatMap_cons, littleEndianBytes_toDigest, ← ih]
    simp [bytes]

theorem flatMap_map' {α β γ : Type} (f : α → β) (g : β → List γ) (l : List α) :
    (l.map f).flatMap g = l.flatMap (fun a => g (f a)) := by
  induction l with
  | nil => rfl
  | cons x t ih => simp [List.flatMap_cons, ih]

end LeanSphincsProofs
