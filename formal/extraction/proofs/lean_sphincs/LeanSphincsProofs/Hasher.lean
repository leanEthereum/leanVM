import LeanSphincsProofs.Common

/-!
# `keccak256::Hasher` computes Keccak-256

`HasherSpec` (`Defs.lean`) asks that `keccak256::Hasher` compute Keccak-256. This file proves it
from what the sponge step `absorb` and the output `digest_of` compute (`SpongeSpec`, which
`Sponge.lean` and `Keccak.lean` prove): the buffering of `update`, `block_of`, and the padding of
`final_block`.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM Std.Do
open LeanVM.Semantics (KeccakState)
open LeanVM.Semantics.Keccak (lane)
open LeanVM.Protocol.KeccakHash

namespace LeanSphincsProofs

/-- A Rust lane as the statement's. -/
def lane64 (x : Std.U64) : UInt64 := UInt64.ofBitVec x.bv

/-- A Rust Keccak state, `[u64; 25]`, as the statement's: lane `i` at index `i`. -/
def toState (a : Array Std.U64 25#usize) : KeccakState :=
  Vector.ofFn fun i : Fin 25 ↦ lane64 a.val[i.val]!

/-- What `absorb` and `digest_of` compute (proved for Keccak-f[1600] in `Keccak.lean`):
`absorb` XORs the block's 17 lanes into the state's first 17 and permutes with `π`, and
`digest_of` gives the first four lanes' bytes, each lane little-endian. -/
structure SpongeSpec (π : KeccakState → KeccakState) : Prop where
  absorb : ∀ (state : Array Std.U64 25#usize) (block : Array Std.U64 17#usize),
    ∃ state', keccak256.absorb state block = ok state' ∧
      toState state' = π (Vector.ofFn fun i : Fin 25 ↦
        if i.val < 17 then lane (toState state) i ^^^ lane64 block.val[i.val]!
        else lane (toState state) i)
  digest_of : ∀ state : Array Std.U64 25#usize,
    ∃ d, keccak256.digest_of state = ok d ∧
      bytes d.val = digestBytes #v[lane (toState state) 0, lane (toState state) 1,
        lane (toState state) 2, lane (toState state) 3]

namespace Hasher

/-! ## The statement's sponge, a block at a time -/

/-- One block absorbed. -/
def absorbBlock (π : KeccakState → KeccakState) (s : KeccakState) (block : List UInt8) :
    KeccakState :=
  Id.run (absorbBlockWith (inId π) s block)

/-- The state after the first `n` whole blocks of `data`. -/
def blocks (π : KeccakState → KeccakState) : ℕ → KeccakState → List UInt8 → KeccakState
  | 0, s, _ => s
  | n + 1, s, data => blocks π n (absorbBlock π s (data.take rate)) (data.drop rate)

theorem absorbWith_eq (π : KeccakState → KeccakState) (n : ℕ) (s : KeccakState) (data : List UInt8) :
    Id.run (absorbWith (inId π) n s data) =
      absorbBlock π (blocks π n s data) (padBlock (data.drop (rate * n))) := by
  induction n generalizing s data with
  | zero => simp [absorbWith, blocks, absorbBlock]
  | succ n ih =>
    simp only [absorbWith, blocks, Id.run_bind]
    rw [show rate * (n + 1) = rate + rate * n by ring, ← List.drop_drop]
    exact ih _ _

theorem blocks_succ (π : KeccakState → KeccakState) (n : ℕ) (s : KeccakState) (data : List UInt8) :
    blocks π (n + 1) s data =
      absorbBlock π (blocks π n s data) ((data.drop (rate * n)).take rate) := by
  induction n generalizing s data with
  | zero => simp [blocks]
  | succ n ih =>
    rw [blocks, ih, blocks, show rate * (n + 1) = rate + rate * n by ring, ← List.drop_drop]

/-- The first `n` blocks do not depend on what follows them. -/
theorem blocks_append (π : KeccakState → KeccakState) (n : ℕ) (s : KeccakState) (l t : List UInt8)
    (h : rate * n ≤ l.length) : blocks π n s (l ++ t) = blocks π n s l := by
  induction n generalizing s l with
  | zero => rfl
  | succ n ih =>
    have h' : rate * n + rate ≤ l.length := h
    have hr : rate ≤ l.length := by omega
    rw [blocks, blocks, List.take_append_of_le_length hr, List.drop_append_of_le_length hr]
    exact ih _ _ (by simp only [List.length_drop]; omega)

/-! ## The library models -/

/-- `&s[..e]`. -/
theorem slice_index_to {α : Type} (s : Slice α) (e : Std.Usize) (he : e.val ≤ s.length) :
    ∃ t, core.Slice.Insts.CoreOpsIndexIndex.index
        (core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice α) s { «end» := e } =
        ok t ∧ t.val = s.val.take e.val := by
  have he' : e.val ≤ s.val.length := he
  simp [core.Slice.Insts.CoreOpsIndexIndex.index,
    core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
    rust_primitives.slice.slice_length, rust_primitives.slice.slice_slice, Slice.subslice, he']

/-- `&s[b..]`. -/
theorem slice_index_from {α : Type} (s : Slice α) (b : Std.Usize) (hb : b.val ≤ s.length) :
    ∃ t, core.Slice.Insts.CoreOpsIndexIndex.index
        (core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice α) s { start := b } =
        ok t ∧ t.val = s.val.drop b.val := by
  have hb' : b.val ≤ s.val.length := hb
  simp [core.Slice.Insts.CoreOpsIndexIndex.index,
    core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
    rust_primitives.slice.slice_length, rust_primitives.slice.slice_slice, Slice.subslice, hb',
    List.slice]

/-- `&a[..e]` of an array. -/
theorem array_index_to {α : Type} {N : Std.Usize} (a : Array α N) (e : Std.Usize)
    (he : e.val ≤ N.val) :
    ∃ t, core.Array.Insts.CoreOpsIndexIndex.index
        (core.Slice.Insts.CoreOpsIndexIndex
          (core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice α)) a { «end» := e } =
        ok t ∧ t.val = a.val.take e.val := by
  obtain ⟨t, ht, hv⟩ := slice_index_to a.to_slice e (by simpa using he)
  refine ⟨t, ?_, by simpa using hv⟩
  simp only [core.Array.Insts.CoreOpsIndexIndex.index, core.array.Array.as_slice,
    rust_primitives.slice.array_as_slice, Aeneas.Std.bind_ok]
  exact ht

/-- `&a[b..e]` of an array. -/
theorem array_index_range {α : Type} {N : Std.Usize} (a : Array α N) (b e : Std.Usize)
    (h : b.val ≤ e.val) (he : e.val ≤ N.val) :
    ∃ t, core.Array.Insts.CoreOpsIndexIndex.index
        (core.Slice.Insts.CoreOpsIndexIndex
          (core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice α)) a
          { start := b, «end» := e } = ok t ∧ t.val = List.slice b.val e.val a.val := by
  have h1 : b ≤ e := by scalar_tac
  simp [core.Array.Insts.CoreOpsIndexIndex.index, core.array.Array.as_slice,
    rust_primitives.slice.array_as_slice, core.Slice.Insts.CoreOpsIndexIndex.index,
    core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
    rust_primitives.slice.slice_length, rust_primitives.slice.slice_slice, Slice.subslice, h1, h, he]

/-- The primitive under `from_fn`, for a closure that returns `g i` at `i` and keeps itself. -/
theorem array_from_fn_eq {T F : Type} (N : Std.Usize) (inst : core.ops.function.FnMut F Std.Usize T)
    (c : F) (g : ℕ → T)
    (h : ∀ i : Std.Usize, i.val < N.val → inst.call_mut c i = ok (g i.val, c)) :
    ∃ a, rust_primitives.slice.array_from_fn N inst c = ok a ∧
      a.val = (List.range N.val).map g := by
  have go : ∀ n, n ≤ N.val →
      rust_primitives.slice.array_from_fn_go inst c n = ok ((List.range n).map g, c) := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      have hv : (⟨BitVec.ofNat UScalarTy.Usize.numBits n⟩ : Std.Usize).val = n := by
        have := N.hBounds
        simp only [UScalar.val, BitVec.toNat_ofNat]
        exact Nat.mod_eq_of_lt (by scalar_tac)
      rw [rust_primitives.slice.array_from_fn_go, ih (by omega)]
      simp only [Aeneas.Std.bind_ok]
      rw [h _ (by rw [hv]; omega), hv]
      simp [List.range_succ]
  unfold rust_primitives.slice.array_from_fn
  rw [go N.val (Nat.le_refl _)]
  simp

/-- `<[u8; 8]>::try_from(s)` of a slice of eight bytes: those bytes. -/
theorem try_from_8 (s : Slice Std.U8) (h : s.val.length = 8) :
    ∃ a : Array Std.U8 8#usize,
      core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from
        8#usize core.U8.Insts.CoreMarkerCopy s = ok (core.result.Result.Ok a) ∧
      a.val = s.val := by
  have hs : s.len = 8#usize := by
    apply UScalar.eq_of_val_eq
    simp [h]
  obtain ⟨a, ha, hav⟩ := array_from_fn_eq 8#usize
    (core.convert.TryFromArrayShared0SliceTryFromSliceError.try_from.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT
      8#usize core.U8.Insts.CoreMarkerCopy) s (fun i ↦ s.val[i]!) (by
      intro i hi
      have h8 : i.val < 8 := by simpa using hi
      have hidx : s.index_usize i ⦃ x => x = s.val[i.val]! ⦄ := by
        step*
        rw [x_post1]
        exact (getElem!_pos s.val i.val x_post).symm
      obtain ⟨x, hx, rfl⟩ := WP.spec_imp_exists hidx
      simp [core.convert.TryFromArrayShared0SliceTryFromSliceError.try_from.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT.call_mut,
        rust_primitives.slice.slice_index, hx])
  refine ⟨a, ?_, ?_⟩
  · simp [core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from,
      rust_primitives.slice.slice_length, hs, ha]
  · rw [hav]
    apply List.ext_getElem
    · simp [h]
    · intro n h1 h2
      simp [h2]

/-! ## A lane from its bytes -/

theorem or_shift (a b k : ℕ) (h : a < 2 ^ k) : a ||| b <<< k = a + b * 2 ^ k := by
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt h, Nat.shiftLeft_eq]; omega

/-- The statement's lane of eight bytes is the number they spell. -/
theorem lane8 (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) :
    (littleEndianLane [b0, b1, b2, b3, b4, b5, b6, b7] 0).toNat =
      leNat [b0, b1, b2, b3, b4, b5, b6, b7] := by
  have h0 := b0.toNat_lt; have h1 := b1.toNat_lt; have h2 := b2.toNat_lt; have h3 := b3.toNat_lt
  have h4 := b4.toNat_lt; have h5 := b5.toNat_lt; have h6 := b6.toNat_lt; have h7 := b7.toNat_lt
  simp only [littleEndianLane, List.range_succ, leNat]
  simp
  simp only [Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)]
  simp only [← Nat.shiftLeft_eq]
  rw [or_shift _ _ 8 (by omega), or_shift _ _ 16 (by omega), or_shift _ _ 24 (by omega),
    or_shift _ _ 32 (by omega), or_shift _ _ 40 (by omega), or_shift _ _ 48 (by omega),
    or_shift _ _ 56 (by omega)]
  omega

/-- Lane `i` of a byte string reads its bytes `8 i` to `8 i + 7`. -/
theorem lane_slice (l : List UInt8) (i : ℕ) :
    littleEndianLane l i = littleEndianLane ((l.drop (8 * i)).take 8) 0 := by
  simp only [littleEndianLane]
  apply List.foldl_ext
  intro acc k hk
  have hk8 : k < 8 := by simpa using hk
  simp [List.getD, hk8]

/-- The statement's lane `i` of a byte string that holds it, as a number. -/
theorem lane_toNat (l : List UInt8) (i : ℕ) (h : 8 * i + 8 ≤ l.length) :
    (littleEndianLane l i).toNat = leNat ((l.drop (8 * i)).take 8) := by
  rw [lane_slice]
  have hlen : ((l.drop (8 * i)).take 8).length = 8 := by simp; omega
  match (l.drop (8 * i)).take 8, hlen with
  | [b0, b1, b2, b3, b4, b5, b6, b7], _ => exact lane8 ..

/-- The number little-endian bytes spell, as Aeneas reads it. -/
theorem fromLEBytes_toNat (l : List Byte) :
    (BitVec.fromLEBytes l).toNat = l.foldr (fun b acc ↦ b.toNat + 256 * acc) 0 := by
  induction l with
  | nil => simp [BitVec.fromLEBytes]
  | cons b l ih =>
    have hb := b.isLt
    have hl := (BitVec.fromLEBytes l).isLt
    have hw : 2 ^ (8 * (l.length + 1)) = 256 * 2 ^ (8 * l.length) := by
      rw [Nat.mul_add, Nat.pow_add]; ring
    simp only [BitVec.fromLEBytes, List.length_cons, BitVec.toNat_or, BitVec.toNat_setWidth,
      BitVec.toNat_shiftLeft, List.foldr_cons, ← ih]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (a := (BitVec.fromLEBytes l).toNat) (by omega),
      Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; omega), Nat.or_comm,
      ← Nat.shiftLeft_add_eq_or_of_lt (by omega), Nat.shiftLeft_eq]
    omega

/-- `u64::from_le_bytes`: the number its bytes spell. -/
theorem from_le_bytes_toNat (a : Array Std.U8 8#usize) :
    (lane64 (Aeneas.Std.core.num.U64.from_le_bytes a)).toNat = leNat (bytes a.val) := by
  have h : ∀ l : List Std.U8, (l.map U8.bv).foldr (fun b acc ↦ b.toNat + 256 * acc) 0 =
      leNat (bytes l) := by
    intro l
    induction l with
    | nil => rfl
    | cons x xs ih => simp only [List.map_cons, List.foldr_cons, ih, bytes, leNat]; rfl
  simp only [lane64, Aeneas.Std.core.num.U64.from_le_bytes, UInt64.toNat_ofBitVec]
  erw [BitVec.toNat_cast]
  · rw [fromLEBytes_toNat, h]
  · simp

/-- `block_of`'s closure: lane `i` of the block. -/
theorem block_of_closure (b : Array Std.U8 136#usize) (i : Std.Usize) (hi : i.val < 17) :
    ∃ x, keccak256.block_of.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut b i =
        ok (x, b) ∧ lane64 x = littleEndianLane (bytes b.val) i.val := by
  have hmul : 8#usize * i ⦃ r => r.val = 8 * i.val ⦄ := by step*
  obtain ⟨i1, hi1, hi1v⟩ := WP.spec_imp_exists hmul
  have hadd : i1 + 8#usize ⦃ r => r.val = 8 * i.val + 8 ⦄ := by step*
  obtain ⟨i2, hi2, hi2v⟩ := WP.spec_imp_exists hadd
  obtain ⟨s, hs, hsv⟩ := array_index_range b i1 i2 (by omega) (by simp; omega)
  have hlen : s.val.length = 8 := by simp [hsv, List.slice, hi1v, hi2v]; omega
  obtain ⟨a, ha, hav⟩ := try_from_8 s hlen
  refine ⟨Aeneas.Std.core.num.U64.from_le_bytes a, ?_, ?_⟩
  · unfold keccak256.block_of.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
    simp only [hi1, hi2, Aeneas.Std.bind_ok, hs, ha, core.result.Result.unwrap,
      core.num.U64.from_le_bytes, rust_primitives.arithmetic.from_le_bytes_u64]
  · apply UInt64.toNat_inj.mp
    rw [from_le_bytes_toNat, lane_toNat _ _ (by simp; omega), hav, hsv, hi1v, hi2v]
    simp [List.slice, bytes, List.map_take, List.map_drop]

/-- The primitive under `from_fn`, for a closure that keeps itself and returns at `i` something
`P i` holds of. -/
theorem array_from_fn_pred {T F : Type} [Inhabited T] (N : Std.Usize)
    (inst : core.ops.function.FnMut F Std.Usize T) (c : F) (P : ℕ → T → Prop)
    (h : ∀ i : Std.Usize, i.val < N.val → ∃ x, inst.call_mut c i = ok (x, c) ∧ P i.val x) :
    ∃ a, rust_primitives.slice.array_from_fn N inst c = ok a ∧ ∀ i < N.val, P i a.val[i]! := by
  have go : ∀ n, n ≤ N.val → ∃ l : List T,
      rust_primitives.slice.array_from_fn_go inst c n = ok (l, c) ∧ l.length = n ∧
        ∀ i < n, P i l[i]! := by
    intro n
    induction n with
    | zero => intro _; exact ⟨[], rfl, rfl, fun i hi ↦ absurd hi (Nat.not_lt_zero i)⟩
    | succ n ih =>
      intro hn
      obtain ⟨l, hl, hlen, hP⟩ := ih (by omega)
      have hv : (⟨BitVec.ofNat UScalarTy.Usize.numBits n⟩ : Std.Usize).val = n := by
        have := N.hBounds
        simp only [UScalar.val, BitVec.toNat_ofNat]
        exact Nat.mod_eq_of_lt (by scalar_tac)
      obtain ⟨x, hx, hPx⟩ := h ⟨BitVec.ofNat UScalarTy.Usize.numBits n⟩ (by rw [hv]; omega)
      rw [hv] at hPx
      refine ⟨l ++ [x], ?_, by simp [hlen], ?_⟩
      · rw [rust_primitives.slice.array_from_fn_go, hl]
        simp only [Aeneas.Std.bind_ok]
        rw [hx]
        simp only [Aeneas.Std.bind_ok]
      · intro i hi
        by_cases hin : i < n
        · rw [getElem!_pos _ i (by simp [hlen]; omega), List.getElem_append_left (by omega),
            ← getElem!_pos l i (by omega)]
          exact hP i hin
        · obtain rfl : i = n := by omega
          rw [getElem!_pos _ i (by simp [hlen]), List.getElem_append_right (by omega)]
          simpa [hlen] using hPx
  obtain ⟨l, hl, hlen, hP⟩ := go N.val (Nat.le_refl _)
  unfold rust_primitives.slice.array_from_fn
  rw [hl]
  simp only [Aeneas.Std.bind_ok, hlen, ↓reduceDIte]
  exact ⟨_, rfl, by simpa using hP⟩

/-- **`block_of`**: the 17 lanes of a block of 136 bytes. -/
theorem block_of_eq (b : Array Std.U8 136#usize) :
    ∃ a, keccak256.block_of b = ok a ∧
      ∀ i < 17, lane64 a.val[i]! = littleEndianLane (bytes b.val) i :=
  array_from_fn_pred 17#usize keccak256.block_of.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64 b
    (fun i x ↦ lane64 x = littleEndianLane (bytes b.val) i)
    (fun i hi ↦ block_of_closure b i hi)

/-! ## The padding -/

/-- `&mut a[..e]`. -/
theorem array_index_mut_range_to {α : Type} {N : Std.Usize} (a : Array α N) (e : Std.Usize)
    (he : e.val ≤ N.val) :
    ∃ s back, core.Array.Insts.CoreOpsIndexIndexMut.index_mut
      (core.Slice.Insts.CoreOpsIndexIndexMut
        (core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice α))
      a { «end» := e } = ok (s, back) ∧
      s.val = a.val.take e.val ∧ ∀ t : Slice α, (back t).val = a.val.setSlice! 0 t.val := by
  simp [core.Array.Insts.CoreOpsIndexIndexMut.index_mut, core.array.Array.as_mut_slice,
    rust_primitives.slice.array_as_mut_slice, core.Slice.Insts.CoreOpsIndexIndexMut.index_mut,
    core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
    rust_primitives.slice.slice_slice_mut, Slice.subslice, Array.to_slice_mut]
  refine ⟨_, _, by simp only [he, ↓reduceIte]; exact Aeneas.Std.bind_ok _ _, by simp, fun t => ?_⟩
  rw [Array.from_slice_val _ _ (by simp)]
  simp

/-- `a[i]`. -/
theorem array_index_usize {α : Type} [Inhabited α] {N : Std.Usize} (a : Array α N) (i : Std.Usize)
    (h : i.val < N.val) : a.index_usize i = ok a.val[i.val]! := by
  have hs : a.index_usize i ⦃ x => x = a.val[i.val]! ⦄ := by
    step*
    rw [x_post1]
    exact (getElem!_pos a.val i.val (by simpa using h)).symm
  obtain ⟨x, hx, rfl⟩ := WP.spec_imp_exists hs
  exact hx

/-- `a[i] = x`. -/
theorem array_update {α : Type} {N : Std.Usize} (a : Array α N) (i : Std.Usize) (x : α)
    (h : i.val < N.val) : ∃ a', a.update i x = ok a' ∧ a'.val = a.val.set i.val x := by
  have hs : a.update i x ⦃ a' => a'.val = a.val.set i.val x ⦄ := by
    step*
  exact WP.spec_imp_exists hs

theorem b8_xor (x y : Std.U8) : b8 (x ^^^ y) = b8 x ^^^ b8 y := by
  simp [b8]

theorem modify_eq_set {α : Type} [Inhabited α] (l : List α) (i : ℕ) (f : α → α) (h : i < l.length) :
    l.modify i f = l.set i (f l[i]!) := by
  rw [List.modify_eq_set_getElem?]
  simp [h]

theorem bytes_set (l : List Std.U8) (i : ℕ) (x : Std.U8) :
    bytes (l.set i x) = (bytes l).set i (b8 x) := by
  simp [bytes, List.map_set]

theorem bytes_getElem! (l : List Std.U8) (i : ℕ) : (bytes l)[i]! = b8 l[i]! := by
  by_cases h : i < l.length
  · simp [bytes, h]
  · simp [bytes, h]
    rfl

/-- Writing a short list over the start of a constant one. -/
theorem setSlice!_zero_replicate {α : Type} (n : ℕ) (x : α) (t : List α) (h : t.length ≤ n) :
    (List.replicate n x).setSlice! 0 t = t ++ List.replicate (n - t.length) x := by
  simp only [List.setSlice!, List.take_zero, List.nil_append, Nat.sub_zero, List.length_replicate,
    Nat.zero_add, List.drop_replicate]
  rw [Nat.min_eq_left h, List.take_of_length_le (Nat.le_refl _)]

/-- **`final_block`**: the 17 lanes of the padded last block. -/
theorem final_block_eq (tail : Slice Std.U8) (h : tail.length < 136) :
    ∃ a, keccak256.final_block tail = ok a ∧
      ∀ i < 17, lane64 a.val[i]! = littleEndianLane (padBlock (bytes tail.val)) i := by
  have h' : tail.val.length < 136 := h
  obtain ⟨z, hz, hzv⟩ := array_repeat 136#usize core.U8.Insts.CoreCloneClone (fun _ ↦ rfl) 0#u8
  have hlt : tail.len < 136#usize := by scalar_tac
  have hlv : tail.len.val = tail.val.length := by simp
  obtain ⟨s, back, hidx, hsv, hback⟩ := array_index_mut_range_to z tail.len (by simp; omega)
  have hcopy := copy_from_slice_u8 s tail (by simp [Slice.length, hsv, hzv]; omega)
  have hbv : (back tail).val = tail.val ++ List.replicate (136 - tail.val.length) 0#u8 := by
    rw [hback, hzv]
    exact setSlice!_zero_replicate 136 _ _ (by omega)
  have hi1 := array_index_usize (back tail) tail.len (by simp; omega)
  obtain ⟨b2, hb2, hb2v⟩ := array_update (back tail) tail.len ((back tail).val[tail.len.val]! ^^^ 1#u8)
    (by simp; omega)
  have hsub : 136#usize - 1#usize = ok 135#usize := by
    have : 136#usize - 1#usize ⦃ r => r = 135#usize ⦄ := by step*
    obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists this
    exact hr
  have hi4 := array_index_usize b2 135#usize (by decide)
  obtain ⟨b3, hb3, hb3v⟩ := array_update b2 135#usize (b2.val[(135#usize).val]! ^^^ 128#u8)
    (by decide)
  obtain ⟨a, ha, hav⟩ := block_of_eq b3
  have hpad : bytes b3.val = padBlock (bytes tail.val) := by
    have hL : bytes (back tail).val =
        bytes tail.val ++ List.replicate (rate - (bytes tail.val).length) 0 := by
      rw [hbv]
      simp [bytes, rate]
      exact Or.inr rfl
    have hbl : (bytes tail.val).length < 136 := by simpa using h'
    rw [hb3v, bytes_set, b8_xor, ← bytes_getElem!, hb2v, bytes_set, b8_xor, ← bytes_getElem!, hL,
      hlv, ← bytes_length tail.val]
    simp only [padBlock]
    rw [modify_eq_set _ _ _ (by simp [rate]; omega), modify_eq_set _ _ _ (by simp [rate]; omega)]
    have e1 : (135#usize).val = rate - 1 := by decide
    have e2 : b8 1#u8 = padFirst := by decide
    have e3 : b8 128#u8 = padLast := by decide
    rw [e1, e2, e3]
  refine ⟨a, ?_, fun i hi ↦ by rw [← hpad]; exact hav i hi⟩
  unfold keccak256.final_block
  simp only [keccak256.RATE, keccak256.PAD_FIRST, keccak256.PAD_LAST, hz, core.slice.Slice.len,
    rust_primitives.slice.slice_length, massert, hlt, hidx, hsub, lift, Aeneas.Std.bind_ok,
    ↓reduceIte]
  show (do
    let s1 ← core.slice.Slice.copy_from_slice core.U8.Insts.CoreMarkerCopy s tail
    let i1 ← (back s1).index_usize tail.len
    let bytes2 ← (back s1).update tail.len (i1 ^^^ 1#u8)
    let i4 ← bytes2.index_usize 135#usize
    let bytes3 ← bytes2.update 135#usize (i4 ^^^ 128#u8)
    keccak256.block_of bytes3) = ok a
  simp only [hcopy, hi1, hb2, hi4, hb3, ha, Aeneas.Std.bind_ok]

/-! ## The hasher -/

/-- `a.min(b)` on `usize`. -/
theorem usize_min (a b : Std.Usize) :
    core.Usize.Insts.CoreCmpOrd.min a b = ok (if a.val ≤ b.val then a else b) := by
  simp only [core.cmp.Ord.min, core.cmp.min, core.Usize.Insts.CoreCmpOrd, core.mkUOrd,
    Aeneas.Std.bind_ok]
  rcases Nat.lt_trichotomy a.val b.val with h | h | h
  · simp [Nat.compare_eq_lt.mpr h, Nat.le_of_lt h]
  · simp [h]
  · simp [Nat.compare_eq_gt.mpr h, Nat.not_le.mpr h]

/-- One sponge step, given the block's lanes: the statement's. -/
theorem absorb_eq {π : KeccakState → KeccakState} (S : SpongeSpec π)
    (st : Array Std.U64 25#usize) (blk : Array Std.U64 17#usize) (B : List UInt8)
    (hB : ∀ i < 17, lane64 blk.val[i]! = littleEndianLane B i) :
    ∃ st', keccak256.absorb st blk = ok st' ∧ toState st' = absorbBlock π (toState st) B := by
  obtain ⟨st', h1, h2⟩ := S.absorb st blk
  refine ⟨st', h1, ?_⟩
  refine Eq.trans h2 (congrArg π (congrArg Vector.ofFn (funext fun i ↦ ?_)))
  split_ifs with hi
  · rw [hB i.val hi]
  · rfl

/-- `h` has absorbed the bytes `l`: its state is the sponge's after the whole blocks of `l`, and
its buffer holds the bytes after them. -/
structure Absorbed (π : KeccakState → KeccakState) (h : keccak256.Hasher) (l : List UInt8) :
    Prop where
  state : toState h.state = blocks π (l.length / rate) (Vector.replicate 25 0) l
  len : h.buf_len.val = l.length % rate
  buf : bytes (h.buf.val.take h.buf_len.val) = l.drop (rate * (l.length / rate))

theorem new_absorbed (π : KeccakState → KeccakState) :
    ∃ h, keccak256.Hasher.new = ok h ∧ Absorbed π h [] := by
  obtain ⟨a, ha, hav⟩ := array_repeat 25#usize core.U64.Insts.CoreCloneClone (fun _ ↦ rfl) 0#u64
  obtain ⟨b, hb, hbv⟩ := array_repeat 136#usize core.U8.Insts.CoreCloneClone (fun _ ↦ rfl) 0#u8
  have h0 : (0#usize).val = 0 := rfl
  refine ⟨⟨a, b, 0#usize⟩, by simp only [keccak256.Hasher.new, ha, hb, Aeneas.Std.bind_ok], ?_⟩
  constructor
  · show toState a = Vector.replicate 25 0
    apply Vector.ext
    intro i hi
    simp only [toState, Vector.getElem_ofFn, Vector.getElem_replicate]
    have hav' : a.val = List.replicate 25 0#u64 := hav
    rw [hav', List.getElem!_replicate _ hi]
    rfl
  · show (0#usize).val = _
    rw [h0]; rfl
  · show bytes (b.val.take (0#usize).val) = _
    rw [h0]; rfl

/-- One turn of `update`'s loop on bytes still to absorb: some of them go into the buffer, and a
full buffer into the sponge. -/
theorem update_body {π : KeccakState → KeccakState} (S : SpongeSpec π) (h : keccak256.Hasher)
    (l : List UInt8) (hA : Absorbed π h l) (d : Slice Std.U8) (hd : 0 < d.val.length) :
    ∃ h' d', keccak256.Hasher.update_loop.body h d = ok (ControlFlow.cont (h', d')) ∧
      d'.val.length < d.val.length ∧
      ∃ t, bytes d.val = t ++ bytes d'.val ∧ Absorbed π h' (l ++ t) := by
  obtain ⟨hst, hlen, hbuf⟩ := hA
  have hr : l.length % rate < 136 := Nat.mod_lt _ (by decide)
  have hne : ¬ (d.len = 0#usize) := by
    intro h0
    have hl : d.len.val = d.val.length := by simp
    rw [h0] at hl
    have : (0#usize).val = 0 := rfl
    omega
  have hsub : keccak256.RATE - h.buf_len ⦃ r => r.val = 136 - h.buf_len.val ⦄ := by
    simp only [keccak256.RATE]
    step*
  obtain ⟨i, hi, hiv⟩ := WP.spec_imp_exists hsub
  obtain ⟨take, htake, htv⟩ : ∃ take : Std.Usize, core.Usize.Insts.CoreCmpOrd.min i d.len = ok take ∧
      take.val = min (136 - h.buf_len.val) d.val.length := by
    refine ⟨_, usize_min i d.len, ?_⟩
    split_ifs with hle
    · rw [hiv]; simp at hle; omega
    · simp at hle ⊢; omega
  have hle : h.buf_len.val + take.val ≤ 136 := by omega
  have hadd : h.buf_len + take ⦃ r => r.val = h.buf_len.val + take.val ⦄ := by
    step*
  obtain ⟨i2, hi2, hi2v⟩ := WP.spec_imp_exists hadd
  obtain ⟨s, back, hidx, hsv, hback⟩ := array_index_mut_range h.buf h.buf_len i2 (by omega)
    (by simp; omega)
  obtain ⟨s1, hs1, hs1v⟩ := slice_index_to d take (by simp [Slice.length]; omega)
  have hcopy := copy_from_slice_u8 s s1 (by
    simp [Slice.length, hsv, hs1v, List.slice]
    omega)
  obtain ⟨d1, hd1, hd1v⟩ := slice_index_from d take (by simp [Slice.length]; omega)
  have htpos : 0 < take.val := by omega
  have hsplit : bytes d.val = bytes (d.val.take take.val) ++ bytes d1.val := by
    rw [hd1v]; simp [bytes]
  have hbody : keccak256.Hasher.update_loop.body h d =
      (if i2 = keccak256.RATE then do
        let a1 ← keccak256.block_of (back s1)
        let a2 ← keccak256.absorb h.state a1
        ok (ControlFlow.cont (({ state := a2, buf := back s1, buf_len := 0#usize } : keccak256.Hasher), d1))
      else ok (ControlFlow.cont ({ h with buf := back s1, buf_len := i2 }, d1))) := by
    unfold keccak256.Hasher.update_loop.body
    simp only [core.slice.Slice.is_empty, core.slice.Slice.len, rust_primitives.slice.slice_length,
      hne, decide_false, Bool.false_eq_true, ↓reduceIte, Aeneas.Std.bind_ok, hi, htake, hi2, hidx,
      hs1, hd1]
    show (do
      let s2 ← core.slice.Slice.copy_from_slice core.U8.Insts.CoreMarkerCopy s s1
      if i2 = keccak256.RATE then do
        let a1 ← keccak256.block_of (back s2)
        let a2 ← keccak256.absorb h.state a1
        ok (ControlFlow.cont (({ state := a2, buf := back s2, buf_len := 0#usize } : keccak256.Hasher), d1))
      else ok (ControlFlow.cont ({ h with buf := back s2, buf_len := i2 }, d1))) = _
    have hk : ∀ {β : Type} (k : Slice Std.U8 → RustM β),
        (do
          let s2 ← core.slice.Slice.copy_from_slice core.U8.Insts.CoreMarkerCopy s s1
          k s2) = k s1 := by
      intro β k
      simp only [hcopy, Aeneas.Std.bind_ok]
    exact hk _
  have hrate : rate = 136 := rfl
  rw [hrate] at hst hlen hbuf hr
  have hdlt : d1.val.length < d.val.length := by rw [hd1v]; simp; omega
  have htl : (bytes (d.val.take take.val)).length = take.val := by simp; omega
  have hkey : bytes ((back s1).val.take (h.buf_len.val + take.val)) =
      l.drop (136 * (l.length / 136)) ++ bytes (d.val.take take.val) := by
    rw [hback, hs1v, ← hbuf]
    have hb136 : h.buf.val.length = 136 := by simp
    have htk : (d.val.take take.val).length = take.val := by simp; omega
    simp only [List.setSlice!, htk, hb136]
    rw [Nat.min_eq_left (by omega), List.take_of_length_le (i := take.val) (by omega),
      List.take_append_of_le_length (by simp; omega),
      List.take_of_length_le (by simp; omega)]
    simp [bytes]
  have hll : l.length = 136 * (l.length / 136) + l.length % 136 := (Nat.div_add_mod _ _).symm
  have hR : keccak256.RATE = 136#usize := by unfold keccak256.RATE; rfl
  have h136 : (136#usize).val = 136 := rfl
  by_cases hfull : h.buf_len.val + take.val = 136
  · have hi2R : i2 = keccak256.RATE := by
      rw [hR]
      apply UScalar.eq_of_val_eq
      rw [hi2v, hfull, h136]
    obtain ⟨a1, ha1, ha1v⟩ := block_of_eq (back s1)
    obtain ⟨st', hst', hst'v⟩ := absorb_eq S h.state a1 (bytes (back s1).val) ha1v
    refine ⟨⟨st', back s1, 0#usize⟩, d1, ?_, hdlt, bytes (d.val.take take.val), hsplit, ?_⟩
    · rw [hbody]
      simp only [hi2R, ↓reduceIte, ha1, hst', Aeneas.Std.bind_ok]
    · have hbl : (back s1).val.length = 136 := by simp
      have hwhole : bytes (back s1).val =
          l.drop (136 * (l.length / 136)) ++ bytes (d.val.take take.val) := by
        rw [← hkey, hfull, List.take_of_length_le (by omega)]
      have hlen' : (l ++ bytes (d.val.take take.val)).length = 136 * (l.length / 136 + 1) := by
        rw [List.length_append, htl]; omega
      constructor
      · show toState st' = _
        have hw2 : ((l ++ bytes (d.val.take take.val)).drop (136 * (l.length / 136))).take 136 =
            bytes (back s1).val := by
          rw [List.drop_append_of_le_length (by omega), ← hwhole, List.take_of_length_le (by simp)]
        rw [hrate, hlen', Nat.mul_div_cancel_left _ (by decide), blocks_succ, hst'v, hst,
          blocks_append _ _ _ _ _ (by rw [hrate]; omega), hrate, hw2]
      · show (0#usize).val = _
        rw [hrate, hlen']
        simp
      · show bytes ((back s1).val.take (0#usize).val) = _
        rw [hrate, hlen', Nat.mul_div_cancel_left _ (by decide), List.drop_of_length_le (by omega)]
        rfl
  · have hi2R : ¬ i2 = keccak256.RATE := by
      intro e
      rw [hR] at e
      have hv := congrArg UScalar.val e
      rw [hi2v, h136] at hv
      exact hfull hv
    refine ⟨{ h with buf := back s1, buf_len := i2 }, d1, ?_, hdlt, bytes (d.val.take take.val),
      hsplit, ?_⟩
    · rw [hbody]
      simp only [hi2R, ↓reduceIte]
    · have hdiv : (l ++ bytes (d.val.take take.val)).length / 136 = l.length / 136 := by
        rw [List.length_append, htl]; omega
      constructor
      · show toState h.state = _
        rw [hrate, hdiv, hst, blocks_append _ _ _ _ _ (by rw [hrate]; omega)]
      · show i2.val = _
        rw [hrate, List.length_append, htl]; omega
      · show bytes ((back s1).val.take i2.val) = _
        rw [hrate, hdiv, hi2v, hkey, List.drop_append_of_le_length (by omega)]

/-- A loop whose body keeps an invariant and decreases a measure returns, with what the
invariant gives on leaving. -/
theorem loop_induct {α β : Type} (body : α → RustM (ControlFlow α β)) (inv : α → Prop)
    (Q : β → Prop) (μ : α → ℕ)
    (hstep : ∀ x, inv x → ∃ r, body x = ok r ∧
      (match r with
        | .cont x' => inv x' ∧ μ x' < μ x
        | .done y => Q y)) :
    ∀ x, inv x → ∃ y, loop body x = ok y ∧ Q y := by
  intro x
  induction h : μ x using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    intro hx
    obtain ⟨r, hr, hpost⟩ := hstep x hx
    rw [loop.eq_def, hr, Aeneas.Std.bind_ok]
    cases r with
    | cont x' =>
      obtain ⟨hi, hlt⟩ := hpost
      exact ih _ (h ▸ hlt) x' rfl hi
    | done y => exact ⟨y, rfl, hpost⟩

/-- **`update`'s loop**: every byte of the slice absorbed. -/
theorem update_loop_absorbed {π : KeccakState → KeccakState} (S : SpongeSpec π)
    (h : keccak256.Hasher) (l : List UInt8) (hA : Absorbed π h l) (m : Slice Std.U8) :
    ∃ h', keccak256.Hasher.update_loop h m = ok h' ∧ Absorbed π h' (l ++ bytes m.val) := by
  unfold keccak256.Hasher.update_loop
  refine loop_induct
    (fun x : keccak256.Hasher × Slice Std.U8 ↦ keccak256.Hasher.update_loop.body x.1 x.2)
    (fun x ↦ ∃ l', Absorbed π x.1 l' ∧ l' ++ bytes x.2.val = l ++ bytes m.val)
    (fun h' ↦ Absorbed π h' (l ++ bytes m.val)) (fun x ↦ x.2.val.length) ?_ (h, m) ⟨l, hA, rfl⟩
  rintro ⟨h1, d⟩ ⟨l', hA', hl'⟩
  simp only at hA' hl' ⊢
  by_cases hd : d.val.length = 0
  · have h0 : d.len = 0#usize := by
      apply UScalar.eq_of_val_eq
      simp [hd]
    refine ⟨.done h1, ?_, ?_⟩
    · unfold keccak256.Hasher.update_loop.body
      simp only [core.slice.Slice.is_empty, core.slice.Slice.len,
        rust_primitives.slice.slice_length, h0, decide_true, ↓reduceIte, Aeneas.Std.bind_ok]
    · have : d.val = [] := List.length_eq_zero_iff.mp hd
      rw [this] at hl'
      have e : l' = l ++ bytes m.val := by simpa [bytes] using hl'
      exact e ▸ hA'
  · obtain ⟨h', d', hbody, hlt, t, ht, hA''⟩ := update_body S h1 l' hA' d (by omega)
    refine ⟨.cont (h', d'), hbody, ⟨l' ++ t, hA'', ?_⟩, hlt⟩
    rw [List.append_assoc, ← ht, hl']

/-- **`finalize`**: Keccak-256 of what was absorbed. -/
theorem finalize_absorbed {π : KeccakState → KeccakState} (S : SpongeSpec π)
    (h : keccak256.Hasher) (l : List UInt8) (hA : Absorbed π h l) :
    ∃ d, keccak256.Hasher.finalize h = ok d ∧ bytes d.val = hashBytes π l := by
  obtain ⟨hst, hlen, hbuf⟩ := hA
  have hr : l.length % rate < 136 := Nat.mod_lt _ (by decide)
  obtain ⟨s, hs, hsv⟩ := array_index_to h.buf h.buf_len (by simp; omega)
  have hsl : s.length < 136 := by
    show s.val.length < 136
    rw [hsv]; simp; omega
  obtain ⟨a, ha, hav⟩ := final_block_eq s hsl
  obtain ⟨st', hst', hst'v⟩ := absorb_eq S h.state a _ hav
  obtain ⟨d, hd, hdv⟩ := S.digest_of st'
  refine ⟨d, by simp only [keccak256.Hasher.finalize, hs, ha, hst', hd, Aeneas.Std.bind_ok], ?_⟩
  have hfin : toState st' =
      Id.run (absorbWith (inId π) (l.length / rate) (Vector.replicate 25 0) l) := by
    rw [absorbWith_eq, hst'v, hst, hsv, hbuf]
  rw [hdv, hfin]
  rfl

end Hasher

open Hasher in
/-- **`keccak256::Hasher` computes Keccak-256 over `π`**, given what `absorb` and `digest_of`
compute: the assumption of the theorem about `verify` (`HasherSpec`, `Defs.lean`), from the
smaller one. -/
def hasherSpec_of_sponge {π : KeccakState → KeccakState} (S : SpongeSpec π) : HasherSpec π where
  Absorbed := Absorbed π
  new := new_absorbed π
  update := by
    intro h l m hA
    obtain ⟨h', hh', hA'⟩ := update_loop_absorbed S h l hA m
    exact ⟨h', fun x ↦ x, by simp only [keccak256.Hasher.update, hh', Aeneas.Std.bind_ok], hA',
      fun _ ↦ rfl⟩
  finalize := finalize_absorbed S

end LeanSphincsProofs
