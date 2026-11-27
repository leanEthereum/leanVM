import Keccak256Proofs.Library

/-!
# Truncation, and digests as numbers

`keccak256::truncate` keeps a hash output's first bytes, the statement's `truncateHash`; a Rust
digest is the number its bytes spell, least significant first.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM Std.Do
open HashSig HashSig.OverPermutation
open LeanVM.Semantics (KeccakState)
open LeanVM.Protocol.KeccakHash (digestBytes keccak256With)

namespace Keccak256Proofs

/-- The values `try_from` reads off a slice: its first `n`. -/
theorem try_from_go {α : Type} (N : Std.Usize) (inst : core.marker.Copy α) :
    ∀ (n : ℕ) (c : Slice α), n ≤ c.length →
      rust_primitives.slice.array_from_fn_go
        (core.convert.TryFromArrayShared0SliceTryFromSliceError.try_from.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT
          N inst) c n = ok (c.val.take n, c) := by
  intro n
  induction n with
  | zero => intro c _; simp [rust_primitives.slice.array_from_fn_go]
  | succ n ih =>
    intro c hn
    have hn' : n < c.val.length := hn
    simp only [rust_primitives.slice.array_from_fn_go]
    erw [ih c (by omega)]
    erw [Aeneas.Std.bind_ok]
    simp [core.convert.TryFromArrayShared0SliceTryFromSliceError.try_from.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT.call_mut,
      rust_primitives.slice.slice_index, Slice.index_usize]
    have hmax : c.val.length ≤ Usize.max := by scalar_tac
    have hv : ((BitVec.ofNat System.Platform.numBits n)#uscalar : Std.Usize).val = n := by
      show (BitVec.ofNat System.Platform.numBits n).toNat = n
      rw [BitVec.toNat_ofNat]
      apply Nat.mod_eq_of_lt
      have : Usize.max = 2 ^ System.Platform.numBits - 1 := by
        simp [Usize.max, Usize.numBits]
      have hpos : 0 < 2 ^ System.Platform.numBits := Nat.two_pow_pos _
      omega
    rw [hv, List.getElem?_eq_getElem hn']
    erw [Aeneas.Std.bind_ok]
    rw [List.take_succ_eq_append_getElem hn']

/-- `Truncate_16`: the first sixteen bytes of a hash output. -/
theorem truncate_16 (d : Array Std.U8 32#usize) :
    ∃ r : Array Std.U8 16#usize, keccak256.truncate 16#usize d = ok r ∧ r.val = d.val.take 16 := by
  have hd : d.val.length = 32 := by simp
  have hb : (List.take 16 d.val).length ≤ Usize.max := by simp; scalar_tac
  have hgo := try_from_go 16#usize core.U8.Insts.CoreMarkerCopy 16
    (Slice.from (List.take 16 d.val) hb) (by simp [Slice.length])
  have hlen : (Slice.from (List.take 16 d.val) hb).len = 16#usize := by
    apply UScalar.eq_of_val_eq
    simp
  have hl : (List.take 16 (Slice.from (List.take 16 d.val) hb).val).length = 16 := by simp
  refine ⟨Array.from _ hl, ?_, by simp⟩
  simp [keccak256.truncate, core.Array.Insts.CoreOpsIndexIndex.index,
    core.array.Array.as_slice, rust_primitives.slice.array_as_slice,
    core.Slice.Insts.CoreOpsIndexIndex.index,
    core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
    rust_primitives.slice.slice_length, rust_primitives.slice.slice_slice, Slice.subslice,
    core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from,
    rust_primitives.slice.array_from_fn, core.result.Result.unwrap, hlen]
  erw [hgo]
  erw [Aeneas.Std.bind_ok]
  simp only [hl, ↓reduceDIte]
  exact congrArg ok (Aeneas.Std.Array.ext _ _ (by simp))

theorem leNat_take (l : List UInt8) (k : ℕ) : leNat (l.take k) = leNat l % 256 ^ k := by
  induction l generalizing k with
  | nil => simp [leNat]
  | cons b bs ih =>
    have hb : b.toNat < 256 := b.toNat_lt
    cases k with
    | zero => simp [leNat, Nat.mod_one]
    | succ k =>
      have key := ih k
      simp only [leNat, List.take_succ_cons, List.foldr_cons] at key ⊢
      rw [key, Nat.pow_succ']
      generalize List.foldr (fun b acc ↦ b.toNat + 256 * acc) 0 bs = X
      have hM : 0 < 256 ^ k := Nat.pow_pos (by norm_num)
      generalize 256 ^ k = M at hM ⊢
      have hX := Nat.div_add_mod X M
      have hlt := Nat.mod_lt X hM
      generalize X / M = q at hX
      generalize X % M = r at hX hlt ⊢
      subst hX
      rw [show b.toNat + 256 * (M * q + r) = (b.toNat + 256 * r) + (256 * M) * q by ring,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem digestBytes_length (d : LeanVM.Protocol.Digest) : (digestBytes d).length = 32 := by
  simp [digestBytes, LeanVM.Protocol.KeccakHash.wordBytes, List.length_flatMap]

theorem leNat_cons (b : UInt8) (l : List UInt8) : leNat (b :: l) = b.toNat + 256 * leNat l := rfl

/-- The low 128 bits of the number a byte string spells are spelled by its first 16 bytes. -/
theorem truncateHash_leNat (l : List UInt8) :
    truncateHash (BitVec.ofNat 256 (leNat l)) = BitVec.ofNat 128 (leNat (l.take 16)) := by
  apply BitVec.eq_of_toNat_eq
  have happ := leNat_append (l.take 16) (l.drop 16)
  rw [List.take_append_drop] at happ
  have hlt := leNat_lt (l.take 16)
  have hlen : (l.take 16).length ≤ 16 := by simp
  simp only [truncateHash, digestBits, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat,
    Nat.shiftRight_zero]
  rcases Nat.lt_or_ge l.length 16 with hs | hs
  · rw [List.drop_eq_nil_of_le (by omega)] at happ
    rw [happ]; simp [leNat]
  · have h16 : (l.take 16).length = 16 := by simp; omega
    rw [h16] at happ hlt
    rw [happ]
    omega

/-- `truncate`: the first 16 bytes of a hash output. -/
theorem truncate_eq (d : Array Std.U8 32#usize) :
    ∃ a : Array Std.U8 16#usize, keccak256.truncate 16#usize d = ok a ∧ a.val = d.val.take 16 := by
  have hlen : d.val.length = 32 := by simp
  have hb : (List.take 16 d.val).length ≤ Usize.max := by simp; scalar_tac
  have hs : (Slice.from (List.take 16 d.val) hb).len = 16#usize := by
    have : (Slice.from (List.take 16 d.val) hb).len.val = 16 := by
      rw [Slice.len_val, Slice.length, slice_from_val]; simp [hlen]
    scalar_tac
  obtain ⟨a, ha, hav⟩ := array_from_fn_eq 16#usize
    (core.convert.TryFromArrayShared0SliceTryFromSliceError.try_from.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT
      16#usize core.U8.Insts.CoreMarkerCopy)
    (Slice.from (List.take 16 d.val) hb) (fun i => (List.take 16 d.val)[i]!) (by
      intro i hi
      have hidx : (Slice.from (List.take 16 d.val) hb).index_usize i
          ⦃ x => x = (List.take 16 d.val)[i.val]! ⦄ := by
        step*
        have h16 : i.val < 16 := by simpa using hi
        simp [x_post1, h16]
      obtain ⟨x, hx, rfl⟩ := WP.spec_imp_exists hidx
      simp [core.convert.TryFromArrayShared0SliceTryFromSliceError.try_from.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT.call_mut,
        rust_primitives.slice.slice_index, hx])
  refine ⟨a, ?_, ?_⟩
  · unfold keccak256.truncate
    simp [core.Array.Insts.CoreOpsIndexIndex.index, core.array.Array.as_slice,
      rust_primitives.slice.array_as_slice, core.Slice.Insts.CoreOpsIndexIndex.index,
      core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
      rust_primitives.slice.slice_length, rust_primitives.slice.slice_slice, Slice.subslice,
      core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from,
      core.result.Result.unwrap, hs, ha]
  · rw [hav]
    apply List.ext_getElem
    · simp [hlen]
    · intro n h1 h2
      simp at h1
      simp [h1]

/-- The truncation of a Keccak-256 digest, as the statement's truncated hash. -/
theorem toDigest_truncate {π : KeccakState → KeccakState} (l : List UInt8)
    (d : Array Std.U8 32#usize) (a : Array Std.U8 16#usize) (hd : bytes d.val = hashBytes π l)
    (ha : a.val = d.val.take 16) :
    toDigest a = truncateHash (Id.run (keccakHash (inId π) l)) := by
  rw [keccakHash_inId, truncateHash_leNat, ← hd, toDigest, ha]
  simp only [bytes, List.map_take]
  rfl

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

/-- A Rust digest as a number: the one its bytes spell, least significant first. -/
theorem toDigest_toNat (a : Array Std.U8 16#usize) : (toDigest a).toNat = leNat (bytes a.val) := by
  have h := leNat_lt (bytes a.val)
  have hl : (bytes a.val).length = 16 := by simp [bytes]
  rw [hl] at h
  show leNat (bytes a.val) % 2 ^ 128 = leNat (bytes a.val)
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h (by norm_num))

/-! ## Equality of digests -/

/-- One step of `==` on `[u8; N]`: on to the next index, or `false` at a difference. -/
theorem array_eq_body {N : Std.Usize} (a b : Array Std.U8 N) (i : Std.Usize) (h : i.val < N.val) :
    ⦃ ⌜ True ⌝ ⦄
    core.Array.Insts.CoreCmpPartialEqArray.eq_loop.body core.U8.Insts.CoreCmpPartialEqU8 a b i
    ⦃ ⇓ r => ⌜ match r with
      | .cont i1 => a.val[i.val]! = b.val[i.val]! ∧ i1.val = i.val + 1
      | .done v => v = false ∧ a.val[i.val]! ≠ b.val[i.val]! ⌝ ⦄ := by
  have ha : a.to_slice.length = N.val := by simp
  have hb : b.to_slice.length = N.val := by simp
  hax_mvcgen [core.Array.Insts.CoreCmpPartialEqArray.eq_loop.body, core.U8.Insts.CoreCmpPartialEqU8,
    rust_primitives.slice.array_index]
  case vc1.hQ =>
    rename_i x hx y hy heq r hr
    obtain ⟨hxa, rfl⟩ := hx
    obtain ⟨hyb, rfl⟩ := hy
    have hla : i.val < a.val.length := by simpa using h
    have hlb : i.val < b.val.length := by simpa using h
    refine ⟨?_, by scalar_tac⟩
    rw [getElem!_pos a.val i.val hla, getElem!_pos b.val i.val hlb]
    simpa using heq
  case vc2.h_fail => scalar_tac
  case vc3.hQ =>
    rename_i x hx y hy hne
    obtain ⟨hxa, rfl⟩ := hx
    obtain ⟨hyb, rfl⟩ := hy
    have hla : i.val < a.val.length := by simpa using h
    have hlb : i.val < b.val.length := by simpa using h
    refine ⟨trivial, ?_⟩
    rw [getElem!_pos a.val i.val hla, getElem!_pos b.val i.val hlb]
    simpa using hne
  case vc4.h_fail => rename_i hge; omega
  case vc5.h_fail => rename_i hge; omega

/-- `==` on `[u8; N]`, from index `i` on: whether the arrays agree from there. -/
theorem array_eq_loop {N : Std.Usize} (a b : Array Std.U8 N) (n : ℕ) :
    ∀ i : Std.Usize, N.val - i.val = n → i.val ≤ N.val →
      core.Array.Insts.CoreCmpPartialEqArray.eq_loop core.U8.Insts.CoreCmpPartialEqU8 a b i =
        ok (decide (a.val.drop i.val = b.val.drop i.val)) := by
  have hla : a.val.length = N.val := by simp
  have hlb : b.val.length = N.val := by simp
  induction n with
  | zero =>
    intro i hn hi
    have hlt : ¬ (i < N) := by scalar_tac
    unfold core.Array.Insts.CoreCmpPartialEqArray.eq_loop
    rw [loop.eq_def]
    simp [core.Array.Insts.CoreCmpPartialEqArray.eq_loop.body, hlt]
    rw [List.drop_of_length_le (by omega), List.drop_of_length_le (by omega)]
  | succ n ih =>
    intro i hn hi
    obtain ⟨r, hr, hp⟩ := ok_of_triple (array_eq_body a b i (by omega))
    have hda : a.val.drop i.val = a.val[i.val]! :: a.val.drop (i.val + 1) := by
      rw [List.drop_eq_getElem_cons (by omega), getElem!_pos a.val i.val (by omega)]
    have hdb : b.val.drop i.val = b.val[i.val]! :: b.val.drop (i.val + 1) := by
      rw [List.drop_eq_getElem_cons (by omega), getElem!_pos b.val i.val (by omega)]
    unfold core.Array.Insts.CoreCmpPartialEqArray.eq_loop
    rw [loop.eq_def, hr, Aeneas.Std.bind_ok]
    match r, hp with
    | .cont i1, hp =>
      obtain ⟨he, h1⟩ := hp
      have := ih i1 (by omega) (by omega)
      unfold core.Array.Insts.CoreCmpPartialEqArray.eq_loop at this
      simp only [this, hda, hdb, he, h1, List.cons.injEq, true_and]
    | .done v, hp =>
      obtain ⟨rfl, hne⟩ := hp
      simp only [hda, hdb, List.cons.injEq, hne, false_and, decide_false]

/-- `==` on `[u8; N]` is equality. -/
theorem array_eq {N : Std.Usize} (a b : Array Std.U8 N) :
    core.Array.Insts.CoreCmpPartialEqArray.eq core.U8.Insts.CoreCmpPartialEqU8 a b =
      ok (decide (a = b)) := by
  have h := array_eq_loop a b N.val 0#usize (by simp) (by simp)
  simp only [core.Array.Insts.CoreCmpPartialEqArray.eq, h]
  congr 1
  have : (0#usize).val = 0 := rfl
  rw [this, List.drop_zero, List.drop_zero]
  congr 1
  apply propext
  constructor
  · exact (Array.eq_iff a b).mpr
  · rintro rfl; rfl

theorem leNat_inj : ∀ (l l' : List UInt8), l.length = l'.length → leNat l = leNat l' → l = l'
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | b :: bs, b' :: bs', h, he => by
    have hb := b.toNat_lt
    have hb' := b'.toNat_lt
    simp only [leNat, List.foldr_cons] at he
    have h1 : b.toNat = b'.toNat := by omega
    have h2 : leNat bs = leNat bs' := by simp only [leNat]; omega
    rw [leNat_inj bs bs' (by simpa using h) h2, UInt8.toNat_inj.mp h1]

theorem b8_inj {x y : Std.U8} (h : b8 x = b8 y) : x = y := by
  have hb : x.bv = y.bv := by simpa [b8] using h
  cases x; cases y; simp_all

theorem bytes_inj : ∀ {l l' : List Std.U8}, bytes l = bytes l' → l = l'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [bytes] at h
  | _ :: _, [], h => by simp [bytes] at h
  | x :: xs, y :: ys, h => by
    simp only [bytes, List.map_cons, List.cons.injEq] at h
    rw [b8_inj h.1, bytes_inj (l := xs) (l' := ys) h.2]

/-- Distinct Rust digests are distinct statement digests. -/
theorem toDigest_inj {a b : Array Std.U8 16#usize} (h : toDigest a = toDigest b) : a = b := by
  have ha : (bytes a.val).length = 16 := by simp [bytes]
  have hb : (bytes b.val).length = 16 := by simp [bytes]
  have e : (256 : ℕ) ^ 16 = 2 ^ 128 := by norm_num
  have la := leNat_lt (bytes a.val)
  have lb := leNat_lt (bytes b.val)
  rw [ha, e] at la
  rw [hb, e] at lb
  have hn : leNat (bytes a.val) = leNat (bytes b.val) := by
    have h' : BitVec.ofNat 128 (leNat (bytes a.val)) = BitVec.ofNat 128 (leNat (bytes b.val)) := h
    have := congrArg BitVec.toNat h'
    simp only [BitVec.toNat_ofNat] at this
    rwa [Nat.mod_eq_of_lt la, Nat.mod_eq_of_lt lb] at this
  exact (Array.eq_iff a b).mpr (bytes_inj (leNat_inj _ _ (by rw [ha, hb]) hn))

/-- Distinct Rust messages are distinct statement messages. -/
theorem toMessage_inj {a b : Array Std.U8 32#usize} (h : toMessage a = toMessage b) : a = b := by
  have ha : (bytes a.val).length = 32 := by simp [bytes]
  have hb : (bytes b.val).length = 32 := by simp [bytes]
  have e : (256 : ℕ) ^ 32 = 2 ^ 256 := by norm_num
  have la := leNat_lt (bytes a.val)
  have lb := leNat_lt (bytes b.val)
  rw [ha, e] at la
  rw [hb, e] at lb
  have hn : leNat (bytes a.val) = leNat (bytes b.val) := by
    have h' : BitVec.ofNat 256 (leNat (bytes a.val)) = BitVec.ofNat 256 (leNat (bytes b.val)) := h
    have := congrArg BitVec.toNat h'
    simp only [BitVec.toNat_ofNat] at this
    rwa [Nat.mod_eq_of_lt la, Nat.mod_eq_of_lt lb] at this
  exact (Array.eq_iff a b).mpr (bytes_inj (leNat_inj _ _ (by rw [ha, hb]) hn))

end Keccak256Proofs
