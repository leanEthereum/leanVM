import LeanSphincsProofs.Common

/-!
# `hash.rs`: addresses and the tweakable hash

`th` is the truncated Keccak-256 of `PK.seed ‖ ADRS ‖ M` (`th_spec`, from `HasherSpec`), and the
address functions lay out the statement's `Address.toBytes` (`keyAdrs_spec`, `adrsWord_spec`,
`treeAdrs_spec`). Before them, what the Rust library models they step through compute, and how
Rust's bytes are the statement's.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM Std.Do
open HashSig HashSig.OverPermutation Sphincs
open LeanVM.Semantics (KeccakState)
open LeanVM.Protocol.KeccakHash (digestBytes keccak256With)

namespace LeanSphincsProofs

/-! ## The library models -/

theorem setSlice!_length {α : Type} (l : List α) (i : ℕ) (s : List α) :
    (l.setSlice! i s).length = l.length := by
  simp only [List.setSlice!, List.length_append, List.length_take, List.length_drop]
  omega

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

/-- `&mut a[b..]`. -/
theorem array_index_mut_range_from {α : Type} {N : Std.Usize} (a : Array α N) (b : Std.Usize)
    (hb : b.val ≤ N.val) :
    ∃ s back, core.Array.Insts.CoreOpsIndexIndexMut.index_mut
      (core.Slice.Insts.CoreOpsIndexIndexMut
        (core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice α))
      a { start := b } = ok (s, back) ∧
      s.val = a.val.drop b.val ∧ ∀ t : Slice α, (back t).val = a.val.setSlice! b.val t.val := by
  simp [core.Array.Insts.CoreOpsIndexIndexMut.index_mut, core.array.Array.as_mut_slice,
    rust_primitives.slice.array_as_mut_slice, core.Slice.Insts.CoreOpsIndexIndexMut.index_mut,
    core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
    rust_primitives.slice.slice_slice_mut, rust_primitives.slice.slice_length, Slice.subslice,
    Array.to_slice_mut]
  refine ⟨_, _, by simp only [hb, ↓reduceIte]; exact Aeneas.Std.bind_ok _ _, by simp [List.slice], fun t => ?_⟩
  rw [Array.from_slice_val _ _ (by simp)]
  simp

/-- `x.to_be_bytes()` for a `u64`. -/
theorem u64_to_be_bytes (x : Std.U64) :
    core.num.U64.to_be_bytes x = ok (Aeneas.Std.core.num.U64.to_be_bytes x) := rfl

theorem fill_step {α : Type} (l s : List α) (v : α) (i : ℕ)
    (h : l = List.replicate i v ++ s.drop i) (hi : i < s.length) :
    l.set i v = List.replicate (i + 1) v ++ s.drop (i + 1) := by
  subst h
  rw [List.set_append_right _ _ (by simp), List.length_replicate, Nat.sub_self,
    List.drop_eq_getElem_cons hi, List.set_cons_zero, List.replicate_succ', List.append_assoc]
  rfl

/-- `fill`'s loop invariant after `i` bytes. -/
def fillInv (s : Slice Std.U8) (v : Std.U8) (i : Std.Usize) (acc : Slice Std.U8) : RustM Prop :=
  ok (acc.val = List.replicate i.val v ++ s.val.drop i.val)

@[spec]
theorem fill_loop_spec (s : Slice Std.U8) (v : Std.U8) (n : Std.Usize) (hn : n.val ≤ s.length) :
    ⦃ ⌜ True ⌝ ⦄
    core.slice.Slice.fill_loop core.U8.Insts.CoreCloneClone { start := 0#usize, «end» := n } s v
    ⦃ ⇓ r => ⌜ (fillInv s v n r).holds ⌝ ⦄ := by
  unfold core.slice.Slice.fill_loop
  apply Hax.loop_range_spec_unsigned (inv := fillInv s v)
  · simp
  · simp [fillInv]
  · intro acc i _ hi hinv
    simp only [fillInv, holds_ok] at hinv
    have hlen : acc.length = s.length := by
      have hn' : n.val ≤ s.val.length := hn
      show acc.val.length = s.val.length
      rw [hinv]; simp; omega
    hax_mvcgen [core.slice.Slice.fill_loop.body, fillInv, core.U8.Insts.CoreCloneClone.clone]
    case vc1.hQ =>
      rename_i hlt nx hnx r1 r2 hr s1 r hs1 hr'
      obtain ⟨hx, rfl, rfl⟩ := hr
      refine ⟨hlt, trivial, hnx, ?_⟩
      have hs : s.val.length = s.length := rfl
      simp only [fillInv, holds_ok, hr', hnx]
      simp [s1]
      exact fill_step _ _ _ _ hinv (by have : n.val ≤ s.val.length := hn; omega)
    case vc2.h_fail =>
      rename_i hlt nx hnx r1 r2 hr s1 hs1
      obtain ⟨hx, rfl, rfl⟩ := hr
      have : s1.length = acc.length := by simp [s1]
      omega
    case vc1.hQ =>
      have : i.val = n.val := by scalar_tac
      rw [hinv, this]
    scalar_tac

/-- `s.fill(v)` on bytes: every byte `v`. -/
theorem slice_fill_u8 (s : Slice Std.U8) (v : Std.U8) :
    ∃ r, core.slice.Slice.fill core.U8.Insts.CoreCloneClone s v = ok r ∧
      r.val = List.replicate s.length v := by
  have key : ⦃ ⌜ True ⌝ ⦄ core.slice.Slice.fill core.U8.Insts.CoreCloneClone s v
      ⦃ ⇓ r => ⌜ r.val = List.replicate s.length v ⌝ ⦄ := by
    hax_mvcgen [core.slice.Slice.fill, fillInv, core.slice.Slice.len,
      rust_primitives.slice.slice_length]
    case vc1.hn => scalar_tac
    case vc2.h_ok =>
      rename_i hpos k hk h1 r1 x back hx s2 r hs2 hr hinv
      obtain ⟨hlt, rfl, rfl⟩ := hx
      have hsl : s.len.val = s.val.length := by simp
      have hk1 : k.val + 1 = s.val.length := by scalar_tac
      have hstep := fill_step r1.val s.val v k.val hinv (by omega)
      rw [hr]
      simp only [s2, Slice.set_val_eq, List.set_set]
      rw [hstep, hk1, List.drop_length, List.append_nil]
    case vc3.h_fail =>
      rename_i hpos k hk h1 r1 x back hx s2 hs2 hinv
      obtain ⟨hlt, rfl, rfl⟩ := hx
      have : s2.length = r1.length := by simp [s2]
      omega
    case vc4.h_fail =>
      rename_i hpos k hk h1 r1 hlen hinv
      have hsl : s.len.val = s.val.length := by simp
      have : r1.val.length = s.val.length := by rw [hinv]; simp; scalar_tac
      have : r1.length = r1.val.length := rfl
      scalar_tac
    case vc5.h_fail => scalar_tac
    case vc6.hQ =>
      rename_i hpos
      have hsl : s.len.val = s.val.length := by simp
      have h0 : s.val.length = 0 := by scalar_tac
      have : s.length = 0 := h0
      rw [this, List.replicate_zero]
      exact List.eq_nil_of_length_eq_zero h0
  obtain ⟨r, hr⟩ := Hax.triple_noThrow_exists_ok key
  exact ⟨r, hr, Hax.triple_noThrow_elim key hr⟩

/-! ## Rust's bytes and the statement's -/

@[simp] theorem bytes_append (l₁ l₂ : List Std.U8) : bytes (l₁ ++ l₂) = bytes l₁ ++ bytes l₂ := by
  simp [bytes]

/-- **`u64::to_be_bytes` is the statement's `bigEndianBytes 8`.** -/
theorem bytes_u64_to_be_bytes (x : Std.U64) :
    bytes (Aeneas.Std.core.num.U64.to_be_bytes x).val = bigEndianBytes 8 x.bv := by
  have h : x.bv.toBEBytes = [x.bv.extractLsb' 56 8, x.bv.extractLsb' 48 8, x.bv.extractLsb' 40 8,
      x.bv.extractLsb' 32 8, x.bv.extractLsb' 24 8, x.bv.extractLsb' 16 8, x.bv.extractLsb' 8 8,
      x.bv.extractLsb' 0 8] := by
    simp [BitVec.toBEBytes, BitVec.toLEBytes]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_bits
  simp only [Aeneas.Std.core.num.U64.to_be_bytes, Array.from_val, h, bytes, List.map_cons,
    List.map_nil, b8]
  rfl

/-! ## The library models, as triples for `hax_mvcgen` -/

theorem triple_of_exists {α : Type} {x : RustM α} {P : α → Prop} (h : ∃ r, x = ok r ∧ P r) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ := by
  obtain ⟨r, hr, hp⟩ := h
  exact Hax.triple_of_ok hr hp

theorem exists_of_triple {α : Type} {x : RustM α} {P : α → Prop}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) : ∃ r, x = ok r ∧ P r := by
  obtain ⟨r, hr⟩ := Hax.triple_noThrow_exists_ok h
  exact ⟨r, hr, Hax.triple_noThrow_elim h hr⟩

@[spec]
theorem array_index_mut_range_triple {α : Type} {N : Std.Usize} (a : Array α N) (b e : Std.Usize)
    (h : b.val ≤ e.val) (he : e.val ≤ N.val) :
    ⦃ ⌜ True ⌝ ⦄
    core.Array.Insts.CoreOpsIndexIndexMut.index_mut
      (core.Slice.Insts.CoreOpsIndexIndexMut
        (core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice α))
      a { start := b, «end» := e }
    ⦃ ⇓ r => ⌜ r.1.val = List.slice b.val e.val a.val ∧
      ∀ t : Slice α, (r.2 t).val = a.val.setSlice! b.val t.val ⌝ ⦄ := by
  obtain ⟨s, back, h1, h2, h3⟩ := array_index_mut_range a b e h he
  exact Hax.triple_of_ok h1 ⟨h2, h3⟩

@[spec]
theorem array_index_mut_range_to_triple {α : Type} {N : Std.Usize} (a : Array α N) (e : Std.Usize)
    (he : e.val ≤ N.val) :
    ⦃ ⌜ True ⌝ ⦄
    core.Array.Insts.CoreOpsIndexIndexMut.index_mut
      (core.Slice.Insts.CoreOpsIndexIndexMut
        (core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice α))
      a { «end» := e }
    ⦃ ⇓ r => ⌜ r.1.val = a.val.take e.val ∧
      ∀ t : Slice α, (r.2 t).val = a.val.setSlice! 0 t.val ⌝ ⦄ := by
  obtain ⟨s, back, h1, h2, h3⟩ := array_index_mut_range_to a e he
  exact Hax.triple_of_ok h1 ⟨h2, h3⟩

@[spec]
theorem array_index_mut_range_from_triple {α : Type} {N : Std.Usize} (a : Array α N)
    (b : Std.Usize) (hb : b.val ≤ N.val) :
    ⦃ ⌜ True ⌝ ⦄
    core.Array.Insts.CoreOpsIndexIndexMut.index_mut
      (core.Slice.Insts.CoreOpsIndexIndexMut
        (core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice α))
      a { start := b }
    ⦃ ⇓ r => ⌜ r.1.val = a.val.drop b.val ∧
      ∀ t : Slice α, (r.2 t).val = a.val.setSlice! b.val t.val ⌝ ⦄ := by
  obtain ⟨s, back, h1, h2, h3⟩ := array_index_mut_range_from a b hb
  exact Hax.triple_of_ok h1 ⟨h2, h3⟩

@[spec]
theorem copy_from_slice_u8_triple (d s : Slice Std.U8) (h : d.length = s.length) :
    ⦃ ⌜ True ⌝ ⦄ core.slice.Slice.copy_from_slice core.U8.Insts.CoreMarkerCopy d s
    ⦃ ⇓ r => ⌜ r = s ⌝ ⦄ :=
  Hax.triple_of_ok (copy_from_slice_u8 d s h) rfl

@[spec]
theorem slice_fill_u8_triple (s : Slice Std.U8) (v : Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ core.slice.Slice.fill core.U8.Insts.CoreCloneClone s v
    ⦃ ⇓ r => ⌜ r.val = List.replicate s.length v ⌝ ⦄ :=
  triple_of_exists (slice_fill_u8 s v)

@[spec]
theorem array_repeat_u8_triple (N : Std.Usize) (x : Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ core.array.repeat N core.U8.Insts.CoreCloneClone x
    ⦃ ⇓ a => ⌜ a.val = List.replicate N.val x ⌝ ⦄ :=
  triple_of_exists (array_repeat N _ (fun _ => rfl) x)

/-! ## Addresses, as bytes -/

/-- `Adrs::word`: four bytes of the address set to a big-endian word. -/
@[spec]
theorem adrs_word_triple (a : lean_sphincs.hash.Adrs) (pos : Std.Usize) (v : Std.U32)
    (h : pos.val + 4 ≤ 32) :
    ⦃ ⌜ True ⌝ ⦄ lean_sphincs.hash.Adrs.word a pos v
    ⦃ ⇓ r => ⌜ r.val = a.val.setSlice! pos.val (Aeneas.Std.core.num.U32.to_be_bytes v).val ⌝ ⦄ := by
  hax_mvcgen [lean_sphincs.hash.Adrs.word, core.num.U32.to_be_bytes,
    rust_primitives.arithmetic.to_be_bytes_u32]
  case vc1.h => scalar_tac
  case vc2.he => scalar_tac
  case vc3.h =>
    rename_i e he r hr
    have ha : a.val.length = 32 := by simp
    show r.1.val.length = (Aeneas.Std.core.num.U32.to_be_bytes v).to_slice.val.length
    rw [hr.1]
    simp [List.slice]
    scalar_tac
  case vc4 =>
    rename_i e he r hr s a1 hs
    simp [a1, hr.2, hs]
  case vc5.h_fail => scalar_tac

theorem bytes_setSlice! (l : List Std.U8) (i : ℕ) (s : List Std.U8) :
    bytes (l.setSlice! i s) = (bytes l).setSlice! i (bytes s) := by
  simp [List.setSlice!, bytes, List.map_take, List.map_drop]

/-- Writing over the middle of three pieces replaces it. -/
theorem setSlice!_mid {α : Type} (p w q w' : List α) (hw : w'.length = w.length) :
    (p ++ w ++ q).setSlice! p.length w' = p ++ w' ++ q := by
  simp [List.setSlice!, hw]

/-- `setSlice!_mid` at a stated index. -/
theorem setSlice!_mid' {α : Type} (p w q w' : List α) (i : ℕ) (hi : p.length = i)
    (hw : w'.length = w.length) : (p ++ w ++ q).setSlice! i w' = p ++ w' ++ q := by
  subst hi; exact setSlice!_mid p w q w' hw

theorem bytes_replicate_zero (n : ℕ) : bytes (List.replicate n 0#u8) = List.replicate n 0 := by
  simp only [bytes, List.map_replicate]; rfl

@[simp] theorem bigEndianBytes_length (n : ℕ) (v : BitVec (8 * n)) :
    (bigEndianBytes n v).length = n := by
  simp [bigEndianBytes]

/-- `Adrs::word` on an address whose bytes are `p ‖ w ‖ q`, `w` the four at `pos`. -/
theorem adrs_word_bytes (a : lean_sphincs.hash.Adrs) (pos : Std.Usize) (v : Std.U32)
    (p w q : List UInt8) (hb : bytes a.val = p ++ w ++ q) (hp : p.length = pos.val)
    (hw : w.length = 4) :
    ∃ a', lean_sphincs.hash.Adrs.word a pos v = ok a' ∧
      bytes a'.val = p ++ bigEndianBytes 4 v.bv ++ q := by
  have hlen : (bytes a.val).length = 32 := by simp
  have hpos : pos.val + 4 ≤ 32 := by
    rw [hb] at hlen; simp at hlen; omega
  obtain ⟨a', ha', hv⟩ := exists_of_triple (adrs_word_triple a pos v hpos)
  refine ⟨a', ha', ?_⟩
  rw [hv, bytes_setSlice!, hb, bytes_u32_to_be_bytes, ← hp]
  exact setSlice!_mid p w q _ (by simp [hw])

/-- `Adrs::new`: the layer, four zero bytes, the tree, sixteen zero bytes. -/
theorem adrs_new_bytes (layer : Std.U32) (tree : Std.U64) :
    ∃ a, lean_sphincs.hash.Adrs.new layer tree = ok a ∧
      bytes a.val = bigEndianBytes 4 layer.bv ++ List.replicate 4 0 ++ bigEndianBytes 8 tree.bv ++
        List.replicate 16 0 := by
  have key : ⦃ ⌜ True ⌝ ⦄ lean_sphincs.hash.Adrs.new layer tree
      ⦃ ⇓ r => ⌜ r.val = ((List.replicate 32 0#u8).setSlice! 0
        (Aeneas.Std.core.num.U32.to_be_bytes layer).val).setSlice! 8
        (Aeneas.Std.core.num.U64.to_be_bytes tree).val ⌝ ⦄ := by
    hax_mvcgen [lean_sphincs.hash.Adrs.new, core.num.U32.to_be_bytes, core.num.U64.to_be_bytes,
      rust_primitives.arithmetic.to_be_bytes_u32, rust_primitives.arithmetic.to_be_bytes_u64]
    case vc2.h =>
      rename_i r0 h0 r hr
      show r.1.val.length = (Aeneas.Std.core.num.U32.to_be_bytes layer).to_slice.val.length
      rw [hr.1, h0]; simp
    case vc5.h =>
      rename_i r0 h0 r hr s out1 hs r' hr'
      show r'.1.val.length = (Aeneas.Std.core.num.U64.to_be_bytes tree).to_slice.val.length
      rw [hr'.1]; simp [List.slice, out1]
    case vc6 =>
      rename_i r0 h0 r hr s out1 hs r' hr' s' out2 hs'
      simp [out2, out1, hr'.2, hr.2, hs, hs', h0]
  obtain ⟨a, ha, hv⟩ := exists_of_triple key
  refine ⟨a, ha, ?_⟩
  rw [hv, bytes_setSlice!, bytes_setSlice!, bytes_u32_to_be_bytes, bytes_u64_to_be_bytes,
    bytes_replicate_zero]
  rw [show List.replicate 32 (0 : UInt8) = [] ++ List.replicate 4 0 ++ List.replicate 28 0 from rfl,
    setSlice!_mid' _ _ _ _ 0 rfl (by simp), List.nil_append,
    show List.replicate 28 (0 : UInt8) = List.replicate 4 0 ++ List.replicate 8 0 ++
      List.replicate 16 0 from rfl,
    ← List.append_assoc, ← List.append_assoc, setSlice!_mid' _ _ _ _ 8 (by simp) (by simp)]

/-- `Adrs::with_type` on an address whose first sixteen bytes are `p`: the type, then twelve zero
bytes. -/
theorem adrs_with_type_bytes (a : lean_sphincs.hash.Adrs) (t : Std.U32) (p q : List UInt8)
    (hb : bytes a.val = p ++ q) (hp : p.length = 16) :
    ∃ a', lean_sphincs.hash.Adrs.with_type a t = ok a' ∧
      bytes a'.val = p ++ bigEndianBytes 4 t.bv ++ List.replicate 12 0 := by
  have key : ⦃ ⌜ True ⌝ ⦄ lean_sphincs.hash.Adrs.with_type a t
      ⦃ ⇓ r => ⌜ r.val = (a.val.setSlice! 20 (List.replicate 12 0#u8)).setSlice! 16
        (Aeneas.Std.core.num.U32.to_be_bytes t).val ⌝ ⦄ := by
    hax_mvcgen [lean_sphincs.hash.Adrs.with_type]
    case vc2.success.success.success =>
      rename_i r hr s a1 hs r' hr'
      have hl : r.1.length = 12 := by
        show r.1.val.length = 12
        rw [hr.1]; simp
      rw [hr']
      simp [a1, hr.2, hs, hl]
    case vc3 => scalar_tac
  obtain ⟨a', ha', hv⟩ := exists_of_triple key
  refine ⟨a', ha', ?_⟩
  have hlen : (bytes a.val).length = 32 := by simp
  have hq : q.length = 16 := by rw [hb] at hlen; simp at hlen; omega
  rw [hv, bytes_setSlice!, bytes_setSlice!, bytes_u32_to_be_bytes, bytes_replicate_zero, hb]
  rw [show p ++ q = (p ++ q.take 4) ++ q.drop 4 ++ [] by simp,
    setSlice!_mid' _ _ _ _ 20 (by simp [hp, hq]) (by simp [hq]), List.append_nil,
    setSlice!_mid' _ _ _ _ 16 hp (by simp [hq])]

/-! ## Addresses, as the statement's -/

theorem u64_bv_eq_ofNat (x : Std.U64) : x.bv = BitVec.ofNat 64 x.val := by
  apply BitVec.eq_of_toNat_eq
  simp

/-- A key's tree address with a type set: the layer, the tree, the type, and twelve zero bytes. -/
theorem tree_adrs_with_type_bytes (k : lean_sphincs.wots.OtsKey) (t : Std.U32) :
    ∃ a a', lean_sphincs.wots.OtsKey.tree_adrs k = ok a ∧
      lean_sphincs.hash.Adrs.with_type a t = ok a' ∧
      bytes a'.val = bigEndianBytes 4 (BitVec.ofNat 32 k.layer.val) ++ List.replicate 4 0 ++
        bigEndianBytes 8 (BitVec.ofNat 64 k.tree.val) ++ bigEndianBytes 4 t.bv ++
        List.replicate 12 0 := by
  obtain ⟨a, ha, hb⟩ := adrs_new_bytes (UScalar.cast .U32 k.layer) k.tree
  obtain ⟨a', ha', hb'⟩ := adrs_with_type_bytes a t _ _ hb (by simp)
  refine ⟨a, a', ?_, ha', ?_⟩
  · simp only [lean_sphincs.wots.OtsKey.tree_adrs, lift]
    exact (Aeneas.Std.bind_ok _ _).trans ha
  · rw [hb', show U32.bv (UScalar.cast .U32 k.layer) = _ from cast_u32_bv k.layer,
      ← u64_bv_eq_ofNat]

theorem toBytes_eq (A : Sphincs.Address) :
    A.toBytes = bigEndianBytes 4 A.layer ++ List.replicate 4 0 ++ bigEndianBytes 8 A.tree ++
      bigEndianBytes 4 (BitVec.ofNat 32 A.addressType.word) ++ bigEndianBytes 4 A.keyPair ++
      bigEndianBytes 4 A.chainOrTreeHeight ++ bigEndianBytes 4 A.hashOrTreeIndex := rfl

theorem bigEndianBytes_zero : bigEndianBytes 4 (BitVec.ofNat 32 0) = List.replicate 4 0 := by
  decide

/-- **`OtsKey::tree_adrs` then `with_type`.** -/
theorem treeAdrs_spec : TreeAdrsSpec := by
  intro k t T ht _
  obtain ⟨a, a', ha, ha', hb⟩ := tree_adrs_with_type_bytes k t
  refine ⟨a, a', ha, ha', ?_⟩
  rw [AdrsIs, hb, toBytes_eq, u32_bv_eq_ofNat t, ht]
  simp only [makeAddress, bigEndianBytes_zero, List.append_assoc]
  rfl

/-- **`OtsKey::adrs`.** -/
theorem keyAdrs_spec : KeyAdrsSpec := by
  intro k t T ht _
  obtain ⟨a, a', ha, ha', hb⟩ := tree_adrs_with_type_bytes k t
  obtain ⟨a'', ha'', hb''⟩ := adrs_word_bytes a' 20#usize k.leaf
    (bigEndianBytes 4 (BitVec.ofNat 32 k.layer.val) ++ List.replicate 4 0 ++
      bigEndianBytes 8 (BitVec.ofNat 64 k.tree.val) ++ bigEndianBytes 4 t.bv)
    (List.replicate 4 0) (List.replicate 8 0)
    (by rw [hb, List.append_assoc _ (List.replicate 4 0) (List.replicate 8 0)]; rfl)
    (by simp) (by simp)
  refine ⟨a'', ?_, ?_⟩
  · simp only [lean_sphincs.wots.OtsKey.adrs, ha]
    erw [Aeneas.Std.bind_ok, ha', Aeneas.Std.bind_ok]
    exact ha''
  · rw [AdrsIs, hb'', toBytes_eq, u32_bv_eq_ofNat t, ht, u32_bv_eq_ofNat k.leaf]
    simp only [makeAddress, bigEndianBytes_zero, List.append_assoc]
    rfl

/-- **`Adrs::with_chain`, `with_tree_height`, `with_hash`, `with_tree_index`.** -/
theorem adrsWord_spec : AdrsWordSpec := by
  intro a A v h
  rw [AdrsIs, toBytes_eq] at h
  have h5 := adrs_word_bytes a 24#usize v _ _ _ h (by simp) (by simp)
  have h6 := adrs_word_bytes a 28#usize v _ _ []
    (by rw [h, List.append_nil]) (by simp) (by simp)
  rw [List.append_nil] at h6
  exact ⟨h5, h5, h6, h6⟩

/-! ## The tweakable hash -/

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

/-- **`th`**: the truncated Keccak-256 of `PK.seed ‖ ADRS ‖ M`. -/
theorem th_spec {π : KeccakState → KeccakState} (H : HasherSpec π) : ThSpec π := by
  intro seed adrs m
  obtain ⟨h0, hn, ha0⟩ := H.new
  obtain ⟨h1, b1, hu1, ha1, hb1⟩ := H.update h0 [] seed.to_slice ha0
  obtain ⟨h2, b2, hu2, ha2, hb2⟩ := H.update h1 _ adrs.to_slice ha1
  obtain ⟨h3, b3, hu3, ha3, hb3⟩ := H.update h2 _ m ha2
  obtain ⟨d, hf, hd⟩ := H.finalize h3 _ ha3
  obtain ⟨r, hr, hrv⟩ := truncate_16 d
  refine ⟨r, ?_, ?_⟩
  · simp [lean_sphincs.hash.th, lean_sphincs.hash.hasher, keccak256.prefixed_hasher,
      lean_sphincs.hash.Adrs.as_bytes, core.array.Array.as_slice,
      rust_primitives.slice.array_as_slice, hn, hu1, hu2, hu3, hb1, hb2, hf, hr]
  · have hl : (hashBytes π ([] ++ bytes seed.to_slice.val ++ bytes adrs.to_slice.val ++
        bytes m.val)).length = 32 := digestBytes_length _
    have hs : seed.to_slice.val = seed.val := by simp
    have hA : (Array.to_slice adrs).val = adrs.val := by simp
    rw [List.nil_append, hs, hA] at hd hl
    have hbr : bytes r.val = (hashBytes π (bytes seed.val ++ bytes adrs.val ++ bytes m.val)).take 16 := by
      rw [hrv, ← hd]; simp [bytes, List.map_take]
    show BitVec.ofNat 128 (leNat (bytes r.val)) =
      truncateHash (BitVec.ofNat 256 (leNat (hashBytes π (bytes seed.val ++ bytes adrs.val ++ bytes m.val))))
    rw [hbr, leNat_take]
    apply BitVec.eq_of_toNat_eq
    simp [truncateHash, digestBits]

theorem array_map_clone_fold {α : Type} (N : Std.Usize) (inst : core.clone.Clone α)
    (hclone : ∀ y, inst.clone y = ok y) (c : core.array.CloneArray.clone.closure α N) :
    ∀ (l acc : List α),
      List.foldlM (fun (s : List α × core.array.CloneArray.clone.closure α N) x => do
          let __x ← (core.array.CloneArray.clone.closure.Insts.CoreOpsFunctionFnMutTupleTT N
            inst).call_mut s.2 x
          match __x with
          | (v, f') => ok (s.1 ++ [v], f')) (acc, c) l = ok (acc ++ l, c) := by
  intro l
  induction l with
  | nil => intro acc; simp [List.foldlM]; rfl
  | cons x xs ih =>
    intro acc
    simp [List.foldlM,
      core.array.CloneArray.clone.closure.Insts.CoreOpsFunctionFnMutTupleTT.call_mut, hclone]
    have ih' := ih (acc ++ [x])
    simp [core.array.CloneArray.clone.closure.Insts.CoreOpsFunctionFnMutTupleTT.call_mut,
      hclone] at ih'
    exact ih'

/-- `clone` of an array whose elements' `clone` returns its argument. -/
theorem array_clone {α : Type} {N : Std.Usize} (inst : core.clone.Clone α)
    (hclone : ∀ y, inst.clone y = ok y) (a : Array α N) :
    core.Array.Insts.CoreCloneClone.clone inst a = ok a := by
  have hf := array_map_clone_fold N inst hclone () a.val []
  simp only [core.Array.Insts.CoreCloneClone.clone, core.array.Array.map,
    rust_primitives.slice.array_map]
  split
  · rename_i heq; erw [hf, RustM.match.ok] at heq; cases heq
  · rename_i heq; erw [hf, RustM.match.ok] at heq; cases heq
  · rename_i result heq
    erw [hf, RustM.match.ok] at heq
    cases heq
    exact congrArg ok (Aeneas.Std.Array.ext _ _ (by simp))

/-- **`Hasher::clone`** returns the hasher. -/
theorem hasher_clone (h : keccak256.Hasher) :
    keccak256.Hasher.Insts.CoreCloneClone.clone h = ok h := by
  simp only [keccak256.Hasher.Insts.CoreCloneClone.clone,
    array_clone core.U64.Insts.CoreCloneClone (fun _ => rfl),
    array_clone core.U8.Insts.CoreCloneClone (fun _ => rfl),
    core.Usize.Insts.CoreCloneClone.clone]
  simp

end LeanSphincsProofs
