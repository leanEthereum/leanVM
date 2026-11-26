import LeanSphincsProofs.Common

/-!
# `wots.rs`: the one-time key of an index, a chain, and the one-time leaf

`OtsKey::of_index`, `chain` and `wots_leaf` (with `encoder`, `encode`, `codeword` and
`wots_leaf_hash`), as extracted, compute the statement's `treeOfIndex` and `leafOfIndex`,
`Verification.chainWalk` and `Verification.otsLeaf`. The facts about `hash.rs` they rest on are
hypotheses here, proved in `Hash.lean`.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM Std.Do
open HashSig HashSig.OverPermutation Sphincs
open LeanVM.Semantics (KeccakState)
open LeanVM.Protocol.KeccakHash (digestBytes keccak256With)
open lean_sphincs

namespace LeanSphincsProofs

namespace Wots

/-! ## Loops over a range, folds and `from_fn`, as equations -/

/-- A loop over `s..e` whose body, below the end, steps to the next index keeping `inv`, and at
the end returns its state: it returns a state satisfying `inv e`. -/
theorem range_loop {β : Type}
    (body : core.ops.range.Range Std.Usize × β →
      RustM (ControlFlow (core.ops.range.Range Std.Usize × β) β))
    (e : Std.Usize) (inv : Nat → β → Prop)
    (hdone : ∀ (i : Std.Usize) acc, e.val ≤ i.val →
      body ({ start := i, «end» := e }, acc) = ok (.done acc))
    (hstep : ∀ (i : Std.Usize) acc, i.val < e.val → inv i.val acc →
      ∃ (i' : Std.Usize) (acc' : β), i'.val = i.val + 1 ∧
        body ({ start := i, «end» := e }, acc) = ok (.cont ({ start := i', «end» := e }, acc')) ∧
        inv i'.val acc')
    (s : Std.Usize) (init : β) (hs : s.val ≤ e.val) (hinit : inv s.val init) :
    ∃ r, loop body ({ start := s, «end» := e }, init) = ok r ∧ inv e.val r := by
  suffices gen : ∀ (n : Nat) (i : Std.Usize) acc, e.val - i.val = n → i.val ≤ e.val →
      inv i.val acc → ∃ r, loop body ({ start := i, «end» := e }, acc) = ok r ∧ inv e.val r from
    gen _ s init rfl hs hinit
  intro n
  induction n with
  | zero =>
    intro i acc hn hle hinv
    have hie : i.val = e.val := by omega
    refine ⟨acc, ?_, hie ▸ hinv⟩
    rw [loop.eq_def, hdone i acc (by omega), Aeneas.Std.bind_ok]
  | succ n ih =>
    intro i acc hn hle hinv
    obtain ⟨i', acc', hi', hbody, hinv'⟩ := hstep i acc (by omega) hinv
    rw [loop.eq_def, hbody, Aeneas.Std.bind_ok]
    exact ih i' acc' (by omega) (by omega) hinv'

/-- A fold over `s..e` whose closure keeps `inv` and itself: it returns a value satisfying
`inv e`. -/
theorem range_fold {B F : Type} (inst : core.ops.function.FnMut F (B × Std.Usize) B) (f : F)
    (e : Std.Usize) (inv : Nat → B → Prop)
    (hstep : ∀ (i : Std.Usize) acc, i.val < e.val → inv i.val acc →
      ∃ acc', inst.call_mut f (acc, i) = ok (acc', f) ∧ inv (i.val + 1) acc')
    (s : Std.Usize) (init : B) (hs : s.val ≤ e.val) (hinit : inv s.val init) :
    ∃ r, core.iter.traits.iterator.Iterator.fold.default
        (core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator core.Usize.Insts.CoreIterRangeStep)
        inst { start := s, «end» := e } init f = ok r ∧ inv e.val r := by
  unfold core.iter.traits.iterator.Iterator.fold.default core.iter.traits.iterator.iter_fold
    core.iter.traits.iterator.iter_fold_loop
  generalize hbody : (fun x : core.ops.range.Range Std.Usize × F × B => match x with
    | (iter2, f1, accum1) => core.iter.traits.iterator.iter_fold_loop.body
        (core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator
          core.Usize.Insts.CoreIterRangeStep) inst iter2 f1 accum1) = body
  have hdone : ∀ (i : Std.Usize) acc, e.val ≤ i.val →
      body ({ start := i, «end» := e }, f, acc) = ok (.done acc) := by
    intro i acc hi
    subst hbody
    simp only [core.iter.traits.iterator.iter_fold_loop.body,
      core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator, range_next_ge i e hi,
      Aeneas.Std.bind_ok]
    rfl
  have hcont : ∀ (i : Std.Usize) acc, i.val < e.val → inv i.val acc →
      ∃ (i' : Std.Usize) (acc' : B), i'.val = i.val + 1 ∧
        body ({ start := i, «end» := e }, f, acc) =
          ok (.cont ({ start := i', «end» := e }, f, acc')) ∧ inv i'.val acc' := by
    intro i acc hi hinv
    obtain ⟨i', hi', hnext⟩ := range_next_lt i e hi
    obtain ⟨acc', hcall, hinv'⟩ := hstep i acc hi hinv
    refine ⟨i', acc', hi', ?_, hi' ▸ hinv'⟩
    subst hbody
    simp only [core.iter.traits.iterator.iter_fold_loop.body,
      core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator, hnext, Aeneas.Std.bind_ok]
    show (do let (accum1, f1) ← inst.call_mut f (acc, i); ok (ControlFlow.cont (_, f1, accum1))) = _
    rw [hcall]
    simp
  suffices gen : ∀ (n : Nat) (i : Std.Usize) acc, e.val - i.val = n → i.val ≤ e.val →
      inv i.val acc → ∃ r, loop body ({ start := i, «end» := e }, f, acc) = ok r ∧ inv e.val r from
    gen _ s init rfl hs hinit
  intro n
  induction n with
  | zero =>
    intro i acc hn hle hinv
    have hie : i.val = e.val := by omega
    refine ⟨acc, ?_, hie ▸ hinv⟩
    rw [loop.eq_def, hdone i acc (by omega), Aeneas.Std.bind_ok]
  | succ n ih =>
    intro i acc hn hle hinv
    obtain ⟨i', acc', hi', hb, hinv'⟩ := hcont i acc (by omega) hinv
    rw [loop.eq_def, hb, Aeneas.Std.bind_ok]
    exact ih i' acc' (by omega) (by omega) hinv'

/-- The primitive under `from_fn`, for a closure that returns `g i` at `i` and keeps itself. -/
theorem array_from_fn_eq {T F : Type} (N : Std.Usize) (inst : core.ops.function.FnMut F Std.Usize T)
    (c : F) (g : Nat → T)
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

/-- `from_fn` of a closure that returns `g i` at `i` and keeps itself: the array of the `g i`. -/
theorem from_fn_eq {T F : Type} (N : Std.Usize) (inst : core.ops.function.FnMut F Std.Usize T)
    (c : F) (g : Nat → T)
    (h : ∀ i : Std.Usize, i.val < N.val → inst.call_mut c i = ok (g i.val, c)) :
    ∃ a, core.array.from_fn N inst c = ok a ∧ a.val = (List.range N.val).map g :=
  array_from_fn_eq N inst c g h

/-! ## `OtsKey::of_index` -/

/-- `LAYER_HEIGHTS[l]`: 8, 8 and 10. -/
theorem layer_height (l : Std.Usize) (h : l.val < 3) :
    Array.index_usize internals.LAYER_HEIGHTS l ⦃ r => r.val = if l.val = 2 then 10 else 8 ⦄ := by
  have : l = 0#usize ∨ l = 1#usize ∨ l = 2#usize := by
    rcases (by omega : l.val = 0 ∨ l.val = 1 ∨ l.val = 2) with h | h | h
    · left; scalar_tac
    · right; left; scalar_tac
    · right; right; scalar_tac
  rcases this with rfl | rfl | rfl <;>
    simp [internals.LAYER_HEIGHTS, Array.index_usize]

/-- The loop of `of_index` (and of `path_range`): the heights of the layers below `e ≤ 2`, 8 each. -/
theorem of_index_loop_eq (e : Std.Usize) (he : e.val ≤ 2) :
    ∃ r : Std.Usize, wots.OtsKey.of_index_loop { start := 0#usize, «end» := e } 0#usize = ok r ∧
      r.val = 8 * e.val := by
  unfold wots.OtsKey.of_index_loop
  refine range_loop (fun x => wots.OtsKey.of_index_loop.body x.1 x.2) e
    (fun n (acc : Std.Usize) => acc.val = 8 * n) ?_ ?_ 0#usize 0#usize (by scalar_tac) (by simp)
  · intro i acc hi
    simp only [wots.OtsKey.of_index_loop.body,
      core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next, range_next_ge i e hi,
      Aeneas.Std.bind_ok]
    rfl
  · intro i acc hi hacc
    obtain ⟨i', hi', hnext⟩ := range_next_lt i e hi
    have h : wots.OtsKey.of_index_loop.body { start := i, «end» := e } acc
        ⦃ r => ∃ acc' : Std.Usize, r = .cont ({ start := i', «end» := e }, acc') ∧
          acc'.val = 8 * i'.val ⦄ := by
      unfold wots.OtsKey.of_index_loop.body
      simp only [core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next, hnext,
        Aeneas.Std.bind_ok]
      step with layer_height as ⟨h, hh⟩
      have h8 : h.val = 8 := by split at hh <;> omega
      step*
    obtain ⟨r, hr, acc', rfl, hacc'⟩ := WP.spec_imp_exists h
    exact ⟨i', acc', hi', hr, hacc'⟩

/-- `OtsKey::of_index` at a layer below 3 and an index below `2^26`, by its fields. -/
theorem of_index_eq (layer : Std.Usize) (idx : Std.U64) (hl : layer.val < 3) :
    ∃ k, wots.OtsKey.of_index layer idx = ok k ∧ k.layer = layer ∧
      k.tree.val = idx.val / 2 ^ (8 * layer.val + if layer.val = 2 then 10 else 8) ∧
      k.leaf.val = idx.val / 2 ^ (8 * layer.val) % 2 ^ (if layer.val = 2 then 10 else 8) % 2 ^ 32 := by
  obtain ⟨below, hloop, hbelow⟩ := of_index_loop_eq layer (by omega)
  have h : wots.OtsKey.of_index layer idx ⦃ k => k.layer = layer ∧
      k.tree.val = idx.val / 2 ^ (8 * layer.val + if layer.val = 2 then 10 else 8) ∧
      k.leaf.val =
        idx.val / 2 ^ (8 * layer.val) % 2 ^ (if layer.val = 2 then 10 else 8) % 2 ^ 32 ⦄ := by
    unfold wots.OtsKey.of_index
    step with layer_height as ⟨height, hheight⟩
    simp only [hloop, Aeneas.Std.bind_ok]
    have hcase : height.val = 8 ∨ height.val = 10 := by split at hheight <;> omega
    have hpow : (1 : Nat) <<< height.val % U64.size = 2 ^ height.val := by
      rcases hcase with h | h <;> rw [h] <;> simp [U64.size, U64.numBits]
    step*
    · rcases hcase with h | h <;> omega
    · rw [i1_post, hpow]; exact Nat.one_le_two_pow
    · have hi2 : i2.val = 2 ^ height.val - 1 := by rw [i2_post, i1_post, hpow]
      refine ⟨?_, ?_⟩
      · rw [i_post, e_post, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
          Nat.div_div_eq_div_mul, ← Nat.pow_add, hbelow, hheight]
      · rw [i4_post, UScalar.cast_val_eq, i3_post, UScalar.val_and, hi2,
          Nat.and_two_pow_sub_one_eq_mod, e_post, Nat.shiftRight_eq_div_pow, hbelow, hheight]
        rfl
  exact WP.spec_imp_exists h

end Wots

open Wots in
/-- **`OtsKey::of_index`** is the statement's key of a layer on the way up from an index. -/
theorem ofIndex_spec : OfIndexSpec := by
  intro layer idx l index hlayer hidx
  have hl3 : l.val < 3 := l.isLt
  obtain ⟨k, hk, hkl, hkt, hkf⟩ := of_index_eq layer idx (by omega)
  refine ⟨k, hk, by rw [hkl, hlayer], ?_, ?_⟩
  · rw [hkt, hidx, hlayer]; rfl
  · rw [hkf, hidx, hlayer]
    show _ % 2 ^ 32 = index.val / 2 ^ (8 * l.val) % 2 ^ (if l.val = 2 then 10 else 8)
    apply Nat.mod_eq_of_lt
    have : index.val / 2 ^ (8 * l.val) % 2 ^ (if l.val = 2 then 10 else 8) < 2 ^ 10 := by
      split
      · exact Nat.mod_lt _ (by decide)
      · exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)
    omega

namespace Wots

/-! ## Bytes and the numbers they spell -/

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

/-! ## The tweakable hash at an address -/

/-- `CHAIN_LEN` is 4. -/
theorem chain_len : internals.CHAIN_LEN = ok 4#usize := by
  have h : internals.CHAIN_LEN ⦃ r => r = 4#usize ⦄ := by
    unfold internals.CHAIN_LEN internals.W
    step*
    · rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> scalar_tac
    · have hb : (4 : Nat) < Usize.size := by
        rw [Usize.size_def]; cases System.Platform.numBits_eq <;> simp [Usize.numBits, *]
      have : r.val = 4 := by rw [r_post]; exact Nat.mod_eq_of_lt hb
      scalar_tac
  obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists h
  exact hr

end Wots

open Wots in
/-- **`chain`** walks the statement's chain. -/
theorem chain_spec {π : KeccakState → KeccakState} (hth : ThSpec π) (hk : KeyAdrsSpec)
    (hw : AdrsWordSpec) : ChainSpec π := by
  intro seed k i start steps v layer tree leaf chainIndex hkey hi hss
  obtain ⟨hkl, hkt, hkf⟩ := hkey
  have hl3 : layer.val < 3 := layer.isLt
  obtain ⟨a, ha, hA⟩ := hk k hash.WOTS_HASH .wotsHash (by simp [hash.WOTS_HASH, AddressType.word])
    (by omega)
  obtain ⟨adrs, hadrs, hAdrs⟩ := (hw a _ (UScalar.cast .U32 i) hA).1
  have hsum : start + steps ⦃ r => r.val = start.val + steps.val ⦄ := by step*
  obtain ⟨i1, hi1, hi1v⟩ := WP.spec_imp_exists hsum
  have hfold := range_fold
    wots.chain.closure.Insts.CoreOpsFunctionFnMutPairArrayU816UsizeArrayU816 (seed, adrs) i1
    (fun j (acc : Array Std.U8 16#usize) => start.val ≤ j ∧
      toDigest acc = Id.run (Verification.chainWalk (inId π)
        (toDigest seed) layer tree leaf chainIndex start.val (j - start.val) (toDigest v)))
    ?_ start v (by omega) ⟨Nat.le_refl _, by simp [Verification.chainWalk, walkChain]⟩
  · obtain ⟨r, hr, -, hinv⟩ := hfold
    refine ⟨r, ?_, by rw [hinv, hi1v]; congr 2; omega⟩
    have h4 : i1.val < 4 := by omega
    unfold wots.chain
    simp [hi1, chain_len, ha, hadrs, hr, lift, massert, h4]
  · intro j acc hj ⟨hsj, hinv⟩
    obtain ⟨a2, ha2, hA2⟩ := (hw adrs _ (UScalar.cast .U32 j) hAdrs).2.2.1
    obtain ⟨d, hd, hdig⟩ := th_adrs hth seed a2 _ acc.to_slice hA2
    have hlt : start.val + (j.val - start.val) < chainLength - 1 := by
      simp only [chainLength, winternitzBits]; omega
    refine ⟨d, ?_, by omega, ?_⟩
    · simp [wots.chain.closure.Insts.CoreOpsFunctionFnMutPairArrayU816UsizeArrayU816.call_mut, lift,
        ha2, core.array.Array.as_slice, rust_primitives.slice.array_as_slice, hd]
    · have hprev : Id.run (Verification.chainWalk (inId π) (toDigest seed) layer tree leaf chainIndex
          start.val (j.val - start.val + 1) (toDigest v)) =
          Id.run (Verification.addressedHash (inId π) (toDigest seed)
            (hashDomainFields (.chain layer tree leaf chainIndex
              ⟨start.val + (j.val - start.val), hlt⟩)) (littleEndianBytes 16 (toDigest acc))) := by
        rw [hinv]
        simp only [Verification.chainWalk, walkChain, dite_eq_left_of_eq_true (eq_true hlt)]
        rfl
      rw [hdig, show j.val + 1 - start.val = (j.val - start.val) + 1 by omega, hprev,
        littleEndianBytes_toDigest]
      have hjj : start.val + (j.val - start.val) = j.val := by omega
      congr 2
      · simp [hashDomainFields, makeAddress, hkl, hkt, hkf, hjj]
        rw [← hi]; exact cast_u32_bv i
      · simp [Array.to_slice]

namespace Wots

/-! ## The hasher -/

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

/-- `u32::to_be_bytes` gives the statement's big-endian bytes. -/
theorem bytes_to_be_bytes_u32 (x : Std.U32) :
    bytes (Aeneas.Std.core.num.U32.to_be_bytes x).val = bigEndianBytes 4 x.bv := by
  obtain ⟨v⟩ := x
  change BitVec 32 at v
  simp [Aeneas.Std.core.num.U32.to_be_bytes, bytes, b8, bigEndianBytes, BitVec.toBEBytes,
    BitVec.toLEBytes, List.ofFn, Fin.foldr_succ]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> bv_bits

/-- The truncation of a Keccak-256 digest, as the statement's truncated hash. -/
theorem toDigest_truncate {π : KeccakState → KeccakState} (l : List UInt8)
    (d : Array Std.U8 32#usize) (a : Array Std.U8 16#usize) (hd : bytes d.val = hashBytes π l)
    (ha : a.val = d.val.take 16) :
    toDigest a = truncateHash (Id.run (keccakHash (inId π) l)) := by
  rw [keccakHash_inId, truncateHash_leNat, ← hd, toDigest, ha]
  simp only [bytes, List.map_take]
  rfl

/-- `hasher`: a hasher that has absorbed `PK.seed ‖ ADRS`. -/
theorem hasher_absorbed {π : KeccakState → KeccakState} (H : HasherSpec π)
    (seed : Array Std.U8 16#usize) (adrs : hash.Adrs) :
    ∃ h, hash.hasher seed adrs = ok h ∧ H.Absorbed h (bytes seed.val ++ bytes adrs.val) := by
  obtain ⟨h0, hnew, habs0⟩ := H.new
  obtain ⟨h1, b1, hu1, habs1, hb1⟩ := H.update h0 [] seed.to_slice habs0
  obtain ⟨h2, b2, hu2, habs2, hb2⟩ := H.update h1 _ adrs.to_slice habs1
  refine ⟨h2, ?_, by simpa [Array.to_slice] using habs2⟩
  simp [hash.hasher, hash.Adrs.as_bytes, keccak256.prefixed_hasher, core.array.Array.as_slice,
    rust_primitives.slice.array_as_slice, hnew, hu1, hu2, hb1, hb2]

/-- `encoder`: a hasher that has absorbed `PK.seed ‖ ADRS_enc(K) ‖ M`. -/
theorem encoder_absorbed {π : KeccakState → KeccakState} (H : HasherSpec π) (hk : KeyAdrsSpec)
    (seed : Array Std.U8 16#usize) (k : wots.OtsKey) (msg : Array Std.U8 16#usize)
    (hl : k.layer.val < 2 ^ 32) :
    ∃ h, wots.encoder seed k msg = ok h ∧ H.Absorbed h (bytes seed.val ++
      (makeAddress k.layer.val k.tree.val .wotsEncoding k.leaf.val 0 0).toBytes ++ bytes msg.val) := by
  obtain ⟨a, ha, hA⟩ := hk k hash.WOTS_ENC .wotsEncoding (by simp [hash.WOTS_ENC, AddressType.word]) hl
  obtain ⟨h1, hh1, habs1⟩ := hasher_absorbed H seed a
  obtain ⟨h2, b2, hu2, habs2, hb2⟩ := H.update h1 _ msg.to_slice habs1
  refine ⟨h2, ?_, by rw [← hA]; simpa [Array.to_slice] using habs2⟩
  simp [wots.encoder, ha, hh1, core.array.Array.as_slice, rust_primitives.slice.array_as_slice,
    hu2, hb2]

/-! ## The codeword -/

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

/-- `u128::from_be_bytes` of a digest: the number its bytes spell, most significant first. -/
theorem from_be_bytes_val (a : Array Std.U8 16#usize) :
    (Aeneas.Std.core.num.U128.from_be_bytes a).val = leNat (bytes a.val).reverse := by
  have h : ∀ l : List Std.U8, (l.map U8.bv).foldr (fun b acc ↦ b.toNat + 256 * acc) 0 =
      leNat (bytes l) := by
    intro l
    induction l with
    | nil => rfl
    | cons x xs ih => simp only [List.map_cons, List.foldr_cons, ih, bytes, leNat_cons]; rfl
  simp only [Aeneas.Std.core.num.U128.from_be_bytes, UScalar.val, BitVec.fromBEBytes,
    BitVec.toNat_cast, fromLEBytes_toNat, ← List.map_reverse, h, bytes]

/-- Two bits of a number, read from the byte that holds them. -/
theorem two_bits_of_byte (n q s : Nat) (hs : s ≤ 6) :
    n / 2 ^ (8 * q + s) % 4 = n / 256 ^ q % 256 / 2 ^ s % 4 := by
  have h1 : ∀ x : Nat, x / 2 ^ s % 4 = x % (2 ^ s * 4) / 2 ^ s := fun x =>
    (Nat.mod_mul_right_div_self x (2 ^ s) 4).symm
  have hd : 2 ^ s * 4 ∣ 256 := by
    rw [show (4 : Nat) = 2 ^ 2 by rfl, ← Nat.pow_add, show (256 : Nat) = 2 ^ 8 by rfl]
    exact Nat.pow_dvd_pow 2 (by omega)
  rw [Nat.pow_add, ← Nat.div_div_eq_div_mul, Nat.pow_mul, show (2 : Nat) ^ 8 = 256 by rfl, h1, h1,
    Nat.mod_mod_of_dvd _ hd]

/-- Digit `i` of a digest: the big-endian number's bits `2 (63 - i)`, as `codeword` reads them,
are the little-endian number's bits `8 ⌊i / 4⌋ + 6 - 2 (i mod 4)`, as `base_2b` does. -/
theorem digit_eq (l : List UInt8) (hl : l.length = 16) (i : Nat) (hi : i < 64) :
    leNat l.reverse / 2 ^ (2 * (63 - i)) % 4 = leNat l / 2 ^ (8 * (i / 4) + 6 - 2 * (i % 4)) % 4 := by
  have hr : 2 * (63 - i) = 8 * (15 - i / 4) + (6 - 2 * (i % 4)) := by omega
  have hq : 8 * (i / 4) + 6 - 2 * (i % 4) = 8 * (i / 4) + (6 - 2 * (i % 4)) := by omega
  rw [hr, hq, two_bits_of_byte _ _ _ (by omega), two_bits_of_byte _ _ _ (by omega),
    leNat_byte l.reverse (15 - i / 4) (by simp; omega), leNat_byte l (i / 4) (by omega),
    List.getElem_reverse]
  congr 4
  simp [hl]
  omega

/-- The digit `codeword` reads at `n` from the big-endian number `d`, as a byte. -/
def digitU8 (d : Std.U128) (n : Nat) : Std.U8 := ⟨BitVec.ofNat 8 (d.val >>> (2 * (63 - n)) % 4)⟩

theorem digitU8_val (d : Std.U128) (n : Nat) : (digitU8 d n).val = d.val >>> (2 * (63 - n)) % 4 := by
  simp only [digitU8, UScalar.val]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))

/-- `codeword`'s closure: digit `n`, and itself. -/
theorem codeword_closure (d : Std.U128) (n : Std.Usize) (hn : n.val < 64) :
    wots.codeword.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut d n =
      ok (digitU8 d n.val, d) := by
  have h : wots.codeword.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut d n
      ⦃ r => r = (digitU8 d n.val, d) ⦄ := by
    unfold wots.codeword.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut
    simp only [internals.V, internals.W, chain_len, Aeneas.Std.bind_ok]
    step*
    have h5 : i5.val = 4 := by rw [i5_post, UScalar.cast_val_eq]; rfl
    have h6 : i6.val = 2 ^ 2 - 1 := by rw [i6_post, h5]; rfl
    have h2 : i2.val = 2 * (63 - n.val) := by omega
    have hv : i8.val = (digitU8 d n.val).val := by
      rw [digitU8_val, i8_post, UScalar.cast_val_eq, i7_post, UScalar.val_and, h6,
        Nat.and_two_pow_sub_one_eq_mod, i3_post, h2]
      exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))
    exact (UScalar.eq_equiv _ _).2 hv
  obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists h
  exact hr

/-- The sum loop of `codeword`: the sum of the 64 digits. -/
theorem codeword_loop_eq (x : Array Std.U8 64#usize) (hx : ∀ n < 64, (x.val[n]!).val < 4) :
    ∃ r : Std.Usize, wots.codeword_loop { start := 0#usize, «end» := 64#usize } x 0#usize = ok r ∧
      r.val = ∑ j ∈ Finset.range 64, (x.val[j]!).val := by
  have h64 : (64#usize).val = 64 := by decide
  unfold wots.codeword_loop
  obtain ⟨r, hr, hsum, -⟩ := range_loop (fun p => wots.codeword_loop.body x p.1 p.2) 64#usize
    (fun n (acc : Std.Usize) => acc.val = ∑ j ∈ Finset.range n, (x.val[j]!).val ∧ acc.val ≤ 3 * n)
    (by
      intro i acc hi
      simp only [wots.codeword_loop.body,
        core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next, range_next_ge i _ hi,
        Aeneas.Std.bind_ok]
      rfl)
    (by
      intro i acc hi ⟨hacc, hb⟩
      obtain ⟨i', hi', hnext⟩ := range_next_lt i _ hi
      have hxi := hx i.val (by omega)
      have h : wots.codeword_loop.body x { start := i, «end» := 64#usize } acc
          ⦃ r => ∃ acc' : Std.Usize, r = .cont ({ start := i', «end» := 64#usize }, acc') ∧
            acc'.val = acc.val + (x.val[i.val]!).val ⦄ := by
        unfold wots.codeword_loop.body
        simp only [core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next, hnext,
          Aeneas.Std.bind_ok]
        step*
        have h2 : i2.val = i1.val := by
          rw [i2_post, UScalar.cast_val_eq]
          exact Nat.mod_eq_of_lt (by scalar_tac)
        refine ⟨sum1, rfl, ?_⟩
        rw [sum1_post, h2, i1_post1, getElem!_pos x.val i.val i1_post]
      obtain ⟨r, hr, acc', rfl, hacc'⟩ := WP.spec_imp_exists h
      refine ⟨i', acc', hi', hr, ?_, ?_⟩
      · rw [hi', Finset.sum_range_succ, hacc', hacc]
      · omega)
    0#usize 0#usize (by scalar_tac) (by simp)
  exact ⟨r, hr, by rw [hsum, h64]⟩

/-- A Rust digest as a number: the one its bytes spell, least significant first. -/
theorem toDigest_toNat (a : Array Std.U8 16#usize) : (toDigest a).toNat = leNat (bytes a.val) := by
  have h := leNat_lt (bytes a.val)
  have hl : (bytes a.val).length = 16 := by simp [bytes]
  rw [hl] at h
  show leNat (bytes a.val) % 2 ^ 128 = leNat (bytes a.val)
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h (by norm_num))

/-- The digit `codeword` reads is the statement's `base_2b` digit. -/
theorem digitU8_base2b (a : Array Std.U8 16#usize) (i : ChainIndex) :
    (digitU8 (Aeneas.Std.core.num.U128.from_be_bytes a) i.val).val =
      (TargetSum.base2bDigits (toDigest a) i).val := by
  rw [digitU8_val, from_be_bytes_val, Nat.shiftRight_eq_div_pow,
    digit_eq _ (by simp [bytes]) _ i.isLt]
  simp [TargetSum.base2bDigits, winternitzBits, toDigest_toNat, Nat.shiftRight_eq_div_pow]

/-- **`codeword`** decodes as the statement's `decodeDigest`: the same digits, or neither a
codeword. -/
theorem codeword_eq (a : Array Std.U8 16#usize) :
    ∃ o, wots.codeword a = ok o ∧
      (ofOption o).map (fun (x : Array Std.U8 64#usize) (i : ChainIndex) => (x.val[i.val]!).val) =
        (TargetSum.decodeDigest (toDigest a)).map (fun e i => (e i).val) := by
  have h64 : (64#usize).val = 64 := by decide
  obtain ⟨x, hx, hxv⟩ := from_fn_eq 64#usize
    wots.codeword.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8
    (Aeneas.Std.core.num.U128.from_be_bytes a)
    (digitU8 (Aeneas.Std.core.num.U128.from_be_bytes a))
    (fun i hi => codeword_closure _ i (by omega))
  have hxn : ∀ n < 64, x.val[n]! = digitU8 (Aeneas.Std.core.num.U128.from_be_bytes a) n := by
    intro n hn
    rw [hxv, h64]
    simp [hn]
  have hdig : ∀ i : ChainIndex,
      (x.val[i.val]!).val = (TargetSum.base2bDigits (toDigest a) i).val := fun i => by
    rw [hxn i.val i.isLt]
    exact digitU8_base2b a i
  obtain ⟨s, hs, hsv⟩ := codeword_loop_eq x (fun n hn => by
    rw [hxn n hn, digitU8_val]
    exact Nat.mod_lt _ (by decide))
  have hsum : s.val = TargetSum.sum (TargetSum.base2bDigits (toDigest a)) := by
    rw [hsv, ← Fin.sum_univ_eq_sum_range (fun j => (x.val[j]!).val) 64]
    exact Finset.sum_congr rfl (fun i _ => hdig i)
  have hrun : wots.codeword a = ok (if s = 128#usize then some x else none) := by
    simp [wots.codeword, core.num.U128.from_be_bytes, rust_primitives.arithmetic.from_be_bytes_u128,
      hx, internals.V, hs, internals.TARGET_SUM, core.bool.Bool.then_some]
  refine ⟨_, hrun, ?_⟩
  have h128 : (128#usize).val = 128 := by decide
  by_cases hv : s = 128#usize
  · have hvalid : TargetSum.Valid (TargetSum.base2bDigits (toDigest a)) := by
      show TargetSum.sum _ = targetSum
      rw [← hsum, hv, h128]; rfl
    have hdec : TargetSum.decodeDigest (toDigest a) =
        some (TargetSum.base2bDigits (toDigest a)) := by
      unfold TargetSum.decodeDigest
      split
      · rfl
      · next h => exact absurd hvalid h
    rw [hdec]
    simp only [hv, ↓reduceIte, ofOption, Option.map_some]
    exact congrArg some (funext hdig)
  · have hinvalid : ¬ TargetSum.Valid (TargetSum.base2bDigits (toDigest a)) := by
      show ¬ TargetSum.sum _ = targetSum
      rw [← hsum]
      intro h
      exact hv ((UScalar.eq_equiv _ _).2 (by rw [h, h128]; rfl))
    have hdec : TargetSum.decodeDigest (toDigest a) = none := by
      unfold TargetSum.decodeDigest
      split
      · next h => exact absurd h hinvalid
      · rfl
    rw [hdec]
    simp only [hv, ↓reduceIte, ofOption, Option.map_none]

/-- **`encode`** on a hasher that has absorbed `l`: the truncated hash of `l ‖ BE_32(c)`,
decoded. -/
theorem encode_eq {π : KeccakState → KeccakState} (H : HasherSpec π)
    (hclone : ∀ h, keccak256.Hasher.Insts.CoreCloneClone.clone h = ok h)
    (h : keccak256.Hasher) (l : List UInt8) (hl : H.Absorbed h l) (c : Std.U32) :
    ∃ o, wots.encode h c = ok o ∧
      (ofOption o).map (fun (x : Array Std.U8 64#usize) (i : ChainIndex) => (x.val[i.val]!).val) =
        (TargetSum.decodeDigest (truncateHash (Id.run (keccakHash (inId π)
          (l ++ bigEndianBytes 4 c.bv))))).map (fun e i => (e i).val) := by
  obtain ⟨h1, back, hup, hA1, -⟩ := H.update h l (Aeneas.Std.core.num.U32.to_be_bytes c).to_slice hl
  obtain ⟨d, hfin, hd⟩ := H.finalize h1 _ hA1
  obtain ⟨a, ha, hav⟩ := truncate_eq d
  obtain ⟨o, ho, hov⟩ := codeword_eq a
  refine ⟨o, ?_, ?_⟩
  · simp [wots.encode, hclone, u32_to_be_bytes, core.array.Array.as_slice,
      rust_primitives.slice.array_as_slice, hup, hfin, ha, ho]
  · rw [hov, toDigest_truncate _ d a (by simpa [Array.to_slice, bytes_to_be_bytes_u32] using hd) hav]

/-! ## The one-time leaf -/

/-- `from_fn` of a closure that keeps itself and returns, at `i`, something satisfying `P i`. -/
theorem from_fn_pred {T F : Type} [Inhabited T] (N : Std.Usize)
    (inst : core.ops.function.FnMut F Std.Usize T) (c : F) (P : Nat → T → Prop)
    (h : ∀ i : Std.Usize, i.val < N.val → ∃ r, inst.call_mut c i = ok (r, c) ∧ P i.val r) :
    ∃ a, core.array.from_fn N inst c = ok a ∧ ∀ n < N.val, P n a.val[n]! := by
  have hex : ∀ n : Nat, ∃ r : T, n < N.val →
      (∀ i : Std.Usize, i.val = n → inst.call_mut c i = ok (r, c)) ∧ P n r := by
    intro n
    by_cases hn : n < N.val
    · have hv : (⟨BitVec.ofNat UScalarTy.Usize.numBits n⟩ : Std.Usize).val = n := by
        have := N.hBounds
        simp only [UScalar.val, BitVec.toNat_ofNat]
        exact Nat.mod_eq_of_lt (by scalar_tac)
      obtain ⟨r, hr, hp⟩ := h _ (by rw [hv]; exact hn)
      rw [hv] at hp
      refine ⟨r, fun _ => ⟨fun i hi => ?_, hp⟩⟩
      have : i = ⟨BitVec.ofNat UScalarTy.Usize.numBits n⟩ :=
        (UScalar.eq_equiv _ _).2 (by rw [hi, hv])
      rw [this]
      exact hr
    · exact ⟨default, fun h => absurd h hn⟩
  choose g hg using hex
  obtain ⟨a, ha, hav⟩ := from_fn_eq N inst c g (fun i hi => (hg i.val hi).1 i rfl)
  refine ⟨a, ha, fun n hn => ?_⟩
  rw [hav]
  simpa [hn] using (hg n hn).2

/-- The statement's `otsLeaf` where the counter encodes the message: the leaf hash of the chains'
ends. -/
theorem otsLeaf_some {π : KeccakState → KeccakState} (s : PublicParameter) (l : Layer)
    (t : TreeIndex) (f : TreeLeafIndex) (m : Digest) (c : EncodingCounter)
    (v : ChainIndex → Digest) (e : Encoding)
    (h : Id.run (Verification.encode (inId π) s l t f m c) = some e) :
    Id.run (Verification.otsLeaf (inId π) s l t f m c v) =
      some (Id.run (Verification.leafHash (inId π) s l t f
        (fun i => Id.run (Verification.recoverChain (inId π) s l t f i (e i) (v i))))) := by
  have h' : Verification.encode (inId π) s l t f m c = (pure (some e) : Id _) := h
  simp only [Verification.otsLeaf, h', pure_bind, Id.run_bind, Id.run_pure, sequenceFin_id]

/-- The statement's `otsLeaf` where the counter does not encode the message: nothing. -/
theorem otsLeaf_none {π : KeccakState → KeccakState} (s : PublicParameter) (l : Layer)
    (t : TreeIndex) (f : TreeLeafIndex) (m : Digest) (c : EncodingCounter)
    (v : ChainIndex → Digest)
    (h : Id.run (Verification.encode (inId π) s l t f m c) = none) :
    Id.run (Verification.otsLeaf (inId π) s l t f m c v) = none := by
  have h' : Verification.encode (inId π) s l t f m c = (pure none : Id _) := h
  simp only [Verification.otsLeaf, h', pure_bind, Id.run_pure]

/-- An element of an array, by an index within it. -/
theorem array_index_eq {α : Type} [Inhabited α] {N : Std.Usize} (a : Array α N) (i : Std.Usize)
    (h : i.val < N.val) : Array.index_usize a i = ok (a.val[i.val]!) := by
  have hs : Array.index_usize a i ⦃ x => x = a.val[i.val]! ⦄ := by
    step*
    rw [x_post1, getElem!_pos a.val i.val x_post]
  obtain ⟨x, hx, rfl⟩ := WP.spec_imp_exists hs
  exact hx

end Wots

open Wots in
/-- **`wots_leaf`** recovers the statement's one-time leaf, or like it finds no codeword. -/
theorem wotsLeaf_spec {π : KeccakState → KeccakState} (H : HasherSpec π)
    (hclone : ∀ h, keccak256.Hasher.Insts.CoreCloneClone.clone h = ok h)
    (hth : ThSpec π) (hk : KeyAdrsSpec) (hw : AdrsWordSpec) : WotsLeafSpec π := by
  intro seed k msg c sig layer tree leaf hkey
  have hchain := chain_spec hth hk hw
  have hkey' := hkey
  obtain ⟨hkl, hkt, hkf⟩ := hkey
  have hl3 : layer.val < 3 := layer.isLt
  have h64 : (64#usize).val = 64 := by decide
  obtain ⟨h, hh, habs⟩ := encoder_absorbed H hk seed k msg (by omega)
  obtain ⟨o, ho, hov⟩ := encode_eq H hclone h _ habs c
  have henc : Id.run (Verification.encode (inId π) (toDigest seed) layer tree leaf (toDigest msg)
        c.bv) =
      TargetSum.decodeDigest (truncateHash (Id.run (keccakHash (inId π)
        (bytes seed.val ++ (makeAddress k.layer.val k.tree.val .wotsEncoding k.leaf.val 0 0).toBytes
          ++ bytes msg.val ++ bigEndianBytes 4 c.bv)))) := by
    simp only [Verification.encode, Verification.tweakableHash, Verification.addressedHash,
      addressedHashInput, hasherInput,
      hashDomainFields, littleEndianBytes_toDigest, hkl, hkt, hkf, List.append_assoc,
      bind_pure_comp, Id.run_map]
  rw [← henc] at hov
  match o, ho, hov with
  | .None, ho, hov =>
    refine ⟨.None, ?_, ?_⟩
    · simp [wots.wots_leaf, hh, ho,
        core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch]
      rfl
    · have hnone : Id.run (Verification.encode (inId π) (toDigest seed) layer tree leaf
          (toDigest msg) c.bv) = none := by
        simpa [ofOption] using hov.symm
      rw [otsLeaf_none _ _ _ _ _ _ _ hnone]
      rfl
  | .Some val, ho, hov =>
    obtain ⟨e, he, hev⟩ : ∃ e, Id.run (Verification.encode (inId π) (toDigest seed) layer tree leaf
        (toDigest msg) c.bv) = some e ∧ ∀ i : ChainIndex, (val.val[i.val]!).val = (e i).val := by
      cases hd : Id.run (Verification.encode (inId π) (toDigest seed) layer tree leaf
          (toDigest msg) c.bv) with
      | none => rw [hd] at hov; simp [ofOption] at hov
      | some e =>
        rw [hd] at hov
        simp only [ofOption, Option.map_some, Option.some.injEq] at hov
        exact ⟨e, rfl, fun i => congrFun hov i⟩
    obtain ⟨ends, hends, hendsv⟩ := from_fn_pred 64#usize
      wots.wots_leaf.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU816 (val, seed, k, sig)
      (fun n r => ∀ hn : n < 64, toDigest r = Id.run (Verification.recoverChain (inId π)
        (toDigest seed) layer tree leaf ⟨n, hn⟩ (e ⟨n, hn⟩) (toDigest sig.val[n]!)))
      (by
        intro n hn0
        have hi64 : n.val < 64 := by omega
        have hstart := hev ⟨n.val, hi64⟩
        have he4 : (e ⟨n.val, hi64⟩).val < 4 := (e ⟨n.val, hi64⟩).isLt
        simp only at hstart
        have hc : wots.wots_leaf.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU816.call_mut
            (val, seed, k, sig) n ⦃ r => r.2 = (val, seed, k, sig) ∧
              ∀ hn : n.val < 64, toDigest r.1 = Id.run (Verification.recoverChain (inId π)
                (toDigest seed) layer tree leaf ⟨n.val, hn⟩ (e ⟨n.val, hn⟩)
                (toDigest sig.val[n.val]!)) ⦄ := by
          unfold wots.wots_leaf.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU816.call_mut
          simp only [chain_len, Aeneas.Std.bind_ok]
          step*
          · have h1 : start.val = i.val := by
              rw [start_post, UScalar.cast_val_eq]
              exact Nat.mod_eq_of_lt (by scalar_tac)
            have h2 : i.val = (e ⟨n.val, hi64⟩).val := by
              rw [i_post1, ← hstart, getElem!_pos val.val n.val i_post]
            omega
          · have h1 : start.val = i.val := by
              rw [start_post, UScalar.cast_val_eq]
              exact Nat.mod_eq_of_lt (by scalar_tac)
            have h2 : i.val = (e ⟨n.val, hi64⟩).val := by
              rw [i_post1, ← hstart, getElem!_pos val.val n.val i_post]
            obtain ⟨r, hr, hrv⟩ := hchain seed k n start i3 a3 layer tree leaf ⟨n.val, hi64⟩ hkey'
              rfl (by omega)
            rw [hr]
            simp only [Aeneas.Std.bind_ok]
            refine (WP.spec_ok _).2 ⟨rfl, fun hn => ?_⟩
            rw [hrv]
            unfold Verification.recoverChain
            rw [i3_post, i2_post, h1, h2, a3_post1, getElem!_pos sig.val n.val a3_post]
            rfl
        obtain ⟨⟨r, c'⟩, hr, hc', hrv⟩ := WP.spec_imp_exists hc
        simp only at hc' hrv
        subst hc'
        exact ⟨r, hr, hrv⟩)
    obtain ⟨a, ha, hA⟩ := hk k hash.WOTS_PK .wotsPublicKey
      (by simp [hash.WOTS_PK, AddressType.word]) (by omega)
    obtain ⟨d, hd, hdv⟩ := th_digests_adrs hth seed a _ ends.to_slice hA
      (by simp [Slice.length]; scalar_tac)
    have hl : ends.val.map toDigest = List.ofFn (fun i : ChainIndex =>
        Id.run (Verification.recoverChain (inId π) (toDigest seed) layer tree leaf i (e i)
          (toDigest sig.val[i.val]!))) := by
      have hlen : ends.val.length = 64 := by simp
      apply List.ext_getElem
      · rw [List.length_map, List.length_ofFn, hlen]
        rfl
      · intro n h1 h2
        have hn : n < 64 := by simpa using h1
        simp only [List.getElem_map, List.getElem_ofFn]
        have := hendsv n (by omega) hn
        rw [getElem!_pos ends.val n (by simpa using h1)] at this
        exact this
    have hpay : bytes ((ends.to_slice.val.map Array.val).flatten) = digestsPayload
        (fun i : ChainIndex => Id.run (Verification.recoverChain (inId π) (toDigest seed) layer
          tree leaf i (e i) (toDigest sig.val[i.val]!))) := by
      rw [bytes_flatten]
      unfold digestsPayload
      have hs : ends.to_slice.val = ends.val := by simp [Array.to_slice]
      rw [hs]
      exact (flatMap_map' toDigest (littleEndianBytes 16) ends.val).symm.trans
        (congrArg (fun l => l.flatMap (littleEndianBytes 16)) hl)
    refine ⟨.Some (val, d), ?_, ?_⟩
    · simp [wots.wots_leaf, hh, ho,
        core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, hends,
        wots.wots_leaf_hash, ha, core.array.Array.as_slice, rust_primitives.slice.array_as_slice, hd]
    · rw [otsLeaf_some _ _ _ _ _ _ _ e he]
      simp only [ofOption, Option.map_some]
      refine congrArg some ?_
      rw [hdv, hpay]
      simp only [Verification.leafHash, Verification.tweakableHash, hashDomainFields, hkl, hkt, hkf]

end LeanSphincsProofs
