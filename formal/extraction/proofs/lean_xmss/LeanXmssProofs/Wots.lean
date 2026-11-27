import LeanXmssProofs.Hash
import LeanXmssProofs.Popcount

/-!
# `wots.rs`: a chain, the codeword, and the one-time leaf

`chain`, `chain_ends`, `is_codeword`, `codeword`, `message_digest` and `wots_leaf` (with
`chain_input`, `wots_leaf_hash`, and `layer_hi`, `tweak` and `Tweak::step` of `hash.rs`), as
extracted, compute the statement's `Verification.chainWalk`, `recoverChain`, `Codeword.decode`,
`messageDigest` and `otsLeaf`.

`chain` is a `fold` over a range and `chain_ends` and `codeword` are `from_fn`s of closures: they
are proved as extracted. `is_codeword` sums the digits with two population counts, whose library
model is a loop over the 128 bits (`Popcount.lean`).
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM Std.Do
open HashSig HashSig.OverPermutation LeanXmss
open LeanVM.Semantics (KeccakState)
open LeanVM.Protocol.KeccakHash (digestBytes keccak256With)
open lean_xmss
open Keccak256Proofs

namespace LeanXmssProofs

/-! ## The constants -/

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

/-- `V` is 58. -/
theorem v_eq : internals.V = ok 58#usize := by
  have h : internals.V ⦃ r => r = 58#usize ⦄ := by
    unfold internals.V internals.DIGITS hash.N internals.W ZERO_DIGITS
    step*
  obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists h
  exact hr

/-- `TOP` is `2^23`. -/
theorem top_eq : hash.TOP = ok 8388608#u32 := by
  have h : hash.TOP ⦃ r => r = 8388608#u32 ⦄ := by
    unfold hash.TOP
    step*
  obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists h
  exact hr

/-- `layer_hi`: the field, and bit 23 on the top layer. -/
theorem layer_hi_eq (layer : Std.Usize) (field : Std.U32) (hl : layer.val ≤ 1)
    (hf : field.val < 2 ^ 23) :
    ∃ r, hash.layer_hi layer field = ok r ∧ r.val = field.val + 2 ^ 23 * layer.val := by
  have h : hash.layer_hi layer field ⦃ r => r.val = field.val + 2 ^ 23 * layer.val ⦄ := by
    unfold hash.layer_hi
    simp only [top_eq, lift, Aeneas.Std.bind_ok]
    step*
    have hc : (UScalar.cast .U32 layer).val = layer.val := by
      rw [UScalar.cast_val_eq]
      exact Nat.mod_eq_of_lt (by scalar_tac)
    rw [UScalar.val_or, i2_post, hc]
    rcases (by omega : layer.val = 0 ∨ layer.val = 1) with h | h <;> rw [h]
    · simp
    · have := Nat.two_pow_add_eq_or_of_lt hf 1
      rw [Nat.or_comm, show 1 * 8388608 = 2 ^ 23 * 1 by norm_num, ← this]
      omega
  exact WP.spec_imp_exists h

/-! ## Addresses -/

/-- `tweak`: an address of a type below 32 with `hi` below `2^24`, at step 0. -/
theorem tweak_eq (t : Std.U8) (hi lo : Std.U32) (ht : t.val < 32) (hh : hi.val < 2 ^ 24) :
    hash.tweak t hi lo = ok { t, step := 0#u8, hi, lo } := by
  have h : hash.tweak t hi lo ⦃ r => r = { t, step := 0#u8, hi, lo } ⦄ := by
    unfold hash.tweak
    step*
  obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists h
  exact hr

/-- `Tweak::step`: the same address at a step below 8. -/
theorem tweak_step_eq (tw : hash.Tweak) (s : Std.Usize) (hs : s.val < 8) :
    ∃ tw', hash.Tweak.impl.step tw s = ok tw' ∧ tw'.t = tw.t ∧ tw'.hi = tw.hi ∧ tw'.lo = tw.lo ∧
      tw'.step.val = s.val := by
  have h : hash.Tweak.impl.step tw s ⦃ tw' => tw'.t = tw.t ∧ tw'.hi = tw.hi ∧ tw'.lo = tw.lo ∧
      tw'.step.val = s.val ⦄ := by
    unfold hash.Tweak.impl.step
    step*
  exact WP.spec_imp_exists h

/-- The fields of an address built by `tweak` on a layer, then `step`. -/
theorem toFields_eq (tw : hash.Tweak) (t s hi lo : ℕ) (ht : tw.t.val = t) (hs : tw.step.val = s)
    (hh : tw.hi.val = hi) (hl : tw.lo.val = lo) : toFields tw = tweakFields t s hi lo := by
  rw [toFields, ht, hs, hh, hl]

/-! ## A chain -/

/-- `chain_input`: the address of a chain step and its payload, the value then the chain. -/
theorem chain_input_eq (layer : Std.Usize) (e : Std.U32) (i frm : Std.Usize)
    (value : Array Std.U8 16#usize) (hl : layer.val ≤ 1) (hf : frm.val < 8) :
    ∃ tw p, wots.chain_input layer e i frm value = ok (tw, p) ∧ tw.t.val = 1 ∧
      toFields tw = tweakFields 1 frm.val (0 + 2 ^ 23 * layer.val) e.val ∧
      ∃ a : Array Std.U8 16#usize, p.val = [value, a] ∧
        bytes a.val = littleEndianBytes 16 (BitVec.ofNat 128 i.val) := by
  obtain ⟨hi, hhi, hhiv⟩ := layer_hi_eq layer 0#u32 hl (by decide)
  have htw := tweak_eq hash.TWEAK_CHAIN hi e (by simp [hash.TWEAK_CHAIN]) (by
    rw [hhiv]; simp; omega)
  obtain ⟨tw, htw', ht, hh, hlo, hst⟩ := tweak_step_eq { t := hash.TWEAK_CHAIN, step := 0#u8, hi, lo := e } frm hf
  obtain ⟨a, ha, hab⟩ := u128_to_le_bytes (UScalar.cast .U128 i)
  refine ⟨tw, Array.make 2#usize [value, a] (by rfl), ?_, by rw [ht]; simp [hash.TWEAK_CHAIN], ?_, a, rfl, ?_⟩
  · simp [wots.chain_input, hhi, htw, htw', lift, ha]
  · exact toFields_eq tw _ _ _ _ (by rw [ht]; simp [hash.TWEAK_CHAIN]) hst (by rw [hh]; exact hhiv)
      (by rw [hlo])
  · rw [hab]
    congr 2
    rw [UScalar.cast_val_eq]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le i.hBounds (by
      rcases System.Platform.numBits_eq with h | h <;> simp [UScalarTy.numBits, h]))

section
variable {π : KeccakState → KeccakState}

/-- **`chain`** walks the statement's chain. -/
theorem chain_spec (H : HasherSpec π) (pp : Array Std.U8 16#usize) (layer : Std.Usize)
    (e : Std.U32) (i start steps : Std.Usize) (v : Array Std.U8 16#usize) (l : Layer)
    (key : KeyIndex) (ci : ChainIndex) (hl : layer.val = l.val) (he : e.val = key.val)
    (hi : i.val = ci.val) (hss : start.val + steps.val ≤ 3) :
    ∃ r, wots.chain pp layer e i start steps v = ok r ∧
      toDigest r = Id.run (Verification.chainWalk (inId π) (toDigest pp) l key ci start.val
        steps.val (toDigest v)) := by
  have hl1 : layer.val ≤ 1 := by have := l.isLt; simp only [layerCount] at this; omega
  have hsum : start + steps ⦃ r => r.val = start.val + steps.val ⦄ := by step*
  obtain ⟨i1, hi1, hi1v⟩ := WP.spec_imp_exists hsum
  have hfold := range_fold
    wots.chain.closure.Insts.CoreOpsFunctionFnMutPairArrayU816UsizeArrayU816 (layer, e, i, pp) i1
    (fun j (acc : Array Std.U8 16#usize) => start.val ≤ j ∧
      toDigest acc = Id.run (Verification.chainWalk (inId π)
        (toDigest pp) l key ci start.val (j - start.val) (toDigest v)))
    ?_ start v (by omega) ⟨Nat.le_refl _, by simp [Verification.chainWalk, walkChain]⟩
  · obtain ⟨r, hr, -, hinv⟩ := hfold
    refine ⟨r, ?_, by rw [hinv, hi1v]; congr 2; omega⟩
    have h4 : i1.val < 4 := by omega
    unfold wots.chain
    simp [hi1, chain_len, hr, massert, h4]
  · intro j acc hj ⟨hsj, hinv⟩
    obtain ⟨tw, p, hin, ht, hF, a, hp, ha⟩ := chain_input_eq layer e i j acc hl1 (by omega)
    obtain ⟨d, hd, hdig⟩ := th_digests_spec H pp tw p.to_slice (by omega)
      (by simp [Slice.length]; scalar_tac)
    have hlt : start.val + (j.val - start.val) < chainLength - 1 := by
      simp only [chainLength, winternitzBits]; omega
    refine ⟨d, ?_, by omega, ?_⟩
    · simp [wots.chain.closure.Insts.CoreOpsFunctionFnMutPairArrayU816UsizeArrayU816.call_mut,
        hin, core.array.Array.as_slice, rust_primitives.slice.array_as_slice, hd]
    · have hprev : Id.run (Verification.chainWalk (inId π) (toDigest pp) l key ci
          start.val (j.val - start.val + 1) (toDigest v)) =
          Id.run (Verification.tweakableHash (inId π) (toDigest pp)
            (.chain l key ⟨start.val + (j.val - start.val), hlt⟩)
            (Verification.chainPayload ci (toDigest acc))) := by
        rw [hinv]
        simp only [Verification.chainWalk, walkChain, dite_eq_left_of_eq_true (eq_true hlt)]
        rfl
      rw [hdig, show j.val + 1 - start.val = (j.val - start.val) + 1 by omega, hprev, hF]
      have hjj : start.val + (j.val - start.val) = j.val := by omega
      have hpay : bytes ((p.to_slice.val.map Array.val).flatten) =
          Verification.chainPayload ci (toDigest acc) := by
        simp [Array.to_slice, hp, Verification.chainPayload, littleEndianBytes_toDigest, ha, hi]
      rw [hpay]
      simp only [Verification.tweakableHash, hashDomainFields, layerHi, hjj, hl, he]

/-- **`chain_ends`** walks each chain from its digit to its end. -/
theorem chain_ends_spec (H : HasherSpec π) (pp : Array Std.U8 16#usize) (layer : Std.Usize)
    (e : Std.U32) (x : Array Std.U8 58#usize) (values : Array (Array Std.U8 16#usize) 58#usize)
    (l : Layer) (key : KeyIndex) (enc : Encoding) (hl : layer.val = l.val) (he : e.val = key.val)
    (hx : ∀ i : ChainIndex, (x.val[i.val]!).val = (enc i).val) :
    ∃ ends, wots.chain_ends pp layer e x values = ok ends ∧
      ∀ n (hn : n < 58), toDigest ends.val[n]! = Id.run (Verification.recoverChain (inId π)
        (toDigest pp) l key ⟨n, hn⟩ (enc ⟨n, hn⟩) (toDigest values.val[n]!)) := by
  have h58 : (58#usize).val = 58 := by decide
  obtain ⟨ends, hends, hendsv⟩ := from_fn_pred 58#usize
    wots.chain_ends.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU816 (x, pp, layer, e, values)
    (fun n r => ∀ hn : n < 58, toDigest r = Id.run (Verification.recoverChain (inId π)
      (toDigest pp) l key ⟨n, hn⟩ (enc ⟨n, hn⟩) (toDigest values.val[n]!)))
    (by
      intro n hn0
      have hi58 : n.val < 58 := by omega
      have hstart := hx ⟨n.val, hi58⟩
      have he4 : (enc ⟨n.val, hi58⟩).val < 4 := (enc ⟨n.val, hi58⟩).isLt
      simp only at hstart
      have hc : wots.chain_ends.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU816.call_mut
          (x, pp, layer, e, values) n ⦃ r => r.2 = (x, pp, layer, e, values) ∧
            ∀ hn : n.val < 58, toDigest r.1 = Id.run (Verification.recoverChain (inId π)
              (toDigest pp) l key ⟨n.val, hn⟩ (enc ⟨n.val, hn⟩)
              (toDigest values.val[n.val]!)) ⦄ := by
        unfold wots.chain_ends.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU816.call_mut
        simp only [chain_len, Aeneas.Std.bind_ok]
        step*
        · have h1 : start.val = i2.val := by
            rw [start_post, UScalar.cast_val_eq]
            exact Nat.mod_eq_of_lt (by scalar_tac)
          have h2 : i2.val = (enc ⟨n.val, hi58⟩).val := by
            rw [i2_post1, ← hstart, getElem!_pos x.val n.val i2_post]
          omega
        · have h1 : start.val = i2.val := by
            rw [start_post, UScalar.cast_val_eq]
            exact Nat.mod_eq_of_lt (by scalar_tac)
          have h2 : i2.val = (enc ⟨n.val, hi58⟩).val := by
            rw [i2_post1, ← hstart, getElem!_pos x.val n.val i2_post]
          obtain ⟨r, hr, hrv⟩ := chain_spec H pp layer e n start i5 a3 l key ⟨n.val, hi58⟩ hl he
            rfl (by omega)
          rw [hr]
          simp only [Aeneas.Std.bind_ok]
          refine (WP.spec_ok _).2 ⟨rfl, fun hn => ?_⟩
          rw [hrv]
          unfold Verification.recoverChain
          rw [i5_post, i4_post, h1, h2, a3_post1, getElem!_pos values.val n.val a3_post]
          rfl
      obtain ⟨⟨r, c'⟩, hr, hc', hrv⟩ := WP.spec_imp_exists hc
      simp only at hc' hrv
      subst hc'
      exact ⟨r, hr, hrv⟩)
  exact ⟨ends, hends, fun n hn => hendsv n (by omega) hn⟩

end

/-! ## The codeword -/

/-- `LOW` is `0b0101…01`: the low bit of each of the 64 digits. -/
theorem low_eq : ∃ L, wots.is_codeword.LOW = ok L ∧ L.val = lowBits 64 := by
  have h : wots.is_codeword.LOW ⦃ L => L.val = lowBits 64 ⦄ := by
    unfold wots.is_codeword.LOW
    step*
    rw [L_post]
    decide
  exact WP.spec_imp_exists h

/-- **`is_codeword`**: the digits past the 58th are zero and the others sum to 106. -/
theorem is_codeword_eq (d : Std.U128) :
    wots.is_codeword d = ok (decide (d.val / 2 ^ 116 = 0 ∧
      ∑ i ∈ Finset.range 58, d.val / 2 ^ (2 * i) % 4 = 106)) := by
  obtain ⟨L, hL, hLv⟩ := low_eq
  obtain ⟨c1, hc1, hc1v⟩ := count_ones_eq (d &&& L)
  obtain ⟨c2, hc2, hc2v⟩ := count_ones_eq (d &&& ~~~ L)
  have hle1 := popcount_le (d &&& L).val 128
  have hle2 := popcount_le (d &&& ~~~ L).val 128
  have hlo : ∀ j < 2 * 64, L.val.testBit j = decide (j % 2 = 0) := by
    intro j hj
    rw [hLv, testBit_lowBits]
    apply decide_eq_decide.mpr
    omega
  have hhi : ∀ j < 2 * 64, (~~~ L).val.testBit j = decide (j % 2 = 1) := by
    intro j hj
    have hb : (~~~ L).val.testBit j = (~~~ L.bv).getLsbD j := rfl
    have hb' : L.bv.getLsbD j = L.val.testBit j := rfl
    rw [hb, BitVec.getLsbD_not, hb', hlo j hj]
    have : j < 128 := by omega
    by_cases h0 : j % 2 = 0
    · simp [h0, this]
    · have h1 : j % 2 = 1 := by omega
      simp [h1, this]
  have hsum : c1.val + 2 * c2.val = ∑ i ∈ Finset.range 64, d.val / 2 ^ (2 * i) % 4 := by
    rw [hc1v, hc2v, UScalar.val_and, UScalar.val_and]
    exact popcount_digits d.val L.val (~~~ L).val 64 hlo hhi
  have h : wots.is_codeword d ⦃ r => r = decide (d.val / 2 ^ 116 = 0 ∧
      ∑ i ∈ Finset.range 58, d.val / 2 ^ (2 * i) % 4 = 106) ⦄ := by
    unfold wots.is_codeword
    simp only [v_eq, internals.W, hL, lift, hc1, hc2, Aeneas.Std.bind_ok]
    step*
    · have h0 : i2 = 0#u128 := by assumption
      have hd0 : d.val / 2 ^ 116 = 0 := by
        have := congrArg UScalar.val h0
        rw [i2_post, i1_post, Nat.shiftRight_eq_div_pow] at this
        exact this
      have hlt : d.val < 2 ^ 116 := by
        rcases Nat.lt_or_ge d.val (2 ^ 116) with h | h
        · exact h
        · have := Nat.div_pos h (Nat.two_pow_pos 116)
          omega
      have htail : ∑ i ∈ Finset.range 64, d.val / 2 ^ (2 * i) % 4 =
          ∑ i ∈ Finset.range 58, d.val / 2 ^ (2 * i) % 4 := by
        rw [show 64 = 58 + 6 by rfl, Finset.sum_range_add]
        have : ∀ x ∈ Finset.range 6, d.val / 2 ^ (2 * (58 + x)) % 4 = 0 := by
          intro x _
          have hp : 2 ^ 116 ≤ 2 ^ (2 * (58 + x)) := Nat.pow_le_pow_right (by decide) (by omega)
          rw [Nat.div_eq_of_lt (by omega)]
        rw [Finset.sum_eq_zero this, Nat.add_zero]
      have ht : (UScalar.cast UScalarTy.U32 internals.TARGET_SUM).val = 106 := by
        rw [UScalar.cast_val_eq]
        simp [internals.TARGET_SUM]
      apply decide_eq_decide.mpr
      rw [UScalar.eq_equiv, ht, i10_post, i9_post, hsum, htail]
      simp only [hd0, true_and]
  obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists h
  exact hr

/-- `u128::from_le_bytes` of a digest: the number its bytes spell, the statement's digest. -/
theorem from_le_bytes_val (a : Array Std.U8 16#usize) :
    (Aeneas.Std.core.num.U128.from_le_bytes a).val = (toDigest a).toNat := by
  have h : ∀ l : List Std.U8, (l.map U8.bv).foldr (fun b acc ↦ b.toNat + 256 * acc) 0 =
      leNat (bytes l) := by
    intro l
    induction l with
    | nil => rfl
    | cons x xs ih => simp only [List.map_cons, List.foldr_cons, ih, bytes, leNat_cons]; rfl
  rw [toDigest_toNat]
  simp only [Aeneas.Std.core.num.U128.from_le_bytes, UScalar.val, BitVec.toNat_cast,
    fromLEBytes_toNat, h]

/-- The digit `codeword` reads at `n` from the number `d`, as a byte. -/
def digitU8 (d : Std.U128) (n : ℕ) : Std.U8 := ⟨BitVec.ofNat 8 (d.val >>> (2 * n) % 4)⟩

theorem digitU8_val (d : Std.U128) (n : ℕ) : (digitU8 d n).val = d.val >>> (2 * n) % 4 := by
  simp only [digitU8, UScalar.val]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))

/-- `codeword`'s closure: digit `n`, and itself. -/
theorem codeword_closure (d : Std.U128) (n : Std.Usize) (hn : n.val < 58) :
    wots.codeword.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut d n =
      ok (digitU8 d n.val, d) := by
  have h : wots.codeword.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut d n
      ⦃ r => r = (digitU8 d n.val, d) ⦄ := by
    unfold wots.codeword.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut
    simp only [internals.W, chain_len, Aeneas.Std.bind_ok]
    step*
    have h3 : i3.val = 4 := by rw [i3_post, UScalar.cast_val_eq]; rfl
    have h4 : i4.val = 2 ^ 2 - 1 := by rw [i4_post, h3]; rfl
    have hv : i6.val = (digitU8 d n.val).val := by
      rw [digitU8_val, i6_post, UScalar.cast_val_eq, i5_post, UScalar.val_and, h4,
        Nat.and_two_pow_sub_one_eq_mod, i1_post, i_post]
      exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))
    exact (UScalar.eq_equiv _ _).2 hv
  obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists h
  exact hr

/-- The digit `codeword` reads is the statement's digit of the digest. -/
theorem digitU8_digestDigits (a : Array Std.U8 16#usize) (i : ChainIndex) :
    (digitU8 (Aeneas.Std.core.num.U128.from_le_bytes a) i.val).val =
      (digestDigits (toDigest a) i).val := by
  rw [digitU8_val, from_le_bytes_val]
  simp [digestDigits, winternitzBits]

/-- **`codeword`** decodes as the statement's `Codeword.decode`: the same digits, or neither a
codeword. -/
theorem codeword_eq (a : Array Std.U8 16#usize) :
    ∃ o, wots.codeword a = ok o ∧
      (ofOption o).map (fun (x : Array Std.U8 58#usize) (i : ChainIndex) => (x.val[i.val]!).val) =
        (Codeword.decode (toDigest a)).map (fun e i => (e i).val) := by
  have h58 : (58#usize).val = 58 := by decide
  have hdv := from_le_bytes_val a
  obtain ⟨x, hx, hxv⟩ := from_fn_eq 58#usize
    wots.codeword.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8
    (Aeneas.Std.core.num.U128.from_le_bytes a)
    (digitU8 (Aeneas.Std.core.num.U128.from_le_bytes a))
    (fun i hi => codeword_closure _ i (by omega))
  have hxn : ∀ n < 58, x.val[n]! = digitU8 (Aeneas.Std.core.num.U128.from_le_bytes a) n := by
    intro n hn
    rw [hxv, h58]
    simp [hn]
  have hdig : ∀ i : ChainIndex, (x.val[i.val]!).val = (digestDigits (toDigest a) i).val := fun i => by
    rw [hxn i.val i.isLt]
    exact digitU8_digestDigits a i
  have hvalid : ((Aeneas.Std.core.num.U128.from_le_bytes a).val / 2 ^ 116 = 0 ∧
      ∑ i ∈ Finset.range 58, (Aeneas.Std.core.num.U128.from_le_bytes a).val / 2 ^ (2 * i) % 4 = 106) ↔
      Codeword.Valid (toDigest a) := by
    have hs : Codeword.sum (digestDigits (toDigest a)) =
        ∑ i ∈ Finset.range 58, (toDigest a).toNat / 2 ^ (2 * i) % 4 := by
      unfold Codeword.sum
      rw [← Fin.sum_univ_eq_sum_range (fun i => (toDigest a).toNat / 2 ^ (2 * i) % 4) 58]
      apply Finset.sum_congr rfl
      intro i _
      simp [digestDigits, winternitzBits, Nat.shiftRight_eq_div_pow]
    rw [hdv]
    show _ ↔ (_ ∧ _)
    rw [hs]
    rfl
  have hrun : ∀ b : Bool, b = decide ((Aeneas.Std.core.num.U128.from_le_bytes a).val / 2 ^ 116 = 0 ∧
      ∑ i ∈ Finset.range 58,
        (Aeneas.Std.core.num.U128.from_le_bytes a).val / 2 ^ (2 * i) % 4 = 106) →
      wots.codeword a = ok (if b then .Some x else .None) := by
    intro b hb
    simp only [wots.codeword, core.num.U128.from_le_bytes,
      rust_primitives.arithmetic.from_le_bytes_u128, is_codeword_eq, core.bool.Bool.then,
      wots.codeword.closure.Insts.CoreOpsFunctionFnOnceTupleArrayU858.call_once, hx,
      Aeneas.Std.bind_ok, ← hb]
    cases b <;> rfl
  by_cases hv : Codeword.Valid (toDigest a)
  · have hdec : Codeword.decode (toDigest a) = some (digestDigits (toDigest a)) := by
      unfold Codeword.decode
      split
      · rfl
      · next h => exact absurd hv h
    refine ⟨.Some x, hrun true (decide_eq_true (hvalid.mpr hv)).symm, ?_⟩
    rw [hdec]
    exact congrArg some (funext hdig)
  · have hdec : Codeword.decode (toDigest a) = none := by
      unfold Codeword.decode
      split
      · next h => exact absurd h hv
      · rfl
    refine ⟨.None, hrun false (decide_eq_false (mt hvalid.mp hv)).symm, ?_⟩
    rw [hdec]
    rfl

/-! ## The one-time leaf -/

section
variable {π : KeccakState → KeccakState}

/-- **`message_digest`**: the statement's digest of a message under a key and a randomizer. -/
theorem message_digest_spec (H : HasherSpec π) (pp : Array Std.U8 16#usize) (layer : Std.Usize)
    (e : Std.U32) (randomizer : Array Std.U8 16#usize) (message : Slice Std.U8) (l : Layer)
    (key : KeyIndex) (hl : layer.val = l.val) (he : e.val = key.val) :
    ∃ d, wots.message_digest pp layer e randomizer message = ok d ∧
      toDigest d = Id.run (Verification.messageDigest (inId π) (toDigest pp) l key
        (bytes message.val) (toDigest randomizer)) := by
  have hl1 : layer.val ≤ 1 := by have := l.isLt; simp only [layerCount] at this; omega
  obtain ⟨hi, hhi, hhiv⟩ := layer_hi_eq layer 0#u32 hl1 (by decide)
  have htw := tweak_eq hash.TWEAK_MSG hi e (by simp [hash.TWEAK_MSG]) (by rw [hhiv]; simp; omega)
  obtain ⟨h, hh, habs⟩ := hasher_absorbed H pp { t := hash.TWEAK_MSG, step := 0#u8, hi, lo := e }
    (by simp [hash.TWEAK_MSG])
  obtain ⟨h1, b1, hu1, habs1, -⟩ := H.update h _ message habs
  obtain ⟨h2, b2, hu2, habs2, -⟩ := H.update h1 _ randomizer.to_slice habs1
  obtain ⟨d, hf, hd⟩ := H.finalize h2 _ habs2
  obtain ⟨r, hr, hrv⟩ := truncate_eq d
  refine ⟨r, ?_, ?_⟩
  · simp [wots.message_digest, hhi, htw, hh, hu1, core.array.Array.as_slice,
      rust_primitives.slice.array_as_slice, hu2, hf, hr]
  · rw [toDigest_th pp _ (bytes message.val ++ bytes randomizer.val) d r
      (by simpa [Array.to_slice, List.append_assoc] using hd) hrv]
    simp only [Verification.messageDigest, Verification.tweakableHash, hashDomainFields,
      littleEndianBytes_toDigest]
    congr 2
    exact toFields_eq _ _ _ _ _ (by simp [hash.TWEAK_MSG]) rfl (by rw [hhiv, layerHi, hl]; rfl)
      (by rw [he])

/-- `wots_leaf_hash`: the statement's leaf of a key's chain ends. -/
theorem wots_leaf_hash_spec (H : HasherSpec π) (pp : Array Std.U8 16#usize) (layer : Std.Usize)
    (e : Std.U32) (ends : Array (Array Std.U8 16#usize) 58#usize) (l : Layer) (key : KeyIndex)
    (hl : layer.val = l.val) (he : e.val = key.val) :
    ∃ d, wots.wots_leaf_hash pp layer e ends = ok d ∧
      toDigest d = Id.run (Verification.leafHash (inId π) (toDigest pp) l key
        (fun i => toDigest ends.val[i.val]!)) := by
  have hl1 : layer.val ≤ 1 := by have := l.isLt; simp only [layerCount] at this; omega
  obtain ⟨hi, hhi, hhiv⟩ := layer_hi_eq layer 0#u32 hl1 (by decide)
  have htw := tweak_eq hash.TWEAK_LEAF hi e (by simp [hash.TWEAK_LEAF]) (by rw [hhiv]; simp; omega)
  obtain ⟨d, hd, hdv⟩ := th_digests_spec H pp { t := hash.TWEAK_LEAF, step := 0#u8, hi, lo := e }
    ends.to_slice (by simp [hash.TWEAK_LEAF]) (by simp [Slice.length]; scalar_tac)
  refine ⟨d, ?_, ?_⟩
  · simp [wots.wots_leaf_hash, wots.leaf_tweak, hhi, htw, core.array.Array.as_slice,
      rust_primitives.slice.array_as_slice, hd]
  · have hof : List.ofFn (fun i : ChainIndex => toDigest ends.val[i.val]!) =
        ends.val.map toDigest := by
      have hlen : ends.val.length = 58 := by simp
      apply List.ext_getElem
      · rw [List.length_ofFn, List.length_map, hlen]; rfl
      · intro n h1 h2
        rw [List.getElem_ofFn, List.getElem_map, getElem!_pos ends.val n (by simpa using h2)]
    have hpay : bytes ((ends.to_slice.val.map Array.val).flatten) = digestsPayload
        (fun i : ChainIndex => toDigest ends.val[i.val]!) := by
      have hs : ends.to_slice.val = ends.val := by simp [Array.to_slice]
      rw [bytes_flatten, digestsPayload, hof, hs]
      exact (flatMap_map' toDigest (littleEndianBytes 16) ends.val).symm
    rw [hdv, hpay]
    simp only [Verification.leafHash, Verification.tweakableHash, hashDomainFields]
    congr 2
    exact toFields_eq _ _ _ _ _ (by simp [hash.TWEAK_LEAF]) rfl (by rw [hhiv, layerHi, hl]; rfl)
      (by rw [he])

/-- The statement's `otsLeaf` where the digest is a codeword: the leaf of the chains' ends. -/
theorem otsLeaf_some (P : PublicParameter) (l : Layer) (key : KeyIndex) (m : HashInput)
    (r : Randomizer) (v : ChainIndex → Digest) (enc : Encoding)
    (h : Codeword.decode (Id.run (Verification.messageDigest (inId π) P l key m r)) = some enc) :
    Id.run (Verification.otsLeaf (inId π) P l key m r v) =
      some (Id.run (Verification.leafHash (inId π) P l key
        (fun i => Id.run (Verification.recoverChain (inId π) P l key i (enc i) (v i))))) := by
  simp only [Verification.otsLeaf, Id.run_bind]
  rw [h]
  simp only [Id.run_bind, Id.run_pure, sequenceFin_id]

/-- The statement's `otsLeaf` where the digest is not a codeword: nothing. -/
theorem otsLeaf_none (P : PublicParameter) (l : Layer) (key : KeyIndex) (m : HashInput)
    (r : Randomizer) (v : ChainIndex → Digest)
    (h : Codeword.decode (Id.run (Verification.messageDigest (inId π) P l key m r)) = none) :
    Id.run (Verification.otsLeaf (inId π) P l key m r v) = none := by
  simp only [Verification.otsLeaf, Id.run_bind]
  rw [h]
  rfl

/-- **`wots_leaf`** recovers the statement's one-time leaf, or like it finds no codeword. -/
theorem wots_leaf_spec (H : HasherSpec π) (pp : Array Std.U8 16#usize) (layer : Std.Usize)
    (e : Std.U32) (message : Slice Std.U8) (randomizer : Array Std.U8 16#usize)
    (values : Array (Array Std.U8 16#usize) 58#usize) (l : Layer) (key : KeyIndex)
    (hl : layer.val = l.val) (he : e.val = key.val) :
    ∃ o, wots.wots_leaf pp layer e message randomizer values = ok o ∧
      (ofOption o).map (fun p ↦ toDigest p.2) =
        Id.run (Verification.otsLeaf (inId π) (toDigest pp) l key (bytes message.val)
          (toDigest randomizer) (fun i ↦ toDigest values.val[i.val]!)) := by
  obtain ⟨dg, hdg, hdgv⟩ := message_digest_spec H pp layer e randomizer message l key hl he
  obtain ⟨o, ho, hov⟩ := codeword_eq dg
  rw [hdgv] at hov
  match o, ho, hov with
  | .None, ho, hov =>
    refine ⟨.None, ?_, ?_⟩
    · simp [wots.wots_leaf, hdg, ho, core.option.Option.Insts.CoreOpsTry_traitTry.branch,
        core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
        core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual,
        core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual]
    · have hnone : Codeword.decode (Id.run (Verification.messageDigest (inId π) (toDigest pp) l key
          (bytes message.val) (toDigest randomizer))) = none := by
        simpa [ofOption] using hov.symm
      rw [otsLeaf_none _ _ _ _ _ _ hnone]
      rfl
  | .Some x, ho, hov =>
    obtain ⟨enc, henc, hev⟩ : ∃ enc, Codeword.decode (Id.run (Verification.messageDigest (inId π)
        (toDigest pp) l key (bytes message.val) (toDigest randomizer))) = some enc ∧
        ∀ i : ChainIndex, (x.val[i.val]!).val = (enc i).val := by
      cases hd : Codeword.decode (Id.run (Verification.messageDigest (inId π)
          (toDigest pp) l key (bytes message.val) (toDigest randomizer))) with
      | none => rw [hd] at hov; simp [ofOption] at hov
      | some enc =>
        rw [hd] at hov
        simp only [ofOption, Option.map_some, Option.some.injEq] at hov
        exact ⟨enc, rfl, fun i => congrFun hov i⟩
    obtain ⟨ends, hends, hendsv⟩ := chain_ends_spec H pp layer e x values l key enc hl he hev
    obtain ⟨d, hd, hdv⟩ := wots_leaf_hash_spec H pp layer e ends l key hl he
    refine ⟨.Some (x, d), ?_, ?_⟩
    · simp [wots.wots_leaf, hdg, ho, core.option.Option.Insts.CoreOpsTry_traitTry.branch,
        core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, hends, hd]
    · rw [otsLeaf_some _ _ _ _ _ _ enc henc]
      simp only [ofOption, Option.map_some]
      refine congrArg some ?_
      rw [hdv]
      exact congrArg (fun f => Id.run (Verification.leafHash (inId π) (toDigest pp) l key f))
        (funext fun i => hendsv i.val i.isLt)

end

end LeanXmssProofs
