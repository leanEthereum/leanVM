module

public import X86.Sphincs.Encode

/-!
# One layer

`layerRest` walks the chains from the codeword's digits, hashes their ends into the key's leaf,
folds the leaf up the tree into `msg` and moves the registers to the next layer
(`layerRest_ok`). `layer` is the key's header, the encoding, the digits, then `layerRest` when the
digits sum to `128` and `r12 := 4` when not (`layer_ok`): `msg` becomes `layerRoot`'s root, or
`r12 = 4` when it has none.
-/

@[expose] public section

namespace X86.SphincsVerifier

open LeanVM.Protocol.KeccakHash HashSig HashSig.OverPermutation _root_.Sphincs Keccak

variable {base : UInt64} {V : Nat → UInt64} {s : QState} {E : QState → Prop}

/-- The one-time leaf of the chains walked from the digits `dg`. -/
abbrev leafOf (seed : BitVec 128) (L : Layer) (tree : TreeIndex) (leaf : TreeLeafIndex)
    (dg : ChainIndex → Nat) (vals : ChainIndex → Digest) : Digest :=
  Id.run (Verification.addressedHash (m := Id) LeanVM.Semantics.keccakF1600 seed
    (makeAddress L.val tree.val .wotsPublicKey leaf.val 0 0)
    (digestsPayload fun i ↦ chainEnd seed L tree leaf i (dg i) (vals i)))

/-- `rbp := ` the layer's height. -/
theorem height_ok {L : Layer} (hr12 : s.reg .r12 = L.val.toUInt64) :
    WP (.ite (.cmp .eq .r12 (.imm 2)) (I (.movi .rbp 10)) (I (.movi .rbp 8))) s
      (fun s' ↦ s' = s.setReg .rbp (layerHeight L).toUInt64) E := by
  have hL := L.isLt
  unfold layerCount at hL
  apply WP.ite
  rw [cond_eq_imm hr12 (imm_nat 2) (by omega) (by omega)]
  by_cases h : L.val = 2
  · simp only [h, decide_true, ite_true]
    refine WP.ins' ?_
    simp only [QInstr.step]
    rw [show layerHeight L = 10 by simp [layerHeight, h], imm_nat]
  · simp only [h, decide_false, Bool.false_eq_true, ite_false]
    refine WP.ins' ?_
    simp only [QInstr.step]
    rw [show layerHeight L = 8 by simp [layerHeight, h], imm_nat]

theorem layerRest_ok (hb : Fits base) (hI : Inv base V s) {pk : _root_.Sphincs.PublicKey}
    {m : Message} {sig : Signature} (hS : Static pk m sig V) {L : Layer} {tree : TreeIndex}
    {leaf : TreeLeafIndex} {dg : ChainIndex → Nat} (hdg : ∀ i, dg i < 4) {n : Nat}
    (hn : n < 2 ^ 64)
    (hA0 : V adrsRec = L.val.toUInt64) (hA3 : V (adrsRec + 3) = tree.val.toUInt64)
    (hA5 : V (adrsRec + 5) = leaf.val.toUInt64)
    (hd : ∀ i : ChainIndex, V (digits + i.val) = (dg i).toUInt64)
    (hr12 : s.reg .r12 = L.val.toUInt64) (hr11 : s.reg .r11 = (145 * L.val).toUInt64)
    (hr10 : s.reg .r10 = leaf.val.toUInt64) (hr15 : s.reg .r15 = n.toUInt64) :
    WP layerRest s (fun s' ↦ ∃ V', Inv base V' s' ∧ Frame V V' ∧
      V' msg = digestLo (treeCur pk.publicSeed L tree leaf (Verification.layerPath sig L)
        (layerHeight L) (leafOf pk.publicSeed L tree leaf dg (sig.layers L).chainValues)) ∧
      V' (msg + 1) = digestHi (treeCur pk.publicSeed L tree leaf (Verification.layerPath sig L)
        (layerHeight L) (leafOf pk.publicSeed L tree leaf dg (sig.layers L).chainValues)) ∧
      s'.reg .r12 = (L.val + 1).toUInt64 ∧ s'.reg .r11 = (145 * (L.val + 1)).toUInt64 ∧
      s'.reg .r15 = (n / 2 ^ 8).toUInt64 ∧
      RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r11, .r12, .r13, .r14, .r15, .rbp] s s') E := by
  have hL := L.isLt
  have htr := tree.isLt
  have hlf := leaf.isLt
  unfold layerCount at hL
  unfold indexBits at htr
  have hlf' : leaf.val < 2 ^ 32 := Nat.lt_of_lt_of_le hlf
    (Nat.pow_le_pow_right (by decide) (by unfold layerHeight topLayer; split <;> decide))
  have hctx : Context.ctxWords = 3200 := rfl
  have har : adrsRec = 1200 := rfl
  have hsb : smallBuf = 1280 := rfl
  have hbb : bigBuf = 1296 := rfl
  have hval : val = 1210 := rfl
  have hmsg : msg = 1208 := rfl
  have hsw : scratchWords = 84 := rfl
  have hmd : mdBuf = 1152 := rfl
  have hdgs : digits = 1216 := rfl
  unfold layerRest setField
  step
  apply WP.blk_cons
  refine WP.mono (chains_ok (L := L) (tree := tree) (leaf := leaf) hb (hI.setReg (by decide) _) hS
    hdg hA0 hA3 hA5 hd (by simp; rfl) (by simp [hr11])) (fun s1 ⟨V1, h1, e1, d1, f1⟩ ↦ ?_)
    (fun _ h ↦ h)
  have hf1 : ∀ r, r ∉ [Reg64.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r13, .r14] → s1.reg r = s.reg r :=
    fun r hr ↦ by
      rw [f1 r hr]; simp only [QState.setReg_reg]; rw [ite_no (fun h ↦ hr (by simp [h]))]
  refine blk_storei_cw' h1 (by omega) fun s2 h2 hs2 ↦ ?_
  refine blk_storei_cw' h2 (by omega) fun s3 h3 hs3 ↦ ?_
  refine blk_storei_cw' h3 (by omega) fun s4 h4 hs4 ↦ ?_
  obtain ⟨V4, hV4⟩ : ∃ V4, V4 = Function.update (Function.update (Function.update V1
      (adrsRec + 4) (Int64.toUInt64 1)) (adrsRec + 6) (Int64.toUInt64 0)) (adrsRec + 7)
      (Int64.toUInt64 0) := ⟨_, rfl⟩
  rw [← hV4] at h4
  have e4 : ∀ k, k ≠ adrsRec + 4 → k ≠ adrsRec + 6 → k ≠ adrsRec + 7 → V4 k = V1 k :=
    fun k h4 h6 h7 ↦ by
      rw [hV4, Function.update_of_ne h7, Function.update_of_ne h6, Function.update_of_ne h4]
  have hkc : ∀ k, Kept k → ¬ChainsWrites k := fun k hk ↦ by
    unfold ChainsWrites StepWrites; unfold Kept at hk; omega
  have hA : AdrsAt V4 L.val tree.val .wotsPublicKey leaf.val 0 0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [e4 _ (by omega) (by omega) (by omega), e1 _ (by unfold ChainsWrites StepWrites; omega),
        hA0]
    · rw [e4 _ (by omega) (by omega) (by omega), e1 _ (by unfold ChainsWrites StepWrites; omega),
        hS.zero1]
    · rw [e4 _ (by omega) (by omega) (by omega), e1 _ (by unfold ChainsWrites StepWrites; omega),
        hS.zero2]
    · rw [e4 _ (by omega) (by omega) (by omega), e1 _ (by unfold ChainsWrites StepWrites; omega),
        hA3]
    · rw [hV4, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_self, imm_nat]
      rfl
    · rw [e4 _ (by omega) (by omega) (by omega), e1 _ (by unfold ChainsWrites StepWrites; omega),
        hA5]
    · rw [hV4, Function.update_of_ne (by omega), Function.update_self, imm_nat]
    · rw [hV4, Function.update_self, imm_nat]
  have hpay : wordsBytes (words V4 (bigBuf + 6) (2 * chainCount)) =
      digestsPayload fun i ↦ chainEnd pk.publicSeed L tree leaf i (dg i)
        ((sig.layers L).chainValues i) := by
    apply words_digests
    intro i
    have := i.isLt
    unfold chainCount at this
    rw [e4 _ (by omega) (by omega) (by omega), e4 _ (by omega) (by omega) (by omega)]
    exact d1 i
  have hth : th (tweakWords V4 bigBuf 1072) 1072 =
      leafOf pk.publicSeed L tree leaf dg (sig.layers L).chainValues := by
    rw [th_tweakWords hA (by omega) (by omega) (by omega) (by omega) (by omega)
      (by rw [e4 _ (by omega) (by omega) (by omega), e1 _ (by unfold ChainsWrites StepWrites; omega),
        hS.big0])
      (by rw [e4 _ (by omega) (by omega) (by omega), e1 _ (by unfold ChainsWrites StepWrites; omega),
        hS.big1]) ?_ (by omega)]
    rw [show (1072 + 7) / 8 - 6 = 2 * chainCount from rfl, hpay, List.take_of_length_le]
    rw [← hpay, wordsBytes_length, words_length]
    unfold chainCount
    omega
  apply WP.blk_cons
  refine WP.mono (tweak_ok hb h4 (buf := bigBuf) (len := 1072) (dst := val) (by omega) (by omega)
    (by omega) (by omega) (Or.inr (by omega)) (by omega) (by omega)
    (tweakWords_drop _ (by decide) (by decide))) (fun s5 ⟨V5, h5, e5, d5, d5', f5⟩ ↦ ?_)
    (fun _ h ↦ h)
  rw [hth] at d5 d5'
  have hf5 : ∀ r, r ∉ [Reg64.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r13, .r14] → s5.reg r = s.reg r :=
    fun r hr ↦ by
      rw [f5 r (fun h ↦ hr (by simp_all)), hs4, hs3, hs2, hf1 r hr]
  have e5' : ∀ k, ¬ChainsWrites k → k ≠ adrsRec + 7 → k ≠ adrsRec + 6 → k ≠ adrsRec + 4 →
      ¬(bigBuf + 2 ≤ k ∧ k < bigBuf + 6) → V5 k = V k := fun k hk h7 h6 h4 hb' ↦ by
    unfold ChainsWrites StepWrites at hk
    rw [e5 k (by omega) (by omega) (by omega) (by omega), e4 k h4 h6 h7,
      e1 k (by unfold ChainsWrites StepWrites; omega)]
  have hS5 : Static pk m sig V5 := hS.frame fun k hk ↦ e5' k (hkc k hk)
    (by unfold Kept at hk; omega) (by unfold Kept at hk; omega) (by unfold Kept at hk; omega)
    (by unfold Kept at hk; omega)
  apply WP.blk_cons
  refine WP.mono (height_ok (L := L) (by rw [hf5 .r12 (by simp), hr12]))
    (fun s6 hs6 ↦ ?_) (fun _ h ↦ h)
  subst hs6
  apply WP.blk_cons
  refine WP.mono (foldTree_ok (L := L) (tree := tree) (leaf := leaf) (sig := sig) hb
    (h5.setReg (by decide) _) hS5
    (by rw [e5' _ (by unfold ChainsWrites StepWrites; omega) (by omega) (by omega) (by omega)
      (by omega), hA0])
    (by rw [e5' _ (by unfold ChainsWrites StepWrites; omega) (by omega) (by omega) (by omega)
      (by omega), hA3])
    d5 d5' (by simp [hf5 .r10 (by simp), hr10]) (by simp) (by simp [hf5 .r11 (by simp), hr11]))
    (fun s7 ⟨V7, h7, e7, d7, d7', f7⟩ ↦ ?_) (fun _ h ↦ h)
  apply WP.blk_cons
  refine WP.mono (mv2_ok h7 (src := val) (dst := msg) (by omega) (by omega) (by omega))
    (fun s8 ⟨h8, f8⟩ ↦ ?_) (fun _ h ↦ h)
  have hf8 : ∀ r, r ∉ [Reg64.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r13, .r14, .rbp] →
      s8.reg r = s.reg r := fun r hr ↦ by
    rw [f8 r (fun h ↦ hr (by simp_all)), f7 r (fun h ↦ hr (by simp_all))]
    simp only [QState.setReg_reg]
    rw [ite_no (fun h ↦ hr (by simp [h])), hf5 r (fun h ↦ hr (by simp_all))]
  step; step; step
  rw [hf8 .r15 (by simp), hr15, toUInt64_shr (by omega) hn, hf8 .r12 (by simp), hr12, imm_nat,
    toUInt64_add, hf8 .r11 (by simp), hr11, imm_nat, toUInt64_add,
    show 145 * L.val + 145 = 145 * (L.val + 1) by omega]
  apply WP.blk_nil
  refine ⟨_, ((h8.setReg (by decide) _).setReg (by decide) _).setReg (by decide) _,
    fun k hk ↦ ?_, ?_, ?_, by simp, by simp, by simp, fun r hr ↦ ?_⟩
  · have hk' := hk
    unfold Kept at hk'
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      e7 k (by unfold FoldWrites NodeWrites; omega),
      e5' k (hkc k hk) (by omega) (by omega) (by omega) (by omega)]
  · rw [Function.update_of_ne (by omega), Function.update_self, d7]
  · rw [Function.update_self, d7']
  · simp only [QState.setReg_reg]
    rw [ite_no (fun h ↦ hr (by simp [h])), ite_no (fun h ↦ hr (by simp [h])),
      ite_no (fun h ↦ hr (by simp [h])), hf8 r (fun h ↦ hr (by simp_all))]

/-! ## A layer -/

theorem sum_lt (D : Digest) : TargetSum.sum (TargetSum.base2bDigits D) < 2 ^ 64 := by
  rw [← sum_digitOf]
  have : ∑ j ∈ Finset.range 64, digitOf D j ≤ ∑ j ∈ Finset.range 64, 3 :=
    Finset.sum_le_sum fun j _ ↦ Nat.le_of_lt_succ (digitOf_lt D j)
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at this
  omega

/-- `layerRoot` by the encoding's digit sum. -/
theorem layerRoot_eq (seed : BitVec 128) (idx : Index) (sig : Signature) (L : Layer) (d : Digest) :
    layerRoot seed idx sig L d =
      if TargetSum.sum (TargetSum.base2bDigits (encDigest seed L (treeOfIndex L idx)
          (leafOfIndex L idx) d (sig.layers L).counter)) = 128 then
        some (treeCur seed L (treeOfIndex L idx) (leafOfIndex L idx) (Verification.layerPath sig L)
          (layerHeight L) (leafOf seed L (treeOfIndex L idx) (leafOfIndex L idx)
            (fun i ↦ (TargetSum.base2bDigits (encDigest seed L (treeOfIndex L idx)
              (leafOfIndex L idx) d (sig.layers L).counter) i).val) (sig.layers L).chainValues))
      else none := by
  rw [layerRoot, otsLeaf_id]
  split
  · rw [Option.map_some]
  · rfl

theorem layer_ok (hb : Fits base) (hI : Inv base V s) {pk : _root_.Sphincs.PublicKey}
    {m : Message} {sig : Signature} (hS : Static pk m sig V) {L : Layer} {idx : Index}
    {d : Digest} (hm0 : V msg = digestLo d) (hm1 : V (msg + 1) = digestHi d)
    (hr12 : s.reg .r12 = L.val.toUInt64) (hr11 : s.reg .r11 = (145 * L.val).toUInt64)
    (hr15 : s.reg .r15 = (idx.val / 2 ^ (8 * L.val)).toUInt64) :
    WP layer s (fun s' ↦ ∃ V', Inv base V' s' ∧ Frame V V' ∧
      (layerRoot pk.publicSeed idx sig L d = none → s'.reg .r12 = (4 : Nat).toUInt64) ∧
      (∀ r, layerRoot pk.publicSeed idx sig L d = some r → V' msg = digestLo r ∧
        V' (msg + 1) = digestHi r ∧ s'.reg .r12 = (L.val + 1).toUInt64 ∧
        s'.reg .r11 = (145 * (L.val + 1)).toUInt64 ∧
        s'.reg .r15 = (idx.val / 2 ^ (8 * (L.val + 1))).toUInt64) ∧
      RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15, .rbp]
        s s') E := by
  have hL := L.isLt
  have hidx := idx.isLt
  unfold layerCount at hL
  unfold indexBits at hidx
  have hctx : Context.ctxWords = 3200 := rfl
  have har : adrsRec = 1200 := rfl
  have hsb : smallBuf = 1280 := rfl
  have hmsg : msg = 1208 := rfl
  have hsw : scratchWords = 84 := rfl
  have hmd : mdBuf = 1152 := rfl
  have hbb : bigBuf = 1296 := rfl
  have hdgs : digits = 1216 := rfl
  have hn : idx.val / 2 ^ (8 * L.val) < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  unfold layer
  rw [show inp + 538 = 666 from rfl]
  refine wp_blk_take_drop 7 (WP.mono (header_ok hI hr12 hr15)
    (fun s1 ⟨V1, h1, e1, a0, a3, a4, a5, a6, a7, r10, r9, f1⟩ ↦ ?_) (fun _ h ↦ h))
  have F1 : Frame V V1 := fun k hk ↦ e1 k (by unfold Kept at hk; omega)
  have hA1 : AdrsAt V1 L.val (treeOfIndex L idx).val .wotsEncoding (leafOfIndex L idx).val 0 0 :=
    ⟨a0, by rw [e1 _ (by omega)]; exact hS.zero1, by rw [e1 _ (by omega)]; exact hS.zero2, a3, a4,
      a5, a6, a7⟩
  refine wp_blk_take_drop 6 (WP.mono (encode_ok (sig := sig) (d := d) hb h1 (hS.frame F1) hA1
    (by rw [e1 _ (by omega)]; exact hm0) (by rw [e1 _ (by omega)]; exact hm1)
    (by rw [f1 .r11 (by simp), hr11]))
    (fun s2 ⟨V2, h2, e2, w0, w1, f2⟩ ↦ ?_) (fun _ h ↦ h))
  refine wp_blk_take_drop 2 (WP.mono (digits_ok h2 w0 w1)
    (fun s3 ⟨V3, h3, e3, d3, r3, f3⟩ ↦ ?_) (fun _ h ↦ h))
  have F3 : Frame V V3 := fun k hk ↦ by
    have hk' := hk
    unfold Kept at hk'
    rw [e3 k (by omega), e2 k (by omega) (by omega), F1 k hk]
  have hreg : ∀ r, r ∉ [Reg64.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r9, .r10, .rbp] →
      s3.reg r = s.reg r := fun r hr ↦ by
    rw [f3 r (fun h ↦ hr (by simp_all)), f2 r (fun h ↦ hr (by simp_all)),
      f1 r (fun h ↦ hr (by simp_all))]
  have r10' : s3.reg .r10 = (leafOfIndex L idx).val.toUInt64 := by
    rw [f3 .r10 (by simp), f2 .r10 (by simp), r10]
  have hc := cond_ne_imm (s := s3) (k := 128) r3 (imm_nat 128) (sum_lt _) (by omega)
  apply WP.ite
  by_cases hsum : TargetSum.sum (TargetSum.base2bDigits (encDigest pk.publicSeed L
    (treeOfIndex L idx) (leafOfIndex L idx) d (sig.layers L).counter)) = 128
  · rw [hsum, decide_eq_false (by simp)] at hc
    rw [hc, ite_no Bool.false_ne_true]
    refine WP.mono (layerRest_ok (pk := pk) (m := m) (sig := sig) (L := L)
      (tree := treeOfIndex L idx) (leaf := leafOfIndex L idx)
      (dg := fun i ↦ (TargetSum.base2bDigits (encDigest pk.publicSeed L (treeOfIndex L idx)
        (leafOfIndex L idx) d (sig.layers L).counter) i).val) hb h3 (hS.frame F3)
      (fun i ↦ (TargetSum.base2bDigits _ i).isLt) hn
      (by rw [e3 _ (by omega), e2 _ (by omega) (by omega)]; exact a0)
      (by rw [e3 _ (by omega), e2 _ (by omega) (by omega)]; exact a3)
      (by rw [e3 _ (by omega), e2 _ (by omega) (by omega)]; exact a5) d3
      (by rw [hreg .r12 (by simp), hr12]) (by rw [hreg .r11 (by simp), hr11]) r10'
      (by rw [hreg .r15 (by simp), hr15]))
      (fun s4 ⟨V4, h4, F4, m0, m1, r12, r11, r15, f4⟩ ↦
        ⟨V4, h4, F3.trans F4, fun h ↦ ?_, fun r h ↦ ?_, ?_⟩) (fun _ h ↦ h)
    · rw [layerRoot_eq, ite_yes hsum] at h
      exact absurd h (by simp)
    · rw [layerRoot_eq, ite_yes hsum, Option.some.injEq] at h
      subst h
      refine ⟨m0, m1, r12, r11, ?_⟩
      rw [r15, Nat.div_div_eq_div_mul, ← Nat.pow_add, show 8 * L.val + 8 = 8 * (L.val + 1) by omega]
    · intro r hr
      rw [f4 r (fun h ↦ hr (by simp_all)), hreg r (fun h ↦ hr (by simp_all))]
  · rw [decide_eq_true hsum] at hc
    rw [hc, ite_yes rfl]
    refine WP.ins' ?_
    simp only [QInstr.step]
    refine ⟨V3, h3.setReg (by decide) _, F3, fun _ ↦ by simp only [QState.setReg_reg, ite_true]; rfl,
      fun r h ↦ ?_, fun r hr ↦ ?_⟩
    · rw [layerRoot_eq, ite_no hsum] at h
      exact absurd h (by simp)
    · simp only [QState.setReg_reg]
      rw [ite_no (fun h ↦ hr (by simp [h])), hreg r (fun h ↦ hr (by simp_all))]

end X86.SphincsVerifier
