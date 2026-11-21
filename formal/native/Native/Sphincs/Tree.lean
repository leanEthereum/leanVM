module

public import Native.Sphincs.Chain
public import Native.Sphincs.Path

/-!
# A layer's tree

`foldTree` folds the key's leaf value in `val` up its path in the layer's signature, `rbp` levels,
the node at height `z + 1` addressed `makeAddress layer tree TREE 0 (z + 1) (leaf >> (z + 1))`
(`foldTree_ok`): the root `treeFold` gives.
-/

@[expose] public section

namespace Native.SphincsVerifier

open LeanVM.Protocol.KeccakHash HashSig HashSig.OverPermutation _root_.Sphincs Keccak

/-! ## The specification, in `Id` -/

/-- The layer's tree's value after `z` levels from `v`. -/
abbrev treeCur (seed : BitVec 128) (L : Layer) (tree : TreeIndex) (leaf : TreeLeafIndex)
    (path : Nat → Digest) (z : Nat) (v : Digest) : Digest :=
  Id.run (Verification.treeFold (m := Id) LeanVM.Semantics.keccakF1600 seed L tree leaf path z v)

theorem treeCur_succ (seed : BitVec 128) (L : Layer) (tree : TreeIndex) (leaf : TreeLeafIndex)
    (path : Nat → Digest) (z : Nat) (v : Digest) :
    treeCur seed L tree leaf path (z + 1) v = Id.run (Verification.addressedHash (m := Id)
      LeanVM.Semantics.keccakF1600 seed (makeAddress L.val tree.val .tree 0 (z + 1)
        (leaf.val / 2 ^ (z + 1)))
      (if leaf.val.testBit z then nodePayload (path z) (treeCur seed L tree leaf path z v)
        else nodePayload (treeCur seed L tree leaf path z v) (path z))) := rfl

/-! ## The levels -/

variable {base : UInt64} {V : Nat → UInt64} {s : QState} {E : QState → Prop}

/-- The words the tree's levels write. -/
def NodeWrites (k : Nat) : Prop :=
  k < 84 ∨ k = adrsRec + 6 ∨ k = adrsRec + 7 ∨ (smallBuf + 2 ≤ k ∧ k < smallBuf + 10) ∨ k = val ∨
    k = val + 1

/-- Level `z`'s sibling in layer `L`'s signature. -/
theorem Static.path {pk : _root_.Sphincs.PublicKey} {m : Message} {sig : Signature}
    (hS : Static pk m sig V) (L : Layer) {z : Nat} (hz : z < layerHeight L) {k : Nat} (hk : k < 2) :
    V (z * 2 ^ 1 + 145 * L.val + 795 + k) =
      digestWord (Verification.layerPath sig L z) k := by
  rw [show z * 2 ^ 1 + 145 * L.val + 795 + k = inp + (layerOff L.val + (129 + 2 * z + k)) by
      unfold inp layerOff; omega, hS.layer L (by omega), layerWord_path _ ⟨z, hz⟩ hk]
  simp only [Verification.layerPath, dite_yes hz]

theorem foldLevels_ok (hb : Fits base) (hI : Inv base V s) {pk : _root_.Sphincs.PublicKey}
    {m : Message} {sig : Signature} (hS : Static pk m sig V) {L : Layer} {tree : TreeIndex}
    {leaf : TreeLeafIndex} {v : Digest}
    (hA0 : V adrsRec = L.val.toUInt64) (hA3 : V (adrsRec + 3) = tree.val.toUInt64)
    (hA4 : V (adrsRec + 4) = AddressType.tree.word.toUInt64)
    (hA5 : V (adrsRec + 5) = (0 : Nat).toUInt64)
    (hv0 : V val = digestLo v) (hv1 : V (val + 1) = digestHi v)
    (hr13 : s.reg .r13 = (0 : Nat).toUInt64) (hr14 : s.reg .r14 = leaf.val.toUInt64)
    (hrbp : s.reg .rbp = (layerHeight L).toUInt64) (hr11 : s.reg .r11 = (145 * L.val).toUInt64) :
    WP (.loop (.cmp .ltu .r13 (.reg .rbp)) (blk [
      I (.mov .rax .r13), I (.addi .rax 1), I (.store (cw (adrsRec + 6)) .rax),
      I (.mov .rax .r14), I (.shri .rax 1), I (.store (cw (adrsRec + 7)) .rax),
      I (.mov .rcx .r13), I (.shli .rcx 1), I (.add .rcx .r11),
      pathNode 795,
      tweak smallBuf 80 val,
      I (.shri .r14 1), I (.addi .r13 1)])) s
      (fun s' ↦ ∃ V', Inv base V' s' ∧ (∀ k, ¬NodeWrites k → V' k = V k) ∧
        V' val = digestLo (treeCur pk.publicSeed L tree leaf (Verification.layerPath sig L)
          (layerHeight L) v) ∧
        V' (val + 1) = digestHi (treeCur pk.publicSeed L tree leaf (Verification.layerPath sig L)
          (layerHeight L) v) ∧
        RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r13, .r14] s s') E := by
  have hL := L.isLt
  have htr := tree.isLt
  have hlf := leaf.isLt
  have hH := layerHeight_le L
  unfold layerCount at hL
  unfold indexBits at htr
  have hlf' : leaf.val < 2 ^ 10 := Nat.lt_of_lt_of_le hlf
    (Nat.pow_le_pow_right (by decide) (by unfold layerHeight topLayer; split <;> decide))
  have hctx : Context.ctxWords = 3200 := rfl
  have har : adrsRec = 1200 := rfl
  have hsb : smallBuf = 1280 := rfl
  have hval : val = 1210 := rfl
  have hsw : scratchWords = 84 := rfl
  have hmd : mdBuf = 1152 := rfl
  refine WP.loop (fun s' ↦ ∃ z V', Inv base V' s' ∧ z ≤ layerHeight L ∧
      (∀ k, ¬NodeWrites k → V' k = V k) ∧
      V' val = digestLo (treeCur pk.publicSeed L tree leaf (Verification.layerPath sig L) z v) ∧
      V' (val + 1) = digestHi (treeCur pk.publicSeed L tree leaf (Verification.layerPath sig L) z v) ∧
      s'.reg .r13 = z.toUInt64 ∧ s'.reg .r14 = (leaf.val / 2 ^ z).toUInt64 ∧
      RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r13, .r14] s s')
    (fun s' ↦ layerHeight L - (s'.reg .r13).toNat)
    ⟨0, V, hI, by omega, fun _ _ ↦ rfl, hv0, hv1, hr13, by simpa using hr14, fun _ _ ↦ rfl⟩ ?_ ?_
  · rintro s1 ⟨z, V1, h1, hz, e1, v1, v1', r13, r14, f1⟩ hcond
    have rbp1 : s1.reg .rbp = (layerHeight L).toUInt64 := by rw [f1 .rbp (by simp), hrbp]
    have r11 : s1.reg .r11 = (145 * L.val).toUInt64 := by rw [f1 .r11 (by simp), hr11]
    rw [cond_ltu_reg r13 rbp1 (by omega) (by omega)] at hcond
    have hzh : z < layerHeight L := by simpa using hcond
    have hlz : leaf.val / 2 ^ z < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
    step; step
    rw [r13, imm_nat, toUInt64_add]
    refine blk_store_cw' (h1.setReg (by decide) _) (by omega) fun s2 h2 hs2 ↦ ?_
    simp only [QState.setReg_reg, ite_true] at h2
    have r13' : s2.reg .r13 = z.toUInt64 := by rw [hs2]; simpa using r13
    have r14' : s2.reg .r14 = (leaf.val / 2 ^ z).toUInt64 := by rw [hs2]; simpa using r14
    have r11' : s2.reg .r11 = (145 * L.val).toUInt64 := by rw [hs2]; simpa using r11
    step; step
    rw [r14', toUInt64_shr (show 1 < 64 by omega) hlz]
    refine blk_store_cw' (h2.setReg (by decide) _) (by omega) fun s3 h3 hs3 ↦ ?_
    simp only [QState.setReg_reg, ite_true] at h3
    have r13'' : s3.reg .r13 = z.toUInt64 := by rw [hs3]; simpa using r13'
    have r14'' : s3.reg .r14 = (leaf.val / 2 ^ z).toUInt64 := by rw [hs3]; simpa using r14'
    have r11'' : s3.reg .r11 = (145 * L.val).toUInt64 := by rw [hs3]; simpa using r11'
    step; step; step
    rw [r13'', toUInt64_shl (show 1 < 64 by omega) (show z * 2 ^ 1 < 2 ^ 64 by omega), r11'',
      toUInt64_add]
    apply WP.blk_cons
    refine WP.mono (pathNode_ok (h3.frame (s' := s3.setReg .rcx (z * 2 ^ 1 + 145 * L.val).toUInt64)
      rfl (by simp)) (sib := 795)
      (n := z * 2 ^ 1 + 145 * L.val) (b := leaf.val / 2 ^ z)
      (cur := treeCur pk.publicSeed L tree leaf (Verification.layerPath sig L) z v)
      (other := Verification.layerPath sig L z) (by simp) (by simp [r14'']) hlz (by omega)
      ?hv0 ?hv1 ?ho0 ?ho1) (fun s4 ⟨V4, h4, e4, p4, f4⟩ ↦ ?_) (fun _ h ↦ h)
    case hv0 => rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), v1]
    case hv1 => rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), v1']
    case ho0 =>
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        e1 _ (by unfold NodeWrites; omega), ← Nat.add_zero (z * 2 ^ 1 + 145 * L.val + 795)]
      exact (hS.path L hzh (by omega)).trans (digestWord_zero _)
    case ho1 =>
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        e1 _ (by unfold NodeWrites; omega), ← Nat.add_assoc]
      exact (hS.path L hzh (by omega)).trans (digestWord_one _)
    have hV4 : ∀ k, k < smallBuf + 6 → ¬NodeWrites k → V4 k = V k := fun k hk hw ↦ by
      rw [e4 k (by omega), Function.update_of_ne (by unfold NodeWrites at hw; omega),
        Function.update_of_ne (by unfold NodeWrites at hw; omega), e1 k hw]
    have hA : AdrsAt V4 L.val tree.val .tree 0 (z + 1) (leaf.val / 2 ^ z / 2 ^ 1) := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hV4 _ (by omega) (by unfold NodeWrites; omega), hA0]
      · rw [hV4 _ (by omega) (by unfold NodeWrites; omega), hS.zero1]
      · rw [hV4 _ (by omega) (by unfold NodeWrites; omega), hS.zero2]
      · rw [hV4 _ (by omega) (by unfold NodeWrites; omega), hA3]
      · rw [hV4 _ (by omega) (by unfold NodeWrites; omega), hA4]
      · rw [hV4 _ (by omega) (by unfold NodeWrites; omega), hA5]
      · rw [e4 _ (by omega), Function.update_of_ne (by omega), Function.update_self]
      · rw [e4 _ (by omega), Function.update_self]
    have hth : th (tweakWords V4 smallBuf 80) 80 =
        treeCur pk.publicSeed L tree leaf (Verification.layerPath sig L) (z + 1) v := by
      rw [th_tweakWords hA (by omega) (by omega) (by omega) (by omega)
        (by have : leaf.val / 2 ^ z / 2 ^ 1 ≤ leaf.val := Nat.le_trans (Nat.div_le_self _ _)
              (Nat.div_le_self _ _)
            omega)
        (by rw [hV4 _ (by omega) (by unfold NodeWrites; omega), hS.small0])
        (by rw [hV4 _ (by omega) (by unfold NodeWrites; omega), hS.small1]) p4 (by omega),
        treeCur_succ, Nat.testBit_div_two_pow, Nat.zero_add, Nat.div_div_eq_div_mul, ← Nat.pow_add]
    apply WP.blk_cons
    refine WP.mono (tweak_ok hb h4 (buf := smallBuf) (len := 80) (dst := val) (by omega) (by omega)
      (by omega) (by omega) (Or.inr (by omega)) (by omega) (by omega)
      (tweakWords_drop _ (by decide) (by decide))) (fun s5 ⟨V5, h5, e5, d5, d5', f5⟩ ↦ ?_)
      (fun _ h ↦ h)
    rw [hth] at d5 d5'
    have hreg : ∀ r, r ∉ [Reg64.rax, .rbx, .rcx, .rdx, .rsi, .r8] → s5.reg r = s3.reg r := by
      intro r hr
      rw [f5 r hr, f4 r (fun h ↦ hr (by simp_all))]
      simp only [QState.setReg_reg]
      rw [ite_no (fun h ↦ hr (by simp [h]))]
    step
    rw [hreg .r14 (by simp), r14'', toUInt64_shr (show 1 < 64 by omega) hlz]
    step
    rw [hreg .r13 (by simp), r13'', imm_nat, toUInt64_add]
    apply WP.blk_nil
    refine ⟨⟨z + 1, V5, h5.setReg (by decide) _ |>.setReg (by decide) _, by omega, fun k hk ↦ ?_,
      d5, d5', by simp, ?_, ?_⟩, ?_⟩
    · rw [e5 k (by unfold NodeWrites at hk; omega) (by unfold NodeWrites at hk; omega)
        (by unfold NodeWrites at hk; omega) (by unfold NodeWrites at hk; omega)]
      rw [e4 k (by unfold NodeWrites at hk; omega),
        Function.update_of_ne (by unfold NodeWrites at hk; omega),
        Function.update_of_ne (by unfold NodeWrites at hk; omega), e1 k hk]
    · simp only [QState.setReg_reg, reduceCtorEq, ite_false, ite_true]
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
    · intro r hr
      simp only [QState.setReg_reg]
      rw [ite_no (fun h ↦ hr (by simp [h])), ite_no (fun h ↦ hr (by simp [h])),
        hreg r (fun h ↦ hr (by simp_all)), hs3]
      simp only [QState.setReg_reg]
      rw [ite_no (fun h ↦ hr (by simp [h])), hs2]
      simp only [QState.setReg_reg]
      rw [ite_no (fun h ↦ hr (by simp [h])), f1 r hr]
    · simp only [QState.setReg_reg, ite_true, toNat_toUInt64' (show z + 1 < 2 ^ 64 by omega),
        toNat_toUInt64' (show z < 2 ^ 64 by omega)]
      omega
  · rintro s1 ⟨z, V1, h1, hz, e1, v1, v1', r13, r14, f1⟩ hcond
    have rbp1 : s1.reg .rbp = (layerHeight L).toUInt64 := by rw [f1 .rbp (by simp), hrbp]
    rw [cond_ltu_reg r13 rbp1 (by omega) (by omega)] at hcond
    have hzh : z = layerHeight L := by simp at hcond; omega
    subst hzh
    exact ⟨V1, h1, e1, v1, v1', f1⟩

/-! ## The tree -/

/-- The words `foldTree` writes. -/
def FoldWrites (k : Nat) : Prop := NodeWrites k ∨ k = adrsRec + 4 ∨ k = adrsRec + 5

theorem foldTree_ok (hb : Fits base) (hI : Inv base V s) {pk : _root_.Sphincs.PublicKey}
    {m : Message} {sig : Signature} (hS : Static pk m sig V) {L : Layer} {tree : TreeIndex}
    {leaf : TreeLeafIndex} {v : Digest}
    (hA0 : V adrsRec = L.val.toUInt64) (hA3 : V (adrsRec + 3) = tree.val.toUInt64)
    (hv0 : V val = digestLo v) (hv1 : V (val + 1) = digestHi v)
    (hr10 : s.reg .r10 = leaf.val.toUInt64)
    (hrbp : s.reg .rbp = (layerHeight L).toUInt64) (hr11 : s.reg .r11 = (145 * L.val).toUInt64) :
    WP foldTree s (fun s' ↦ ∃ V', Inv base V' s' ∧ (∀ k, ¬FoldWrites k → V' k = V k) ∧
        V' val = digestLo (treeCur pk.publicSeed L tree leaf (Verification.layerPath sig L)
          (layerHeight L) v) ∧
        V' (val + 1) = digestHi (treeCur pk.publicSeed L tree leaf (Verification.layerPath sig L)
          (layerHeight L) v) ∧
        RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r13, .r14] s s') E := by
  have hctx : Context.ctxWords = 3200 := rfl
  have har : adrsRec = 1200 := rfl
  have hsb : smallBuf = 1280 := rfl
  have hval : val = 1210 := rfl
  have hbb : bigBuf = 1296 := rfl
  unfold foldTree setField
  rw [show inp + 667 = 795 from rfl]
  refine blk_storei_cw' hI (by omega) fun s1 h1 hs1 ↦ ?_
  refine blk_storei_cw' h1 (by omega) fun s2 h2 hs2 ↦ ?_
  step; step
  have hV2 : ∀ k, k ≠ adrsRec + 4 → k ≠ adrsRec + 5 →
      Function.update (Function.update V (adrsRec + 4) (Int64.toUInt64 2)) (adrsRec + 5)
        (Int64.toUInt64 0) k = V k := fun k h4 h5 ↦ by
    rw [Function.update_of_ne h5, Function.update_of_ne h4]
  have hS2 := hS.frame fun k hk ↦ hV2 k (by unfold Kept at hk; unfold mdBuf at hk; omega)
    (by unfold Kept at hk; unfold mdBuf at hk; omega)
  apply WP.blk_cons
  refine WP.mono (foldLevels_ok (L := L) (tree := tree) (leaf := leaf) (v := v) hb
    ((h2.setReg (by decide) _).setReg (by decide) _) hS2
    (by rw [hV2 _ (by omega) (by omega), hA0]) (by rw [hV2 _ (by omega) (by omega), hA3])
    (by rw [Function.update_of_ne (by omega), Function.update_self, imm_nat]; rfl)
    (by rw [Function.update_self, imm_nat])
    (by rw [hV2 _ (by omega) (by omega), hv0]) (by rw [hV2 _ (by omega) (by omega), hv1])
    (by simp only [QState.setReg_reg, ite_true]; rfl) (by simp [hs2, hs1, hr10])
    (by simp [hs2, hs1, hrbp]) (by simp [hs2, hs1, hr11]))
    (fun s3 ⟨V3, h3, e3, d3, d3', f3⟩ ↦ WP.blk_nil ⟨V3, h3, fun k hk ↦ ?_, d3, d3', ?_⟩)
    (fun _ h ↦ h)
  · unfold FoldWrites at hk
    rw [e3 k (fun h ↦ hk (Or.inl h)), hV2 k (by omega) (by omega)]
  · intro r hr
    rw [f3 r hr]
    simp only [QState.setReg_reg]
    rw [ite_no (fun h ↦ hr (by simp [h])), ite_no (fun h ↦ hr (by simp [h])), hs2, hs1]

end Native.SphincsVerifier
