module

public import X86.Sphincs.Hash
public import X86.Sphincs.Input

/-!
# The chains of a one-time key

`chain` walks chain `r13` of the layer's key from its digit to the end and puts the end into the
leaf's input in the big buffer (`chain_ok`); the loop over the 64 chains puts every end there
(`chains_ok`). A step's address is `makeAddress layer tree WOTS_HASH leaf i t`, `t` the position
it leaves, as `chainWalk`'s.
-/

@[expose] public section

namespace X86.SphincsVerifier

open LeanVM.Protocol.KeccakHash HashSig HashSig.OverPermutation _root_.Sphincs Keccak

/-! ## The specification, in `Id` -/

/-- Chain `i`'s value `j` steps from position `x`, from `v`. -/
abbrev chainCur (seed : BitVec 128) (L : Layer) (tree : TreeIndex) (leaf : TreeLeafIndex)
    (i : ChainIndex) (x : Nat) (v : Digest) (j : Nat) : Digest :=
  Id.run (Verification.chainWalk (m := Id) LeanVM.Semantics.keccakF1600 seed L tree leaf i x j v)

theorem chainCur_succ (seed : BitVec 128) (L : Layer) (tree : TreeIndex) (leaf : TreeLeafIndex)
    (i : ChainIndex) {x j : Nat} (v : Digest) (h : x + j < 3) :
    chainCur seed L tree leaf i x v (j + 1) = Id.run (Verification.addressedHash (m := Id)
      LeanVM.Semantics.keccakF1600 seed (makeAddress L.val tree.val .wotsHash leaf.val i.val (x + j))
        (littleEndianBytes 16 (chainCur seed L tree leaf i x v j))) := by
  have e : chainCur seed L tree leaf i x v (j + 1) = if h' : x + j < chainLength - 1 then
      Id.run (Verification.tweakableHash (m := Id) LeanVM.Semantics.keccakF1600 seed
        (.chain L tree leaf i ⟨x + j, h'⟩) (littleEndianBytes 16 (chainCur seed L tree leaf i x v j)))
      else 0 := rfl
  rw [e, dite_yes (show x + j < chainLength - 1 from h)]
  rfl

/-! ## A chain's steps -/

variable {base : UInt64} {V : Nat → UInt64} {s : QState} {E : QState → Prop}

/-- The words a chain's steps write. -/
def StepWrites (k : Nat) : Prop :=
  k < 84 ∨ k = adrsRec + 7 ∨ (smallBuf + 2 ≤ k ∧ k < smallBuf + 8) ∨ k = val ∨ k = val + 1

theorem chainSteps_ok (hb : Fits base) (hI : Inv base V s) {pk : _root_.Sphincs.PublicKey}
    {m : Message} {sig : Signature} (hS : Static pk m sig V) {L : Layer} {tree : TreeIndex}
    {leaf : TreeLeafIndex} {i : ChainIndex} {x : Nat} {v : Digest} (hx : x ≤ 3)
    (hA0 : V adrsRec = L.val.toUInt64) (hA3 : V (adrsRec + 3) = tree.val.toUInt64)
    (hA4 : V (adrsRec + 4) = AddressType.wotsHash.word.toUInt64)
    (hA5 : V (adrsRec + 5) = leaf.val.toUInt64) (hA6 : V (adrsRec + 6) = i.val.toUInt64)
    (hv0 : V val = digestLo v) (hv1 : V (val + 1) = digestHi v)
    (hr14 : s.reg .r14 = x.toUInt64) :
    WP (.loop (.cmp .ltu .r14 (.imm 3)) (blk [
      I (.store (cw (adrsRec + 7)) .r14),
      mv2 val (smallBuf + 6),
      tweak smallBuf 64 val,
      I (.addi .r14 1)])) s
      (fun s' ↦ ∃ V', Inv base V' s' ∧ (∀ k, ¬StepWrites k → V' k = V k) ∧
        V' val = digestLo (chainCur pk.publicSeed L tree leaf i x v (3 - x)) ∧
        V' (val + 1) = digestHi (chainCur pk.publicSeed L tree leaf i x v (3 - x)) ∧
        RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r14] s s') E := by
  have hi := i.isLt
  have hL := L.isLt
  have htr := tree.isLt
  have hlf := leaf.isLt
  unfold chainCount at hi
  unfold layerCount at hL
  unfold indexBits at htr
  have hlf' : leaf.val < 2 ^ 32 := Nat.lt_of_lt_of_le hlf
    (Nat.pow_le_pow_right (by decide) (by unfold layerHeight topLayer; split <;> decide))
  have hctx : Context.ctxWords = 3200 := rfl
  have har : adrsRec = 1200 := rfl
  have hsb : smallBuf = 1280 := rfl
  have hval : val = 1210 := rfl
  have hsw : scratchWords = 84 := rfl
  refine WP.loop (fun s' ↦ ∃ j V', Inv base V' s' ∧ x + j ≤ 3 ∧
      (∀ k, ¬StepWrites k → V' k = V k) ∧
      V' val = digestLo (chainCur pk.publicSeed L tree leaf i x v j) ∧
      V' (val + 1) = digestHi (chainCur pk.publicSeed L tree leaf i x v j) ∧
      s'.reg .r14 = (x + j).toUInt64 ∧ RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r14] s s')
    (fun s' ↦ 3 - (s'.reg .r14).toNat)
    ⟨0, V, hI, by omega, fun _ _ ↦ rfl, hv0, hv1, by simpa using hr14, fun _ _ ↦ rfl⟩ ?_ ?_
  · rintro s1 ⟨j, V1, h1, hj, e1, v1, v1', r14, f1⟩ hcond
    rw [cond_ltu_imm (k := 3) (K := 3) r14 (imm_nat 3) (by omega) (by omega)] at hcond
    have hj3 : x + j < 3 := by simpa using hcond
    refine blk_store_cw' h1 (by omega) fun s2 h2 hs2 ↦ ?_
    rw [r14] at h2
    have r14' : s2.reg .r14 = (x + j).toUInt64 := by rw [hs2, r14]
    apply WP.blk_cons
    refine WP.mono (mv2_ok h2 (src := val) (dst := smallBuf + 6) (by omega) (by omega) (by omega))
      (fun s3 ⟨h3, f3⟩ ↦ ?_) (fun _ h ↦ h)
    rw [show smallBuf + 6 + 1 = smallBuf + 7 from rfl] at h3
    have hV3 : ∀ k, k ≠ adrsRec + 7 → k ≠ smallBuf + 6 → k ≠ smallBuf + 7 →
        Function.update (Function.update (Function.update V1 (adrsRec + 7) (x + j).toUInt64)
          (smallBuf + 6) (Function.update V1 (adrsRec + 7) (x + j).toUInt64 val))
          (smallBuf + 7) (Function.update V1 (adrsRec + 7) (x + j).toUInt64 (val + 1)) k = V1 k :=
      fun k h7 h6 h7' ↦ by
        rw [Function.update_of_ne h7', Function.update_of_ne h6, Function.update_of_ne h7]
    have hA : AdrsAt (Function.update (Function.update (Function.update V1 (adrsRec + 7)
        (x + j).toUInt64) (smallBuf + 6) (Function.update V1 (adrsRec + 7) (x + j).toUInt64 val))
        (smallBuf + 7) (Function.update V1 (adrsRec + 7) (x + j).toUInt64 (val + 1)))
        L.val tree.val .wotsHash leaf.val i.val (x + j) := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hV3 _ (by omega) (by omega) (by omega), e1 _ (by unfold StepWrites; omega), hA0]
      · rw [hV3 _ (by omega) (by omega) (by omega), e1 _ (by unfold StepWrites; omega), hS.zero1]
      · rw [hV3 _ (by omega) (by omega) (by omega), e1 _ (by unfold StepWrites; omega), hS.zero2]
      · rw [hV3 _ (by omega) (by omega) (by omega), e1 _ (by unfold StepWrites; omega), hA3]
      · rw [hV3 _ (by omega) (by omega) (by omega), e1 _ (by unfold StepWrites; omega), hA4]
      · rw [hV3 _ (by omega) (by omega) (by omega), e1 _ (by unfold StepWrites; omega), hA5]
      · rw [hV3 _ (by omega) (by omega) (by omega), e1 _ (by unfold StepWrites; omega), hA6]
      · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_self]
    have hth : th (tweakWords (Function.update (Function.update (Function.update V1 (adrsRec + 7)
        (x + j).toUInt64) (smallBuf + 6) (Function.update V1 (adrsRec + 7) (x + j).toUInt64 val))
        (smallBuf + 7) (Function.update V1 (adrsRec + 7) (x + j).toUInt64 (val + 1))) smallBuf 64)
        64 = chainCur pk.publicSeed L tree leaf i x v (j + 1) := by
      rw [chainCur_succ _ _ _ _ _ _ hj3, th_tweakWords hA (by omega) (by omega) (by omega)
        (by omega) (by omega)
        (by rw [hV3 _ (by omega) (by omega) (by omega), e1 _ (by unfold StepWrites; omega),
          hS.small0])
        (by rw [hV3 _ (by omega) (by omega) (by omega), e1 _ (by unfold StepWrites; omega),
          hS.small1]) ?_ (by omega)]
      apply payload_digest
      · rw [Function.update_of_ne (by omega), Function.update_self, Function.update_of_ne (by omega),
          v1]
      · rw [Function.update_self, Function.update_of_ne (by omega), v1']
    apply WP.blk_cons
    refine WP.mono (tweak_ok hb h3 (buf := smallBuf) (len := 64) (dst := val) (by omega) (by omega)
      (by omega) (by omega) (Or.inr (by omega)) (by omega) (by omega)
      (tweakWords_drop _ (by decide) (by decide))) (fun s4 ⟨V4, h4, e4, d4, d4', f4⟩ ↦ ?_)
      (fun _ h ↦ h)
    rw [hth] at d4 d4'
    have r14'' : s4.reg .r14 = (x + j).toUInt64 := by
      rw [f4 .r14 (by simp), f3 .r14 (by simp), r14']
    step
    rw [r14'', imm_nat, toUInt64_add]
    apply WP.blk_nil
    refine ⟨⟨j + 1, V4, h4.setReg (by decide) _, by omega, fun k hk ↦ ?_, d4, d4', by
      simp only [QState.setReg_reg, ite_true, Nat.add_assoc], ?_⟩, ?_⟩
    · unfold StepWrites at hk
      rw [e4 k (by omega) (by omega) (by omega) (by omega), hV3 k (by omega) (by omega) (by omega),
        e1 k (by unfold StepWrites; omega)]
    · intro r hr
      simp only [QState.setReg_reg]
      rw [ite_no (fun h ↦ hr (by simp [h])), f4 r (fun h ↦ hr (by simp_all)),
        f3 r (fun h ↦ hr (by simp_all)), hs2, f1 r hr]
    · simp only [QState.setReg_reg, ite_true, r14, toNat_toUInt64' (show x + j + 1 < 2 ^ 64 by omega),
        toNat_toUInt64' (show x + j < 2 ^ 64 by omega)]
      omega
  · rintro s1 ⟨j, V1, h1, hj, e1, v1, v1', r14, f1⟩ hcond
    rw [cond_ltu_imm (k := 3) (K := 3) r14 (imm_nat 3) (by omega) (by omega)] at hcond
    have hj3 : j = 3 - x := by simp at hcond; omega
    subst hj3
    exact ⟨V1, h1, e1, v1, v1', f1⟩

/-! ## One chain -/

theorem cw_eval_rax {s : QState} (h : s.reg .rdi = base) (v : UInt64) (k : Nat) :
    (cw k).eval (s.setReg .rax v) = base + (8 * k).toUInt64 := by
  rw [cw_eval, QState.setReg_reg, ite_no (by decide), h]

theorem layerHeight_le (L : Layer) : layerHeight L ≤ 10 := by unfold layerHeight; split <;> omega

/-- Word `k` of layer `L`'s signature. -/
theorem Static.layer {pk : _root_.Sphincs.PublicKey} {m : Message} {sig : Signature}
    (hS : Static pk m sig V) (L : Layer) {k : Nat} (hk : k < 129 + 2 * layerHeight L) :
    V (inp + (layerOff L.val + k)) = layerWord (sig.layers L) k := by
  have hL := L.isLt
  have := layerHeight_le L
  unfold layerCount at hL
  rw [hS.input _ (by unfold inputWords layerOff; omega), encode_layer pk m sig L.val L.isLt hk]

/-- The words chain `i` writes. -/
def ChainWrites (i k : Nat) : Prop :=
  StepWrites k ∨ k = adrsRec + 4 ∨ k = adrsRec + 6 ∨ k = bigBuf + 6 + 2 * i ∨ k = bigBuf + 7 + 2 * i

/-- Chain `i`'s end, from its value in the signature and its digit `x`. -/
abbrev chainEnd (seed : BitVec 128) (L : Layer) (tree : TreeIndex) (leaf : TreeLeafIndex)
    (i : ChainIndex) (x : Nat) (v : Digest) : Digest :=
  chainCur seed L tree leaf i x v (3 - x)

theorem chain_ok (hb : Fits base) (hI : Inv base V s) {pk : _root_.Sphincs.PublicKey}
    {m : Message} {sig : Signature} (hS : Static pk m sig V) {L : Layer} {tree : TreeIndex}
    {leaf : TreeLeafIndex} {i : ChainIndex} {x : Nat} (hx : x < 4)
    (hA0 : V adrsRec = L.val.toUInt64) (hA3 : V (adrsRec + 3) = tree.val.toUInt64)
    (hA5 : V (adrsRec + 5) = leaf.val.toUInt64) (hd : V (digits + i.val) = x.toUInt64)
    (hr13 : s.reg .r13 = i.val.toUInt64) (hr11 : s.reg .r11 = (145 * L.val).toUInt64) :
    WP chain s (fun s' ↦ ∃ V', Inv base V' s' ∧ (∀ k, ¬ChainWrites i.val k → V' k = V k) ∧
      V' (bigBuf + 6 + 2 * i.val) =
        digestLo (chainEnd pk.publicSeed L tree leaf i x ((sig.layers L).chainValues i)) ∧
      V' (bigBuf + 7 + 2 * i.val) =
        digestHi (chainEnd pk.publicSeed L tree leaf i x ((sig.layers L).chainValues i)) ∧
      RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r14] s s') E := by
  have hi := i.isLt
  have hL := L.isLt
  unfold chainCount at hi
  unfold layerCount at hL
  have hctx : Context.ctxWords = 3200 := rfl
  have har : adrsRec = 1200 := rfl
  have hsb : smallBuf = 1280 := rfl
  have hbb : bigBuf = 1296 := rfl
  have hval : val = 1210 := rfl
  have hinp : inp = 128 := rfl
  have hdg : digits = 1216 := rfl
  have hsw : scratchWords = 84 := rfl
  unfold chain setField
  rw [show inp + 539 = 667 from rfl, show inp + 540 = 668 from rfl]
  refine blk_storei_cw' hI (by omega) fun s1 h1 hs1 ↦ ?_
  have r13 : s1.reg .r13 = i.val.toUInt64 := by rw [hs1, hr13]
  refine blk_store_cw' h1 (by omega) fun s2 h2 hs2 ↦ ?_
  rw [r13] at h2
  have r13' : s2.reg .r13 = i.val.toUInt64 := by rw [hs2, r13]
  have r11' : s2.reg .r11 = (145 * L.val).toUInt64 := by rw [hs2, hs1, hr11]
  step; step; step
  rw [r13', toUInt64_shl (show 1 < 64 by omega) (show i.val * 2 ^ 1 < 2 ^ 64 by omega), r11',
    toUInt64_add]
  have hin : ∀ k < 2, V (i.val * 2 ^ 1 + 145 * L.val + 667 + k) =
      digestWord ((sig.layers L).chainValues i) k := by
    intro k hk
    rw [show i.val * 2 ^ 1 + 145 * L.val + 667 + k =
      inp + (layerOff L.val + (1 + 2 * i.val + k)) by unfold layerOff; omega,
      hS.layer L (by have := layerHeight_le L; omega), layerWord_chain _ _ hk]
  obtain ⟨V2, hV2⟩ : ∃ V2, V2 = Function.update (Function.update V (adrsRec + 4) (Int64.toUInt64 0))
      (adrsRec + 6) i.val.toUInt64 := ⟨_, rfl⟩
  rw [← hV2] at h2
  have hV2k : ∀ k, k ≠ adrsRec + 4 → k ≠ adrsRec + 6 → V2 k = V k := fun k h4 h6 ↦ by
    rw [hV2, Function.update_of_ne h6, Function.update_of_ne h4]
  apply WP.blk_cons
  refine WP.mono (mv_ok (j := i.val * 2 ^ 1 + 145 * L.val + 667) (k := val)
    (h2.frame (s' := s2.setReg .rcx (i.val * 2 ^ 1 + 145 * L.val).toUInt64) rfl (by simp))
    (by rw [cwi_eval (n := i.val * 2 ^ 1 + 145 * L.val) _ (by simp), QState.setReg_reg,
      ite_no (by decide), h2.rdi]) (by omega)
    (by rw [cw_eval]; simp [h2.rdi]) (by omega)) (fun s3 ⟨h3, f3⟩ ↦ ?_) (fun _ h ↦ h)
  have r3 : s3.reg .rcx = (i.val * 2 ^ 1 + 145 * L.val).toUInt64 := by rw [f3 .rcx (by simp)]; simp
  apply WP.blk_cons
  refine WP.mono (mv_ok (j := i.val * 2 ^ 1 + 145 * L.val + 668) (k := val + 1) h3
    (by rw [cwi_eval _ r3, h3.rdi]) (by omega) (by rw [cw_eval_rax h3.rdi]) (by omega))
    (fun s4 ⟨h4, f4⟩ ↦ ?_) (fun _ h ↦ h)
  obtain ⟨V4, hV4⟩ : ∃ V4, V4 = Function.update (Function.update V2 val
      (V2 (i.val * 2 ^ 1 + 145 * L.val + 667))) (val + 1) (Function.update V2 val
      (V2 (i.val * 2 ^ 1 + 145 * L.val + 667)) (i.val * 2 ^ 1 + 145 * L.val + 668)) :=
    ⟨_, rfl⟩
  rw [← hV4] at h4
  have hV4k : ∀ k, k ≠ adrsRec + 4 → k ≠ adrsRec + 6 → k ≠ val → k ≠ val + 1 → V4 k = V k :=
    fun k h4 h6 h0 h1 ↦ by
      rw [hV4, Function.update_of_ne h1, Function.update_of_ne h0, hV2k k h4 h6]
  have hv0 : V4 val = digestLo ((sig.layers L).chainValues i) := by
    rw [hV4, Function.update_of_ne (by omega), Function.update_self, hV2k _ (by omega) (by omega)]
    exact (hin 0 (by omega)).trans (digestWord_zero _)
  have hv1 : V4 (val + 1) = digestHi ((sig.layers L).chainValues i) := by
    rw [hV4, Function.update_self, Function.update_of_ne (by omega), hV2k _ (by omega) (by omega),
      show i.val * 2 ^ 1 + 145 * L.val + 668 = i.val * 2 ^ 1 + 145 * L.val + 667 + 1 by omega]
    exact (hin 1 (by omega)).trans (digestWord_one _)
  have hS4 : Static pk m sig V4 := hS.frame fun k hk ↦ hV4k k
    (by unfold Kept at hk; unfold mdBuf at hk; omega) (by unfold Kept at hk; unfold mdBuf at hk; omega)
    (by unfold Kept at hk; unfold mdBuf at hk; omega) (by unfold Kept at hk; unfold mdBuf at hk; omega)
  have r13'' : s4.reg .r13 = i.val.toUInt64 := by
    rw [f4 .r13 (by simp), f3 .r13 (by simp)]; simp [r13']
  refine blk_load_cwi h4 r13'' (by omega) ?_
  rw [hV4k _ (by omega) (by omega) (by omega) (by omega), Nat.add_comm i.val digits, hd]
  apply WP.blk_cons
  refine WP.mono (chainSteps_ok (L := L) (tree := tree) (leaf := leaf) (i := i) (x := x) hb
    (h4.setReg (by decide) _) hS4 (by omega)
    (by rw [hV4k _ (by omega) (by omega) (by omega) (by omega), hA0])
    (by rw [hV4k _ (by omega) (by omega) (by omega) (by omega), hA3])
    (by rw [hV4, Function.update_of_ne (by omega), Function.update_of_ne (by omega), hV2,
          Function.update_of_ne (by omega), Function.update_self, imm_nat]; rfl)
    (by rw [hV4k _ (by omega) (by omega) (by omega) (by omega), hA5])
    (by rw [hV4, Function.update_of_ne (by omega), Function.update_of_ne (by omega), hV2,
          Function.update_self])
    hv0 hv1 (by simp)) (fun s5 ⟨V5, h5, e5, d5, d5', f5⟩ ↦ ?_) (fun _ h ↦ h)
  have r13_5 : s5.reg .r13 = i.val.toUInt64 := by
    rw [f5 .r13 (by simp)]; simp [r13'']
  step; step
  rw [r13_5, toUInt64_shl (show 1 < 64 by omega) (show i.val * 2 ^ 1 < 2 ^ 64 by omega)]
  apply WP.blk_cons
  refine WP.mono (mv_ok (j := val) (k := i.val * 2 ^ 1 + (bigBuf + 6))
    (h5.frame (s' := s5.setReg .rcx (i.val * 2 ^ 1).toUInt64) rfl (by simp))
    (by rw [cw_eval]; simp [h5.rdi]) (by omega)
    (by rw [cwi_eval (n := i.val * 2 ^ 1) _ (by simp)]; simp [h5.rdi])
    (by omega)) (fun s6 ⟨h6, f6⟩ ↦ ?_) (fun _ h ↦ h)
  have r6 : s6.reg .rcx = (i.val * 2 ^ 1).toUInt64 := by rw [f6 .rcx (by simp)]; simp
  refine WP.mono (mv_ok (j := val + 1) (k := i.val * 2 ^ 1 + (bigBuf + 7)) h6
    (by rw [cw_eval, h6.rdi]) (by omega)
    (by rw [cwi_eval (n := i.val * 2 ^ 1) _ (by simp [r6])]; simp [h6.rdi])
    (by omega)) (fun s7 ⟨h7, f7⟩ ↦ ⟨_, h7, fun k hk ↦ ?_, ?_, ?_, ?_⟩) (fun _ h ↦ h)
  · have hk' := hk
    unfold ChainWrites at hk'
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      e5 k (fun h ↦ hk (Or.inl h)), hV4k k (by omega) (by omega) (by unfold StepWrites at hk'; omega)
        (by unfold StepWrites at hk'; omega)]
  · rw [Function.update_of_ne (by omega), show bigBuf + 6 + 2 * i.val = i.val * 2 ^ 1 + (bigBuf + 6)
      by omega, Function.update_self, d5]
  · rw [show bigBuf + 7 + 2 * i.val = i.val * 2 ^ 1 + (bigBuf + 7) by omega, Function.update_self,
      Function.update_of_ne (by omega), d5']
  · intro r hr
    rw [f7 r (fun h ↦ hr (by simp_all)), f6 r (fun h ↦ hr (by simp_all))]
    simp only [QState.setReg_reg]
    rw [ite_no (fun h ↦ hr (by simp [h])), f5 r (fun h ↦ hr (by simp_all))]
    simp only [QState.setReg_reg]
    rw [ite_no (fun h ↦ hr (by simp [h])), f4 r (fun h ↦ hr (by simp_all)),
      f3 r (fun h ↦ hr (by simp_all))]
    simp only [QState.setReg_reg]
    rw [ite_no (fun h ↦ hr (by simp [h])), hs2, hs1]

/-! ## The 64 chains -/

/-- The words the chains write. -/
def ChainsWrites (k : Nat) : Prop :=
  StepWrites k ∨ k = adrsRec + 4 ∨ k = adrsRec + 6 ∨ (bigBuf + 6 ≤ k ∧ k < bigBuf + 134)

theorem ChainWrites.chains {c k : Nat} (hc : c < 64) (h : ChainWrites c k) : ChainsWrites k := by
  unfold ChainWrites at h
  unfold ChainsWrites
  rcases h with h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · unfold bigBuf at *; omega
  · unfold bigBuf at *; omega

theorem chains_ok (hb : Fits base) (hI : Inv base V s) {pk : _root_.Sphincs.PublicKey}
    {m : Message} {sig : Signature} (hS : Static pk m sig V) {L : Layer} {tree : TreeIndex}
    {leaf : TreeLeafIndex} {dg : ChainIndex → Nat} (hdg : ∀ i, dg i < 4)
    (hA0 : V adrsRec = L.val.toUInt64) (hA3 : V (adrsRec + 3) = tree.val.toUInt64)
    (hA5 : V (adrsRec + 5) = leaf.val.toUInt64)
    (hd : ∀ i : ChainIndex, V (digits + i.val) = (dg i).toUInt64)
    (hr13 : s.reg .r13 = (0 : Nat).toUInt64) (hr11 : s.reg .r11 = (145 * L.val).toUInt64) :
    WP (.loop (.cmp .ltu .r13 (.imm 64)) (blk [chain, I (.addi .r13 1)])) s
      (fun s' ↦ ∃ V', Inv base V' s' ∧ (∀ k, ¬ChainsWrites k → V' k = V k) ∧
        (∀ i : ChainIndex,
          V' (bigBuf + 6 + 2 * i.val) =
            digestLo (chainEnd pk.publicSeed L tree leaf i (dg i) ((sig.layers L).chainValues i)) ∧
          V' (bigBuf + 6 + 2 * i.val + 1) =
            digestHi (chainEnd pk.publicSeed L tree leaf i (dg i) ((sig.layers L).chainValues i))) ∧
        RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r13, .r14] s s') E := by
  have hctx : Context.ctxWords = 3200 := rfl
  have har : adrsRec = 1200 := rfl
  have hbb : bigBuf = 1296 := rfl
  have hdg' : digits = 1216 := rfl
  have hsb : smallBuf = 1280 := rfl
  have hval : val = 1210 := rfl
  refine WP.loop (fun s' ↦ ∃ c V', Inv base V' s' ∧ c ≤ 64 ∧
      (∀ k, ¬ChainsWrites k → V' k = V k) ∧
      (∀ i : ChainIndex, i.val < c →
        V' (bigBuf + 6 + 2 * i.val) =
          digestLo (chainEnd pk.publicSeed L tree leaf i (dg i) ((sig.layers L).chainValues i)) ∧
        V' (bigBuf + 6 + 2 * i.val + 1) =
          digestHi (chainEnd pk.publicSeed L tree leaf i (dg i) ((sig.layers L).chainValues i))) ∧
      s'.reg .r13 = c.toUInt64 ∧ RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r13, .r14] s s')
    (fun s' ↦ 64 - (s'.reg .r13).toNat)
    ⟨0, V, hI, by omega, fun _ _ ↦ rfl, fun i hi ↦ absurd hi (by omega), hr13, fun _ _ ↦ rfl⟩
    ?_ ?_
  · rintro s1 ⟨c, V1, h1, hc, e1, d1, r13, f1⟩ hcond
    rw [cond_ltu_imm (k := 64) (K := 64) r13 (imm_nat 64) (by omega) (by omega)] at hcond
    have hc64 : c < 64 := by simpa using hcond
    have hkc : ∀ k, Kept k → ¬ChainsWrites k := fun k hk ↦ by
      unfold ChainsWrites StepWrites; unfold Kept at hk; unfold mdBuf at hk; omega
    have hr11' : s1.reg .r11 = (145 * L.val).toUInt64 := by rw [f1 .r11 (by simp), hr11]
    apply WP.blk_cons
    refine WP.mono (chain_ok (pk := pk) (m := m) (sig := sig) (L := L) (tree := tree)
      (leaf := leaf) (i := ⟨c, hc64⟩) (x := dg ⟨c, hc64⟩) hb h1
      (hS.frame fun k hk ↦ e1 k (hkc k hk)) (hdg _)
      (by rw [e1 _ (by unfold ChainsWrites StepWrites; omega), hA0])
      (by rw [e1 _ (by unfold ChainsWrites StepWrites; omega), hA3])
      (by rw [e1 _ (by unfold ChainsWrites StepWrites; omega), hA5])
      (by show V1 (digits + c) = _
          rw [e1 _ (by unfold ChainsWrites StepWrites; omega)]; exact hd ⟨c, hc64⟩)
      r13 hr11') (fun s2 ⟨V2, h2, e2, d2, d2', f2⟩ ↦ ?_) (fun _ h ↦ h)
    dsimp only at e2 d2 d2'
    step
    rw [f2 .r13 (by simp), r13, imm_nat, toUInt64_add]
    apply WP.blk_nil
    refine ⟨⟨c + 1, V2, h2.setReg (by decide) _, by omega, fun k hk ↦ ?_, fun i hi ↦ ?_, by simp,
      ?_⟩, ?_⟩
    · rw [e2 k (fun h ↦ hk (h.chains hc64)), e1 k hk]
    · rcases Nat.lt_or_ge i.val c with h' | h'
      · have := d1 i h'
        rw [e2 _ (by unfold ChainWrites StepWrites; omega),
          e2 _ (by unfold ChainWrites StepWrites; omega)]
        exact this
      · have hic : i = ⟨c, hc64⟩ := Fin.ext (by simp; omega)
        subst hic
        exact ⟨d2, by rw [show bigBuf + 6 + 2 * c + 1 = bigBuf + 7 + 2 * c by omega]; exact d2'⟩
    · intro r hr
      simp only [QState.setReg_reg]
      rw [ite_no (fun h ↦ hr (by simp [h])), f2 r (fun h ↦ hr (by simp_all)), f1 r hr]
    · simp only [QState.setReg_reg, ite_true,
        toNat_toUInt64' (show c + 1 < 2 ^ 64 by omega), toNat_toUInt64' (show c < 2 ^ 64 by omega)]
      omega
  · rintro s1 ⟨c, V1, h1, hc, e1, d1, r13, f1⟩ hcond
    rw [cond_ltu_imm (k := 64) (K := 64) r13 (imm_nat 64) (by omega) (by omega)] at hcond
    have hc64 : c = 64 := by simp at hcond; omega
    subst hc64
    exact ⟨V1, h1, e1, fun i ↦ d1 i i.isLt, f1⟩

end X86.SphincsVerifier
