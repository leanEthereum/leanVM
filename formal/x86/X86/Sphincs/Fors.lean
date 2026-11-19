module

public import X86.Sphincs.Path
public import X86.Sphincs.Input
public import X86.Sphincs.DigestSpec

/-!
# FORS

`fors` recovers FORS tree `κ`'s root for each `κ`, from its leaf at `forsLeaves + κ` and its
opening in the input, into the roots' input in the big buffer, then hashes the roots into `msg`
(`fors_ok`): the FORS public key `forsRecover` gives.
-/

@[expose] public section

namespace X86.SphincsVerifier

open LeanVM.Protocol.KeccakHash HashSig HashSig.OverPermutation _root_.Sphincs Keccak

/-! ## The specification, in `Id` -/

theorem foldPath_succ_id (node : Nat → Nat → HashInput → Id Digest) (leaf : Nat)
    (sib : Nat → Digest) (l : Nat) (v : Digest) :
    Id.run (foldPath node leaf sib (l + 1) v) =
      Id.run (node l (leaf / 2 ^ (l + 1)) (if leaf.testBit l then
        nodePayload (sib l) (Id.run (foldPath node leaf sib l v))
        else nodePayload (Id.run (foldPath node leaf sib l v)) (sib l))) := rfl

theorem treeOfIndex_zero (idx : Index) : (treeOfIndex 0 idx).val = idx.val / 256 := rfl

theorem leafOfIndex_zero (idx : Index) : (leafOfIndex 0 idx).val = idx.val % 256 := by
  simp [leafOfIndex, bitsBelowLayer, layerHeight]

/-- FORS tree `κ`'s path: node `z`'s children's hash. -/
abbrev forsNode (seed : BitVec 128) (idx : Index) (κ : ForsTreeIndex) :
    Nat → Nat → HashInput → Id Digest :=
  fun level node ↦ Verification.tweakableHash (m := Id) LeanVM.Semantics.keccakF1600 seed
    (.forsNode idx κ (level + 1) node)

/-- FORS tree `κ`'s path's siblings. -/
abbrev forsSib (o : ForsTreeOpening) : Nat → Digest :=
  fun level ↦ if h : level < forsTreeHeight then o.path ⟨level, h⟩ else 0

/-- FORS tree `κ`'s value after `z` levels. -/
abbrev forsCur (seed : BitVec 128) (idx : Index) (κ : ForsTreeIndex) (leaf : ForsLeafIndex)
    (o : ForsTreeOpening) (z : Nat) : Digest :=
  Id.run (foldPath (forsNode seed idx κ) leaf.val (forsSib o) z
    (Id.run (Verification.forsLeafHash (m := Id) LeanVM.Semantics.keccakF1600 seed idx κ leaf
      o.secret)))

theorem forsCur_succ (seed : BitVec 128) (idx : Index) (κ : ForsTreeIndex) (lf : ForsLeafIndex)
    (o : ForsTreeOpening) (z : Nat) :
    forsCur seed idx κ lf o (z + 1) = Id.run (forsNode seed idx κ z (lf.val / 2 ^ (z + 1))
      (if lf.val.testBit z then nodePayload (forsSib o z) (forsCur seed idx κ lf o z)
        else nodePayload (forsCur seed idx κ lf o z) (forsSib o z))) := rfl

theorem forsTreeRecover_id (seed : BitVec 128) (idx : Index) (κ : ForsTreeIndex)
    (leaf : ForsLeafIndex) (o : ForsTreeOpening) :
    Id.run (Verification.forsTreeRecover (m := Id) LeanVM.Semantics.keccakF1600 seed idx κ leaf o) =
      forsCur seed idx κ leaf o forsTreeHeight := rfl

theorem forsRecover_id (seed : BitVec 128) (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex)
    (op : ForsTreeIndex → ForsTreeOpening) :
    Id.run (Verification.forsRecover (m := Id) LeanVM.Semantics.keccakF1600 seed idx lv op) =
      Id.run (Verification.forsPublicKey (m := Id) LeanVM.Semantics.keccakF1600 seed idx
        fun κ ↦ forsCur seed idx κ (lv κ) (op κ) forsTreeHeight) := by
  simp only [Verification.forsRecover, Id.run_bind, sequenceFin_id]
  rfl

theorem forsTreeIndex_succ (κ : ForsTreeIndex) {z lf : Nat} (hz : z < 10) :
    forsTreeIndex κ (z + 1) (lf / 2 ^ (z + 1)) = lf / 2 ^ z / 2 ^ 1 + κ.val * 2 ^ (10 - z) / 2 ^ 1 := by
  unfold forsTreeIndex forsTreeHeight
  have h1 : lf / 2 ^ z / 2 ^ 1 = lf / 2 ^ (z + 1) := by rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  have h2 : κ.val * 2 ^ (10 - z) / 2 ^ 1 = κ.val * 2 ^ (10 - (z + 1)) := by
    rw [show 10 - z = (10 - (z + 1)) + 1 by omega, Nat.pow_succ, ← Nat.mul_assoc, Nat.pow_one,
      Nat.mul_div_cancel _ (by decide)]
  rw [h1, h2, Nat.add_comm]

theorem forsNode_eq (seed : BitVec 128) (idx : Index) (κ : ForsTreeIndex) {z lf : Nat}
    (hz : z < 10) (payload : HashInput) :
    Id.run (forsNode seed idx κ z (lf / 2 ^ (z + 1)) payload) =
      Id.run (Verification.addressedHash (m := Id) LeanVM.Semantics.keccakF1600 seed
        (makeAddress 0 (idx.val / 256) .forsTree (idx.val % 256) (z + 1)
          (lf / 2 ^ z / 2 ^ 1 + κ.val * 2 ^ (10 - z) / 2 ^ 1)) payload) := by
  show Id.run (Verification.addressedHash (m := Id) LeanVM.Semantics.keccakF1600 seed
    (hashDomainFields (.forsNode idx κ (z + 1) (lf / 2 ^ (z + 1)))) payload) = _
  rw [hashDomainFields, treeOfIndex_zero, leafOfIndex_zero, forsTreeIndex_succ κ hz]

/-! ## A FORS tree's path -/

variable {base : UInt64} {V : Nat → UInt64} {s : QState} {E : QState → Prop}

/-- The words a FORS tree's levels write. -/
def LevelWrites (k : Nat) : Prop :=
  k < 84 ∨ k = adrsRec + 6 ∨ k = adrsRec + 7 ∨ (smallBuf + 2 ≤ k ∧ k < smallBuf + 10) ∨ k = val ∨
    k = val + 1

/-- The FORS levels' loop's state after `z` levels. -/
def LevelInv (base : UInt64) (V₀ : Nat → UInt64) (s₀ : QState) (seed : BitVec 128) (idx : Index)
    (κ : ForsTreeIndex) (lf : ForsLeafIndex) (o : ForsTreeOpening) (s : QState) : Prop :=
  ∃ z V, Inv base V s ∧ z ≤ 10 ∧ (∀ k, ¬LevelWrites k → V k = V₀ k) ∧
    V val = digestLo (forsCur seed idx κ lf o z) ∧ V (val + 1) = digestHi (forsCur seed idx κ lf o z) ∧
    s.reg .r10 = z.toUInt64 ∧ s.reg .r14 = (lf.val / 2 ^ z).toUInt64 ∧
    s.reg .r9 = (κ.val * 2 ^ (10 - z)).toUInt64 ∧
    RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r9, .r10, .r14] s₀ s

theorem forsLevels_ok (hb : Fits base) (hI : Inv base V s) {pk : _root_.Sphincs.PublicKey}
    {m : Message} {sig : Signature} (hS : Static pk m sig V) {idx : Index} {κ : ForsTreeIndex}
    {lf : ForsLeafIndex}
    (hA0 : V adrsRec = (0 : Nat).toUInt64) (hA3 : V (adrsRec + 3) = (idx.val / 256).toUInt64)
    (hA4 : V (adrsRec + 4) = AddressType.forsTree.word.toUInt64)
    (hA5 : V (adrsRec + 5) = (idx.val % 256).toUInt64)
    (hv0 : V val = digestLo (forsCur pk.publicSeed idx κ lf (sig.forsOpening κ) 0))
    (hv1 : V (val + 1) = digestHi (forsCur pk.publicSeed idx κ lf (sig.forsOpening κ) 0))
    (hr10 : s.reg .r10 = (0 : Nat).toUInt64) (hr14 : s.reg .r14 = lf.val.toUInt64)
    (hr9 : s.reg .r9 = (κ.val * 2 ^ 10).toUInt64) (hr13 : s.reg .r13 = (22 * κ.val).toUInt64) :
    WP (.loop (.cmp .ltu .r10 (.imm 10)) (blk [
      I (.mov .rax .r10), I (.addi .rax 1), I (.store (cw (adrsRec + 6)) .rax),
      I (.shri .r9 1),
      I (.mov .rax .r14), I (.shri .rax 1), I (.add .rax .r9), I (.store (cw (adrsRec + 7)) .rax),
      I (.mov .rcx .r10), I (.shli .rcx 1), I (.add .rcx .r13),
      pathNode (inp + 12),
      tweak smallBuf 80 val,
      I (.shri .r14 1), I (.addi .r10 1)])) s
      (fun s' ↦ ∃ V', Inv base V' s' ∧ (∀ k, ¬LevelWrites k → V' k = V k) ∧
        V' val = digestLo (forsCur pk.publicSeed idx κ lf (sig.forsOpening κ) 10) ∧
        V' (val + 1) = digestHi (forsCur pk.publicSeed idx κ lf (sig.forsOpening κ) 10) ∧
        RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r9, .r10, .r14] s s') E := by
  have hκ := κ.isLt
  have hlf := lf.isLt
  have hidx := idx.isLt
  unfold forsTreeCount at hκ
  unfold forsTreeHeight at hlf
  unfold indexBits at hidx
  have hctx : Context.ctxWords = 3200 := rfl
  have har : adrsRec = 1200 := rfl
  have hsb : smallBuf = 1280 := rfl
  have hval : val = 1210 := rfl
  have hinp : inp = 128 := rfl
  have hsw : scratchWords = 84 := rfl
  have hmd : mdBuf = 1152 := rfl
  refine WP.loop (LevelInv base V s pk.publicSeed idx κ lf (sig.forsOpening κ))
    (fun s' ↦ 10 - (s'.reg .r10).toNat)
    ⟨0, V, hI, by omega, fun _ _ ↦ rfl, hv0, hv1, hr10, by simpa using hr14, by simpa using hr9,
      fun _ _ ↦ rfl⟩ ?_ ?_
  · rintro s1 ⟨z, V1, h1, hz, e1, v1, v1', r10, r14, r9, f1⟩ hcond
    rw [cond_ltu_imm (k := 10) (K := 10) r10 (imm_nat 10) (by omega) (by omega)] at hcond
    have hz10 : z < 10 := by simpa using hcond
    have hr13' : s1.reg .r13 = (22 * κ.val).toUInt64 := by rw [f1 .r13 (by simp), hr13]
    have hr12 : ∀ r, r ∉ [Reg64.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r9, .r10, .r14] →
        s1.reg r = s.reg r := f1
    have hk9 : κ.val * 2 ^ (10 - z) < 2 ^ 64 := by
      have : 2 ^ (10 - z) ≤ 2 ^ 10 := Nat.pow_le_pow_right (by omega) (by omega)
      have : κ.val * 2 ^ (10 - z) ≤ κ.val * 2 ^ 10 := Nat.mul_le_mul_left _ this
      omega
    have hlz : lf.val / 2 ^ z < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
    step; step
    rw [r10, imm_nat, toUInt64_add]
    refine blk_store_cw' (h1.setReg (by decide) _) (by omega) fun s2 h2 hs2 ↦ ?_
    simp only [QState.setReg_reg, ite_true] at h2
    have r9' : s2.reg .r9 = (κ.val * 2 ^ (10 - z)).toUInt64 := by rw [hs2]; simpa using r9
    have r10' : s2.reg .r10 = z.toUInt64 := by rw [hs2]; simpa using r10
    have r13' : s2.reg .r13 = (22 * κ.val).toUInt64 := by rw [hs2]; simpa using hr13'
    have r14' : s2.reg .r14 = (lf.val / 2 ^ z).toUInt64 := by rw [hs2]; simpa using r14
    step
    rw [r9', toUInt64_shr (show 1 < 64 by omega) hk9]
    step; step; step
    rw [r14', toUInt64_shr (show 1 < 64 by omega) hlz, toUInt64_add]
    refine blk_store_cw' (by exact h2.frame rfl (by simp)) (by omega) fun s3 h3 hs3 ↦ ?_
    simp only [QState.setReg_reg, ite_true] at h3
    have r9'' : s3.reg .r9 = (κ.val * 2 ^ (10 - z) / 2 ^ 1).toUInt64 := by rw [hs3]; simp
    have r10'' : s3.reg .r10 = z.toUInt64 := by rw [hs3]; simpa using r10'
    have r13'' : s3.reg .r13 = (22 * κ.val).toUInt64 := by rw [hs3]; simpa using r13'
    have r14'' : s3.reg .r14 = (lf.val / 2 ^ z).toUInt64 := by rw [hs3]; simpa using r14'
    step; step; step
    rw [r10'', toUInt64_shl (show 1 < 64 by omega) (show z * 2 ^ 1 < 2 ^ 64 by omega), r13'',
      toUInt64_add]
    have hz' : z < forsTreeHeight := hz10
    have hin : ∀ k < 2, V (z * 2 ^ 1 + 22 * κ.val + (inp + 12) + k) =
        digestWord ((sig.forsOpening κ).path ⟨z, hz'⟩) k := by
      intro k hk
      rw [show z * 2 ^ 1 + 22 * κ.val + (inp + 12) + k = inp + (10 + 22 * κ.val + (2 + 2 * z + k))
        by omega, hS.input _ (by unfold inputWords; omega), encode_fors pk m sig κ (by omega),
        forsWord_path _ ⟨z, hz'⟩ hk]
    apply WP.blk_cons
    refine WP.mono (pathNode_ok (h3.frame (s' := s3.setReg .rcx (z * 2 ^ 1 + 22 * κ.val).toUInt64)
      rfl (by simp)) (sib := inp + 12)
      (n := z * 2 ^ 1 + 22 * κ.val) (b := lf.val / 2 ^ z)
      (cur := forsCur pk.publicSeed idx κ lf (sig.forsOpening κ) z)
      (other := (sig.forsOpening κ).path ⟨z, hz'⟩) (by simp) (by simp [r14'']) hlz (by omega)
      ?hv0 ?hv1 ?ho0 ?ho1) (fun s4 ⟨V4, h4, e4, p4, f4⟩ ↦ ?_) (fun _ h ↦ h)
    case hv0 => rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), v1]
    case hv1 => rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), v1']
    case ho0 =>
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        e1 _ (by unfold LevelWrites; omega)]
      exact (hin 0 (by omega)).trans (digestWord_zero _)
    case ho1 =>
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        e1 _ (by unfold LevelWrites; omega), ← Nat.add_assoc]
      exact (hin 1 (by omega)).trans (digestWord_one _)
    -- the node's hash
    have hV4 : ∀ k, k < smallBuf + 6 → ¬LevelWrites k → V4 k = V k := fun k hk hw ↦ by
      rw [e4 k (by omega), Function.update_of_ne (by unfold LevelWrites at hw; omega),
        Function.update_of_ne (by unfold LevelWrites at hw; omega), e1 k hw]
    have hA : AdrsAt V4 0 (idx.val / 256) .forsTree (idx.val % 256) (z + 1)
        (lf.val / 2 ^ z / 2 ^ 1 + κ.val * 2 ^ (10 - z) / 2 ^ 1) := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hV4 _ (by omega) (by unfold LevelWrites; omega), hA0]
      · rw [hV4 _ (by omega) (by unfold LevelWrites; omega), hS.zero1]
      · rw [hV4 _ (by omega) (by unfold LevelWrites; omega), hS.zero2]
      · rw [hV4 _ (by omega) (by unfold LevelWrites; omega), hA3]
      · rw [hV4 _ (by omega) (by unfold LevelWrites; omega), hA4]
      · rw [hV4 _ (by omega) (by unfold LevelWrites; omega), hA5]
      · rw [e4 _ (by omega), Function.update_of_ne (by omega), Function.update_self]
      · rw [e4 _ (by omega), Function.update_self]
    have hth : th (tweakWords V4 smallBuf 80) 80 =
        forsCur pk.publicSeed idx κ lf (sig.forsOpening κ) (z + 1) := by
      rw [th_tweakWords hA (by omega) (by omega) (by omega) (by omega)
        (by have : κ.val * 2 ^ (10 - z) / 2 ^ 1 ≤ κ.val * 2 ^ 10 := Nat.le_trans (Nat.div_le_self _ _)
              (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega)))
            have : lf.val / 2 ^ z / 2 ^ 1 ≤ lf.val := Nat.le_trans (Nat.div_le_self _ _)
              (Nat.div_le_self _ _)
            omega)
        (by rw [hV4 _ (by omega) (by unfold LevelWrites; omega), hS.small0])
        (by rw [hV4 _ (by omega) (by unfold LevelWrites; omega), hS.small1]) p4 (by omega),
        forsCur_succ, forsNode_eq _ _ _ hz10, Nat.testBit_div_two_pow, Nat.zero_add]
      simp only [forsSib, dite_yes hz']
      rfl
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
    rw [hreg .r10 (by simp), r10'', imm_nat, toUInt64_add]
    apply WP.blk_nil
    refine ⟨⟨z + 1, V5, h5.setReg (by decide) _ |>.setReg (by decide) _, by omega, fun k hk ↦ ?_,
      d5, d5', by simp, ?_, ?_, ?_⟩, ?_⟩
    · rw [e5 k (by unfold LevelWrites at hk; omega) (by unfold LevelWrites at hk; omega)
        (by unfold LevelWrites at hk; omega) (by unfold LevelWrites at hk; omega)]
      rw [e4 k (by unfold LevelWrites at hk; omega), Function.update_of_ne (by unfold LevelWrites at hk; omega),
        Function.update_of_ne (by unfold LevelWrites at hk; omega), e1 k hk]
    · simp only [QState.setReg_reg, reduceCtorEq, ite_false, ite_true]
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
    · rw [QState.setReg_reg, ite_no (by decide), QState.setReg_reg, ite_no (by decide),
        hreg .r9 (by simp), r9'']
      congr 1
      rw [show 10 - z = (10 - (z + 1)) + 1 by omega, Nat.pow_succ, ← Nat.mul_assoc, Nat.pow_one,
        Nat.mul_div_cancel _ (by decide)]
    · intro r hr
      simp only [QState.setReg_reg]
      rw [ite_no (fun h ↦ hr (by simp [h])), ite_no (fun h ↦ hr (by simp [h])),
        hreg r (fun h ↦ hr (by simp_all)), hs3]
      simp only [QState.setReg_reg]
      rw [ite_no (fun h ↦ hr (by simp [h])), ite_no (fun h ↦ hr (by simp [h])), hs2]
      simp only [QState.setReg_reg]
      rw [ite_no (fun h ↦ hr (by simp [h])), f1 r hr]
    · simp only [QState.setReg_reg, ite_true, toNat_toUInt64' (show z + 1 < 2 ^ 64 by omega),
        toNat_toUInt64' (show z < 2 ^ 64 by omega)]
      omega
  · rintro s1 ⟨z, V1, h1, hz, e1, v1, v1', r10, r14, r9, f1⟩ hcond
    rw [cond_ltu_imm (k := 10) (K := 10) r10 (imm_nat 10) (by omega) (by omega)] at hcond
    have hz10 : z = 10 := by simp at hcond; omega
    subst hz10
    exact ⟨V1, h1, e1, v1, v1', f1⟩

/-! ## One FORS tree -/

/-- The words a FORS tree writes. -/
def TreeWrites (κ k : Nat) : Prop :=
  LevelWrites k ∨ k = adrsRec + 4 ∨ k = bigBuf + 6 + 2 * κ ∨ k = bigBuf + 7 + 2 * κ

theorem forsLeafHash_eq (seed : BitVec 128) (idx : Index) (κ : ForsTreeIndex) (lf : ForsLeafIndex)
    (o : ForsTreeOpening) :
    forsCur seed idx κ lf o 0 = Id.run (Verification.addressedHash (m := Id)
      LeanVM.Semantics.keccakF1600 seed (makeAddress 0 (idx.val / 256) .forsTree (idx.val % 256) 0
        (κ.val * 2 ^ 10 + lf.val)) (littleEndianBytes 16 o.secret)) := by
  show Id.run (Verification.addressedHash (m := Id) LeanVM.Semantics.keccakF1600 seed
    (hashDomainFields (.forsLeaf idx κ lf)) (littleEndianBytes 16 o.secret)) = _
  rw [hashDomainFields, treeOfIndex_zero, leafOfIndex_zero]
  rfl

theorem forsTree_ok (hb : Fits base) (hI : Inv base V s) {pk : _root_.Sphincs.PublicKey}
    {m : Message} {sig : Signature} (hS : Static pk m sig V) {idx : Index} {κ : ForsTreeIndex}
    {lf : ForsLeafIndex}
    (hA0 : V adrsRec = (0 : Nat).toUInt64) (hA3 : V (adrsRec + 3) = (idx.val / 256).toUInt64)
    (hA5 : V (adrsRec + 5) = (idx.val % 256).toUInt64)
    (hl : V (forsLeaves + κ.val) = lf.val.toUInt64)
    (hr12 : s.reg .r12 = κ.val.toUInt64) (hr13 : s.reg .r13 = (22 * κ.val).toUInt64) :
    WP forsTree s (fun s' ↦ ∃ V', Inv base V' s' ∧ (∀ k, ¬TreeWrites κ.val k → V' k = V k) ∧
      V' (bigBuf + 6 + 2 * κ.val) =
        digestLo (forsCur pk.publicSeed idx κ lf (sig.forsOpening κ) 10) ∧
      V' (bigBuf + 7 + 2 * κ.val) =
        digestHi (forsCur pk.publicSeed idx κ lf (sig.forsOpening κ) 10) ∧
      RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r9, .r10, .r14] s s') E := by
  have hκ := κ.isLt
  have hlf := lf.isLt
  have hidx := idx.isLt
  unfold forsTreeCount at hκ
  unfold forsTreeHeight at hlf
  unfold indexBits at hidx
  have hctx : Context.ctxWords = 3200 := rfl
  have har : adrsRec = 1200 := rfl
  have hsb : smallBuf = 1280 := rfl
  have hbb : bigBuf = 1296 := rfl
  have hval : val = 1210 := rfl
  have hinp : inp = 128 := rfl
  have hsw : scratchWords = 84 := rfl
  have hfl : forsLeaves = 1176 := rfl
  unfold forsTree setField
  refine blk_storei_cw' hI (by omega) fun s1 h1 hs1 ↦ ?_
  refine blk_storei_cw' h1 (by omega) fun s2 h2 hs2 ↦ ?_
  have r12' : s2.reg .r12 = κ.val.toUInt64 := by rw [hs2, hs1, hr12]
  refine blk_load_cwi h2 r12' (by omega) ?_
  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
    show κ.val + forsLeaves = forsLeaves + κ.val from Nat.add_comm _ _, hl]
  step; step; step
  rw [r12', toUInt64_shl (show 10 < 64 by omega) (show κ.val * 2 ^ 10 < 2 ^ 64 by omega),
    toUInt64_add]
  refine blk_store_cw' (by exact h2.frame rfl (by simp)) (by omega) fun s3 h3 hs3 ↦ ?_
  simp only [QState.setReg_reg, ite_true] at h3
  have r13' : s3.reg .r13 = (22 * κ.val).toUInt64 := by rw [hs3]; simp [hs2, hs1, hr13]
  have hin : ∀ k < 2, V (22 * κ.val + (inp + 10 + k)) = digestWord (sig.forsOpening κ).secret k := by
    intro k hk
    rw [show 22 * κ.val + (inp + 10 + k) = inp + (10 + 22 * κ.val + k) by omega,
      hS.input _ (by unfold inputWords; omega), encode_fors pk m sig κ (by omega),
      forsWord_secret _ hk]
  apply WP.blk_cons
  refine WP.mono (mv_ok (j := 22 * κ.val + (inp + 10)) (k := smallBuf + 6) h3
    (by rw [cwi_eval _ r13', h3.rdi]) (by omega) (by rw [cw_eval]; simp [h3.rdi]) (by omega))
    (fun s4 ⟨h4, f4⟩ ↦ ?_) (fun _ h ↦ h)
  have r13'' : s4.reg .r13 = (22 * κ.val).toUInt64 := by rw [f4 .r13 (by simp), r13']
  apply WP.blk_cons
  refine WP.mono (mv_ok (j := 22 * κ.val + (inp + 11)) (k := smallBuf + 7) h4
    (by rw [cwi_eval _ r13'', h4.rdi]) (by omega) (by rw [cw_eval]; simp [h4.rdi]) (by omega))
    (fun s5 ⟨h5, f5⟩ ↦ ?_) (fun _ h ↦ h)
  -- the leaf's hash
  set V5 := Function.update (Function.update (Function.update (Function.update (Function.update V
    (adrsRec + 4) (Int64.toUInt64 3)) (adrsRec + 6) (Int64.toUInt64 0)) (adrsRec + 7)
    (κ.val * 2 ^ 10 + lf.val).toUInt64) (smallBuf + 6) (V (22 * κ.val + (inp + 10))))
    (smallBuf + 7) (V (22 * κ.val + (inp + 11))) with hV5def
  have h5' : Inv base V5 s5 := by
    convert h5 using 2
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega)]
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  have hV5 : ∀ k, (k ≠ adrsRec + 4 ∧ k ≠ adrsRec + 6 ∧ k ≠ adrsRec + 7 ∧ k ≠ smallBuf + 6 ∧
      k ≠ smallBuf + 7) → V5 k = V k := fun k hk ↦ by
    simp only [hV5def]
    rw [Function.update_of_ne hk.2.2.2.2, Function.update_of_ne hk.2.2.2.1,
      Function.update_of_ne hk.2.2.1, Function.update_of_ne hk.2.1, Function.update_of_ne hk.1]
  have hA : AdrsAt V5 0 (idx.val / 256) .forsTree (idx.val % 256) 0 (κ.val * 2 ^ 10 + lf.val) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hV5 _ (by omega), hA0]
    · rw [hV5 _ (by omega), hS.zero1]
    · rw [hV5 _ (by omega), hS.zero2]
    · rw [hV5 _ (by omega), hA3]
    · simp only [hV5def]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self,
        imm_nat]
      rfl
    · rw [hV5 _ (by omega), hA5]
    · simp only [hV5def]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_self, imm_nat]
    · simp only [hV5def]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
  have hth : th (tweakWords V5 smallBuf 64) 64 =
      forsCur pk.publicSeed idx κ lf (sig.forsOpening κ) 0 := by
    rw [forsLeafHash_eq, th_tweakWords hA (by omega) (by omega) (by omega) (by omega) (by omega)
      (by rw [hV5 _ (by omega), hS.small0]) (by rw [hV5 _ (by omega), hS.small1]) ?_ (by omega)]
    apply payload_digest
    · simp only [hV5def]
      rw [Function.update_of_ne (by omega), Function.update_self]
      exact (hin 0 (by omega)).trans (digestWord_zero _)
    · simp only [hV5def]
      rw [Function.update_self]
      exact (hin 1 (by omega)).trans (digestWord_one _)
  apply WP.blk_cons
  refine WP.mono (tweak_ok hb h5' (buf := smallBuf) (len := 64) (dst := val) (by omega) (by omega)
    (by omega) (by omega) (Or.inr (by omega)) (by omega) (by omega)
    (tweakWords_drop _ (by decide) (by decide))) (fun s6 ⟨V6, h6, e6, d6, d6', f6⟩ ↦ ?_)
    (fun _ h ↦ h)
  rw [hth] at d6 d6'
  have hreg6 : ∀ r, r ∉ [Reg64.rax, .rbx, .rcx, .rdx, .rsi, .r8] → s6.reg r = s3.reg r := by
    intro r hr
    rw [f6 r hr, f5 r (fun h ↦ hr (by simp_all)), f4 r (fun h ↦ hr (by simp_all))]
  have r12'' : s6.reg .r12 = κ.val.toUInt64 := by
    rw [hreg6 .r12 (by simp), hs3]; simp [r12']
  have r14'' : s6.reg .r14 = lf.val.toUInt64 := by
    rw [hreg6 .r14 (by simp), hs3]; simp
  step; step; step
  rw [r12'', toUInt64_shl (show 10 < 64 by omega) (show κ.val * 2 ^ 10 < 2 ^ 64 by omega), imm_nat]
  have hW6 : ∀ k, ¬TreeWrites κ.val k → V6 k = V k := fun k hk ↦ by
    unfold TreeWrites LevelWrites at hk
    rw [e6 k (by omega) (by omega) (by omega) (by omega), hV5 k (by omega)]
  have hS6 : Static pk m sig V6 := hS.frame fun k hk ↦ hW6 k (by
    unfold TreeWrites LevelWrites; unfold Kept at hk; unfold mdBuf at hk; omega)
  apply WP.blk_cons
  refine WP.mono (forsLevels_ok (idx := idx) (κ := κ) (lf := lf) hb
    (by exact h6.frame rfl (by simp)) hS6
    (by rw [hW6 _ (by unfold TreeWrites LevelWrites; omega), hA0])
    (by rw [hW6 _ (by unfold TreeWrites LevelWrites; omega), hA3])
    (by rw [e6 _ (by omega) (by omega) (by omega) (by omega)]; simp only [hV5def]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self,
          imm_nat]
        rfl)
    (by rw [hW6 _ (by unfold TreeWrites LevelWrites; omega), hA5]) d6 d6' (by simp)
    (by simp [r14'']) (by simp) (by simp [hreg6 .r13 (by simp), r13']))
    (fun s7 ⟨V7, h7, e7, d7, d7', f7⟩ ↦ ?_) (fun _ h ↦ h)
  have r12_7 : s7.reg .r12 = κ.val.toUInt64 := by
    rw [f7 .r12 (by simp)]; simp [r12'']
  step; step
  rw [r12_7, toUInt64_shl (show 1 < 64 by omega) (show κ.val * 2 ^ 1 < 2 ^ 64 by omega)]
  apply WP.blk_cons
  refine WP.mono (mv_ok (j := val) (k := κ.val * 2 ^ 1 + (bigBuf + 6))
    (h7.frame (s' := s7.setReg .rcx (κ.val * 2 ^ 1).toUInt64) rfl (by simp))
    (by rw [cw_eval]; simp [h7.rdi]) (by omega)
    (by rw [cwi_eval (n := κ.val * 2 ^ 1) _ (by simp)]; simp [h7.rdi])
    (by omega)) (fun s8 ⟨h8, f8⟩ ↦ ?_) (fun _ h ↦ h)
  have r8' : s8.reg .rcx = (κ.val * 2 ^ 1).toUInt64 := by rw [f8 .rcx (by simp)]; simp
  refine WP.mono (mv_ok (j := val + 1) (k := κ.val * 2 ^ 1 + (bigBuf + 7)) h8
    (by rw [cw_eval, h8.rdi]) (by omega)
    (by rw [cwi_eval (n := κ.val * 2 ^ 1) _ (by simp [r8'])]; simp [h8.rdi])
    (by omega)) (fun s9 ⟨h9, f9⟩ ↦ ⟨_, h9, fun k hk ↦ ?_, ?_, ?_, ?_⟩) (fun _ h ↦ h)
  · have hk' := hk
    unfold TreeWrites at hk'
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      e7 k (fun h ↦ hk (Or.inl h)), hW6 k hk]
  · rw [Function.update_of_ne (by omega), show bigBuf + 6 + 2 * κ.val = κ.val * 2 ^ 1 + (bigBuf + 6)
      by omega, Function.update_self, d7]
  · rw [show bigBuf + 7 + 2 * κ.val = κ.val * 2 ^ 1 + (bigBuf + 7) by omega, Function.update_self,
      Function.update_of_ne (by omega), d7']
  · intro r hr
    rw [f9 r (fun h ↦ hr (by simp_all)), f8 r (fun h ↦ hr (by simp_all))]
    simp only [QState.setReg_reg]
    rw [ite_no (fun h ↦ hr (by simp [h])), f7 r hr]
    simp only [QState.setReg_reg]
    rw [ite_no (fun h ↦ hr (by simp [h])), ite_no (fun h ↦ hr (by simp [h])),
      hreg6 r (fun h ↦ hr (by simp_all)), hs3]
    simp only [QState.setReg_reg]
    rw [ite_no (fun h ↦ hr (by simp [h])), ite_no (fun h ↦ hr (by simp [h])), hs2, hs1]

/-! ## The FORS public key -/

/-- The words the FORS trees write. -/
def TreesWrites (k : Nat) : Prop :=
  LevelWrites k ∨ k = adrsRec + 4 ∨ (bigBuf + 6 ≤ k ∧ k < bigBuf + 54)

theorem TreeWrites.trees {c k : Nat} (hc : c < 24) (h : TreeWrites c k) : TreesWrites k := by
  unfold TreeWrites at h
  unfold TreesWrites
  rcases h with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · unfold bigBuf at *; omega
  · unfold bigBuf at *; omega

theorem forsPublicKey_eq (seed : BitVec 128) (idx : Index) (roots : ForsTreeIndex → Digest) :
    Id.run (Verification.forsPublicKey (m := Id) LeanVM.Semantics.keccakF1600 seed idx roots) =
      Id.run (Verification.addressedHash (m := Id) LeanVM.Semantics.keccakF1600 seed
        (makeAddress 0 (idx.val / 256) .forsRoots (idx.val % 256) 0 0) (digestsPayload roots)) := by
  show Id.run (Verification.addressedHash (m := Id) LeanVM.Semantics.keccakF1600 seed
    (hashDomainFields (.forsRoots idx)) (digestsPayload roots)) = _
  rw [hashDomainFields, treeOfIndex_zero, leafOfIndex_zero]

theorem fors_ok (hb : Fits base) (hI : Inv base V s) {pk : _root_.Sphincs.PublicKey}
    {m : Message} {sig : Signature} (hS : Static pk m sig V) {idx : Index}
    {lf : ForsTreeIndex → ForsLeafIndex} (hr15 : s.reg .r15 = idx.val.toUInt64)
    (hl : ∀ κ : ForsTreeIndex, V (forsLeaves + κ.val) = (lf κ).val.toUInt64) :
    WP fors s (fun s' ↦ ∃ V', Inv base V' s' ∧ Frame V V' ∧
      V' msg = digestLo (Id.run (Verification.forsRecover (m := Id) LeanVM.Semantics.keccakF1600
        pk.publicSeed idx lf sig.forsOpening)) ∧
      V' (msg + 1) = digestHi (Id.run (Verification.forsRecover (m := Id)
        LeanVM.Semantics.keccakF1600 pk.publicSeed idx lf sig.forsOpening)) ∧
      RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r9, .r10, .r12, .r13, .r14] s s') E := by
  have hidx := idx.isLt
  unfold indexBits at hidx
  have hctx : Context.ctxWords = 3200 := rfl
  have har : adrsRec = 1200 := rfl
  have hsb : smallBuf = 1280 := rfl
  have hbb : bigBuf = 1296 := rfl
  have hval : val = 1210 := rfl
  have hmsg : msg = 1208 := rfl
  have hsw : scratchWords = 84 := rfl
  have hfl : forsLeaves = 1176 := rfl
  have hmd : mdBuf = 1152 := rfl
  unfold fors setField
  refine blk_storei_cw' hI (by omega) fun s1 h1 hs1 ↦ ?_
  simp only [Nat.add_zero] at h1
  have r15 : s1.reg .r15 = idx.val.toUInt64 := by rw [hs1, hr15]
  step; step
  rw [r15, toUInt64_shr (show 8 < 64 by omega) (by omega)]
  refine blk_store_cw' (by exact h1.frame rfl (by simp)) (by omega) fun s2 h2 hs2 ↦ ?_
  simp only [QState.setReg_reg, ite_true] at h2
  have r15' : s2.reg .r15 = idx.val.toUInt64 := by rw [hs2]; simp [r15]
  step; step
  rw [r15', show (255 : Int64).toUInt64 = (2 ^ 8 - 1 : Nat).toUInt64 from rfl,
    toUInt64_and_mask (show 8 < 64 by omega) (by omega)]
  refine blk_store_cw' (by exact h2.frame rfl (by simp)) (by omega) fun s3 h3 hs3 ↦ ?_
  simp only [QState.setReg_reg, ite_true] at h3
  step; step
  set V3 := Function.update (Function.update (Function.update V adrsRec (Int64.toUInt64 0))
    (adrsRec + 3) (idx.val / 2 ^ 8).toUInt64) (adrsRec + 5) (idx.val % 2 ^ 8).toUInt64 with hV3
  have hV3k : ∀ k, k ≠ adrsRec → k ≠ adrsRec + 3 → k ≠ adrsRec + 5 → V3 k = V k := fun k h0 h3 h5 ↦ by
    rw [hV3, Function.update_of_ne h5, Function.update_of_ne h3, Function.update_of_ne h0]
  have hS3 : Static pk m sig V3 := hS.frame fun k hk ↦ hV3k k (by unfold Kept at hk; omega)
    (by unfold Kept at hk; omega) (by unfold Kept at hk; omega)
  have hA0 : V3 adrsRec = (0 : Nat).toUInt64 := by
    rw [hV3, Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
    rfl
  have hA3 : V3 (adrsRec + 3) = (idx.val / 256).toUInt64 := by
    rw [hV3, Function.update_of_ne (by omega), Function.update_self]
    rfl
  have hA5 : V3 (adrsRec + 5) = (idx.val % 256).toUInt64 := by
    rw [hV3, Function.update_self]
    rfl
  have hl3 : ∀ κ : ForsTreeIndex, V3 (forsLeaves + κ.val) = (lf κ).val.toUInt64 := fun κ ↦ by
    have := κ.isLt; unfold forsTreeCount at this
    rw [hV3k _ (by omega) (by omega) (by omega), hl]
  apply WP.blk_cons
  refine WP.mono (wp_loop (fun s' ↦ ∃ c V', Inv base V' s' ∧ c ≤ 24 ∧
      (∀ k, ¬TreesWrites k → V' k = V3 k) ∧
      (∀ κ : ForsTreeIndex, κ.val < c →
        V' (bigBuf + 6 + 2 * κ.val) =
          digestLo (forsCur pk.publicSeed idx κ (lf κ) (sig.forsOpening κ) 10) ∧
        V' (bigBuf + 7 + 2 * κ.val) =
          digestHi (forsCur pk.publicSeed idx κ (lf κ) (sig.forsOpening κ) 10)) ∧
      s'.reg .r12 = c.toUInt64 ∧ s'.reg .r13 = (22 * c).toUInt64 ∧
      RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r9, .r10, .r12, .r13, .r14] s s')
    (fun s' ↦ 24 - (s'.reg .r12).toNat) ⟨0, V3, ?_, by omega, fun _ _ ↦ rfl,
      fun κ hκ ↦ absurd hκ (by omega), ?_, ?_, ?_⟩ ?_) (fun s4 h ↦ ?_) (fun _ h ↦ h)
  · exact h3.frame rfl (by simp)
  · simp; rfl
  · simp; rfl
  · intro r hr
    simp only [QState.setReg_reg]
    rw [ite_no (fun h ↦ hr (by simp [h])), ite_no (fun h ↦ hr (by simp [h])), hs3]
    simp only [QState.setReg_reg]
    rw [ite_no (fun h ↦ hr (by simp [h])), hs2]
    simp only [QState.setReg_reg]
    rw [ite_no (fun h ↦ hr (by simp [h])), hs1]
  · rintro s1 ⟨c, V1, h1, hc, e1, d1, r12, r13, f1⟩ hcond
    rw [cond_ltu_imm (k := 24) (K := 24) r12 (imm_nat 24) (by omega) (by omega)] at hcond
    have hc24 : c < 24 := by simpa using hcond
    have hkt : ∀ k, Kept k → ¬TreesWrites k := fun k hk ↦ by
      unfold TreesWrites LevelWrites; unfold Kept at hk; omega
    have hlc : V1 (forsLeaves + c) = (lf ⟨c, hc24⟩).val.toUInt64 := by
      rw [e1 _ (by unfold TreesWrites LevelWrites; omega)]; exact hl3 ⟨c, hc24⟩
    apply WP.blk_cons
    refine WP.mono (forsTree_ok (pk := pk) (m := m) (sig := sig) (idx := idx) (κ := ⟨c, hc24⟩)
      (lf := lf ⟨c, hc24⟩) hb h1
      (hS3.frame fun k hk ↦ e1 k (hkt k hk))
      (by rw [e1 _ (by unfold TreesWrites LevelWrites; omega), hA0])
      (by rw [e1 _ (by unfold TreesWrites LevelWrites; omega), hA3])
      (by rw [e1 _ (by unfold TreesWrites LevelWrites; omega), hA5])
      hlc r12 r13)
      (fun s2 ⟨V2, h2, e2, d2, d2', f2⟩ ↦ ?_) (fun _ h ↦ h)
    step; step
    rw [f2 .r12 (by simp), r12, f2 .r13 (by simp), r13, imm_nat, imm_nat, toUInt64_add,
      toUInt64_add]
    apply WP.blk_nil
    refine ⟨⟨c + 1, V2, h2.frame rfl (by simp), by omega, fun k hk ↦ ?_, fun κ hκ ↦ ?_, by simp,
      by simp only [QState.setReg_reg, ite_true]; exact congrArg _ (by ring), ?_⟩, ?_⟩
    · rw [e2 k (fun h ↦ hk (h.trees hc24)), e1 k hk]
    · rcases Nat.lt_or_ge κ.val c with h' | h'
      · have := d1 κ h'
        rw [e2 _ (by unfold TreeWrites LevelWrites; simp only; omega),
          e2 _ (by unfold TreeWrites LevelWrites; simp only; omega)]
        exact this
      · have hκc : κ = ⟨c, hc24⟩ := Fin.ext (by simp; omega)
        subst hκc
        exact ⟨d2, d2'⟩
    · intro r hr
      simp only [QState.setReg_reg]
      rw [ite_no (fun h ↦ hr (by simp [h])), ite_no (fun h ↦ hr (by simp [h])),
        f2 r (fun h ↦ hr (by simp_all)), f1 r hr]
    · simp only [QState.setReg_reg, reduceCtorEq, ite_false, ite_true,
        toNat_toUInt64' (show c + 1 < 2 ^ 64 by omega), toNat_toUInt64' (show c < 2 ^ 64 by omega)]
      omega
  · obtain ⟨⟨c, V4, h4, hc, e4, d4, r12, r13, f4⟩, hcond⟩ := h
    rw [cond_ltu_imm (k := 24) (K := 24) r12 (imm_nat 24) (by omega) (by omega)] at hcond
    have hc24 : c = 24 := by simp at hcond; omega
    subst hc24
    refine blk_storei_cw' h4 (by omega) fun s5 h5 hs5 ↦ ?_
    refine blk_storei_cw' h5 (by omega) fun s6 h6 hs6 ↦ ?_
    refine blk_storei_cw' h6 (by omega) fun s7 h7 hs7 ↦ ?_
    set V7 := Function.update (Function.update (Function.update V4 (adrsRec + 4) (Int64.toUInt64 4))
      (adrsRec + 6) (Int64.toUInt64 0)) (adrsRec + 7) (Int64.toUInt64 0) with hV7
    have hV7k : ∀ k, k ≠ adrsRec + 4 → k ≠ adrsRec + 6 → k ≠ adrsRec + 7 → V7 k = V4 k :=
      fun k h4 h6 h7 ↦ by rw [hV7, Function.update_of_ne h7, Function.update_of_ne h6,
        Function.update_of_ne h4]
    have hA : AdrsAt V7 0 (idx.val / 256) .forsRoots (idx.val % 256) 0 0 := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hV7k _ (by omega) (by omega) (by omega), e4 _ (by unfold TreesWrites LevelWrites; omega),
          hA0]
      · rw [hV7k _ (by omega) (by omega) (by omega), e4 _ (by unfold TreesWrites LevelWrites; omega),
          hS3.zero1]
      · rw [hV7k _ (by omega) (by omega) (by omega), e4 _ (by unfold TreesWrites LevelWrites; omega),
          hS3.zero2]
      · rw [hV7k _ (by omega) (by omega) (by omega), e4 _ (by unfold TreesWrites LevelWrites; omega),
          hA3]
      · rw [hV7, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_self, imm_nat]
        rfl
      · rw [hV7k _ (by omega) (by omega) (by omega), e4 _ (by unfold TreesWrites LevelWrites; omega),
          hA5]
      · rw [hV7, Function.update_of_ne (by omega), Function.update_self, imm_nat]
      · rw [hV7, Function.update_self, imm_nat]
    have hth : th (tweakWords V7 bigBuf 432) 432 = Id.run (Verification.forsRecover (m := Id)
        LeanVM.Semantics.keccakF1600 pk.publicSeed idx lf sig.forsOpening) := by
      rw [forsRecover_id, forsPublicKey_eq, th_tweakWords hA (by omega) (by omega) (by omega)
        (by omega) (by omega)
        (by rw [hV7k _ (by omega) (by omega) (by omega),
          e4 _ (by unfold TreesWrites LevelWrites; omega), hS3.big0])
        (by rw [hV7k _ (by omega) (by omega) (by omega),
          e4 _ (by unfold TreesWrites LevelWrites; omega), hS3.big1]) ?_ (by omega)]
      have hpay : wordsBytes (words V7 (bigBuf + 6) (2 * 24)) = digestsPayload
          (fun κ ↦ forsCur pk.publicSeed idx κ (lf κ) (sig.forsOpening κ) forsTreeHeight) := by
        apply words_digests
        intro κ
        have := κ.isLt
        rw [hV7k _ (by omega) (by omega) (by omega), hV7k _ (by omega) (by omega) (by omega),
          show bigBuf + 6 + 2 * κ.val + 1 = bigBuf + 7 + 2 * κ.val by omega]
        exact d4 κ κ.isLt
      have hlen : (digestsPayload
          (fun κ ↦ forsCur pk.publicSeed idx κ (lf κ) (sig.forsOpening κ) forsTreeHeight)).length =
          384 := by rw [← hpay, wordsBytes_length, words_length]
      rw [show (432 + 7) / 8 - 6 = 2 * 24 from rfl, hpay, List.take_of_length_le (by rw [hlen])]
    apply WP.blk_cons
    refine WP.mono (tweak_ok hb h7 (buf := bigBuf) (len := 432) (dst := msg) (by omega) (by omega)
      (by omega) (by omega) (Or.inr (by omega)) (by omega) (by omega)
      (tweakWords_drop _ (by decide) (by decide))) (fun s8 ⟨V8, h8, e8, d8, d8', f8⟩ ↦
        WP.blk_nil ⟨V8, h8, fun k hk ↦ ?_, hth ▸ d8, hth ▸ d8', ?_⟩) (fun _ h ↦ h)
    · have hk' := hk
      unfold Kept at hk'
      rw [e8 k (by omega) (by omega) (by omega) (by omega), hV7k k (by omega) (by omega) (by omega),
        e4 k (by unfold TreesWrites LevelWrites; omega), hV3k k (by omega) (by omega) (by omega)]
    · intro r hr
      rw [f8 r (fun h ↦ hr (by simp_all)), hs7, hs6, hs5, f4 r hr]

end X86.SphincsVerifier
