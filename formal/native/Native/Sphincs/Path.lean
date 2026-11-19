module

public import Native.Sphincs.Hash

/-!
# A Merkle node's input

`pathNode sib` puts the current value and the sibling at word `sib + rcx` into the small buffer's
payload, in index order by bit `0` of `r14` (`pathNode_ok`): the children of `foldPath`'s node.
-/

@[expose] public section

namespace Native.SphincsVerifier

open LeanVM.Protocol.KeccakHash HashSig HashSig.OverPermutation Keccak

variable {base : UInt64} {V : Nat → UInt64} {s : QState} {E : QState → Prop}

theorem cond_test_bit0 {s : QState} {b : Nat} (hr : s.reg .r14 = b.toUInt64) (hb : b < 2 ^ 64) :
    (Cond.test true .r14 (.imm 1)).eval s = !b.testBit 0 := by
  simp only [Cond.eval, Rhs.eval, hr, show (1 : Int64).toUInt64 = (2 ^ 1 - 1 : Nat).toUInt64 from rfl,
    toUInt64_and_mask (show 1 < 64 by omega) hb, Nat.testBit_zero]
  rcases Nat.mod_two_eq_zero_or_one b with h | h <;> simp [h]

set_option linter.unusedSimpArgs false in
theorem pathNode_ok (hI : Inv base V s) {sib n b : Nat} {cur other : BitVec 128}
    (hrcx : s.reg .rcx = n.toUInt64) (hr14 : s.reg .r14 = b.toUInt64) (hb : b < 2 ^ 64)
    (hn : n + (sib + 1) < mdBuf)
    (hv0 : V val = digestLo cur) (hv1 : V (val + 1) = digestHi cur)
    (ho0 : V (n + sib) = digestLo other) (ho1 : V (n + (sib + 1)) = digestHi other) :
    WP (pathNode sib) s (fun s' ↦ ∃ V', Inv base V' s' ∧
      (∀ k, ¬(smallBuf + 6 ≤ k ∧ k < smallBuf + 10) → V' k = V k) ∧
      (wordsBytes (words V' (smallBuf + 6) 4)).take 32 =
        (if b.testBit 0 then nodePayload other cur else nodePayload cur other) ∧
      RegsFrame [.rax] s s') E := by
  unfold mdBuf at hn
  have hsb : smallBuf = 1280 := rfl
  have hval : val = 1210 := rfl
  have hctx : Context.ctxWords = 3200 := rfl
  have ne0 : n + sib ≠ smallBuf + 6 := by omega
  have ne1 : n + sib ≠ smallBuf + 7 := by omega
  have ne2 : n + sib ≠ smallBuf + 8 := by omega
  have ne3 : n + (sib + 1) ≠ smallBuf + 6 := by omega
  have ne4 : n + (sib + 1) ≠ smallBuf + 7 := by omega
  have ne5 : n + (sib + 1) ≠ smallBuf + 8 := by omega
  have ne6 : val ≠ smallBuf + 6 := by omega
  have ne7 : val + 1 ≠ smallBuf + 6 := by omega
  have ne8 : val ≠ smallBuf + 7 := by omega
  have ne9 : val + 1 ≠ smallBuf + 7 := by omega
  have ne10 : val ≠ smallBuf + 5 := by omega
  unfold pathNode
  apply WP.ite
  rw [cond_test_bit0 hr14 hb]
  cases hbit : b.testBit 0
  · -- current first
    simp only [Bool.not_false, ite_true]
    apply WP.blk_cons
    refine WP.mono (mv2_ok hI (src := val) (dst := smallBuf + 6) (by omega) (by omega) (by omega))
      (fun s1 ⟨h1, f1⟩ ↦ ?_) (fun _ h ↦ h)
    have hrcx1 : s1.reg .rcx = n.toUInt64 := by rw [f1 .rcx (by simp), hrcx]
    apply WP.blk_cons
    refine WP.mono (mv_ok (j := n + sib) (k := smallBuf + 8) h1 (by rw [cwi_eval _ hrcx1, h1.rdi])
      (by omega) (by rw [cw_eval]; simp [h1.rdi]) (by omega)) (fun s2 ⟨h2, f2⟩ ↦ ?_) (fun _ h ↦ h)
    have hrcx2 : s2.reg .rcx = n.toUInt64 := by rw [f2 .rcx (by simp), hrcx1]
    refine WP.mono (mv_ok (j := n + (sib + 1)) (k := smallBuf + 9) h2
      (by rw [cwi_eval _ hrcx2, h2.rdi]) (by omega) (by rw [cw_eval]; simp [h2.rdi]) (by omega))
      (fun s3 ⟨h3, f3⟩ ↦ ⟨_, h3, fun k hk ↦ ?_, ?_, RegsFrame.trans f1 (RegsFrame.trans f2 f3)⟩)
      (fun _ h ↦ h)
    · simp only [Function.update_apply]
      rw [ite_no (by omega), ite_no (by omega), ite_no (by omega), ite_no (by omega)]
    · simp only [Bool.false_eq_true, ite_false]
      apply payload_node <;> simp [hv0, hv1, ho0, ho1, ne0, ne1, ne2, ne3,
        ne4, ne5, ne6, ne7, ne8, ne9, ne10, Nat.add_assoc]
  · -- sibling first
    simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    apply WP.blk_cons
    refine WP.mono (mv_ok (j := n + sib) (k := smallBuf + 6) hI (by rw [cwi_eval _ hrcx, hI.rdi])
      (by omega) (by rw [cw_eval]; simp [hI.rdi]) (by omega)) (fun s1 ⟨h1, f1⟩ ↦ ?_) (fun _ h ↦ h)
    have hrcx1 : s1.reg .rcx = n.toUInt64 := by rw [f1 .rcx (by simp), hrcx]
    apply WP.blk_cons
    refine WP.mono (mv_ok (j := n + (sib + 1)) (k := smallBuf + 7) h1
      (by rw [cwi_eval _ hrcx1, h1.rdi]) (by omega) (by rw [cw_eval]; simp [h1.rdi]) (by omega))
      (fun s2 ⟨h2, f2⟩ ↦ ?_) (fun _ h ↦ h)
    refine WP.mono (mv2_ok h2 (src := val) (dst := smallBuf + 8) (by omega) (by omega) (by omega))
      (fun s3 ⟨h3, f3⟩ ↦ ⟨_, h3, fun k hk ↦ ?_, ?_, RegsFrame.trans f1 (RegsFrame.trans f2 f3)⟩)
      (fun _ h ↦ h)
    · simp only [Function.update_apply]
      rw [ite_no (by omega), ite_no (by omega), ite_no (by omega), ite_no (by omega)]
    · simp only [ite_true]
      apply payload_node <;> simp [Function.update_apply, hv0, hv1, ho0, ho1, ne0, ne1, ne2, ne3,
        ne4, ne5, ne6, ne7, ne8, ne9, ne10, Nat.add_assoc]

end Native.SphincsVerifier
