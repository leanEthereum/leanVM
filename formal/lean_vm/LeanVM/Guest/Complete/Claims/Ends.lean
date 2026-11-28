module

public import LeanVM.Guest.Complete.Claims.Digest
public import LeanVM.Guest.Complete.Claims.MonoAt
public import LeanVM.Guest.B2C.Cells
public import LeanVM.Guest.Memory.AllocA

/-!
# The claim lists' ends, bounded

At the certificates' frame sizes (`B2C.fs`, each below `2^30`, the frame loops' below `2^20` by the
kernel), on `n < 2^19` claims every claim list's end is within `2^36` of its cursor: `chEnd_le`,
`clEnd_le` (`claim_list_chain`, `claim_list_digest`), `anyEnd_le`, `monoEnd_le`
(`child_claim_list_any`, `child_claim_list_mono`).
-/

namespace LeanVM.Guest.Complete

open LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1.Digest
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

set_option maxRecDepth 100000 in
/-- The frame loops' frames, by the kernel. -/
theorem fs_loops : B2C.fs name% «claim_list_chain_loop0» < 2 ^ 20 ∧
    B2C.fs name% «child_claim_list_any_loop0» < 2 ^ 20 ∧ B2C.fs name% «child_claim_list_mono_loop0» < 2 ^ 20 := by
  decide +kernel

theorem lpBlk_le {f : String} {m M F : ℕ} (hm : m ≤ M) (hF : B2C.fs f ≤ F) :
    lpBlk B2C.fs f m ≤ M * F + 2 ^ 30 := by
  unfold lpBlk
  have := B2C.fs_lt (tailKey f)
  have := Nat.mul_le_mul hm hF
  omega

/-- A frame loop over `n / 136` big frames then one over `n % 136 / 17` groups, from `c`. -/
theorem loops_le (al : String → Bool) {L0 L1 : String} (h0 : B2C.fs L0 < 2 ^ 20) {n c w : ℕ}
    (hn : n < 2 ^ 19) (hw : w ≤ 15) :
    allocBase (al L1) (allocBase (al L0) (c + w * (n / 136 + n % 136 / 17 + 1)) + lpBlk B2C.fs L0 (n / 136)) +
      lpBlk B2C.fs L1 (n % 136 / 17) ≤ c + 2 ^ 34 := by
  have e0 := lpBlk_le (f := L0) (m := n / 136) (M := 2 ^ 12) (F := 2 ^ 20) (by omega) h0.le
  have e1 := lpBlk_le (f := L1) (m := n % 136 / 17) (M := 8) (F := 2 ^ 30) (by omega) (B2C.fs_lt _).le
  have a0 := allocBase_le (al L0) (c + w * (n / 136 + n % 136 / 17 + 1))
  have a1 := allocBase_le (al L1) (allocBase (al L0) (c + w * (n / 136 + n % 136 / 17 + 1)) +
    lpBlk B2C.fs L0 (n / 136))
  have hm : w * (n / 136 + n % 136 / 17 + 1) ≤ 15 * (2 ^ 12 + 9) := Nat.mul_le_mul hw (by omega)
  omega

theorem chEnd_le (al : String → Bool) {n c : ℕ} (hn : n < 2 ^ 19) : chEnd B2C.fs al n c ≤ c + 2 ^ 35 := by
  have hl := loops_le al (L1 := name% «claim_list_chain_loop1») fs_loops.1 (c := c) (w := 13) hn (by norm_num)
  have a2 := allocBase_le (al "claim_list_tail") (allocBase (al name% «claim_list_chain_loop1»)
      (allocBase (al name% «claim_list_chain_loop0») (c + 13 * (n / 136 + n % 136 / 17 + 1)) +
        lpBlk B2C.fs name% «claim_list_chain_loop0» (n / 136)) + lpBlk B2C.fs name% «claim_list_chain_loop1» (n % 136 / 17))
  have a3 := allocBase_le (al (clNames.getD (n % 17) ""))
    (allocBase (al "claim_list_tail") (allocBase (al name% «claim_list_chain_loop1»)
      (allocBase (al name% «claim_list_chain_loop0») (c + 13 * (n / 136 + n % 136 / 17 + 1)) +
        lpBlk B2C.fs name% «claim_list_chain_loop0» (n / 136)) + lpBlk B2C.fs name% «claim_list_chain_loop1» (n % 136 / 17)) +
      B2C.fs "claim_list_tail")
  have f1 := B2C.fs_lt "claim_list_tail"
  have f2 := B2C.fs_lt (clNames.getD (n % 17) "")
  show allocBase (al (clNames.getD (n % 17) ""))
    (allocBase (al "claim_list_tail") (allocBase (al name% «claim_list_chain_loop1»)
      (allocBase (al name% «claim_list_chain_loop0») (c + 13 * (n / 136 + n % 136 / 17 + 1)) +
        lpBlk B2C.fs name% «claim_list_chain_loop0» (n / 136)) + lpBlk B2C.fs name% «claim_list_chain_loop1» (n % 136 / 17)) +
      B2C.fs "claim_list_tail") + B2C.fs (clNames.getD (n % 17) "") ≤ c + 2 ^ 35
  omega

theorem clEnd_le (al : String → Bool) {n c : ℕ} (hn : n < 2 ^ 19) : clEnd B2C.fs al n c ≤ c + 2 ^ 36 := by
  unfold clEnd
  split
  · omega
  · have h := chEnd_le al (c := allocBase (al "claim_list_chain") (allocBase (al "list_split") c + B2C.fs "list_split") +
      B2C.fs "claim_list_chain") hn
    have a0 := allocBase_le (al "list_split") c
    have a1 := allocBase_le (al "claim_list_chain") (allocBase (al "list_split") c + B2C.fs "list_split")
    have f0 := B2C.fs_lt "list_split"
    have f1 := B2C.fs_lt "claim_list_chain"
    omega

theorem anyEnd_le (al : String → Bool) {n c : ℕ} (hn : n < 2 ^ 19) : anyEnd B2C.fs al n c ≤ c + 2 ^ 35 := by
  have hl := loops_le al (L1 := name% «child_claim_list_any_loop1») fs_loops.2.1 (c := c) (w := 13) hn (by norm_num)
  have a2 := allocBase_le (al (cclNames.getD (n % 17) "")) (allocBase (al name% «child_claim_list_any_loop1»)
      (allocBase (al name% «child_claim_list_any_loop0») (c + 13 * (n / 136 + n % 136 / 17 + 1)) +
        lpBlk B2C.fs name% «child_claim_list_any_loop0» (n / 136)) + lpBlk B2C.fs name% «child_claim_list_any_loop1» (n % 136 / 17))
  have f2 := B2C.fs_lt (cclNames.getD (n % 17) "")
  unfold anyEnd
  omega

theorem monoEnd_le (al : String → Bool) {n c : ℕ} (hn : n < 2 ^ 19) : monoEnd B2C.fs al n c ≤ c + 2 ^ 35 := by
  have hl := loops_le al (L1 := name% «child_claim_list_mono_loop1») fs_loops.2.2 (c := c) (w := 15) hn le_rfl
  have a2 := allocBase_le (al (mlNames.getD (n % 17) "")) (allocBase (al name% «child_claim_list_mono_loop1»)
      (allocBase (al name% «child_claim_list_mono_loop0») (c + 15 * (n / 136 + n % 136 / 17 + 1)) +
        lpBlk B2C.fs name% «child_claim_list_mono_loop0» (n / 136)) + lpBlk B2C.fs name% «child_claim_list_mono_loop1» (n % 136 / 17))
  have f2 := B2C.fs_lt (mlNames.getD (n % 17) "")
  unfold monoEnd
  omega

end
end LeanVM.Guest.Complete
