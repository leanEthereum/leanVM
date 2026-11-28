/-
  LeanVM.Guest.B1.VsC.VsHonEnds

  The honest callees' cursors bounded: `Hon.hend` from each pinned callee's end bound.
-/

module

public import LeanVM.Guest.B1.VsC.VsOrcPin
public import LeanVM.Guest.Complete.FsSmall

/-!
# `verify_sub`'s pinned ends, bounded

Each cursor `verify_sub`'s windows pass between two non-leaf callees is a few leaves past the last
pinned end (`leafEnd`, every frame below `2^16`: `leafEnd_le`), so the chain of pinned ends `x.ec 4`,
`x.ec 6`, `x.ec 7`, `x.ec 9`, `x.ec 12`, …, `x.ec 16` stays within a sum of the callees' bounds of the
cursor. **`VsCtx.EcSteps`**: each pinned end within its callee's bound (`2^20` for `certify_stack` and
`ring_switch_target`, `2^22` for each link callee but the row side's `2^23`, `2^24` for `verify_keccak`, `2^β` for `open_stacked`),
the bounds vsbnd's and vsc33's producers give; **`VsCtx.hend_of_steps`**: then
`x.ec 16 ≤ x.cur + 3 * 2^38` (`Hon.hend`) for `β ≤ 39` (`open_stacked`'s `2^39`), on a stream of at most `32` chunks.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakHash LeanVM.Guest.B1.Link
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

section
variable {al : String → Bool}

theorem leafEnd_le (g : String) (kc : ℕ) : leafEnd B2C.fs al g kc ≤ kc + 2 ^ 17 := by
  have := allocBase_le (al g) kc
  have := fs_lt16 g
  unfold leafEnd
  omega

theorem allocFs_le (g : String) (kc : ℕ) : allocBase (al g) kc + B2C.fs g ≤ kc + 2 ^ 17 :=
  leafEnd_le g kc

theorem hsB_le : ∀ p, hsB B2C.fs p ≤ (p + 1) * 2 ^ 16
  | 0 => by have := fs_lt16 (tailKey hsLoopName); simp only [hsB]; omega
  | p + 1 => by
    have := fs_lt16 hsLoopName
    have := hsB_le p
    simp only [hsB]
    rw [show (p + 1 + 1) * 2 ^ 16 = (p + 1) * 2 ^ 16 + 2 ^ 16 by ring]
    omega

theorem tsEnd_le (h : ℕ → ℕ) (kc : ℕ) : tsEnd B2C.fs al h kc ≤ kc + 6 * 2 ^ 17 := by
  unfold tsEnd
  have h0 := leafEnd_le (al := al) (Link.tsNames.getD (h 0) "") kc
  have h1 := leafEnd_le (al := al) (Link.tsNames.getD (h 1) "") (leafEnd B2C.fs al (Link.tsNames.getD (h 0) "") kc)
  have h2 := leafEnd_le (al := al) (Link.tsNames.getD (h 2) "") (leafEnd B2C.fs al (Link.tsNames.getD (h 1) "")
    (leafEnd B2C.fs al (Link.tsNames.getD (h 0) "") kc))
  have h3 := leafEnd_le (al := al) (Link.tsNames.getD (h 3) "") (leafEnd B2C.fs al (Link.tsNames.getD (h 2) "")
    (leafEnd B2C.fs al (Link.tsNames.getD (h 1) "") (leafEnd B2C.fs al (Link.tsNames.getD (h 0) "") kc)))
  have h4 := leafEnd_le (al := al) (Link.tsNames.getD (h 4) "") (leafEnd B2C.fs al (Link.tsNames.getD (h 3) "")
    (leafEnd B2C.fs al (Link.tsNames.getD (h 2) "") (leafEnd B2C.fs al (Link.tsNames.getD (h 1) "")
      (leafEnd B2C.fs al (Link.tsNames.getD (h 0) "") kc))))
  have h5 := leafEnd_le (al := al) (Link.tsNames.getD (h 5) "") (leafEnd B2C.fs al (Link.tsNames.getD (h 4) "")
    (leafEnd B2C.fs al (Link.tsNames.getD (h 3) "") (leafEnd B2C.fs al (Link.tsNames.getD (h 2) "")
      (leafEnd B2C.fs al (Link.tsNames.getD (h 1) "") (leafEnd B2C.fs al (Link.tsNames.getD (h 0) "") kc)))))
  omega

theorem frontKc_le (p : ℕ) (h : ℕ → ℕ) (kc : ℕ) :
    frontKc B2C.fs al p h kc ≤ kc + (p + 1) * 2 ^ 16 + 10 * 2 ^ 17 := by
  unfold frontKc
  have e1 := allocFs_le (al := al) "hint_stream" kc
  have e2 := allocBase_le (al hsLoopName) (allocBase (al "hint_stream") kc + B2C.fs "hint_stream")
  have e3 := hsB_le p
  set a := allocBase (al hsLoopName) (allocBase (al "hint_stream") kc + B2C.fs "hint_stream") + hsB B2C.fs p
  have e4 := leafEnd_le (al := al) "g_power_of_word" a
  have e5 := leafEnd_le (al := al) "g_power_of_word" (leafEnd B2C.fs al "g_power_of_word" a)
  have e6 := tsEnd_le (al := al) h (leafEnd B2C.fs al "g_power_of_word" (leafEnd B2C.fs al "g_power_of_word" a))
  omega

theorem tpKc_le (hg : ℕ → ℕ) : ∀ t kc, tpKc B2C.fs al hg t kc ≤ kc + t * 2 ^ 17
  | 0, kc => by simp [tpKc]
  | t + 1, kc => by
    have h1 := tpKc_le hg t kc
    have h2 := leafEnd_le (al := al) (tpNames.getD (hg (t + 1)) "") (tpKc B2C.fs al hg t kc)
    show leafEnd B2C.fs al (tpNames.getD (hg (t + 1)) "") (tpKc B2C.fs al hg t kc) ≤ kc + (t + 1) * 2 ^ 17
    generalize leafEnd B2C.fs al (tpNames.getD (hg (t + 1)) "") (tpKc B2C.fs al hg t kc) = a at h2 ⊢
    generalize tpKc B2C.fs al hg t kc = b at h1 h2 ⊢
    rw [Nat.succ_mul, ← Nat.add_assoc]
    exact h2.trans (Nat.add_le_add_right h1 _)

theorem ph7Fp_le (wd kc : ℕ) : ph7Fp B2C.fs al wd kc ≤ kc + 2 ^ 17 + 15 := by
  unfold ph7Fp
  have := allocBase_le (al "link_rounds__L1_L0") (leafEnd B2C.fs al (seNames.getD (wd - 19) "") kc)
  have := leafEnd_le (al := al) (seNames.getD (wd - 19) "") kc
  omega

theorem ph8End_le (wd kc : ℕ) : ph8End B2C.fs al wd kc ≤ kc + 2 * 2 ^ 17 := by
  unfold ph8End
  have := allocFs_le (al := al) (isNames.getD (wd - 19) "") kc
  have := allocFs_le (al := al) (imNames.getD (wd - 19) "")
    (allocBase (al (isNames.getD (wd - 19) "")) kc + B2C.fs (isNames.getD (wd - 19) ""))
  omega

theorem ph11End_le (n h kc : ℕ) : ph11End B2C.fs al n h kc ≤ kc + 3 * 2 ^ 17 := by
  unfold ph11End
  have := leafEnd_le (al := al) (opsNames.getD n "") kc
  have := leafEnd_le (al := al) "packed_message__L144" (leafEnd B2C.fs al (opsNames.getD n "") kc)
  have := leafEnd_le (al := al) (tpNames.getD h "")
    (leafEnd B2C.fs al "packed_message__L144" (leafEnd B2C.fs al (opsNames.getD n "") kc))
  omega

end

namespace VsCtx

variable (x : VsCtx)

theorem frontEnd_le : x.frontEnd B2C.fs x.al ≤ x.cur + 982 + 256 * x.p + (x.p + 1) * 2 ^ 16 + 12 * 2 ^ 17 := by
  have hs := vsAllocSz_sum x.p
  have h1 := frontKc_le (al := x.al) x.p x.hg (x.cur + (vsAllocSz x.p).sum)
  have h2 := leafEnd_le (al := x.al) "assert_small_g_power" (frontKc B2C.fs x.al x.p x.hg (x.cur + (vsAllocSz x.p).sum))
  have h3 := leafEnd_le (al := x.al) "assert_small_g_power" (leafEnd B2C.fs x.al "assert_small_g_power"
    (frontKc B2C.fs x.al x.p x.hg (x.cur + (vsAllocSz x.p).sum)))
  unfold frontEnd
  split_ifs <;> omega

theorem fpc_le : x.fpc ≤ x.frontEnd B2C.fs x.al + 2 ^ 17 + 15 := by
  unfold fpc
  have := allocBase_le (x.al "certify_stack")
    (leafEnd B2C.fs x.al (cdNames.getD (widthOf x.lay - 19) "") (x.frontEnd B2C.fs x.al))
  have := leafEnd_le (al := x.al) (cdNames.getD (widthOf x.lay - 19) "") (x.frontEnd B2C.fs x.al)
  omega

theorem fpsp_le : x.fpsp ≤ x.ec 4 + 2 * 2 ^ 17 + 15 := by
  unfold fpsp
  have := allocBase_le (x.al "squeeze_packed")
    (leafEnd B2C.fs x.al (omName (1, 1)) (leafEnd B2C.fs x.al (spfName x.lay.stackLog) (x.ec 4)))
  have := leafEnd_le (al := x.al) (spfName x.lay.stackLog) (x.ec 4)
  have := leafEnd_le (al := x.al) (omName (1, 1)) (leafEnd B2C.fs x.al (spfName x.lay.stackLog) (x.ec 4))
  omega

/-- **The pinned ends' steps**: each non-leaf callee's end within its bound of its frame's cursor, `open_stacked`'s
within `2^β`. -/
structure EcSteps (β sl : ℕ) : Prop where
  s4 : x.ec 4 ≤ x.fpc + B2C.fs "certify_stack" + 2 ^ 20
  s6 : x.ec 6 ≤ x.fpsp + B2C.fs "squeeze_packed" + 2 ^ 22
  s7 : x.ec 7 ≤ ph7Fp B2C.fs x.al x.wdS (x.ec 6) + B2C.fs "link_rounds__L1_L0" + 2 ^ 22
  s9 : x.ec 9 ≤ allocBase (x.al (lrsNames.getD (chunkCount x.wdS - 6) "")) (ph8End B2C.fs x.al x.wdS (x.ec 7)) +
    B2C.fs (lrsNames.getD (chunkCount x.wdS - 6) "") + 2 ^ 23
  s12 : x.ec 12 = ph11End B2C.fs x.al x.nS x.h0S (x.ec 9)
  s13 : x.ec 13 ≤ allocBase (x.al (Link.ltNames.getD (x.wdS - 19) "")) (tpKc B2C.fs x.al x.hgS 5 (x.ec 12)) +
    B2C.fs (Link.ltNames.getD (x.wdS - 19) "") + 2 ^ 22
  s14 : x.ec 14 ≤ allocBase (x.al "verify_keccak") (x.ec 13) + B2C.fs "verify_keccak" + 2 ^ 24
  s15 : x.ec 15 ≤ allocBase (x.al "ring_switch_target") (x.ec 14) + B2C.fs "ring_switch_target" + 2 ^ 20
  s16 : x.ec 16 ≤ allocBase (x.al (Whir.openName sl)) (x.ec 15) + B2C.fs (Whir.openName sl) + 2 ^ β

/-- **`Hon.hend` from the pinned ends' steps**, `open_stacked`'s bound `β ≤ 39`, at most `32` chunks. -/
theorem hend_of_steps {β sl : ℕ} (hβ : β ≤ 39) (hp : x.p ≤ 32) (h : x.EcSteps β sl) :
    x.ec 16 ≤ x.cur + 3 * 2 ^ 38 := by
  have hb : 2 ^ β ≤ 2 ^ 39 := Nat.pow_le_pow_right (by norm_num) hβ
  have f0 := x.frontEnd_le
  have f1 := x.fpc_le
  have f2 := x.fpsp_le
  have a4 := fs_lt16 "certify_stack"
  have a6 := fs_lt16 "squeeze_packed"
  have a7 := fs_lt16 "link_rounds__L1_L0"
  have p7 := ph7Fp_le (al := x.al) x.wdS (x.ec 6)
  have p8 := allocFs_le (al := x.al) (lrsNames.getD (chunkCount x.wdS - 6) "") (ph8End B2C.fs x.al x.wdS (x.ec 7))
  have p8' := ph8End_le (al := x.al) x.wdS (x.ec 7)
  have p11 := ph11End_le (al := x.al) x.nS x.h0S (x.ec 9)
  have p13 := allocFs_le (al := x.al) (Link.ltNames.getD (x.wdS - 19) "") (tpKc B2C.fs x.al x.hgS 5 (x.ec 12))
  have p13' := tpKc_le (al := x.al) x.hgS 5 (x.ec 12)
  have p14 := allocFs_le (al := x.al) "verify_keccak" (x.ec 13)
  have p15 := allocFs_le (al := x.al) "ring_switch_target" (x.ec 14)
  have p16 := allocFs_le (al := x.al) (Whir.openName sl) (x.ec 15)
  have s4 := h.s4
  have s6 := h.s6
  have s7 := h.s7
  have s9 := h.s9
  have s12 := h.s12
  have s13 := h.s13
  have s14 := h.s14
  have s15 := h.s15
  have s16 := h.s16
  omega

end VsCtx

end
end LeanVM.Guest.B1.VsC
