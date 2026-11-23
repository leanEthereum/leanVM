/-
  LeanVM.Guest.Count.VsBound

  **`verify_sub`'s words per child at the deployed instance**, at the child's opening arm:
  `vsFixed + osC (μ - 20)` (`vsBoundAt_eq`), its callees' bounds written out by the kernel
  (`kernel_lit`, through the search tree's lookups, `Count.Fast`), so that no number here changes
  with the guest; `open_stacked`'s per arm is `osC` (`Count/VsOs*`).
-/

module

public import LeanVM.Guest.Count.VsOsAll
public import LeanVM.Guest.Count.VsMax
public import LeanVM.Guest.Count.VsWordsOs
public import LeanVM.Guest.KernelLit

namespace LeanVM.Guest.Count

open LeanVM.Guest.B1.Whir

@[expose] public section

/-- `g_power_of_word`'s words. -/
kernel_lit vsBg : ℕ := wSBFast "g_power_of_word"

theorem bg_eq : vsWords.Bg = vsBg := by
  show wSB "g_power_of_word" = _
  rw [← vsBg_eq, wSBFast_eq]

/-- The frames `verify_sub`'s bound names. -/
kernel_lit fsVs : ℕ := fsFast "verify_sub"
kernel_lit fsL0 : ℕ := fsFast "log2_ceil_in_the_exponent__L0_L34"
kernel_lit fsAsg : ℕ := fsFast "assert_small_g_power"
kernel_lit fsRst : ℕ := fsFast "ring_switch_target"
kernel_lit fsCp : ℕ := fsFast "certify_placement"
kernel_lit fsL16 : ℕ := fsFast "log2_ceil_in_the_exponent__L16_L34"

theorem vs_frames : B2C.fs "verify_sub" = fsVs ∧ B2C.fs "log2_ceil_in_the_exponent__L0_L34" = fsL0 ∧
    B2C.fs "assert_small_g_power" = fsAsg ∧ B2C.fs "ring_switch_target" = fsRst ∧
    B2C.fs "certify_placement" = fsCp ∧ B2C.fs "log2_ceil_in_the_exponent__L16_L34" = fsL16 := by
  rw [← fsVs_eq, ← fsL0_eq, ← fsAsg_eq, ← fsRst_eq, ← fsCp_eq, ← fsL16_eq, fsFast_eq]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The statically bounded callees' words: the opening message, the squeeze dispatch's largest
arm. -/
kernel_lit wOm : ℕ := wSBFast "opening_message__L1_L1"
kernel_lit wSq : ℕ := B1.VerifySub.armMax wSBFast B1.VerifySub.squeezeNames

theorem vs_static : wSB "opening_message__L1_L1" = wOm ∧
    B1.VerifySub.armMax wSB B1.VerifySub.squeezeNames = wSq := by
  rw [← wOm_eq, ← wSq_eq, wSBFast_eq]
  exact ⟨rfl, rfl⟩

/-- The bus grind dispatch's largest arm. -/
kernel_lit busGrindMaxV : ℕ := B1.VerifySub.busGrindMax fsFast

theorem busGrindMax_eq : B1.VerifySub.busGrindMax B2C.fs = busGrindMaxV := by
  rw [← busGrindMaxV_eq, fsFast_eq]

/-- **`verify_sub`'s words per child but `open_stacked`'s**: its frame and buffers, and its
callees' bounds in call order (`B1.VerifySub.vsBsWith`). -/
kernel_lit vsFixed : ℕ :=
  fsVs + B1.VerifySub.vsOwnBufs + (vsBg + vsBg + (fsL0 + 2 * fsAsg) + (fsCp + B1.Tables.cpSizes.sum) + (fsL16 + 2 * fsAsg) +
    wSq + wOm + busGrindMaxV + vbgMaxV + vtMaxV + vkBoundV + (fsRst + B1.VerifySub.rstBufs + vsWords.B14) +
    termBoundV)

set_option maxRecDepth 100000 in
/-- **`verify_sub`'s words for a child of stack log `μ`** at the deployed instance: `vsFixed` and
`open_stacked` at the arm (`osC`), whatever the rate. -/
theorem vsBoundAt_eq {μ r : ℕ} (h1 : 20 ≤ μ) (h2 : μ ≤ 30) :
    B1.VerifySub.vsBoundAt vsWordsOs B1.VerifySub.vkBound μ r = vsFixed + osC (μ - 20) := by
  rewrite [B1.VerifySub.vsBoundAt.eq_1, B1.VerifySub.vsBsAt.eq_1, B1.VerifySub.vsBsWith.eq_1,
    show vsWordsOs.Bnd = wSBos from rfl, osBosAt_eq h1 h2,
    show vsWordsOs.toVsWords = vsWords from rfl, vbgMax_eq, vtMax_eq, bg_eq,
    vkBound_eq, termBound_eq, show vsWords.Kst = wSB from rfl, ← vsFixed_eq]
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := vs_frames
  obtain ⟨k1, k2⟩ := vs_static
  rewrite [h1, h2, h3, h4, h5, h6, k1, k2, busGrindMax_eq]
  simp only [List.sum_cons, List.sum_nil, B1.Whir.minOpenLog]
  generalize osC (μ - 20) = x
  clear * -
  omega

end
end LeanVM.Guest.Count
