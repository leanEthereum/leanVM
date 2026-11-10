/-
  LeanVM.Guest.Count.VsBound

  **`verify_sub`'s words per child at the deployed instance**, at the child's candidate:
  `176056 + osC (candidate μ r)` (`vsBoundAt_eq`), its sixteen callees' bounds evaluated by the
  kernel (`open_stacked`'s per candidate, `Count/VsOs*`).
-/

module

public import LeanVM.Guest.Count.VsOsAll
public import LeanVM.Guest.Count.VsMax
public import LeanVM.Guest.Count.VsWordsOs

namespace LeanVM.Guest.Count

open LeanVM.Guest.B1.Whir

@[expose] public section

set_option maxRecDepth 100000 in
theorem bg_eq : vsWords.Bg = 49 := by
  show wSB "g_power_of_word" = 49
  rw [← wSBFast_eq]; decide +kernel

set_option maxRecDepth 100000 in
/-- The frames `verify_sub`'s bound names. -/
theorem vs_frames : B2C.fs "verify_sub" = 2032 ∧ B2C.fs "log2_ceil_in_the_exponent__L0_L34" = 35 ∧
    B2C.fs "assert_small_g_power" = 68 ∧ B2C.fs "ring_switch_target" = 268 ∧
    B2C.fs "certify_placement" = 356 ∧ B2C.fs "log2_ceil_in_the_exponent__L15_L34" = 36 := by
  rw [← fsFast_eq]; decide +kernel

set_option maxRecDepth 100000 in
/-- The statically bounded callees' words: the grind checks, the opening message, the squeeze
dispatch's largest arm. -/
theorem vs_static : wSB "grind_check__L15" = 53 ∧ wSB "opening_message__L1_L1" = 58 ∧
    wSB "grind_check__L14" = 53 ∧ B1.VerifySub.armMax wSB B1.VerifySub.squeezeNames = 498 := by
  rw [← wSBFast_eq]; decide +kernel

set_option maxRecDepth 100000 in
/-- The bus grind dispatch's largest arm with its grind check's frame. -/
theorem busGrindMax_eq : B1.VerifySub.busGrindMax B2C.fs = 61 := by
  unfold B1.VerifySub.busGrindMax
  rw [← fsFast_eq]; decide +kernel

set_option maxRecDepth 100000 in
/-- **`verify_sub`'s words for a child at candidate `candidate μ r`** at the deployed instance:
its frame `2032` and buffers `8706`, `g_power_of_word` (`49`, twice), the two `log2_ceil`
placements (`205`, `206`), `certify_placement` (`486`), the grind checks (`53`, twice), the
squeeze dispatch (`498`), the opening message (`58`), the bus grind dispatch (`61`),
`verify_bus_gkr` (`37006`), `verify_tables` (`37529`), `verify_keccak` (`56391`),
`ring_switch_target` (`3544`) and the terminal (`29130`), `176056` in all, and `open_stacked` at
the candidate (`osC`). -/
theorem vsBoundAt_eq {μ r : ℕ} (h : candidate μ r < 28) :
    B1.VerifySub.vsBoundAt vsWordsOs B1.VerifySub.vkBound μ r = 176056 + osC (candidate μ r) := by
  rw [B1.VerifySub.vsBoundAt.eq_1, B1.VerifySub.vsBsAt.eq_1, B1.VerifySub.vsBsWith.eq_1,
    show vsWordsOs.Bnd = osBnd from rfl, show vsWordsOs.Kr = (fun f => wSK f - B2C.fs f) from rfl,
    osBosAt_eq h, show vsWordsOs.toVsWords = vsWords from rfl, vbgMax_eq, vtMax_eq, bg_eq,
    vkBound_eq, termBound_eq, show vsWords.Kst = wSB from rfl, show vsWords.B14 = 3204 from rfl,
    show B1.Tables.cpSizes.sum = 130 from rfl]
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := vs_frames
  obtain ⟨k1, k2, k3, k4⟩ := vs_static
  rw [h1, h2, h3, h4, h5, h6, k1, k2, k3, k4, busGrindMax_eq]
  simp only [List.sum_cons, List.sum_nil]
  omega

end
end LeanVM.Guest.Count
