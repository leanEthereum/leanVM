/-
  LeanVM.Guest.Count.VsBound

  **`verify_sub`'s words per child at the deployed instance**, at the child's candidate:
  `197050 + osC (candidate μ r)` (`vsBoundAt_eq`), its callees' bounds evaluated by the kernel
  (`open_stacked`'s per candidate, `Count/VsOs*`).
-/

module

public import LeanVM.Guest.Count.VsOsAll
public import LeanVM.Guest.Count.VsMax
public import LeanVM.Guest.B1.VerifySub.CompleteBT

namespace LeanVM.Guest.Count

open LeanVM.Guest.B1.Whir

@[expose] public section

set_option maxRecDepth 100000 in
theorem bg_eq : vsWords.Bg = 49 := by
  show wSB "g_power_of_word" = 49
  rw [← wSBFast_eq]; decide +kernel

set_option maxRecDepth 100000 in
theorem ba_eq : vsWords.Ba = 10 := by
  show wSB "assert_canonical" = 10
  rw [← wSBFast_eq]; decide +kernel

set_option maxRecDepth 100000 in
/-- The frames `verify_sub`'s bound names. -/
theorem vs_frames : B2C.fs "verify_sub" = 1393 ∧ B2C.fs "log2_ceil_in_the_exponent__L0_L34" = 35 ∧
    B2C.fs "assert_small_g_power" = 68 ∧ B2C.fs "ring_switch_target" = 12 ∧
    B2C.fs "certify_placement" = 365 ∧ B2C.fs "log2_ceil_in_the_exponent__L15_L34" = 36 := by
  rw [← fsFast_eq]; decide +kernel

set_option maxRecDepth 100000 in
/-- **`verify_sub`'s words for a child at candidate `candidate μ r`** at the deployed instance:
its frame `1393`, its buffers `8675`, `g_power_of_word` (`49`, twice), the two `log2_ceil`
placements (`205`, `206`: their frames and `assert_small_g_power`'s twice), `assert_canonical`
(`10`, twice), `verify_bus_gkr` (`46339`), `verify_tables` (`37789`), `verify_keccak` (`65770`),
`ring_switch_target` (`5979`), `certify_placement` (`502`) and the terminal (`30074`), `197050`
in all, and `open_stacked` at the candidate (`osC`). -/
theorem vsBoundAt_eq {μ r : ℕ} (h : candidate μ r < 28) :
    B1.VerifySub.vsBoundAt vsWords B1.VerifySub.vkBound μ r = 197050 + osC (candidate μ r) := by
  rw [B1.VerifySub.vsBoundAt.eq_1, B1.VerifySub.vsBsAt.eq_1, vbgMax_eq, vtMax_eq, bg_eq, ba_eq,
    vkBound_eq, termBound_eq]
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := vs_frames
  rw [h1, h2, h3, h4, h5, h6, show vsWords.B14 = 5949 from rfl,
    show vsWords.Bnd = osBnd from rfl, show vsWords.Kr = (fun f => wSK f - B2C.fs f) from rfl,
    osBosAt_eq h,
    show B1.Tables.cpSizes.sum = 137 from rfl]
  simp only [List.sum_cons, List.sum_nil]
  omega

end
end LeanVM.Guest.Count
