/-
  LeanVM.Guest.Count.VsWords

  `verify_sub`'s callees' words at the deployed frame sizes (`VsWords B2C.fs`), from the words
  certificates (`wSB`, `wSK`), B1-d's terminal words (`TermWordsFs`) and `verify_bus_gkr`'s and
  `verify_tables`' words interfaces (`Count/Fn/verify_bus_gkr`, `Count/Fn/verify_tables`), and the terminal's
  callees' weights (`Count/Fn/check_opening_terminal`).
-/

module

public import LeanVM.Guest.CoreRef
public import LeanVM.Guest.Count.StaticW
public import LeanVM.Guest.B1.VerifySub.WordsB
public import LeanVM.Guest.Count.Fn.verify_tables
public import LeanVM.Guest.Count.Fn.verify_bus_gkr
public import LeanVM.Guest.Count.Fn.check_opening_terminal
public import LeanVM.Guest.B1.Terminal.TermWordsFs
public import LeanVM.Guest.B1.Selectors.SharedWeight
public import LeanVM.Guest.Count.RatioV

namespace LeanVM.Guest.Count

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest

@[expose] public section

theorem ratio_le {w A t B : ℕ} (h : 1000 * w ≤ A * t) (ht : t ≤ B) : w ≤ A * B / 1000 :=
  (Nat.le_div_iff_mul_le (by norm_num)).mpr (by
    have := Nat.mul_le_mul_left A ht; rw [Nat.mul_comm w]; omega)

/-- `verify_sub`'s statically bounded callees (`vsStaticS`), each found by `wIdx` and checked. -/
theorem st_ok : (B1.VerifySub.vsStaticS.all fun g => wOkB (wIdx g) g) = true := by decide +kernel

theorem st_totalLe : ∀ g ∈ B1.VerifySub.vsStaticS, TotalLe coreProgram B2C.fs g (fun _ => wSB g) :=
  fun g hg => wSB_totalLe (List.all_eq_true.mp st_ok g hg)

/-- **`verify_sub`'s callees' words at `B2C.fs`.** -/
noncomputable def vsWords : B1.VerifySub.VsWords B2C.fs where
  Bg := wSB "g_power_of_word"
  hg := wSB_totalLe (j := wIdx "g_power_of_word") (by decide +kernel)
  Kst := wSB
  hst := st_totalLe
  vbg := vbgWords
  vt := vtWords
  B14 := 3204
  hl14 := B1.VerifySub.l14_totalLeOn_fs
  Beqc := 184
  K15 := 19
  Bcs := 157
  Brs := 8142
  hEqc := B1.VerifySub.eqc_totalLe_fs
  hL15 := B1.VerifySub.l15_totalLeOn_fs
  hCsF := B1.VerifySub.cs_fs_le
  hrs := B1.VerifySub.rs_totalLeOn_fs
  ωv := fun op => B2C.ωArm B2C.xmssArmC op
  vtW := vtWeights
  Weqc := termWeqc
  W15 := termW15
  Wst := termWst
  Wcs := kCsW
  Wrsw := termWrsw
  hEqcW := fun op => kuSB_weightLe (j := wIdx "eq_prefix_chain") (by cases op <;> decide +kernel)
  hStW := fun op => kuSB_weightLe (j := wIdx "selector_tables") (by cases op <;> decide +kernel)
  hCsW := cs_weightLe
  h15W := fun op rd t args rets hn hv hb ht => ratio_le (krVl15_weight op rd t args rets hn hv hb)
    (ht.trans (by rw [B1.VerifySub.fs_l15]; decide))
  hrswW := fun op rd t args rets hn hv hb ht => ratio_le (krVrsw_weight op rd t args rets hn hv hb)
    (ht.trans (by omega))

end
end LeanVM.Guest.Count
