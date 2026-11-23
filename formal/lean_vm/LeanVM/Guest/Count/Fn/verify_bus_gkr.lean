/-
  LeanVM.Guest.Count.Fn.verify_bus_gkr

  `verify_bus_gkr`'s words interface at the deployed frame sizes (`vbgWords`), from the words certificates
  (`wSK`) and its radix-four layers' bound (`gls_totalLeOn`), and its bound written out by the kernel (`vbgMaxV`).
-/

module

public import LeanVM.Guest.CoreRef
public import LeanVM.Guest.Count.StaticW
public import LeanVM.Guest.Count.Fast
public import LeanVM.Guest.B1.Gkr.VbgWords
public import LeanVM.Guest.B1.Gkr.GlsWords
public import LeanVM.Guest.KernelLit

namespace LeanVM.Guest.Count

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest

@[expose] public section

/-- The radix-four layers' loops' words per iteration (`gkr_layer__L{p}_L{o}_loop0`). -/
noncomputable def kGl (p o : ℕ) : ℕ :=
  wSK (B1.Tables.glLoopName p o) - B2C.fs (B1.Tables.glLoopName p o)

theorem gl_loops_totalLeOn : ∀ p < 4, ∀ o < 2,
    TotalLeOn coreProgram B2C.fs (B1.Tables.glLoopName p o) LoopPre
      (fun a => logG (a.getD 1 0) * kGl p o + B2C.fs (B1.Tables.glLoopName p o)) := by
  intro p hp o ho
  simpa only [kGl, wSKt_eq] using wSKt_totalLeOn (j := wIdx (B1.Tables.glLoopName p o))
    (f := B1.Tables.glLoopName p o) (by interval_cases p <;> interval_cases o <;> decide +kernel)

/-- **`verify_bus_gkr`'s words facts at `B2C.fs`.** -/
noncomputable def vbgWords : B1.Tables.VbgWords B2C.fs where
  KL := B1.Tables.glsKL B2C.fs kGl
  K8 := wSK (name% verify_bus_gkr_loop0) - B2C.fs (name% verify_bus_gkr_loop0)
  hL := B1.Tables.gls_totalLeOn B2C.fs_tailKey_le gl_loops_totalLeOn
  h8 := by simpa only [wSKt_eq] using wSKt_totalLeOn (j := idx% verify_bus_gkr_loop0) (by decide +kernel)

/-- `verify_bus_gkr`'s largest bound, at the search tree's lookups. -/
kernel_lit vbgMaxV : ℕ := B1.Tables.vbgMaxOf fsFast
  (B1.Tables.glsKL fsFast fun p o => wSKFast (B1.Tables.glLoopName p o) - fsFast (B1.Tables.glLoopName p o))
  (wSKFast (name% verify_bus_gkr_loop0) - fsFast (name% verify_bus_gkr_loop0))

theorem vbgWordsMax_eq : B1.Tables.vbgMax B2C.fs vbgWords = vbgMaxV := by
  unfold B1.Tables.vbgMax
  rw [← vbgMaxV_eq, fsFast_eq, wSKFast_eq]; rfl

end
end LeanVM.Guest.Count
