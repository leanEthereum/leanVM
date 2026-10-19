/-
  LeanVM.Guest.CheckWinC

  A window's check, its code read past whole chunks first, decided by the kernel for the guest's
  functions.
-/

module

public import LeanVM.Guest.ExecC

/-!
# A window's check by chunks

`checkWinC G j` is `checkWin G (fnOf j)` with the window's code read by `B2C.execWinC`, which
skips the whole chunks before the window instead of walking the flattened code; the two agree
(`checkWinC_eq`, by `B2C.execWinC_eq`), so the kernel decides `WinOk` through it (`winOk_of_C`).
`Checked.Plain j` says function `j`'s windows take nothing from obligations.
-/

namespace LeanVM.Guest.Check

open LeanVM.Guest LeanVM.Guest.Exec LeanVM.Guest.B2C

@[expose] public section

/-- `checkWin` of function `j`, the window's code read by `execWinC`. -/
noncomputable def checkWinC (G : Glob) (j : ℕ) (cf : Core.Fn) (C : Cert) (main : Bool) (i : ℕ) :
    Bool :=
  match execWinC C.facts (fnOf j) (C.cutAt i).J (C.cutAt i).env (C.endAt (fnOf j) i) with
  | ⟨segs, _⟩ => listSeq segs fun segs ↦ (index segs).seq fun idx ↦ (C.locAt i).seq fun loc ↦
      C.contOk i && C.insOk (nth C.ins i []) && covOk loc (C.stmtsAt cf i) &&
      linkedWeak idx segs (C.fxAt G (fnOf j) cf main i segs idx loc).wJ (C.fxAt G (fnOf j) cf main i segs idx loc).wenv &&
      (bif i == 0 then runAt loc 2 cf.params && main == C.facts.fpOne else true) &&
      (match segAt (C.fxAt G (fnOf j) cf main i segs idx loc) (C.cutAt i).J
          (bookOf (C.cutAt i).facts .nil) (C.cutAt i).bnd with
        | some st => st.seg.env.sub Sym.beq (envOf (C.cutAt i).env) &&
            winEnd C i idx (chkL (C.fxAt G (fnOf j) cf main i segs idx loc) (C.stmtsAt cf i) st [])
        | none => false)

theorem checkWinC_eq (G : Glob) (j : ℕ) (cf : Core.Fn) (C : Cert) (main : Bool) (i : ℕ) :
    checkWinC G j cf C main i = checkWin G (fnOf j) cf C main i := by
  unfold checkWinC checkWin
  rw [execWinC_eq]
  rfl

/-- **A window's check**, decided by chunks. -/
theorem winOk_of_C {j i : ℕ} (h : checkWinC glob j (coreOf j) (certOf j) (j == 1) i = true) :
    WinOk j i := by
  unfold WinOk
  rwa [← checkWinC_eq]

end
end LeanVM.Guest.Check

namespace LeanVM.Guest.Checked

@[expose] public section

/-- Function `j`'s windows take nothing from obligations. -/
def Plain (j : ℕ) : Prop := (certOf j).cuts.all (fun c ↦ c.known.isEmpty && c.sems.isEmpty) = true

theorem plain_of_nil {j : ℕ} (h : (certOf j).cuts.length = 0) : Plain j := by
  unfold Plain
  rw [List.length_eq_zero_iff.mp h]
  rfl

end
end LeanVM.Guest.Checked
