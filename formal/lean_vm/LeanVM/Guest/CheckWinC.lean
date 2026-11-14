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
`Link j G f cf C` carries a check over a function's own view `G` (`checkWinCF`, `CheckView.lean`)
to `WinOk` (`Link.win`).
`Checked.Plain j` says function `j`'s windows take nothing from obligations.
-/

namespace LeanVM.Guest.Check

open LeanVM.Guest LeanVM.Guest.Exec LeanVM.Guest.B2C

@[expose] public section

/-- `checkWin` of function `j`, the window's code read by `execWinC`. -/
noncomputable def checkWinC (G : Glob) (j : ℕ) (cf : Core.Fn) (C : Cert) (main : Bool) (i : ℕ) :
    Bool :=
  checkWinCF G (fnOf j) cf C main i

theorem checkWinC_eq (G : Glob) (j : ℕ) (cf : Core.Fn) (C : Cert) (main : Bool) (i : ℕ) :
    checkWinC G j cf C main i = checkWin G (fnOf j) cf C main i :=
  checkWinCF_eq (fnOf_wellChunked j) G cf C main i

/-- **A window's check**, decided by chunks. -/
theorem winOk_of_C {j i : ℕ} (h : checkWinC glob j (coreOf j) (certOf j) (j == 1) i = true) :
    WinOk j i := by
  unfold WinOk
  rwa [← checkWinC_eq]

/-- **Function `j` is `f`, of core IR `cf` and certificate `C`, and `G` gives its callees what
`glob` does**: a function's checks over its own view `G` (`Fn/<name>/Checked*.lean`) are
`glob`'s (`Link.win`). -/
structure Link (j : ℕ) (G : Glob) (f : CompiledFunction) (cf : Core.Fn) (C : Cert) : Prop where
  code : fnOf j = f
  core : coreOf j = cf
  cert : certOf j = C
  view : glob.restrict C.callees = G.restrict C.callees

/-- What a caller knows of a function of code `f`, core IR `cf` and certificate `C` (`sigOf`). -/
def sigFrom (f : CompiledFunction) (cf : Core.Fn) (C : Cert) : Sig :=
  ⟨cf.name, f.entryPc, cf.params.length, C.nret, C.facts.env, C.pre, C.post, C.mem, C.sem⟩

/-- A function's signature in `glob`, from its code, core IR and certificate. -/
theorem sig_of_link {j : ℕ} {f : CompiledFunction} {cf : Core.Fn} {C : Cert} {s : Sig} (hf : fnOf j = f)
    (hcf : coreOf j = cf) (hC : certOf j = C) (h : sigFrom f cf C = s) : glob.sig j = s := by
  show sigOf j = s
  rw [← h, ← hf, ← hcf, ← hC]
  rfl

/-- `glob` gives each of the functions `l` its signature there and counts it good. -/
def SigsOk (l : List (ℕ × Sig)) : Prop := ∀ p ∈ l, glob.sig p.1 = p.2 ∧ glob.good p.1 = true

theorem SigsOk.nil : SigsOk [] := List.forall_mem_nil _

theorem SigsOk.cons {c : ℕ} {s : Sig} {l : List (ℕ × Sig)} (h : glob.sig c = s) (hg : glob.good c = true)
    (t : SigsOk l) : SigsOk ((c, s) :: l) :=
  List.forall_mem_cons.mpr ⟨⟨h, hg⟩, t⟩

theorem SigsOk.append {l₁ l₂ : List (ℕ × Sig)} (h₁ : SigsOk l₁) (h₂ : SigsOk l₂) : SigsOk (l₁ ++ l₂) :=
  List.forall_mem_append.mpr ⟨h₁, h₂⟩

/-- A function's link from its view's callees `l`: `glob` gives each its signature there
(`restrict_ofSigs`). -/
theorem Link.of {j : ℕ} {l : List (ℕ × Sig)} {f : CompiledFunction} {cf : Core.Fn} {C : Cert}
    (hf : fnOf j = f) (hcf : coreOf j = cf) (hC : certOf j = C)
    (hl : SigsOk l)
    (hcs : C.callees = l.map (·.1)) : Link j (Glob.ofSigs l Data.jtTrie globSem) f cf C :=
  ⟨hf, hcf, hC, restrict_ofSigs hl rfl rfl hcs⟩

/-- **A window's check, over the function's view.** -/
theorem Link.win {j i : ℕ} {G : Glob} {f : CompiledFunction} {cf : Core.Fn} {C : Cert}
    {main : Bool} (h : Link j G f cf C) (hm : (j == 1) = main) (w : checkWinCF G f cf C main i = true) :
    WinOk j i := by
  have hc := fnOf_wellChunked j
  unfold WinOk
  rw [h.code] at hc
  rw [h.code, h.core, h.cert, hm, checkWin_congr h.view, ← checkWinCF_eq hc]
  exact w

end
end LeanVM.Guest.Check

namespace LeanVM.Guest.Checked

@[expose] public section

/-- Function `j`'s windows take nothing from obligations. -/
def Plain (j : ℕ) : Prop :=
  (certOf j).cuts.all (fun c ↦ c.known.isEmpty && c.knownIf.isEmpty && c.sems.isEmpty) = true

theorem plain_of_nil {j : ℕ} (h : (certOf j).cuts.length = 0) : Plain j := by
  unfold Plain
  rw [List.length_eq_zero_iff.mp h]
  rfl

end
end LeanVM.Guest.Checked
