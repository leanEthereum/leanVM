/-
  LeanVM.Guest.Backend.Sound.Obl.World

  A compiled program's obligations, for each function the analysis accepts.
-/

module

public import LeanVM.Guest.Backend.Sound.Obl.Post
public import LeanVM.Guest.Backend.Sound.Main

/-!
# Obligations of a compiled program

The precondition a table asks of callers is `UOf T X`: the signature's bounds (`SigPre`), and
for the functions the table lists in `xs` a further precondition `X` the analysis never
discharges. In a compiled program whose `World.U` is that, the located call relation `W.C` meets
every postcondition the analysis checks (`World.post_of_chk`: a callee's frame was entered with
its precondition, `World.entered_pre`), and a function the analysis accepts has its obligations
(`World.obligations_of_chk`).
-/

namespace LeanVM.Guest.Backend.Obl

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **The precondition a table asks of callers**: the signature's bounds and, for a function the
table lists in `xs`, `X`. -/
def UOf (T : Tab) (X : String → List E → Prop) (rd : Reader) (f : String) (a : List E) : Prop :=
  SigPre rd (T.sig f) a ∧ (f ∈ T.xs → X f a)

variable {κ : ℕ} {W : World κ} {T : Tab} {X : String → List E → Prop}

/-- A frame entered on the run was entered with its function's precondition. -/
theorem World.entered_pre (hW : W.Compiled) {f : String} {fp : K} {a r : List E}
    (h : W.Entered f fp a r) : W.U f a := by
  obtain ⟨-, ⟨-, -, tf', htf', hn', -, hU⟩, -, tf, htf, hn, rfl, -⟩ := h
  obtain rfl := eq_of_name (World.names hW).2.1 htf htf' (hn.trans hn'.symm)
  exact hU

/-- **The located call relation meets the postconditions** the analysis checks. -/
theorem World.post_of_chk (hW : W.Compiled) (hT : PowsOk T) (hκ : κ ≤ 32)
    (hU : W.U = UOf T X W.L.read)
    (hP : ∀ fn ∈ W.core, (T.sig fn.name).post ≠ [] → chkFn T fn = true) (f : String)
    (a r : List E) (h : W.C f a r) : SigPost (T.sig f) (a ++ r) :=
  post_relL hT hκ hP (fun f fp a r hA => by
    have := World.entered_pre hW hA
    rw [hU] at this
    exact this.1) f a r h

/-- **A function the analysis accepts has its obligations**, in a compiled program whose
precondition is the table's and whose functions with a postcondition the analysis accepts. -/
theorem World.obligations_of_chk (hW : W.Compiled) (hT : PowsOk T) (hκ : κ ≤ 32)
    (hU : W.U = UOf T X W.L.read)
    (hP : ∀ fn ∈ W.core, (T.sig fn.name).post ≠ [] → chkFn T fn = true)
    {tf : TracedFn} (htf : tf ∈ W.p) (h : chkFn T tf.core = true) : W.Obligations tf := by
  intro fp _ hpre
  rw [← World.params_vf hW htf fp, hU] at hpre
  exact fn_obl_of_chk hT hκ
    (fun f a hx hs => by rw [hU]; exact ⟨hs, fun hm => absurd hm hx⟩)
    (World.post_of_chk hW hT hκ hU hP) h hpre.1

end
end LeanVM.Guest.Backend.Obl
