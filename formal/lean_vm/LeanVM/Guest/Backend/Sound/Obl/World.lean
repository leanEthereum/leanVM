/-
  LeanVM.Guest.Backend.Sound.Obl.World

  A compiled program's obligations, for each function the analysis accepts.
-/

module

public import LeanVM.Guest.Backend.Sound.Obl.Post
public import LeanVM.Guest.Backend.Sound.Main

/-!
# Obligations of a compiled program

The precondition a table asks of callers is `UOf T R X`: the signature's bounds and relations
(`SigPre`, the relations' meaning `R`), and for the functions whose signature is marked `ext` a
further precondition `X` the analysis never discharges. In a compiled program whose `World.U` is that, the located call relation `W.C` meets
every postcondition the analysis checks (`World.post_of_chk`: a callee's frame was entered with
its precondition, `World.entered_pre`), and a function the analysis accepts has its obligations
(`World.obligations_of_chk`).
-/

namespace LeanVM.Guest.Backend.Obl

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **The precondition a table asks of callers**: the signature's bounds and relations (`R`)
and, for a function whose signature is marked `ext`, `X`. -/
def UOf (T : Tab) (R : Nat → Reader → E → Prop) (X : Reader → String → List E → Prop)
    (rd : Reader) (f : String) (a : List E) : Prop :=
  SigPre R rd (T.sig f) a ∧ ((T.sig f).ext = true → X rd f a)

variable {κ : ℕ} {W : World κ} {T : Tab} {R : Nat → Reader → E → Prop}
  {X : Reader → String → List E → Prop}

/-- A frame entered on the run was entered with its function's precondition. -/
theorem World.entered_pre (hW : W.Compiled) {f : String} {fp : K} {a r : List E}
    (h : W.Entered f fp a r) : W.U f a := by
  obtain ⟨-, ⟨-, -, tf', htf', hn', -, hU⟩, -, tf, htf, hn, rfl, -⟩ := h
  obtain rfl := eq_of_name (World.names hW).2.1 htf htf' (hn.trans hn'.symm)
  exact hU

/-- A call of the located relation is one of the core program's relation, its callee's frame
entered with its precondition. -/
theorem World.C_spec (hW : W.Compiled) {f : String} {a r : List E} (h : W.C f a r) :
    W.core.Rel W.L.read f a r ∧ W.U f a := by
  refine ⟨relL_le_rel _ f a r h, ?_⟩
  obtain ⟨fn, fp, -, hA, -, -⟩ := (relL_iff _ f a r).mp h
  exact World.entered_pre hW hA

/-- **The located call relation meets the postconditions** the analysis checks, and the
relations `xpost` names wherever the core program's relation does. -/
theorem World.post_of_chk (hW : W.Compiled) (hT : PowsOk T) (hκ : κ ≤ 32)
    (hU : W.U = UOf T R X W.L.read)
    (hP : ∀ fn ∈ W.core, (T.sig fn.name).post ≠ [] → chkFn T fn = true)
    (hxp : ∀ f a r, W.core.Rel W.L.read f a r → XPost R W.L.read (T.sig f) (a ++ r))
    (f : String) (a r : List E) (h : W.C f a r) :
    SigPost (T.sig f) (a ++ r) ∧ XPost R W.L.read (T.sig f) (a ++ r) :=
  post_relL hT hκ hP (fun f fp a r hA => by
    have := World.entered_pre hW hA
    rw [hU] at this
    exact this.1) hxp f a r h

theorem World.hU_of (hU : W.U = UOf T R X W.L.read) (f : String) (a : List E)
    (hx : (T.sig f).ext = false) (hs : SigPre R W.L.read (T.sig f) a) : W.U f a := by
  rw [hU]
  exact ⟨hs, fun hm => absurd (hx.symm.trans hm) Bool.false_ne_true⟩

/-- **A function the analysis accepts has its obligations**, in a compiled program whose
precondition is the table's and whose functions with a postcondition the analysis accepts. -/
theorem World.obligations_of_chk (hW : W.Compiled) (hT : PowsOk T) (hκ : κ ≤ 32)
    (hU : W.U = UOf T R X W.L.read)
    (hP : ∀ fn ∈ W.core, (T.sig fn.name).post ≠ [] → chkFn T fn = true)
    (hxp : ∀ f a r, W.core.Rel W.L.read f a r → XPost R W.L.read (T.sig f) (a ++ r))
    {tf : TracedFn} (htf : tf ∈ W.p) (h : chkFn T tf.core = true) : W.Obligations tf := by
  intro fp _ hpre
  rw [← World.params_vf hW htf fp, hU] at hpre
  exact fn_obl_of_chk hT hκ (World.hU_of hU) (World.post_of_chk hW hT hκ hU hP hxp) h hpre.1

/-- **A function the analysis accepts with facts from outside has its obligations**, each fact
`(i, h)` holding of every valuation that meets the function's precondition and satisfies its
first `i` statements under the core program's relation. -/
theorem World.obligations_of_chkF (hW : W.Compiled) (hT : PowsOk T) (hκ : κ ≤ 32)
    (hU : W.U = UOf T R X W.L.read)
    (hP : ∀ fn ∈ W.core, (T.sig fn.name).post ≠ [] → chkFn T fn = true)
    (hxp : ∀ f a r, W.core.Rel W.L.read f a r → XPost R W.L.read (T.sig f) (a ++ r))
    {tf : TracedFn} (htf : tf ∈ W.p) {facts : List (Nat × Hyp)}
    (h : chkFnF T facts tf.core = true)
    (hf : ∀ σ : Val, UOf T R X W.L.read tf.core.name (tf.core.params.map σ) → ∀ p ∈ facts,
      Stmt.HoldsList (W.core.Rel W.L.read) W.L.read σ (tf.core.body.take p.1) True
        (fun _ => True) → p.2.Holds R T W.L.read σ) :
    W.Obligations tf := by
  intro fp _ hpre
  rw [← World.params_vf hW htf fp, hU] at hpre
  exact fnF_obl_of_chk hT hκ (World.hU_of hU) (World.post_of_chk hW hT hκ hU hP hxp) h
    (fun p hp hl => hf _ hpre p hp
      (holdsList_mono (fun f a r h => relL_le_rel _ f a r h) _ id (fun _ h => h) hl)) hpre.1

end
end LeanVM.Guest.Backend.Obl
