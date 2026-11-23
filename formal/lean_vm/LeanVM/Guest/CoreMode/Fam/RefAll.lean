/-
  LeanVM.Guest.CoreMode.Fam.RefAll

  What every family's proof over the honest instances uses: frames have a word, the root instance is
  `main`'s, and a fact carried down from the root to every honest instance.
-/

module

public import LeanVM.Guest.CoreMode.Fam.Ref
public import LeanVM.Guest.CoreMode.Fam.Down
public import LeanVM.Guest.Memory.HonestX

/-!
# Carried down from the root

`Res.fs_pos`: every frame has a word. `root_main`: the honest tree's root instance is `main`'s.
`insts_all`: a fact each instance passes to its callees (`Res.KidStep`) and that `main`'s instance has
holds at every honest instance (`Res.insts_down` from the root).
-/

namespace LeanVM.Guest.Res

open LeanVM.Guest

public section

theorem fs_pos (f : String) : 1 ≤ B2C.fs f := le_trans (by norm_num) (B2C.two_le_fs f)

end

end LeanVM.Guest.Res

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

public section

variable {r : Ref}

/-- **The root's instance is `main`'s.** -/
theorem root_main (hr : r.Ok) {J : Inst} {rest : List Inst}
    (he : r.T.insts B2C.fs coreProgram.loop B2C.H (0, r.T.block B2C.fs coreProgram.loop) r.hdr = J :: rest)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (hJt : J.t = .node f σ bufs kids) : f = "main" := by
  obtain ⟨J', rest', he', ht, -⟩ := head_insts (fs := B2C.fs) (lp := coreProgram.loop) (H := B2C.H) r.T
    (0, r.T.block B2C.fs coreProgram.loop) r.hdr
  rw [he'] at he
  obtain ⟨rfl, -⟩ := List.cons.inj he
  have hn := hr.name
  rw [← ht, hJt] at hn
  simpa only [Tree.name] using hn

/-- **A fact carried down to every honest instance**: passed from each instance to its callees, and had by
an instance of `main`. -/
theorem insts_all (hr : r.Ok) {Q : Inst → Prop}
    (hs : Res.KidStep coreProgram r.img.read B2C.H (honestInsts coreProgram B2C.fs B2C.H r.hdr r.T) Q)
    (hroot : ∀ J, (∀ f σ bufs kids, J.t = .node f σ bufs kids → f = "main") → Q J) :
    ∀ J ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T, Q J := by
  obtain ⟨rd, hH, hXh⟩ := hr.honest
  have hv := Covers.valid hH.toHonest hXh.covers
  exact Res.insts_down hs r.T _ r.hdr hv (fun J h ↦ h) fun J rest he ↦
    hroot J fun _ _ _ _ hJt ↦ root_main hr he hJt

end

end LeanVM.Guest.EndExec
