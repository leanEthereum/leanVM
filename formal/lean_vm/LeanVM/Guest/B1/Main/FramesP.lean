/-
  LeanVM.Guest.B1.Main.FramesP

  The witness convention of B1 (G6's decision, 2026-10-23) for any program: a call relation that
  unfolds at the valuations a frame map names. No guest data.
-/

module

public import LeanVM.Guest.B1.Common.Basic

/-!
# Frame maps, for any program

A **frame map** `V : FrameMap` names, for every call `f args rets`, a valuation of `f`'s values.
`UnfoldsVP P rd C V`: every call of `C` holds because `f`'s body in `P` does at `V f args rets`, its
own calls in `C`; `unfoldsV_relP`: `P.Rel` unfolds at a frame map by choice (`relVP`). `Frames.lean`
states them at `coreProgram`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

/-- **A frame map**: a valuation for every call, by its callee and words. -/
abbrev FrameMap : Type := String → List E → List E → Val

/-- **A call relation that unfolds at the frame map `V`**: a call holds only when the callee's
body holds at the valuation `V f args rets`, its parameters the arguments, its calls in `C`. -/
def UnfoldsVP (P : Program) (rd : Reader) (C : CallRel) (V : FrameMap) : Prop :=
  ∀ f args rets, C f args rets → ∃ fn, P.find? f = some fn ∧
    fn.params.map (V f args rets) = args ∧
    Stmt.HoldsList C rd (V f args rets) fn.body False (fun rs ↦ rs = rets)

open Classical in
/-- A frame map of `P.Rel`, by choice: a valuation holding the callee's body when one does. -/
noncomputable def relVP (P : Program) (rd : Reader) : FrameMap := fun f args rets =>
  if h : ∃ fn σ, P.find? f = some fn ∧ fn.params.map σ = args ∧
      Stmt.HoldsList (P.Rel rd) rd σ fn.body False (fun rs ↦ rs = rets)
  then Classical.choose (Classical.choose_spec h) else fun _ => 0

/-- **`P.Rel` unfolds at `relVP P`.** -/
theorem unfoldsV_relP (P : Program) (rd : Reader) : UnfoldsVP P rd (P.Rel rd) (relVP P rd) := by
  intro f args rets h
  obtain ⟨fn, hf, σ, hp, hb⟩ := (rel_iff P f args rets).mp h
  have hex : ∃ fn σ, P.find? f = some fn ∧ fn.params.map σ = args ∧
      Stmt.HoldsList (P.Rel rd) rd σ fn.body False (fun rs ↦ rs = rets) :=
    ⟨fn, σ, hf, hp, hb⟩
  have hs := Classical.choose_spec (Classical.choose_spec hex)
  have hfn : Classical.choose hex = fn := Option.some.inj (hs.1.symm.trans hf)
  refine ⟨fn, hf, ?_⟩
  unfold relVP
  simp only [hex, ↓reduceDIte]
  rw [← hfn]
  exact hs.2

end
end LeanVM.Guest.B1
