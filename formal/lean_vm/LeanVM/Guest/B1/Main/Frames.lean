/-
  LeanVM.Guest.B1.Main.Frames

  The witness convention of B1 (G6's decision, 2026-10-23): a call relation that unfolds at the
  valuations a frame map names.
-/

module

public import LeanVM.Guest.B1.Common.Basic

/-!
# Frame maps

A **frame map** `V : FrameMap` names, for every call `f args rets`, a valuation of `f`'s values
(on G6's side the valuation of the first frame of the memory whose code holds on the call's
words). `UnfoldsV rd C V`: every call of `C` holds because `f`'s body does at `V f args rets`, its
own calls in `C`. B1's witness statements name every witness as a function of the function's own
valuation and `V`, under `UnfoldsV rd C V` and `C ≤ coreProgram.Rel rd`.

* `unfoldsV_rel`: for `coreProgram.Rel`, a frame map by choice (`relV`) unfolds it.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

/-- **A frame map**: a valuation for every call, by its callee and words. -/
abbrev FrameMap : Type := String → List E → List E → Val

/-- **A call relation that unfolds at the frame map `V`**: a call holds only when the callee's
body holds at the valuation `V f args rets`, its parameters the arguments, its calls in `C`. -/
def UnfoldsV (rd : Reader) (C : CallRel) (V : FrameMap) : Prop :=
  ∀ f args rets, C f args rets → ∃ fn, coreProgram.find? f = some fn ∧
    fn.params.map (V f args rets) = args ∧
    Stmt.HoldsList C rd (V f args rets) fn.body False (fun rs ↦ rs = rets)

open Classical in
/-- A frame map of `coreProgram.Rel`, by choice: a valuation holding the callee's body when one
does. -/
noncomputable def relV (rd : Reader) : FrameMap := fun f args rets =>
  if h : ∃ fn σ, coreProgram.find? f = some fn ∧ fn.params.map σ = args ∧
      Stmt.HoldsList (coreProgram.Rel rd) rd σ fn.body False (fun rs ↦ rs = rets)
  then Classical.choose (Classical.choose_spec h) else fun _ => 0

/-- **`coreProgram.Rel` unfolds at `relV`.** -/
theorem unfoldsV_rel (rd : Reader) : UnfoldsV rd (coreProgram.Rel rd) (relV rd) := by
  intro f args rets h
  obtain ⟨fn, hf, σ, hp, hb⟩ := (rel_iff coreProgram f args rets).mp h
  have hex : ∃ fn σ, coreProgram.find? f = some fn ∧ fn.params.map σ = args ∧
      Stmt.HoldsList (coreProgram.Rel rd) rd σ fn.body False (fun rs ↦ rs = rets) :=
    ⟨fn, σ, hf, hp, hb⟩
  have hs := Classical.choose_spec (Classical.choose_spec hex)
  have hfn : Classical.choose hex = fn := Option.some.inj (hs.1.symm.trans hf)
  refine ⟨fn, hf, ?_⟩
  unfold relV
  simp only [hex, ↓reduceDIte]
  rw [← hfn]
  exact hs.2

end
end LeanVM.Guest.B1
