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
own calls in `C`. `Frames.lean` states them at `coreProgram`.
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

end
end LeanVM.Guest.B1
