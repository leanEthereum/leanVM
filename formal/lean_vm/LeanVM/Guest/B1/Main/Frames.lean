/-
  LeanVM.Guest.B1.Main.Frames

  The witness convention of B1 (G6's decision, 2026-10-23): a call relation that unfolds at the
  valuations a frame map names.
-/

module

public import LeanVM.Guest.B1.Common.Basic
public import LeanVM.Guest.CoreData
public import LeanVM.Guest.B1.Main.FramesP

/-!
# Frame maps

A **frame map** `V : FrameMap` names, for every call `f args rets`, a valuation of `f`'s values
(on G6's side the valuation of the first frame of the memory whose code holds on the call's
words). `UnfoldsV rd C V`: every call of `C` holds because `f`'s body does at `V f args rets`, its
own calls in `C`. B1's witness statements name every witness as a function of the function's own
valuation and `V`, under `UnfoldsV rd C V` and `C ≤ coreProgram.Rel rd`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

/-- **A call relation that unfolds at the frame map `V`**, in `coreProgram`. -/
abbrev UnfoldsV (rd : Reader) (C : CallRel) (V : FrameMap) : Prop := UnfoldsVP coreProgram rd C V

end
end LeanVM.Guest.B1
