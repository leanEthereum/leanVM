/-
  LeanVM.Guest.Located.Interface

  The frame map of a memory: each call's valuation is its callee's first frame holding it, and the
  located relation unfolds along it.
-/

module

public import LeanVM.Guest.Located.Basic
public import LeanVM.Guest.B1.Main.Interface
public import LeanVM.Guest.B1.Main.Frames

/-!
# The located interface

`frameV L` reads each call's valuation off the first frame of the memory at which the callee's
code holds on the call's words (`frameOf`, a classical test of the guest's semantics: the callee's
core IR body, its in-circuit checks included, holding at the frame). The deployed decoder
`LeanVM.Guest.End.decode` replays the run instead (`Located/Replay.lean`).

The convention B1 states its witnesses in (agreed between B1-b, B1-d, B1-f and this assembly;
`B1.FrameMap`, `B1.UnfoldsV` in `B1/Main/Frames.lean`):

* a **frame map** `V : FrameMap` gives, for each call `f args rets`, a valuation of `f`'s values;
* a call relation `C` **unfolds along `V`** (`UnfoldsV rd C V`): every call of `C` is its
  callee's body at the valuation `V f args rets`, its own calls in `C`; and `C` lies below
  `coreProgram.Rel rd`;
* every witness is an explicit function of the valuation of the function that checks it and of
  `V`, every hypothesis on a callee quantifies over the calls of `C`.

On a memory `L` the located relation `RLg L` unfolds along `frameV L`, the valuation of the
call's frame (`unfoldsV_RL`), so a statement for every such `C` and `V` gives one about the
decoded witness.
-/

namespace LeanVM.Guest.Located

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Check
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.B1 LeanVM.Guest.B1.Main LeanVM.Guest.B1.Digest

@[expose] public section

/-- **The frame map of the memory `L`**: a call's valuation is its frame's (`frameOf`). -/
noncomputable def frameV {κ : ℕ} (L : MemoryImage κ) : FrameMap :=
  fun f args rets ↦ valAt L f (frameOf L f args rets)

/-- The located relation unfolds along the memory's frame map. -/
theorem unfoldsV_RL {κ : ℕ} (L : MemoryImage κ) : UnfoldsV L.read (RLg L) (frameV L) :=
  fun _ _ _ h ↦ by
    obtain ⟨fn, hf, hp, hb⟩ := bodyAt_frameOf h
    exact ⟨fn, hf, hp, hb⟩

end
end LeanVM.Guest.Located
