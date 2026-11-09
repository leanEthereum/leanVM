/-
  LeanVM.Guest.Located.Interface

  What the guest's soundness assembly asks of B1, stated as a named proposition: `main`'s
  soundness over any call relation whose calls run at the frames a frame map gives, its witness a
  function of `main`'s valuation and the frame map.
-/

module

public import LeanVM.Guest.Located.Basic
public import LeanVM.Guest.B1.Main.Interface
public import LeanVM.Guest.B1.Main.Frames

/-!
# The located interface

`LeanVM.Guest.End.decodeV` reads the seed, the statement and the witness off a valid execution's
memory: `main`'s frame (`fp = 1`) and the frames of the calls `main` and its callees make, each
the first frame of the memory at which the callee's code holds on the call's words (`frameOf`,
a classical test of the guest's semantics: the callee's core IR body, its in-circuit checks
included, holding at the frame), the witness read there (`Statement/LeanVmGuest.lean`). The
deployed decoder `LeanVM.Guest.End.decode` replays the run instead (`Located/Replay.lean`).

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
decoded witness. `MainSoundV bytecode W` is that statement for `main`, with the witness
`W σ rd V` (B1-f's `decWitV σ rd V piOf`, with B1-d's child proof `piOf`): on a memory image whose
public input cells hold the digest `D`, a run of `main`'s body over `C` gives the seed
`decSeed σ` and the statement `decStmt σ rd` of digest `D`, and `W σ rd V` holds them.
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

/-- **`main`, soundly, its witness `W σ rd V`, over any call relation that unfolds along a frame
map** (B1-f's `main_sound_V bytecode piOf`, `W σ rd V = decWitV σ rd V piOf`): on a memory image
whose public input cells hold the digest `D`, every run of `main`'s body over `C` gives the seed
`decSeed σ` and the statement `decStmt σ rd` of digest `D`, which `W σ rd V` holds. -/
def MainSoundV (bytecode : List K) (W : Val → Reader → FrameMap → NodeWitness) : Prop :=
  bytecode.length = 2 ^ bytecodeVars →
  ∀ (rd : Reader), MemOk rd → ∀ (C : CallRel) (V : FrameMap), UnfoldsV rd C V →
    CallRel.Le C (coreProgram.Rel rd) →
  ∀ (D : Digest) (σ : Val), LoadHolds rd 1 0 (digestHalves D).1 →
    LoadHolds rd 1 1 (digestHalves D).2 →
    Stmt.HoldsList C rd σ Data.core0.body False (fun rs => rs = []) →
      statementDigest (decSeed σ) (decStmt σ rd) = D ∧
        NodeRelation bytecode (decSeed σ) (decStmt σ rd) (W σ rd V)

end
end LeanVM.Guest.Located
