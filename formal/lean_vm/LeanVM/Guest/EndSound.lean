/-
  LeanVM.Guest.EndSound

  B2 for the deployed bytecode, from the certificates (`Sound.lean`) and B1's two statements about
  the core IR, and the end theorems with what remains of B1 as a hypothesis: `verify_sub`'s
  statement with its proof named (`B1.Main.SubSoundW`).
-/

module

public import LeanVM.Guest.EndKnow
public import LeanVM.Guest.Sound
public import LeanVM.Guest.B1.Bits.Tables
public import LeanVM.Guest.B1.VerifySub.Proof

/-!
# B2, proved, and the end theorems from B1's statements

* `expTablesSound`: `exponent_tables`' returns are the exponent tables (B1-a's
  `exponent_tables_holds`).
* `EndPending`: what the end theorems take until B1's ports to the f128 guest land:
  `verify_sub`'s `dims_g[g^0]` below `g^34` (`VsDimsKnown`), its `kappa_base` entries below `vsKbBound`
  (`VsKnown`), its statement with the proof `VerifySub.vsPiOf`, and the walks' cut obligations
  (`WalkKnown`; `walkKnown_proved`, `WalkKnownAll.lean`: whir's `QueriesWalk` and ostack's
  `oqMainWins_of_queryWinsOk` through the certificates' cells, and the GKR layers' parities).
* `b2SoundL_of`, `b2SoundL`: checker K's B2 (`b2_step`, `b2_mainL`), `b2SoundL` from
  `EndPending`.
* `soundHyps_of`: what `EndKnow`'s theorems rest on, from `VsKnown` and `main`'s soundness with
  the witness `W` (`Located.MainSoundV bytecode W`).
* `guest_knowledge_sub`, `decode_binds_sub`: the end theorems for the decoder `decodeV piOf`,
  from `verify_sub`'s statement with its proof named by `piOf` (`B1.Main.SubSoundW bytecode piOf`,
  B1-d's); `aggregate_sound_outer_sub` is in `EndRpm.lean`.
-/

namespace LeanVM.Guest.End

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Node LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash

@[expose] public section

/-- **`exponent_tables`' relation is the exponent tables** (B1-a's `exponent_tables_holds`). -/
theorem expTablesSound : ExpTablesSound := fun rd q h ↦
  (exponent_tables_holds rd [] [q]).mp h

/-- **What the end theorems take** until B1's ports to the f128 guest land
(`VerifySub.vsDimsKnown0_holds`, `VerifySub.vsKnown_holds`, `VerifySub.verify_sub_sound_w`): its
two cut obligations, and its statement with the proof `VerifySub.vsPiOf`; and the walks' cut
obligations (`walkKnown_proved`, `WalkKnownAll.lean`, whose whir walks are not yet on f128). -/
structure EndPending : Prop where
  /-- `dims_g[g^0]` below `g^34` at the call of `verify_tables`. -/
  dims : VsDimsKnown
  /-- `kappa_base`'s entries below `vsKbBound` at the call of `check_opening_terminal`. -/
  kb : VsKnown
  /-- `verify_sub`'s statement, its proof `VerifySub.vsPiOf`. -/
  sound : B1.Main.SubSoundW bytecode VerifySub.vsPiOf
  /-- The walks' cut obligations. -/
  walk : WalkKnown

/-- **B2, proved**, given `verify_sub`'s `dims_g` and `kappa_base` bounds and the walks'
obligations. -/
theorem b2SoundL_of (hvd : VsDimsKnown) (hvs : VsKnown) (hwalk : WalkKnown) : B2SoundL :=
  ⟨b2_step fun _ h2 hj ↦ cutsKnown_of hvd hvs hwalk h2 hj, b2_mainL expTablesSound⟩

/-- **B2, proved**, given `verify_sub`'s obligations. -/
theorem b2SoundL (h : EndPending) : B2SoundL := b2SoundL_of h.dims h.kb h.walk

variable {piOf : Reader → Val → FrameMap → Protocol.Compile.Proof}

/-- **Soundness of the deployed guest, its witness named**, from `verify_sub`'s statement. -/
theorem guest_knowledge_sub (hvd : VsDimsKnown) (hvs : VsKnown) (hwalk : WalkKnown)
    (hv : B1.Main.SubSoundW bytecode piOf) :
    MemoryGuestKnowledge guestProgram (decodeV piOf) :=
  guest_knowledge_V (b2SoundL_of hvd hvs hwalk) hv

/-- **What a consumer learns**, from `verify_sub`'s statement. -/
theorem decode_binds_sub (hvd : VsDimsKnown) (hvs : VsKnown) (hwalk : WalkKnown)
    (hv : B1.Main.SubSoundW bytecode piOf)
    {input : PublicInput} {t : Execution guestProgram} (hvt : ValidExecution guestProgram input t) {iv : Digest}
    {s₀ : NodeStatement} (hs₀ : s₀.deferredClaim.HasBytecodeShape bytecode)
    (hpub : publicInputDigest input = statementDigest iv s₀) :
    ((decodeV piOf t.memory).seed = iv ∧ (decodeV piOf t.memory).statement = s₀) ∨
      HasCollision (collisionCandidates (decodeV piOf t.memory).seed
        (decodeV piOf t.memory).statement iv s₀) :=
  decode_binds_V (b2SoundL_of hvd hvs hwalk) hv hvt hs₀ hpub

end
end LeanVM.Guest.End
