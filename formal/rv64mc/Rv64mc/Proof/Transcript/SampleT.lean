/-
  Rv64mc.Proof.Transcript.SampleT

  `Sponge::sample` is total (`specT`): from a sponge `SpongeT` (`SpongeReprT`) its caller owns (`Owned`), it returns
  with the sponge `SpongeT` again (the ground tag cleared, the state permuted when none was waiting), writing nothing
  outside it and its stack, or ends the run with `a0 = 2` where `duplex` does. Safety only, as `DuplexT`: the
  partial contract's challenge (`Sample.lean`) is `duplex`'s permuted lanes.

  ## Main definitions

  * `PreT`, `PostT`, `specT`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Transcript.DuplexT
import Rv64mc.Spec.Transcript.Sample
import Rv64mc.Gen.Tmpl.Verifier.Transcript.Sponge.Sample

namespace Rv64mc.Proof.Transcript.SampleT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Transcript Rv64mc.Spec.Runtime
open Rv64mc.Proof.Transcript.SpongeReprT
open Rv64mc.Gen.Verifier.Transcript.Sponge.Sample (Link tmpl)

/-- The total precondition: the sponge `SpongeT`, and owned by the caller. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  SpongeT env m (regs .x10) ∧ env.Owned m (regs .x2) (regs .x10) Layouts.Sponge.byteSize

/-- The total postcondition: the sponge `SpongeT` again. -/
def PostT (env : Env) (regs : Reg → Word) (_m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  SpongeT env m' (regs .x10)

/-- **The total contract of `Sponge::sample`**: `PreT` to `PostT`, writing at most the sponge, or ending the run with
    `a0 = 2`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (PostT env) Sample.Out (Stop := AbortStop)

set_option rv_sym.heap true in
/-- **`Sponge::sample` is total.** -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needD : Nat} (hnD : 16 + needD ≤ need)
    (hdx : DuplexT.specT env p L.duplex.idx needD) : specT env p i need := by
  rv_autoT hp with [hL, (by omega : env.stackLimit.toNat + 16 ≤ top.toNat), hpre_13.top_le] using [hdx]
  all_goals exact Or.inl rfl

end Rv64mc.Proof.Transcript.SampleT

/-- info: 'Rv64mc.Proof.Transcript.SampleT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Transcript.SampleT.total
