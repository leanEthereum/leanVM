/-
  Rv64mc.Proof.Bus.BusGrindingBitsT

  `bus_grinding_bits` is total: it returns `BusGrindingBits.Post`'s bit count (`Spec.Bus.BusGrindingBits`), over any
  program holding its template, from `grinding_bits`' total contract (`GrindingBitsT`, a tail call). The partial proof
  (`BusGrindingBits.lean`) ported by `rv_autoT`.

  ## Main definitions

  * `specT`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Bus.BusGrindingBits
import Rv64mc.Proof.Transcript.GrindingBitsT

namespace Rv64mc.Proof.Bus.BusGrindingBitsT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Bus.BusGrindingBits Rv64mc.Proof.Bus.BusGrindingBits
open Rv64mc.Gen.Verifier.Bus.BusGrindingBits (Link tmpl)

/-- **The total contract of `bus_grinding_bits`**: `BusGrindingBits.spec`'s, as a `HoldsT`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need Pre Post

theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need : Nat} (hgb : Transcript.GrindingBitsT.specT env p L.grindingBits.idx need) : specT env p i need := by
  rv_autoT hp with [hL] using [hgb]
  rw [words_eq _ (by assumption)]
  rfl

end Rv64mc.Proof.Bus.BusGrindingBitsT

/-- info: 'Rv64mc.Proof.Bus.BusGrindingBitsT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Bus.BusGrindingBitsT.total
