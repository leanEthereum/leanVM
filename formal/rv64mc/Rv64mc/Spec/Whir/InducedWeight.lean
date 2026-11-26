/-
  Rv64mc.Spec.Whir.InducedWeight

  The contract of `verifier::whir::induced_weight(message_log, queries: &[u64], query_weights: &[E], point: &[E])
  -> Result<E, VerifierError>`, which the compiled code calls with the result's slot (`sret`) in `a0`,
  `message_log` in `a1` and the three slices as pointers and lengths in `a2`..`a7`: it writes
  `Model.inducedWeightRust`'s answer at `sret` (`ResultEAt`), `Err(InducedBasisDimensions)` where the point's
  length is not `message_log`. `message_log < 64`, as every level's (`K(1 << i)` wraps past `63`).
-/

import Rv64mc.Spec.Whir.Basic
import Rv64mc.Model.Whir

namespace Rv64mc.Spec.Whir.InducedWeight

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters

def Pre (env : Env) (qs : List Word) (qw point : List E) (regs : Reg → Word) (m : MachineState) : Prop :=
  env.Owned m (regs .x2) (regs .x10) Layouts.ResultE.byteSize ∧ (regs .x11).toNat < 64 ∧
    SliceArgs WordsAt m (regs .x12) (regs .x13) qs ∧ env.Live m (regs .x12) (8 * qs.length) ∧
    SliceArgs EListAt m (regs .x14) (regs .x15) (qw.map Model.limbs) ∧
    env.Live m (regs .x14) (Layouts.E.byteSize * qw.length) ∧
    SliceArgs EListAt m (regs .x16) (regs .x17) (point.map Model.limbs) ∧
    env.Live m (regs .x16) (Layouts.E.byteSize * point.length)

def Post (qs : List Word) (qw point : List E) (regs : Reg → Word) (_m : MachineState) (_r' : Reg → Word)
    (m' : MachineState) : Prop :=
  ResultEAt m' (regs .x10) (Model.inducedWeightRust (regs .x11).toNat qs qw point)

/-- **The contract of `induced_weight`**, function `i` of `p` with `need` bytes of stack, for every three slices. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ qs qw point, Holds env p i need (Pre env qs qw point) (Post qs qw point) (SretOut Layouts.ResultE.byteSize)

end Rv64mc.Spec.Whir.InducedWeight
