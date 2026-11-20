/-
  Rv64mc.Spec.Layout.KeccakShape

  The contract of `verifier::layout::keccak_shape(table_log_heights: &[usize]) -> KeccakShape`: the slice in `a0`,
  `a1`; the shape's `log_steps`, `Model.keccakShapeOf`'s, in `a0` (its `depth` is the constant `KECCAK_DEPTH`, which
  the code does not return). A slice shorter than six panics.
-/

import Rv64mc.Core.Repr
import Rv64mc.Model.Layout

namespace Rv64mc.Spec.Layout.KeccakShape

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

/-- A leaf without a frame; its panic needs none. -/
def need : Nat := 0

def Pre (hs : List Nat) (regs : Reg → Word) (m : MachineState) : Prop :=
  SliceArgs WordsAt m (regs .x10) (regs .x11) (hs.map (BitVec.ofNat 64))

def Post (hs : List Nat) (_regs : Reg → Word) (_m : MachineState) (r' : Reg → Word) (_m' : MachineState) : Prop :=
  r' .x10 = BitVec.ofNat 64 (Model.keccakShapeOf hs).logSteps

/-- **The contract of `keccak_shape`**, function `i` of `p`, for every slice of heights. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) : Prop :=
  ∀ hs, Holds env p i need (Pre hs) (Post hs)

end Rv64mc.Spec.Layout.KeccakShape
