/-
  Rv64mc.Spec.Multilinear.EqKernel

  The contract of `verifier::multilinear::eq_kernel(point: &[E]) -> Vec<E>`: the result's header at `sret` (`a0`),
  the point as a slice (`a1`, `a2`, its elements' limbs in the heap); the result is `Model.eqKernelRust`'s, in a
  fresh block (`FreshVecE`).
-/

import Rv64mc.Spec.Multilinear.Basic
import Rv64mc.Spec.Whir.Basic
import Rv64mc.Model.Multilinear

namespace Rv64mc.Spec.Multilinear.EqKernel

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters

def Pre (env : Env) (pt : List E) (regs : Reg → Word) (m : MachineState) : Prop :=
  env.Owned m (regs .x2) (regs .x10) Layouts.Vec.byteSize ∧
    SliceArgs EListAt m (regs .x11) (regs .x12) (pt.map Model.limbs) ∧
    env.Live m (regs .x11) (Layouts.E.byteSize * pt.length)

def Post (env : Env) (pt : List E) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) :
    Prop :=
  FreshVecE env m m' (regs .x10) (Model.eqKernelRust pt)

/-- **The contract of `eq_kernel`**, function `i` of `p` with `need` bytes of stack (its frame is 128 bytes; it
    calls `vec::from_elem`, `Scaler::new`, `Scaler::mul` and the panics), for every point. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ pt, Holds env p i need (Pre env pt) (Post env pt) (Whir.SretOut Layouts.Vec.byteSize)

end Rv64mc.Spec.Multilinear.EqKernel
