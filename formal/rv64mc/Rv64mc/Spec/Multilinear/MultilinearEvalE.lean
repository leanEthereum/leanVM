/-
  Rv64mc.Spec.Multilinear.MultilinearEvalE

  The contract of `verifier::multilinear::multilinear_eval::<E>(mle: &[E], point: &[E]) -> Result<E, VerifierError>`:
  the result at `sret` (`a0`), the table and the point as slices (`a1`, `a2` and `a3`, `a4`, their elements' limbs in
  the heap); the result is `Model.multilinearEvalRust`'s (`Spec.Whir.ResultEAt`: `Ok` where it returns a value,
  `Err` where the sizes are refused).
-/

import Rv64mc.Spec.Whir.Basic
import Rv64mc.Model.Multilinear

namespace Rv64mc.Spec.Multilinear.MultilinearEvalE

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters

def Pre (env : Env) (mle pt : List E) (regs : Reg → Word) (m : MachineState) : Prop :=
  env.Owned m (regs .x2) (regs .x10) Layouts.ResultE.byteSize ∧
    SliceArgs EListAt m (regs .x11) (regs .x12) (mle.map Model.limbs) ∧
    env.Live m (regs .x11) (Layouts.E.byteSize * mle.length) ∧
    SliceArgs EListAt m (regs .x13) (regs .x14) (pt.map Model.limbs) ∧
    env.Live m (regs .x13) (Layouts.E.byteSize * pt.length)

def Post (mle pt : List E) (regs : Reg → Word) (_m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  Whir.ResultEAt m' (regs .x10) (Model.multilinearEvalRust mle pt)

/-- **The contract of `multilinear_eval::<E>`**, function `i` of `p` with `need` bytes of stack (its frame is 160
    bytes; it calls `try_allocate_in`, `Vec::reserve`, `Scaler::new`, `Scaler::mul` and the panics), for every
    table and point. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ mle pt, Holds env p i need (Pre env mle pt) (Post mle pt) (Whir.SretOut Layouts.ResultE.byteSize)

end Rv64mc.Spec.Multilinear.MultilinearEvalE
