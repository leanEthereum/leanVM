/-
  Rv64mc.Spec.Multilinear.MultilinearEvalK

  The contract of `verifier::multilinear::multilinear_eval::<K>(mle: &[K], point: &[E]) -> Result<E, VerifierError>`:
  the result at `sret` (`a0`), the table as a slice of words (`a1`, `a2`, `WordsAt`), the point as a slice (`a3`,
  `a4`, its elements' limbs in the heap); the result is `Model.multilinearEvalRust`'s over the table's `E` images
  (`Model.eNew`, `E::from(K)`), as `Spec.Whir.ResultEAt`.
-/

import Rv64mc.Spec.Whir.Basic
import Rv64mc.Model.Multilinear

namespace Rv64mc.Spec.Multilinear.MultilinearEvalK

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters

def Pre (env : Env) (ks : List Word) (pt : List E) (regs : Reg → Word) (m : MachineState) : Prop :=
  env.Owned m (regs .x2) (regs .x10) Layouts.ResultE.byteSize ∧ SliceArgs WordsAt m (regs .x11) (regs .x12) ks ∧
    env.Live m (regs .x11) (Layouts.K.byteSize * ks.length) ∧
    SliceArgs EListAt m (regs .x13) (regs .x14) (pt.map Model.limbs) ∧
    env.Live m (regs .x13) (Layouts.E.byteSize * pt.length)

def Post (ks : List Word) (pt : List E) (regs : Reg → Word) (_m : MachineState) (_r' : Reg → Word)
    (m' : MachineState) : Prop :=
  Whir.ResultEAt m' (regs .x10) (Model.multilinearEvalRust (ks.map Model.eNew) pt)

/-- **The contract of `multilinear_eval::<K>`**, function `i` of `p` with `need` bytes of stack (its frame is 128
    bytes; it calls `alloc`, `Vec::reserve`, `Scaler::new`, `Scaler::mul` and the panics), for every table and
    point. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ ks pt, Holds env p i need (Pre env ks pt) (Post ks pt) (Whir.SretOut Layouts.ResultE.byteSize)

end Rv64mc.Spec.Multilinear.MultilinearEvalK
