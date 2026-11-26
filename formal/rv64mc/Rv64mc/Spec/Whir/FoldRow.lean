/-
  Rv64mc.Spec.Whir.FoldRow

  The contract of `verifier::whir::fold_row(values: Vec<E>, x: K, rounds: &[FoldRound]) -> E`, which the compiled code
  calls with the `Vec`'s header (passed by value, so through a caller's copy) at `a0`, `x` in `a1` and the rounds as a
  pointer and a length in `a2`, `a3`: the result's limbs in `a0`, `a1` are `Model.foldRowRust`'s value wherever it
  has one (one value left; otherwise `assert_eq!` does not return). It folds in place, so it writes the `Vec`'s
  buffer (`Out`), which the caller gave away.
-/

import Rv64mc.Spec.Whir.RingWeight
import Rv64mc.Model.Whir

namespace Rv64mc.Spec.Whir.FoldRow

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters LeanVM.Protocol.Verifier Rv64mc.Spec.Whir.RingWeight

/-- **The `FoldRound`s `rs` from `a`**, round `k` at `a + 32 k`: its `alpha`'s limbs, then its `beta`'s. -/
def RoundsAt (m : MachineState) (a : Word) (rs : List FoldRound) : Prop :=
  a.toNat + Layouts.FoldRound.byteSize * rs.length < 2 ^ 64 ∧ ∀ k (h : k < rs.length),
    EAt m (a + BitVec.ofNat 64 (Layouts.FoldRound.byteSize * k + Layouts.FoldRound.alpha)) (Model.limbs rs[k].alpha) ∧
      EAt m (a + BitVec.ofNat 64 (Layouts.FoldRound.byteSize * k + Layouts.FoldRound.beta)) (Model.limbs rs[k].beta)

def Pre (env : Env) (values : List E) (rs : List FoldRound) (regs : Reg → Word) (m : MachineState) : Prop :=
  env.Owned m (regs .x2) (regs .x10) Layouts.Vec.byteSize ∧ EVecAt env m (regs .x10) values ∧
    regs .x13 = BitVec.ofNat 64 rs.length ∧ RoundsAt m (regs .x12) rs ∧
    env.Live m (regs .x12) (Layouts.FoldRound.byteSize * rs.length)

def Post (values : List E) (rs : List FoldRound) (regs : Reg → Word) (_m : MachineState) (r' : Reg → Word)
    (_m' : MachineState) : Prop :=
  ∀ v, Model.foldRowRust values (BF64.ofBitVec (regs .x11)) rs = some v →
    r' .x10 = (Model.limbs v).1 ∧ r' .x11 = (Model.limbs v).2

/-- It writes the `Vec`'s buffer. -/
def Out (regs : Reg → Word) (m : MachineState) (b : Word) : Prop :=
  InRange (vecPtr m (regs .x10)) (Layouts.E.byteSize * (vecLen m (regs .x10)).toNat) b

/-- **The contract of `fold_row`**, function `i` of `p` with `need` bytes of stack, for every row and rounds. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ values rs, Holds env p i need (Pre env values rs) (Post values rs) Out

end Rv64mc.Spec.Whir.FoldRow
