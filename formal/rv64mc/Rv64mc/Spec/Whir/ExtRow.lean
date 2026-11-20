/-
  Rv64mc.Spec.Whir.ExtRow

  The contract of `verifier::whir::ext_row(words: &[K]) -> Vec<E>`: `sret` in `a0`, the words as a pointer and a
  length in `a1`, `a2`; a fresh `Vec` (`Spec.Multilinear.FreshVecE`) of `Model.extRowRust`'s values, the words'
  full pairs.
-/

import Rv64mc.Spec.Whir.Subspace
import Rv64mc.Spec.Multilinear.Basic

namespace Rv64mc.Spec.Whir.ExtRow

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters

def Pre (env : Env) (ws : List Word) (regs : Reg → Word) (m : MachineState) : Prop :=
  env.Owned m (regs .x2) (regs .x10) Layouts.Vec.byteSize ∧ SliceArgs WordsAt m (regs .x11) (regs .x12) ws ∧
    env.Live m (regs .x11) (Layouts.K.byteSize * ws.length)

def Post (env : Env) (ws : List Word) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) :
    Prop :=
  Spec.Multilinear.FreshVecE env m m' (regs .x10) (Model.extRowRust ws)

/-- **The contract of `ext_row`**, function `i` of `p` with `need` bytes of stack, for every row of words. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ ws, Holds env p i need (Pre env ws) (Post env ws) (SretOut Layouts.Vec.byteSize)

end Rv64mc.Spec.Whir.ExtRow
