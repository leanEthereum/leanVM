/-
  Rv64mc.Spec.Whir.RingWeight

  The contracts of `verifier::ring_switch::ring_weight(r: &[E], r_prime: &[E], coefficients: &[E]) -> E` (the three
  slices as pointers and lengths in `a0`..`a5`, the result's limbs in `a0`, `a1`: `Model.ringWeightRust`'s value
  wherever it has one; on lengths that differ `assert_eq!` does not return), and of `RingWeight::evaluate(&self,
  r_prime: &[E]) -> E` (`self` in `a0`, `r_prime` in `a1`, `a2`), which reads the weight's two `Vec`s
  (`RingWeightAt`) and tail-calls `ring_weight`.
-/

import Rv64mc.Core.Repr
import Rv64mc.Model.RingSwitch

namespace Rv64mc.Spec.Whir.RingWeight

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters

/-- The `E` slice `xs` passed in `a`, `n` (a pointer and a length), its elements live. -/
def ESlice (env : Env) (m : MachineState) (a n : Word) (xs : List E) : Prop :=
  SliceArgs EListAt m a n (xs.map Model.limbs) ∧ env.Live m a (Layouts.E.byteSize * xs.length)

def Pre (env : Env) (r rp cs : List E) (regs : Reg → Word) (m : MachineState) : Prop :=
  ESlice env m (regs .x10) (regs .x11) r ∧ ESlice env m (regs .x12) (regs .x13) rp ∧
    ESlice env m (regs .x14) (regs .x15) cs

def Post (r rp cs : List E) (_regs : Reg → Word) (_m : MachineState) (r' : Reg → Word) (_m' : MachineState) :
    Prop :=
  ∀ v, Model.ringWeightRust r rp cs = some v → r' .x10 = (Model.limbs v).1 ∧ r' .x11 = (Model.limbs v).2

/-- **The contract of `ring_weight`**, function `i` of `p` with `need` bytes of stack, for every three slices. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ r rp cs, Holds env p i need (Pre env r rp cs) (Post r rp cs)

/-- **The `Vec<E>` `xs` at `a`**, its elements live. -/
def EVecAt (env : Env) (m : MachineState) (a : Word) (xs : List E) : Prop :=
  ∃ ptr cap, VecAt EListAt m a ptr cap (xs.map Model.limbs) ∧ env.Live m ptr (Layouts.E.byteSize * xs.length)

/-- **The `RingWeight` `w` at `a`**: its point's and its coefficients' `Vec`s. -/
def RingWeightAt (env : Env) (m : MachineState) (a : Word) (w : Model.RingWeightRust) : Prop :=
  EVecAt env m (a + BitVec.ofNat 64 Layouts.RingWeight.point) w.point ∧
    EVecAt env m (a + BitVec.ofNat 64 Layouts.RingWeight.coefficients) w.coefficients

def EvaluatePre (env : Env) (w : Model.RingWeightRust) (rp : List E) (regs : Reg → Word) (m : MachineState) :
    Prop :=
  RingWeightAt env m (regs .x10) w ∧ ESlice env m (regs .x11) (regs .x12) rp

def EvaluatePost (w : Model.RingWeightRust) (rp : List E) (_regs : Reg → Word) (_m : MachineState)
    (r' : Reg → Word) (_m' : MachineState) : Prop :=
  ∀ v, w.evaluate rp = some v → r' .x10 = (Model.limbs v).1 ∧ r' .x11 = (Model.limbs v).2

/-- **The contract of `RingWeight::evaluate`**, function `i` of `p` with `need` bytes of stack, for every weight
    and opening point. -/
def evaluateSpec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ w rp, Holds env p i need (EvaluatePre env w rp) (EvaluatePost w rp)

end Rv64mc.Spec.Whir.RingWeight
