/-
  Rv64mc.Spec.Whir.RingSwitch

  The contracts of the rest of `ring_switch.rs`:

  * `ring_coefficients(f: &[E], g: &[E]) -> Vec<E>` (`sret` in `a0`, the slices in `a1`..`a4`): a fresh `Vec` of
    `Model.ringCoefficientsRust`'s coefficients;
  * `ring_target(s: &[E], f: &[E], g: &[E]) -> E` (the slices in `a0`..`a5`, the result's limbs in `a0`, `a1`):
    `Model.ringTargetRust`'s target (`f[p]` past the end does not return);
  * `ring_switch(point: Vec<E>, s: &[E], transcript) -> Result<(E, RingWeight), VerifierError>` (`sret` in `a0`, the
    point's `Vec` header, passed by value, at `a1`, `s` in `a2`, `a3`, the transcript in `a4`): the mirror's step
    `Model.ringSwitchRust`; where it returns `(target, w)` and `t'`, the slot holds `Ok` with the target and the
    weight (whose point is the `Vec` moved in), and the transcript is `t'`; where it fails, an `Err`.
-/

import Rv64mc.Spec.Whir.RingWeight
import Rv64mc.Spec.Whir.Basic
import Rv64mc.Spec.Multilinear.Basic

namespace Rv64mc.Spec.Whir.RingSwitch

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Whir.RingWeight Rv64mc.Spec.Transcript

def CoefficientsPre (env : Env) (f g : List E) (regs : Reg → Word) (m : MachineState) : Prop :=
  env.Owned m (regs .x2) (regs .x10) Layouts.Vec.byteSize ∧ ESlice env m (regs .x11) (regs .x12) f ∧
    ESlice env m (regs .x13) (regs .x14) g

def CoefficientsPost (env : Env) (f g : List E) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word)
    (m' : MachineState) : Prop :=
  Spec.Multilinear.FreshVecE env m m' (regs .x10) (Model.ringCoefficientsRust f g)

/-- **The contract of `ring_coefficients`**, function `i` of `p` with `need` bytes of stack. -/
def coefficientsSpec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ f g, Holds env p i need (CoefficientsPre env f g) (CoefficientsPost env f g) (SretOut Layouts.Vec.byteSize)

def TargetPre (env : Env) (s f g : List E) (regs : Reg → Word) (m : MachineState) : Prop :=
  ESlice env m (regs .x10) (regs .x11) s ∧ ESlice env m (regs .x12) (regs .x13) f ∧
    ESlice env m (regs .x14) (regs .x15) g

def TargetPost (s f g : List E) (_regs : Reg → Word) (_m : MachineState) (r' : Reg → Word) (_m' : MachineState) :
    Prop :=
  r' .x10 = (Model.limbs (Model.ringTargetRust s f g)).1 ∧ r' .x11 = (Model.limbs (Model.ringTargetRust s f g)).2

/-- **The contract of `ring_target`**, function `i` of `p` with `need` bytes of stack. -/
def targetSpec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ s f g, Holds env p i need (TargetPre env s f g) (TargetPost s f g)

/-- **The `Result<(E, RingWeight), VerifierError>` at `a`**: `Ok` with the target and the weight, or an `Err`. -/
def ResultAt (env : Env) (m : MachineState) (a : Word) : Option (E × Model.RingWeightRust) → Prop
  | some (target, w) => m.getMem (a + BitVec.ofNat 64 Layouts.ResultERingWeight.tagOffset) ≠
        BitVec.ofNat 64 Layouts.ResultERingWeight.Err.tag ∧
      EAt m (a + BitVec.ofNat 64 (Layouts.ResultERingWeight.Ok.f0 + Layouts.ERingWeight.f0)) (Model.limbs target) ∧
      RingWeightAt env m (a + BitVec.ofNat 64 (Layouts.ResultERingWeight.Ok.f0 + Layouts.ERingWeight.f1)) w
  | none => m.getMem (a + BitVec.ofNat 64 Layouts.ResultERingWeight.tagOffset) =
      BitVec.ofNat 64 Layouts.ResultERingWeight.Err.tag

def SwitchPre (env : Env) (t : Model.TState) (point s : List E) (regs : Reg → Word) (m : MachineState) : Prop :=
  TranscriptAt env m (regs .x14) t ∧ InFrame (regs .x2) (regs .x14) Layouts.Transcript.byteSize ∧
    InFrame (regs .x2) (regs .x10) Layouts.ResultERingWeight.byteSize ∧
    Apart (regs .x10) Layouts.ResultERingWeight.byteSize (regs .x14) Layouts.Transcript.byteSize ∧
    env.Owned m (regs .x2) (regs .x11) Layouts.Vec.byteSize ∧ EVecAt env m (regs .x11) point ∧
    ESlice env m (regs .x12) (regs .x13) s

def SwitchPost (env : Env) (t : Model.TState) (point s : List E) (regs : Reg → Word) (_m : MachineState)
    (_r' : Reg → Word) (m' : MachineState) : Prop :=
  match (Model.ringSwitchRust point s).run t with
  | some (r, t') => ResultAt env m' (regs .x10) (some r) ∧ TranscriptAt env m' (regs .x14) t'
  | none => ResultAt env m' (regs .x10) none

/-- What `ring_switch` writes besides its stack and its allocations: the result's slot and the transcript. -/
def SwitchOut (regs : Reg → Word) (_m : MachineState) (b : Word) : Prop :=
  InRange (regs .x10) Layouts.ResultERingWeight.byteSize b ∨ InRange (regs .x14) Layouts.Transcript.byteSize b

/-- **The contract of `ring_switch`**, function `i` of `p` with `need` bytes of stack, for every transcript state,
    point and slice. -/
def switchSpec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ t point s, Holds env p i need (SwitchPre env t point s) (SwitchPost env t point s) SwitchOut

end Rv64mc.Spec.Whir.RingSwitch
