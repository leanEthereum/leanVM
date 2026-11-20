/-
  Rv64mc.Spec.Layout.Constant

  The contracts of `constant(value: E) -> Form`, `col(index, exponent) -> Form` and `prod(a, b, exponent) -> Form`,
  each called with the result's slot (`sret`) in `a0`: `constant` with the value's limbs in `a1`, `a2`; `col` with
  `index`, `exponent` in `a1`, `a2`; `prod` with `a`, `b`, `exponent` in `a1`, `a2`, `a3`. Each writes its
  `Model` form (`constantRust`, `colRust`, `prodRust`) at `sret`, every buffer allocated by the call.
-/

import Rv64mc.Spec.Layout.Term
import Rv64mc.Spec.Layout.Gpow

namespace Rv64mc.Spec.Layout.Constant

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters LeanVM.Protocol.Verifier

/-- Its frame (32 bytes) and `Form::term`'s. -/
def need : Nat := 32 + Term.need

/-- `sret` a caller's to write. -/
def SretPre (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  env.Owned m (regs .x2) (regs .x10) Layouts.Form.byteSize

def Pre (env : Env) (value : E) (regs : Reg → Word) (m : MachineState) : Prop :=
  regs .x11 = (Model.limbs value).1 ∧ regs .x12 = (Model.limbs value).2 ∧ SretPre env regs m

/-- `sret` holds `f`, its buffers allocated by the call. -/
def Post (env : Env) (f : Form) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) :
    Prop :=
  FormIn (env.next m) (env.next m') m' (regs .x10) f

/-- **The contract of `constant`**, function `i` of `p`. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) : Prop :=
  ∀ value, Holds env p i need (Pre env value) (Post env (Model.constantRust value)) Term.Out

/-! ## `col`, `prod`: their stack a parameter, as `gpow`'s (`E::pow`'s) is -/

def ColPre (env : Env) (regs : Reg → Word) (m : MachineState) : Prop := SretPre env regs m

/-- **The contract of `col`**, function `i` of `p`, with `need` bytes of stack. -/
def colSpec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  Holds env p i need (ColPre env)
    (fun regs m r' m' => Post env (Model.colRust (regs .x11).toNat (regs .x12).toNat) regs m r' m') Term.Out

/-- **The contract of `prod`**, function `i` of `p`, with `need` bytes of stack. -/
def prodSpec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  Holds env p i need (ColPre env)
    (fun regs m r' m' => Post env (Model.prodRust (regs .x11).toNat (regs .x12).toNat (regs .x13).toNat) regs m r' m')
    Term.Out

end Rv64mc.Spec.Layout.Constant
