/-
  Rv64mc.Tactic.Bench.EMul

  The contract of `<E as Mul>::mul`, proved once over any program `p` whose function `i` is the template
  `tmpl L`, from its callees' contracts: the result is the Rust's Karatsuba over whatever `clmul` and `reduce`
  compute, and the ABI is kept (`Abi`). Nothing here names an address of the image.
-/

import Rv64mc.Tactic.Bench.EMulTmpl
import Rv64mc.Tactic.Sym

namespace Rv64mc.Tactic.Bench.EMulAuto

open Rv64mc.Tactic.Bench.EMul

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

variable (cl : Word → Word → Word × Word) (rd : Word → Word → Word)

/-- What `<E as Mul>::mul` computes from the limbs `a0 + a1 y` and `b0 + b1 y`, given what `clmul` (low, high) and
    `reduce` (of low, high) compute: `crates/verifier`'s `Mul for E`. -/
def spec (a0 a1 b0 b1 : Word) : Word × Word :=
  let p0 := cl a0 b0
  let p1 := cl a1 b1
  let mid := cl (a0 ^^^ a1) (b0 ^^^ b1)
  let m0 := mid.1 ^^^ p0.1 ^^^ p1.1
  let m1 := mid.2 ^^^ p0.2 ^^^ p1.2
  (rd (p0.1 ^^^ p1.1) (p0.2 ^^^ p1.2), rd (m0 ^^^ (p1.1 <<< 1)) (m1 ^^^ ((p1.2 <<< 1) ||| (p1.1 >>> 63))))

/-- `clmul(a0, a1)`'s contract: the product's halves in `a0`, `a1`. -/
def ClmulPost (_ret top : Word) (regs : Reg → Word) (m : MachineState) (r' : Reg → Word) (m' : MachineState) :
    Prop :=
  r' .x10 = (cl (regs .x10) (regs .x11)).1 ∧ r' .x11 = (cl (regs .x10) (regs .x11)).2 ∧ Abi top regs r' m m'

/-- `reduce(a0, a1)`'s contract. -/
def ReducePost (_ret top : Word) (regs : Reg → Word) (m : MachineState) (r' : Reg → Word) (m' : MachineState) :
    Prop :=
  r' .x10 = rd (regs .x10) (regs .x11) ∧ Abi top regs r' m m'

/-- The precondition: called from `ret` with the stack at `top`, which has room below it. -/
def Pre (ret top : Word) (regs : Reg → Word) (_m : MachineState) : Prop :=
  Entry ret top regs ∧ 0x10000#64 ≤ top ∧ top ≤ 0x7fffffffffffffff#64

/-- The postcondition: the product in `a0`, `a1`, and the ABI kept. -/
def Post (_ret top : Word) (regs : Reg → Word) (m : MachineState) (r' : Reg → Word) (m' : MachineState) : Prop :=
  r' .x10 = (spec cl rd (regs .x10) (regs .x11) (regs .x12) (regs .x13)).1 ∧
    r' .x11 = (spec cl rd (regs .x10) (regs .x11) (regs .x12) (regs .x13)).2 ∧ Abi top regs r' m m'

/-- Equal arguments, equal values: `congrArg₂` without Mathlib. -/
theorem congr2 {α β γ : Type} (f : α → β → γ) {a a' : α} {b b' : β} (ha : a = a') (hb : b = b') :
    f a b = f a' b' := by subst ha hb; rfl

/-- **The contract of `<E as Mul>::mul`**, by `rv_auto`. -/
theorem ok {E : Type} (c : Context rvIsa E) (p : Lprog (Op Reg) Reg) (L : Link) (i : Nat)
    (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    (hcl : rvIsa.Contract p c L.clmul.idx (fun ret top regs _ => Entry ret top regs) (ClmulPost cl))
    (hrd : rvIsa.Contract p c L.reduce.idx (fun ret top regs _ => Entry ret top regs) (ReducePost rd)) :
    rvIsa.Contract p c i Pre (Post cl rd) := by
  rv_auto hp with [hL] using [hcl, hrd]
  all_goals simp only [spec]
  · exact congr2 rd (by ac_rfl) (by ac_rfl)
  · rw [BitVec.xor_comm (regs .x11), BitVec.xor_comm (regs .x13)]
    exact congr2 rd (by ac_rfl) (by ac_rfl)

end Rv64mc.Tactic.Bench.EMulAuto
