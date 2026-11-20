/-
  Rv64mc.Probe.EMul

  The contract of `<E as Mul>::mul`, proved once over any program `p` whose function `i` is the template
  `tmpl L` that `scripts/gen.py` writes for it, from its callees' contracts: the result is the Rust's Karatsuba over
  whatever `clmul` and `reduce` compute, and the ABI is kept (`Abi`). Nothing here names an address of the image, and
  the template changes only with the function's own code: moving it or its callees rebuilds the link step, not this.
-/

import Rv64mc.Gen.Tmpl.Verifier.Field.E.AsMul.Mul
import Rv64mc.Core.Abi

namespace Rv64mc.Probe.EMul

open RiscvZkvm.Rv64 Lprog Lprog.RiscV
open Rv64mc.Gen.Verifier.Field.E.AsMul.Mul (Link tmpl)

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

set_option maxHeartbeats 2000000 in
/-- **The contract of `<E as Mul>::mul`**, at any index `i` of any program holding its template, in any context:
    from its callees' contracts, the product `spec` and the ABI. The memory a callee keeps (`Abi`'s last part) is
    applied after `lsym`, by `simp` with `bv_omega` deciding each address comparison (`first`, so that a failed
    comparison is a failed rewrite and not an error). -/
theorem ok {E : Type} (c : Context rvIsa E) (p : Lprog (Op Reg) Reg) (L : Link) (i : Nat)
    (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    (hcl : rvIsa.Contract p c L.clmul.idx (fun ret top regs _ => Entry ret top regs) (ClmulPost cl))
    (hrd : rvIsa.Contract p c L.reduce.idx (fun ret top regs _ => Entry ret top regs) (ReducePost rd)) :
    rvIsa.Contract p c i Pre (Post cl rd) := by
  intro G N Q ret top rest regs m ⟨⟨hra, hsp⟩, hlo, hhi⟩ hk
  -- `addrAt` unfolded, so that `Link.WF`'s equations meet the callee's lookup as `simp` leaves it
  lsym hp with [hra, hsp, Lprog.Isa.addrAt, hL.clmul, hL.reduce, hL.s0, hL.s1, hL.s2, hL.s3, hL.s4, Entry, ClmulPost,
      ReducePost, Abi]
    using [hcl, hrd]
  -- the five calls' frames and stack pointers, by position in their postconditions (`ClmulPost`, `ReducePost`)
  all_goals
    have f1 := hret_1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    have f2 := hret_2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    have f3 := hret_3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    have f4 := hret_4.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    have f5 := hret.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    have e1 := hret_1.2.2.1
    have e2 := hret_2.2.2.1
    have e3 := hret_3.2.2.1
    have e4 := hret_4.2.1
    have e5 := hret.2.1
  · simp only [lsym_simp]
    simp (disch := (first | bv_omega | fail "no")) only [f1, f2, f3, f4, f5, MachineState.getMem_setMem_ne,
      MachineState.getMem_setMem_eq]
  · simp [lsym_simp]
  · apply hk
    simp only [Post, Abi, spec, lsym_simp]
    simp (disch := (first | bv_omega | fail "no")) only [f1, f2, f3, f4, f5, MachineState.getMem_setMem_ne,
      MachineState.getMem_setMem_eq]
    refine ⟨?_, ?_, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, ?_, ?_, ?_, ?_,
      fun a ha => ?_⟩
    · exact congr2 rd (by ac_rfl) (by ac_rfl)
    · rw [BitVec.xor_comm (regs .x11) (regs .x10), BitVec.xor_comm (regs .x13) (regs .x12)]
      exact congr2 rd (by ac_rfl) (by ac_rfl)
    rotate_left 4
    · simp (disch := (first | bv_omega | fail "no")) only [f1, f2, f3, f4, f5, MachineState.getMem_setMem_ne]
    all_goals simp only [hret, hret_1, hret_2, hret_3, hret_4]

end Rv64mc.Probe.EMul
