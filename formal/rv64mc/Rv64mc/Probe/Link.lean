/-
  Rv64mc.Probe.Link

  What a relocatable template (`tmpl L`) knows of the program around it: each callee by its index and entry
  (`Callee`), each call site by the `auipc` value and `jalr` offset that reach it (`Site`), and the facts that tie
  them together (`Callee.WF`, `Site.WF`), which the link step proves of the concrete program. A probe of phase 0.

  ## Main results

  * `callee_site`: a call through a site reaches its callee
-/

import LprogRiscV.Lsym

namespace Rv64mc.Probe

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

/-- A function of the program: its index and its entry. -/
structure Callee where
  idx : Nat
  entry : Word

/-- A call site: the value its `auipc ra` writes and its `jalr ra`'s offset. -/
structure Site where
  hi : Word
  lo : Word

/-- The callee's index names a function at its entry. -/
def Callee.WF (p : Lprog (Op Reg) Reg) (c : Callee) : Prop := rvIsa.addrAt p c.idx = some c.entry

/-- The site reaches the callee's entry. -/
def Site.WF (s : Site) (c : Callee) : Prop := (s.hi + s.lo) &&& 0xfffffffffffffffe#64 = c.entry

/-- **A call through a site reaches its callee.** -/
theorem callee_site {p : Lprog (Op Reg) Reg} {c : Callee} {s : Site} (hc : c.WF p) (hs : s.WF c)
    {regs : Reg → Word} (h : regs .x1 = s.hi) :
    rvIsa.callee p regs
      (.indirect (.bin .and (.bin .add (.reg .x1) (.imm s.lo)) (.imm 0xfffffffffffffffe#64)) [c.idx]) =
      some c.idx := by
  simp only [Callee.WF, Site.WF] at hc hs
  simp [Isa.callee, List.find?, hc, Expr.eval, BinOp.eval, h, hs]

/-- The registers a function keeps (`s0`..`s11`). -/
def Saved : List Reg := [.x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27]

/-- **The ABI's part of a postcondition**: the stack pointer back at `top`, the saved registers kept, and the memory
    from `top` up kept. -/
def Abi (top : Word) (regs r' : Reg → Word) (m m' : MachineState) : Prop :=
  r' .x2 = top ∧ r' .x8 = regs .x8 ∧ r' .x9 = regs .x9 ∧ r' .x18 = regs .x18 ∧ r' .x19 = regs .x19 ∧
    r' .x20 = regs .x20 ∧ r' .x21 = regs .x21 ∧ r' .x22 = regs .x22 ∧ r' .x23 = regs .x23 ∧
    r' .x24 = regs .x24 ∧ r' .x25 = regs .x25 ∧ r' .x26 = regs .x26 ∧ r' .x27 = regs .x27 ∧
    ∀ a, top ≤ a → m'.getMem a = m.getMem a

/-- The precondition every contract here has: called from `ret`, with the stack at `top`. -/
def Entry (ret top : Word) (regs : Reg → Word) : Prop := regs .x1 = ret ∧ regs .x2 = top

end Rv64mc.Probe
