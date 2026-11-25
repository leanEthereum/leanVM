/-
  Rv64mc.Tactic.TStep

  Stepping `rvIsa.Total p stmtCtx (WinOk p) Q` goals, the judgement `HoldsT` asks of a function's
  body: the `Total.*` rules (`Total/Judgement.lean`) with the obligation `WinOk` discharged in
  each, and for a load or store the operation's result given, so that the side goals left are
  about the address: in a window (`inWindow`), aligned for its width, and, for a store, over no
  code (`Windows.noCodeAt`). SP1's range check follows from the window (`valid_of_inWindow`).

  `tstep hp` takes one step at a label, a register write or a jump, then computes the state's
  register values (`tnorm`), so that the register file stays a chain of writes of values over the
  entry's rather than of expressions over the previous files; `tsteps hp` as many as it can;
  `tcond hp as h` steps a branch into its two outcomes, each with the comparison's value as a
  hypothesis `h`. A load, a store, a call, a return and an `ECALL` are left to the rules here
  and to `HoldsT.call`, `Aborts.call`, `Total.ext_done`.

  ## Main results

  * `label`, `set`, `goto`, `cond`, `ret`: the rules with `WinOk` discharged
  * `ld8`, `lbu`, `sd8`, `sb`: a load or store of a doubleword or a byte
  * `tnorm`, `tstep`, `tsteps`, `tcond`
-/

import Rv64mc.Core.HoldsT

namespace Rv64mc.TotalRv

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

variable {p : Lprog (Op Reg) Reg} {fd : Lfundef (Op Reg) Reg} {fn pc : Nat} {rv top : Word}
  {rest : List Frame} {regs : Reg → Word} {m : MachineState} {Q : State rvIsa → Prop}

/-- An access in a window passes SP1's range check. -/
theorem valid_of_inWindow {a : Word} {w : Nat} (h : inWindow a w = true) : isValidMemAddrSp1 a = true := by
  have := inWindow_iff.1 h
  exact decide_eq_true (show a.toNat < SP1_MAX_MEMORY by unfold SP1_MAX_MEMORY; omega)

theorem label {kd : LabelKind} {l : LLabel} (hf : p[fn]? = some fd) (hi : fd.body[pc]? = some (.Llabel kd l))
    (h : rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨fn, pc + 1, rv, top⟩ :: rest, regs, m⟩) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ :=
  Total.label hf hi (WinOk.of_ne hf hi nofun) h

theorem set {d : Reg} {e : Expr Reg} (hf : p[fn]? = some fd) (hi : fd.body[pc]? = some (.Lopn (.set d e)))
    (h : rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨fn, pc + 1, rv, top⟩ :: rest, updReg regs d (e.eval regs), m⟩) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ :=
  Total.set hf hi (WinOk.of_set hf hi) h

theorem goto {l : LLabel} (hf : p[fn]? = some fd) (hi : fd.body[pc]? = some (.Lgoto l)) {j : Nat}
    (hl : labelIdx fd.body l = some j) (h : rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨fn, j, rv, top⟩ :: rest, regs, m⟩) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ :=
  Total.goto hf hi hl (WinOk.of_ne hf hi nofun) h

theorem cond {cnd : LOperand Reg} {l : LLabel} (hf : p[fn]? = some fd) (hi : fd.body[pc]? = some (.Lcond cnd l))
    {b : Bool} (hc : condEval cnd regs = some b) {j : Nat} (hl : labelIdx fd.body l = some j)
    (ht : b = true → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨fn, j, rv, top⟩ :: rest, regs, m⟩)
    (hn : b = false → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨fn, pc + 1, rv, top⟩ :: rest, regs, m⟩) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ :=
  Total.cond hf hi hc hl (WinOk.of_ne hf hi nofun) ht hn

theorem ret (hf : p[fn]? = some fd) (hi : fd.body[pc]? = some .Lret) (hra : regs .x1 = rv) (hsp : regs .x2 = top)
    (h : rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, regs, m⟩) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ :=
  Total.ret hf hi hra hsp (WinOk.of_ne hf hi nofun) h

/-- A doubleword load, in a window and 8-byte aligned. -/
theorem ld8 {d : Reg} {a : Expr Reg} (hf : p[fn]? = some fd)
    (hi : fd.body[pc]? = some (.Lopn (.load d .b8 false a))) (hw : inWindow (a.eval regs) 8 = true)
    (hal : (a.eval regs).toNat % 8 = 0)
    (h : rvIsa.Total p stmtCtx (WinOk p) Q
      ⟨⟨fn, pc + 1, rv, top⟩ :: rest, updReg regs d (m.getMem (a.eval regs)), m⟩) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ :=
  Total.opn hf hi
    (by simp [Op.eval, rvMem, valid_of_inWindow hw, alignedFor, isAligned8, hal, Width.bytes])
    (WinOk.of_opn hf hi (by simpa [opWin, Width.bytes] using hw)) h

/-- A byte load, zero-extended, in a window. -/
theorem lbu {d : Reg} {a : Expr Reg} (hf : p[fn]? = some fd)
    (hi : fd.body[pc]? = some (.Lopn (.load d .b1 false a))) (hw : inWindow (a.eval regs) 1 = true)
    (h : rvIsa.Total p stmtCtx (WinOk p) Q
      ⟨⟨fn, pc + 1, rv, top⟩ :: rest, updReg regs d ((m.getByte (a.eval regs)).zeroExtend 64), m⟩) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ :=
  Total.opn hf hi (by simp [Op.eval, rvMem, valid_of_inWindow hw, alignedFor, Width.bytes])
    (WinOk.of_opn hf hi (by simpa [opWin, Width.bytes] using hw)) h

/-- A doubleword store, in a window, 8-byte aligned and over no code. -/
theorem sd8 {a e : Expr Reg} (hf : p[fn]? = some fd) (hi : fd.body[pc]? = some (.Lopn (.store .b8 a e)))
    (hw : inWindow (a.eval regs) 8 = true) (hal : (a.eval regs).toNat % 8 = 0)
    (hnc : noCodeAt m (a.eval regs) 8 = true)
    (h : rvIsa.Total p stmtCtx (WinOk p) Q
      ⟨⟨fn, pc + 1, rv, top⟩ :: rest, regs, m.setMem (a.eval regs) (e.eval regs)⟩) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ :=
  Total.opn hf hi
    (by simp [Op.eval, rvMem, valid_of_inWindow hw, alignedFor, isAligned8, hal, hnc, Width.bytes])
    (WinOk.of_opn hf hi (by simpa [opWin, Width.bytes] using hw)) h

/-- A byte store, in a window and over no code. -/
theorem sb {a e : Expr Reg} (hf : p[fn]? = some fd) (hi : fd.body[pc]? = some (.Lopn (.store .b1 a e)))
    (hw : inWindow (a.eval regs) 1 = true) (hnc : noCodeAt m (a.eval regs) 1 = true)
    (h : rvIsa.Total p stmtCtx (WinOk p) Q
      ⟨⟨fn, pc + 1, rv, top⟩ :: rest, regs, m.setByte (a.eval regs) ((e.eval regs).truncate 8)⟩) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ :=
  Total.opn hf hi (by simp [Op.eval, rvMem, valid_of_inWindow hw, alignedFor, hnc, Width.bytes])
    (WinOk.of_opn hf hi (by simpa [opWin, Width.bytes] using hw)) h

end Rv64mc.TotalRv

/-- The state's register values computed: each `Expr.eval` of a register write unfolded, and a read of a register
    file through its writes resolved, so that the register file stays a chain of writes of values over the entry's.
    Also the side goals' addresses, and `noCodeAt` through a store. -/
macro "tnorm" : tactic => `(tactic| simp only [Lprog.Expr.eval, Lprog.BinOp.eval, Lprog.updReg_apply,
  reduceCtorEq, ↓reduceIte, BitVec.add_zero, BitVec.zero_add, Lprog.RiscV.noCodeAt_setMem])

/-- One step of a `rvIsa.Total … (WinOk p)` goal at a label, a register write or a jump of the template `hp`, then
    `tnorm`. -/
macro "tstep " hp:term : tactic => `(tactic| (first
  | refine Rv64mc.TotalRv.label $hp rfl ?_
  | refine Rv64mc.TotalRv.set $hp rfl ?_
  | refine Rv64mc.TotalRv.goto $hp rfl rfl ?_) <;> try tnorm)

/-- `tstep` while it applies. -/
macro "tsteps " hp:term : tactic => `(tactic| repeat tstep $hp)

/-- A branch of the template `hp`: two goals, `h` the comparison's value, true (the jump) and false, with `tnorm` run
    on it. -/
macro "tcond " hp:term " as " h:ident : tactic =>
  `(tactic| (refine Rv64mc.TotalRv.cond $hp rfl rfl rfl (fun $h => ?_) (fun $h => ?_) <;>
    try simp only [Lprog.Expr.eval, Lprog.BinOp.eval, Lprog.updReg_apply, reduceCtorEq, ↓reduceIte, BitVec.add_zero,
      BitVec.zero_add] at $h:ident))
