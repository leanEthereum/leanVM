/-
  Rv64mc.Tactic.SymTest

  Checks of the executor on small goals: `through` passing a loop's head (`rv_symT`), and `rv_close` on an equation
  whose left side is not an application. The second fails only where a panic aborts (`LEAN_ABORT_ON_PANIC=1`): a
  panic is written to the process's standard error, not to Lean's messages.
-/

import Rv64mc.Tactic.SymT

namespace Rv64mc.Tactic.SymTest

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

noncomputable section

/-- Label `0` (at 1) is the target of the backward jump at 4, and a path first reaches 4 by the forward jump at 0. -/
def loopy : Lfundef (Op Reg) Reg :=
  { name := "loopy", addr := 0, depth := 0,
    body := [LinstrR.Lgoto 1, LinstrR.Llabel (LabelKind.internal) 0, LinstrR.Lopn Op.skip,
      LinstrR.Llabel (LabelKind.internal) 1, LinstrR.Lgoto 0] }

variable {p : Lprog (Op Reg) Reg} {i : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame}
  {R : Reg → Word} {M : MachineState}

/-- Without `through`, the run stops at the loop's head, 1. -/
example (hp : p[i]? = some loopy) (h1 : rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 1, ret, top⟩ :: rest, R, M⟩) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 0, ret, top⟩ :: rest, R, M⟩ := by
  rv_symT hp
  exact h1

/-- `through [1]` passes it, and the run stops where the path comes back to 3. -/
example (hp : p[i]? = some loopy) (h3 : rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 3, ret, top⟩ :: rest, R, M⟩) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 0, ret, top⟩ :: rest, R, M⟩ := by
  rv_symT hp through [1]
  exact h3

/-- `through *` too. -/
example (hp : p[i]? = some loopy) (h3 : rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 3, ret, top⟩ :: rest, R, M⟩) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 0, ret, top⟩ :: rest, R, M⟩ := by
  rv_symT hp through *
  exact h3

/-- A `through` naming another program counter leaves the head a stop. -/
example (hp : p[i]? = some loopy) (h1 : rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 1, ret, top⟩ :: rest, R, M⟩) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 0, ret, top⟩ :: rest, R, M⟩ := by
  rv_symT hp through [2]
  exact h1

end

/-- `rv_close` closes `True` and leaves an equation of two variables it cannot close, without reading into either. -/
example (a b : Word) (h : b = a) : a = b ∧ True := by
  rv_close
  exact h.symm

end Rv64mc.Tactic.SymTest
