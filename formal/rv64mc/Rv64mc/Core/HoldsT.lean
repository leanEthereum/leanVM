/-
  Rv64mc.Core.HoldsT

  The total contract every function of the image is to be proved to satisfy: `Holds`
  (`Core/Holds.lean`) with machine-checked's partial `Isa.Contract` replaced by the total
  `Isa.TContract` (`Total/Contract.lean`), at the statement's machine rather than SP1's.

  * The context is `stmtCtx`, the statement's `step` at an `ECALL`: every `Lext` stops the run,
    and it ends the run (accepts) where `t0 = 0`, the halting `ECALL` that `Halts` asks for. A
    total proof can therefore end the run only at the halting `ECALL`: any other `ECALL` is a
    stop it cannot get past. Its accepting states are every halt, whatever `a0`: what `a0` may
    be there is the contract's `Q` or `Stop`.
  * The obligation at every state is `WinOk`: an operation that loads or stores accesses memory
    wholly inside one of the statement's windows (`inWindow`). `rvIsa`'s memory already checks
    SP1's conditions (`memOkSp1`), and a total proof must show that each operation gives a
    result, so together every access the run makes passes the statement's `memOk`.
  * `HoldsT env p i need Pre Post Out Stop` is `Holds`'s pre- and postcondition, plus `Stop`:
    the registers and memory at which the function may end the whole run, inside the call, at
    the halting `ECALL` (`halt` and every path to it: the allocator's failure, a panic).

  A call through it is `HoldsT.call`. `WinOk` holds at every state that is not at a load or a
  store (`WinOk.of_ne`), and at one whose address is in a window (`WinOk.of_opn`).

  ## Main definitions

  * `stmtCtx`, `opWin`, `WinOk`, `HoldsT`

  ## Main results

  * `HoldsT.call`, `HoldsT.mono_need`
  * `WinOk.of_ne`, `WinOk.of_opn`, `WinOk.nil`
-/

import Rv64mc.Core.Holds
import Rv64mc.EndStatement
import Rv64mc.Total.Contract

namespace Rv64mc

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

/-! ## The statement's machine at Lprog -/

/-- **The statement's external calls**: every `ECALL` stops the run, as `step` does, and it ends the run (accepts)
    at the halting one, `t0 = 0`, whatever `a0`. -/
def stmtCtx : Context rvIsa Unit where
  ext _ _ _ o := o = .trap
  accept _ regs _ := regs .x5 = 0

/-- An operation's memory access lies wholly in one of the statement's windows. -/
def opWin : Op Reg → (Reg → Word) → Prop
  | .load _ w _ a, regs => inWindow (a.eval regs) w.bytes = true
  | .store w a _, regs => inWindow (a.eval regs) w.bytes = true
  | _, _ => True

/-- **The obligation at every state**: at a load or a store, the access lies in a window. -/
def WinOk (p : Lprog (Op Reg) Reg) (s : State rvIsa) : Prop :=
  ∀ op, rvIsa.fetch p s = some (.Lopn op) → opWin op s.regs

namespace WinOk

variable {p : Lprog (Op Reg) Reg} {fd : Lfundef (Op Reg) Reg} {fn pc : Nat} {rv top : Word}
  {rest : List Frame} {regs : Reg → Word} {m : MachineState}

/-- At an instruction that is not an operation. -/
theorem of_ne {i : LinstrR (Op Reg) Reg} (hf : p[fn]? = some fd) (hi : fd.body[pc]? = some i)
    (hne : ∀ op, i ≠ .Lopn op) : WinOk p ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ := by
  intro op h
  rw [SafeN.fetch_eq (fr := ⟨fn, pc, rv, top⟩) hf hi] at h
  exact absurd (Option.some.inj h) (hne op)

/-- At an operation whose access lies in a window. -/
theorem of_opn {op : Op Reg} (hf : p[fn]? = some fd) (hi : fd.body[pc]? = some (.Lopn op))
    (hw : opWin op regs) : WinOk p ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ := by
  intro op' h
  rw [SafeN.fetch_eq (fr := ⟨fn, pc, rv, top⟩) hf hi] at h
  cases h
  exact hw

/-- At a register write. -/
theorem of_set {d : Reg} {e : Expr Reg} (hf : p[fn]? = some fd) (hi : fd.body[pc]? = some (.Lopn (.set d e))) :
    WinOk p ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ :=
  of_opn hf hi trivial

/-- A returned program is at no instruction. -/
theorem nil : WinOk p ⟨[], regs, m⟩ := fun _ h => nomatch h

end WinOk

/-! ## The contract -/

/-- **The total contract of function `i` of `p`**: from its entry with `Pre`, the calling convention's precondition
    and `need` bytes of stack, every load and store in a window, the run either returns, with `Post`, the calling
    convention, the memory frame (writing at most `Out` besides its stack and allocations) and `env.Static`, or ends
    inside the call at the halting `ECALL` with `Stop`; it does not trap, go `wrong` or run forever. -/
def HoldsT (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (need : Nat)
    (Pre : (Reg → Word) → MachineState → Prop)
    (Post : (Reg → Word) → MachineState → (Reg → Word) → MachineState → Prop)
    (Out : (Reg → Word) → MachineState → Word → Prop := fun _ _ _ => False)
    (Stop : (Reg → Word) → MachineState → (Reg → Word) → MachineState → Prop := fun _ _ _ _ => False) : Prop :=
  rvIsa.TContract p stmtCtx (WinOk p) i (Holds.pre env need Pre) (Holds.post env Post Out)
    (fun _ _ regs m r' m' => Stop regs m r' m')

namespace HoldsT

variable {env : Env} {p : Lprog (Op Reg) Reg} {f : Nat} {need : Nat}
  {Pre : (Reg → Word) → MachineState → Prop}
  {Post : (Reg → Word) → MachineState → (Reg → Word) → MachineState → Prop}
  {Out : (Reg → Word) → MachineState → Word → Prop}
  {Stop : (Reg → Word) → MachineState → (Reg → Word) → MachineState → Prop}

/-- The contract as `Total/Contract.lean`'s. -/
theorem contract (h : HoldsT env p f need Pre Post Out Stop) :
    rvIsa.TContract p stmtCtx (WinOk p) f (Holds.pre env need Pre) (Holds.post env Post Out)
      (fun _ _ regs m r' m' => Stop regs m r' m') := h

/-- **A call through a total contract**: the target reaches the callee, the stack has `need` bytes, the invariants
    and `Pre` hold with `ra` the return address, `Q` holds at every halt with `Stop` inside the call, and the run is
    total from every state the callee returns in, after the call. -/
theorem call (h : HoldsT env p f need Pre Post Out Stop) {fn pc : Nat} {fd : Lfundef (Op Reg) Reg}
    {ret rv top : Word} {tgt : Target Reg} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    {Q : State rvIsa → Prop} (hf : p[fn]? = some fd) (hi : fd.body[pc]? = some (.Lcall ret tgt))
    (hc : rvIsa.callee p regs tgt = some f) (hstack : env.stackLimit.toNat + need ≤ (regs .x2).toNat)
    (hst : env.Static m) (hnext : (env.next m).toNat ≤ env.heapEnd.toNat) (hpre : Pre (updReg regs .x1 ret) m)
    (halign : (regs .x2).toNat % 16 = 0)
    (hstop : ∀ fr st r' m', Stop (updReg regs .x1 ret) m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩)
    (hk : ∀ r' m', AbiRegs (regs .x2) (updReg regs .x1 ret) r' →
      env.Frame (regs .x2) (Out (updReg regs .x1 ret) m) m m' → env.Static m' →
      Post (updReg regs .x1 ret) m r' m' → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨fn, pc + 1, rv, top⟩ :: rest, r', m'⟩) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ :=
  Total.call_contract hf hi h hc (WinOk.of_ne hf hi nofun)
    ⟨⟨by simp [updReg_apply], by simp [updReg_apply]⟩, hstack, hst, hnext, hpre, halign⟩
    hstop fun r' m' ⟨ha, hfr, hs, hp⟩ => hk r' m' ha hfr hs hp

/-- **More stack than a contract needs is enough.** -/
theorem mono_need (h : HoldsT env p f need Pre Post Out Stop) {need' : Nat} (hn : need ≤ need') :
    HoldsT env p f need' Pre Post Out Stop :=
  fun Q ret top rest regs m ⟨he, hs, hrest⟩ hstop hk => h Q ret top rest regs m ⟨he, by omega, hrest⟩ hstop hk

end HoldsT

end Rv64mc
