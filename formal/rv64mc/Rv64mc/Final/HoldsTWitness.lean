/-
  Rv64mc.Final.HoldsTWitness

  Guards that `HoldsT` is satisfiable by the functions a total proof meets, and that it excludes
  what it should. `frameFn` is the prologue and epilogue of a non-leaf function (`addi sp, sp, -16;
  sd ra, 8(sp); ld ra, 8(sp); addi sp, sp, 16; ret`): `frameFn_total` proves its total contract at
  any `env` from `HoldsT`'s precondition alone, the store and the load in the stack window
  (`Windows.stack`), the store over no code (`Windows.noCodeAt`), SP1's range and alignment from
  the stack top's bound and alignment. Without `Windows`' bound on the stack top it would be
  false: a top above the stack window puts the store outside both windows. `countdownFn` counts
  `a0` down to zero: `countdownFn_total` is a loop by `Total.loop`, its count an argument.
  `not_total_ecall`: under `stmtCtx` the run cannot pass a system call other than the halt.

  ## Main definitions

  * `frameFn`, `countdownFn`

  ## Main results

  * `frameFn_total`, `countdownFn_total`, `not_total_ecall`
-/

import Rv64mc.Final.Transfer

namespace Rv64mc

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

/-- Saves `ra` in a 16-byte frame, reads it back and returns. -/
def frameFn : Lfundef (Op Reg) Reg where
  name := "frame"
  addr := 0
  depth := 16
  body := [
    .Lopn (.set .x2 (.bin .add (.reg .x2) (.imm 0xfffffffffffffff0#64))),
    .Lopn (.store .b8 (.bin .add (.reg .x2) (.imm 8#64)) (.reg .x1)),
    .Lopn (.load .x1 .b8 false (.bin .add (.reg .x2) (.imm 8#64))),
    .Lopn (.set .x2 (.bin .add (.reg .x2) (.imm 16#64))),
    .Lret]

/-- **A function that stores to and loads from its frame keeps a total contract**, with 16 bytes of stack. -/
theorem frameFn_total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (hp : p[i]? = some frameFn) :
    HoldsT env p i 16 (fun _ _ => True) (fun _ _ _ _ => True) := by
  intro Q ret top rest regs m ⟨⟨⟨hra, hsp⟩, hstk, hst, hnx, _, hal⟩, hwin⟩ _ hk
  have hlay := env.layout
  have htop := hwin.1
  -- the slot of `ra`, at `top - 8`
  generalize hsl : top + 0xfffffffffffffff0#64 + 8#64 = a
  have ha : a.toNat = top.toNat - 8 := by rw [← hsl]; bv_omega
  have hlo : env.stackLimit.toNat ≤ a.toNat := by omega
  have hin : inWindow a 8 = true := hwin.stack hlo (by omega)
  have hok : isValidMemAddrSp1 a = true ∧ alignedFor 8 a = true := by
    simp only [isValidMemAddrSp1, SP1_MAX_MEMORY, alignedFor, isAligned8, ha, decide_eq_true_eq, ite_true,
      beq_iff_eq]
    omega
  have hback : top + 0xfffffffffffffff0#64 + 16#64 = top := by bv_omega
  have hnc := hwin.noCodeAt hin (by decide)
  refine Total.set hp rfl (WinOk.of_set hp rfl) ?_
  refine Total.opn hp rfl (r' := updReg regs .x2 (top + 0xfffffffffffffff0#64))
    (m' := m.setMem a ret) ?_ (WinOk.of_opn hp rfl ?_) ?_
  · simp [Isa.ofOps, Op.eval, rvMem, Expr.eval, BinOp.eval, updReg_apply, hsp, hra, hsl, hok.1, hok.2, hnc,
      Width.bytes]
  · simpa [opWin, Expr.eval, BinOp.eval, updReg_apply, hsp, hsl, Width.bytes] using hin
  refine Total.opn hp rfl (r' := updReg (updReg regs .x2 (top + 0xfffffffffffffff0#64)) .x1 ret)
    (m' := m.setMem a ret) ?_ (WinOk.of_opn hp rfl ?_) ?_
  · simp [Isa.ofOps, Op.eval, rvMem, Expr.eval, BinOp.eval, updReg_apply, hsl, hok.1, hok.2, Width.bytes]
  · simpa [opWin, Expr.eval, BinOp.eval, updReg_apply, hsl, Width.bytes] using hin
  refine Total.set hp rfl (WinOk.of_set hp rfl) ?_
  refine Total.ret hp rfl (by simp [updReg_apply]) (by simp [updReg_apply, Expr.eval, BinOp.eval, hback])
    (WinOk.of_ne hp rfl nofun) ?_
  refine hk _ _ ⟨⟨⟨?_, ?_⟩, ?_, ?_, trivial⟩, rfl⟩
  · simp [updReg_apply, Expr.eval, BinOp.eval, hback]
  · simp [updReg_apply]
  · exact Env.Frame.setMem_stack hnx hlo (by omega)
  · exact Env.static_setMem_stack hst hlo

/-- Counts `a0` down to zero and returns. -/
def countdownFn : Lfundef (Op Reg) Reg where
  name := "countdown"
  addr := 0
  depth := 0
  body := [
    .Llabel .internal 0,
    .Lcond (.cmp "eq" (.reg .x10) (.imm 0)) 1,
    .Lopn (.set .x10 (.bin .add (.reg .x10) (.imm 0xffffffffffffffff#64))),
    .Lgoto 0,
    .Llabel .internal 1,
    .Lret]

/-- **A loop whose count is an argument keeps a total contract**, by `Total.loop` on `a0`. -/
theorem countdownFn_total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (hp : p[i]? = some countdownFn) :
    HoldsT env p i 0 (fun _ _ => True) (fun _ _ _ _ => True) := by
  intro Q ret top rest regs m ⟨⟨⟨hra, hsp⟩, _, hst, hnx, _, _⟩, _⟩ _ hk
  refine Total.loop (fun k (r : Reg → Word) m' => (r .x10).toNat = k ∧ r .x1 = ret ∧ AbiRegs top regs r ∧ m' = m)
    (fun k r m' ⟨hk0, hr1, habi, hm⟩ ih => ?_) _ regs m ⟨rfl, hra, ⟨hsp, by simp only [and_self]⟩, rfl⟩
  subst hm
  refine Total.label hp rfl (WinOk.of_ne hp rfl nofun) ?_
  refine Total.cond hp rfl (b := r .x10 == 0#64) (by simp [condEval, operandVal, cmpEval]) rfl
    (WinOk.of_ne hp rfl nofun) (fun h0 => ?_) (fun h0 => ?_)
  · refine Total.label hp rfl (WinOk.of_ne hp rfl nofun) ?_
    refine Total.ret hp rfl hr1 habi.1 (WinOk.of_ne hp rfl nofun) ?_
    exact hk _ _ ⟨⟨habi, Env.Frame.refl hnx, hst, trivial⟩, rfl⟩
  · refine Total.set hp rfl (WinOk.of_set hp rfl) ?_
    refine Total.goto hp rfl rfl (WinOk.of_ne hp rfl nofun) ?_
    have hne : r .x10 ≠ 0#64 := by simpa using h0
    have hlt : (r .x10 + 0xffffffffffffffff#64).toNat < k := by
      have : (r .x10).toNat ≠ 0 := fun h => hne (BitVec.eq_of_toNat_eq h)
      rw [← hk0]
      bv_omega
    refine ih _ _ _ hlt ⟨by simp only [updReg_apply, ↓reduceIte]; rfl, by simp [updReg_apply, hr1], ?_, rfl⟩
    simp only [AbiRegs, updReg_apply] at habi ⊢
    simpa using habi

/-! ## What the judgement excludes -/

/-- Under `stmtCtx`, a state at an `ECALL` with `t0 ≠ 0` is total for no `Q`: the run cannot pass another system
    call. -/
theorem not_total_ecall (p : Lprog (Op Reg) Reg) (fr : Frame) (rest : List Frame) (regs : Reg → Word)
    (m : MachineState) (k : Nat) (hf : rvIsa.fetch p ⟨fr :: rest, regs, m⟩ = some (.Lext k)) (h5 : regs .x5 ≠ 0)
    (G Q : State rvIsa → Prop) : ¬ rvIsa.Total p stmtCtx G Q ⟨fr :: rest, regs, m⟩ := by
  intro h
  cases h with
  | done _ ha _ =>
    rcases ha with h | ⟨_, _, hacc⟩
    · cases h
    · exact h5 hacc
  | next _ ht _ _ _ => exact ht (step_stmt_trap hf)

end Rv64mc

/-- info: 'Rv64mc.frameFn_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.frameFn_total

/-- info: 'Rv64mc.countdownFn_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.countdownFn_total
