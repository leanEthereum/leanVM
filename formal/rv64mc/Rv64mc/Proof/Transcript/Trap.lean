/-
  Rv64mc.Proof.Transcript.Trap

  A doubleword store at an address that is not a multiple of eight traps (SP1's memory, `rvMem`), and a run that
  traps is safe: so a proof may assume the address of any store it is about to step is aligned. This gives the
  alignment of the stack pointer, which no contract states, from the function's first store into its frame.
-/

import Rv64mc.Tactic.Steps

namespace Rv64mc.Proof.Transcript

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

variable {p : Lprog rvIsa.Op rvIsa.Reg} {E : Type} {c : Context rvIsa E} {G : State rvIsa → Prop} {n : Nat}
  {Q : State rvIsa → Prop} {fn pc : Nat} {rv top : Word} {rest : List Frame} {regs : Reg → Word}
  {m : MachineState} {fd : Lfundef (Op Reg) Reg}

theorem store_misaligned {x v : Word} (hx : x.toNat % 8 ≠ 0) : rvMem.store .b8 x v m = none := by
  simp [rvMem, alignedFor, isAligned8, hx, Width.bytes]

/-- **A store at a misaligned address is safe**, so the run past it may assume the address aligned. -/
theorem safe_aligned_store {a e : Lprog.Expr Reg} {x : Word} (hf : p[fn]? = some fd)
    (hi : fd.body[pc]? = some (.Lopn (.store .b8 a e))) (ha : a.eval regs = x)
    (h : x.toNat % 8 = 0 → rvIsa.SafeN p c G n Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩) :
    rvIsa.SafeN p c G n Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ := by
  by_cases hx : x.toNat % 8 = 0
  · exact h hx
  · exact Tactic.step_store x (e.eval regs) hf hi ha rfl fun m' hm => by rw [store_misaligned hx] at hm; cases hm

end Rv64mc.Proof.Transcript
