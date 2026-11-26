/-
  Rv64mc.Core.HoldsOfHoldsT

  A total contract gives the partial one, under its precondition with `Windows` at the stack pointer:
  `TContract.contract` (`Total/ToContract.lean`) at `HoldsT` and `Holds`. Its hypotheses hold with nothing left to the
  caller for a `HoldsT` that never ends the run (its `Stop` empty, the default): every `ECALL` traps under `stmtCtx`,
  and `WinOk` holds at a returned program. So the statement's machine (`stmtCtx`) and SP1's (`sp1Ctx`) agree on such
  a function: a total run never reaches an `ECALL`, and elsewhere their steps are the same.

  `Windows` stays in the precondition: the total contract says nothing of a state without it, so a partial contract
  whose precondition does not give it does not follow.

  ## Main results

  * `HoldsT.holds`: a total contract with no stopping state gives the partial one, with `Windows` at entry
-/

import Rv64mc.Core.HoldsT
import Rv64mc.Total.ToContract

namespace Rv64mc

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

namespace HoldsT

variable {env : Env} {p : Lprog (Op Reg) Reg} {f : Nat} {need : Nat}
  {Pre : (Reg → Word) → MachineState → Prop}
  {Post : (Reg → Word) → MachineState → (Reg → Word) → MachineState → Prop}
  {Out : (Reg → Word) → MachineState → Word → Prop}

/-- **A total contract with no stopping state gives the partial one**, with `Windows` at the stack pointer added to
    its precondition. -/
theorem holds (h : HoldsT env p f need Pre Post Out) :
    Holds env p f need (fun regs m => Pre regs m ∧ Windows env (regs .x2) m) Post Out :=
  fun G n Q ret top rest regs m ⟨he, hs, hst, hn, ⟨hP, hw⟩, hal⟩ hk =>
    (h.contract.contract (c' := sp1Ctx) (fun _ _ _ => rfl) (fun _ _ => WinOk.nil) fun _ _ _ _ _ _ _ h => h)
      G n Q ret top rest regs m ⟨⟨he, hs, hst, hn, hP, hal⟩, he.2 ▸ hw⟩ fun r' m' hq => hk r' m' hq.1

end HoldsT

end Rv64mc

/-- info: 'Rv64mc.HoldsT.holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.HoldsT.holds
