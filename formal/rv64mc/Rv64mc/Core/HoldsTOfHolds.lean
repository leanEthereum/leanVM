/-
  Rv64mc.Core.HoldsTOfHolds

  A total contract and a partial one of the same function give a total contract with both
  postconditions: `TContract.and_contract` (`Total/Combine.lean`) at `HoldsT` and `Holds`. Its
  hypotheses hold here with nothing left to the caller: `stmtCtx`'s `ECALL`s never continue, so
  every step under it is a step under `sp1Ctx` (`Isa.step_ok_of_ext_not_ok`), and `WinOk` looks at
  the innermost activation only, so it holds at a returned program and under any longer stack.

  So a function with a partial proof (a `Holds` with its functional postcondition and its memory
  frame) needs only a total proof of safety and termination. `HoldsT.of_holds_code` takes it as a bare
  total contract whose postcondition is the code map kept, and gives the `Holds`'s postcondition, memory
  frame, `AbiRegs` and `env.Static` in total form. `HoldsT.of_holds_post` takes it as a `HoldsT` instead,
  whose postcondition is what its callers need for their own total proofs and whose memory frame may be
  the coarsest (`Out := fun _ _ _ => True`, under which the frame says only that `NEXT` grows within the
  heap); that `HoldsT` also proves `AbiRegs` and `env.Static`, which every `HoldsT` postcondition
  includes, and the result keeps only its code map kept.

  ## Main results

  * `HoldsT.of_holds`: both preconditions, both postconditions
  * `HoldsT.of_holds_code`: a bare total contract of the code map kept and a partial one give the
    partial one's postcondition and memory frame in total form
  * `HoldsT.of_holds_post`: the same from a `HoldsT` of any postcondition and memory frame
-/

import Rv64mc.Core.HoldsT
import Rv64mc.Total.Combine

namespace Rv64mc

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

namespace HoldsT

variable {env : Env} {p : Lprog (Op Reg) Reg} {f : Nat} {need : Nat}
  {Pre Pre' : (Reg → Word) → MachineState → Prop}
  {Post Post' : (Reg → Word) → MachineState → (Reg → Word) → MachineState → Prop}
  {Out Out' : (Reg → Word) → MachineState → Word → Prop}
  {Stop : (Reg → Word) → MachineState → (Reg → Word) → MachineState → Prop}

/-- **A total contract and a partial one give a total contract with both postconditions**, under both
    preconditions, with the total contract's memory frame and stopping set. -/
theorem of_holds (ht : HoldsT env p f need Pre Post Out Stop) (hp : Holds env p f need Pre' Post' Out') :
    HoldsT env p f need (fun regs m => Pre regs m ∧ Pre' regs m)
      (fun regs m r' m' => Post regs m r' m' ∧ Post' regs m r' m') Out Stop :=
  (ht.contract.and_contract hp.contract
      (fun _ _ _ _ h => ⟨[], Isa.step_ok_of_ext_not_ok (fun _ _ _ _ h => by cases h) h⟩)
      (fun _ _ => WinOk.nil) fun _ _ _ _ _ h => h).mono
    (fun _ _ _ _ ⟨⟨he, hs, hst, hn, ⟨hP, hP'⟩, hal⟩, hw⟩ =>
      ⟨⟨⟨he, hs, hst, hn, hP, hal⟩, hw⟩, ⟨he, hs, hst, hn, hP', hal⟩⟩)
    (fun _ _ _ _ _ _ _ ⟨⟨⟨ha, hf, hs, hq⟩, hc⟩, ⟨_, _, _, hq'⟩⟩ => ⟨⟨ha, hf, hs, hq, hq'⟩, hc⟩)
    fun _ _ _ _ _ _ _ h => h

/-- **A total contract of the code map kept and a partial one give the partial one's postcondition and
    memory frame in total form**, under the total one's precondition where it implies the partial one's:
    how a function with a `Holds` proof is proved total, by a bare total contract of safety, termination
    and the code map kept. -/
theorem of_holds_code
    (ht : rvIsa.TContract p stmtCtx (WinOk p) f (HoldsT.pre env need Pre)
      (fun _ _ _ m _ m' => m'.code = m.code) fun _ _ regs m r' m' => Stop regs m r' m')
    (hp : Holds env p f need Pre' Post' Out') (hpre : ∀ regs m, Pre regs m → Pre' regs m) :
    HoldsT env p f need Pre Post' Out' Stop :=
  (ht.and_contract hp.contract
      (fun _ _ _ _ h => ⟨[], Isa.step_ok_of_ext_not_ok (fun _ _ _ _ h => by cases h) h⟩)
      (fun _ _ => WinOk.nil) fun _ _ _ _ _ h => h).mono
    (fun _ _ _ _ ⟨⟨he, hs, hst, hn, hP, hal⟩, hw⟩ =>
      ⟨⟨⟨he, hs, hst, hn, hP, hal⟩, hw⟩, ⟨he, hs, hst, hn, hpre _ _ hP, hal⟩⟩)
    (fun _ _ _ _ _ _ _ ⟨hc, hq'⟩ => ⟨hq', hc⟩) fun _ _ _ _ _ _ _ h => h

/-- **A total contract of any postcondition and memory frame and a partial one give the partial one's
    postcondition and memory frame in total form**: `of_holds_code` with the `HoldsT`'s postcondition
    dropped to the code map kept. -/
theorem of_holds_post (ht : HoldsT env p f need Pre Post Out Stop) (hp : Holds env p f need Pre' Post' Out')
    (hpre : ∀ regs m, Pre regs m → Pre' regs m) : HoldsT env p f need Pre Post' Out' Stop :=
  of_holds_code (ht.contract.mono (fun _ _ _ _ h => h) (fun _ _ _ _ _ _ _ h => h.2)
    fun _ _ _ _ _ _ _ h => h) hp hpre

end HoldsT

end Rv64mc

/-- info: 'Rv64mc.HoldsT.of_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.HoldsT.of_holds

/-- info: 'Rv64mc.HoldsT.of_holds_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.HoldsT.of_holds_code

/-- info: 'Rv64mc.HoldsT.of_holds_post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.HoldsT.of_holds_post
