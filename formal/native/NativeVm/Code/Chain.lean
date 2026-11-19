module

public import NativeVm.Code.Contracts

/-!
# The walk as the phases' steps

`Model.verifyExecution` is the seven phases' model steps of `NativeVm.Code.Contracts` bound in
order (`verifyExecution_eq`), so `Model.verify` is a case split on their runs, one after the other
(`verify_chain`): `false` at the first that rejects, else the end check on the last state. `body`'s
proof follows the code phase by phase along it.
-/

@[expose] public section

namespace NativeVm.Code

open NativeVm.Model LeanVM.Parameters

theorem verifyExecution_eq (bc : Array UInt64) (pub : Vector UInt64 4) :
    verifyExecution bc pub = (do
      let r1 ← readAnnouncedSizes bc
      let ood ← phase2M r1.1 r1.2
      let bus ← verifyBusBalance r1.1
      let ev ← tablePhase r1.1 bus
      let pc ← publicInputPhase r1.1 pub
      let r6 ← keccakPhase r1.1 ev
      phase7M r1.1 r1.2 ood (bus.claims ++ tableColumnClaims ev ++ pc ++ r6.1) r6.2.1 r6.2.2) := by
  simp only [verifyExecution, phase2M, phase7M, bind_assoc]

/-- **`Model.verify` phase by phase.** -/
theorem verify_chain (inp : Input) (stream : Array EW) (openings : Array (Array OpeningW)) :
    Model.verify inp.bytecode inp.pub stream openings =
      match (readAnnouncedSizes inp.bytecode).run (start inp stream openings) with
      | none => false
      | some (r1, t1) => match (phase2M r1.1 r1.2).run t1 with
        | none => false
        | some (ood, t2) => match (verifyBusBalance r1.1).run t2 with
          | none => false
          | some (bus, t3) => match (tablePhase r1.1 bus).run t3 with
            | none => false
            | some (ev, t4) => match (publicInputPhase r1.1 inp.pub).run t4 with
              | none => false
              | some (pc, t5) => match (keccakPhase r1.1 ev).run t5 with
                | none => false
                | some (r6, t6) => match (phase7M r1.1 r1.2 ood
                    (bus.claims ++ tableColumnClaims ev ++ pc ++ r6.1) r6.2.1 r6.2.2).run t6 with
                  | none => false
                  | some (_, t7) => t7.cursor == t7.stream.size && t7.phase == t7.openings.size := by
  change (match (verifyExecution inp.bytecode inp.pub).run (start inp stream openings) with
    | some ((), s) => s.cursor == s.stream.size && s.phase == s.openings.size
    | none => false) = _
  rw [verifyExecution_eq]
  simp only [StateT.run_bind, Option.bind_eq_bind]
  generalize (readAnnouncedSizes inp.bytecode).run (start inp stream openings) = o1
  rcases o1 with _ | ⟨r1, t1⟩; · rfl
  simp only [Option.bind_some]
  generalize (phase2M r1.1 r1.2).run t1 = o2
  rcases o2 with _ | ⟨ood, t2⟩; · rfl
  simp only [Option.bind_some]
  generalize (verifyBusBalance r1.1).run t2 = o3
  rcases o3 with _ | ⟨bus, t3⟩; · rfl
  simp only [Option.bind_some]
  generalize (tablePhase r1.1 bus).run t3 = o4
  rcases o4 with _ | ⟨ev, t4⟩; · rfl
  simp only [Option.bind_some]
  generalize (publicInputPhase r1.1 inp.pub).run t4 = o5
  rcases o5 with _ | ⟨pc, t5⟩; · rfl
  simp only [Option.bind_some]
  generalize (keccakPhase r1.1 ev).run t5 = o6
  rcases o6 with _ | ⟨r6, t6⟩; · rfl
  simp only [Option.bind_some]
  generalize (phase7M r1.1 r1.2 ood _ r6.2.1 r6.2.2).run t6 = o7
  rcases o7 with _ | ⟨⟨⟩, t7⟩ <;> rfl

end NativeVm.Code
