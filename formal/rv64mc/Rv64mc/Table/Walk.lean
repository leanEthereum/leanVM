/-
  Rv64mc.Table.Walk

  The top of the call graph at the image (`liftProg Gen.fns`): `verify_execution` from `walk`'s contract, and the
  end theorem from `main`'s contract at the stack `main` needs (`Gen.Needs.Main`), a contract with less stack being
  one with more (`holds_need_mono`). The indices are the generator's (`Rv64mc/Gen/index.tsv`).
-/

import Rv64mc.Proof.Walk.VerifyExecution
import Rv64mc.Final.End
import Rv64mc.Gen.Needs
import Rv64mc.Gen.Link.Verifier.VerifyExecution

namespace Rv64mc.Table.Walk

open RiscvZkvm.Rv64 Lprog Lprog.RiscV MachineChecked.RiscV.Lift Rv64mc.Gen

/-- A contract with `need` bytes of stack holds with more. -/
theorem holds_need_mono {env : Env} {p : Lprog (Op Reg) Reg} {i n n' : Nat}
    {Pre : (Reg → Word) → MachineState → Prop}
    {Post : (Reg → Word) → MachineState → (Reg → Word) → MachineState → Prop}
    {Out : (Reg → Word) → MachineState → Word → Prop} (h : Holds env p i n Pre Post Out) (hn : n ≤ n') :
    Holds env p i n' Pre Post Out :=
  fun G k Q ret top rest regs m ⟨he, hs, hst, hnx, hp⟩ hk ↦
    h G k Q ret top rest regs m ⟨he, by omega, hst, hnx, hp⟩ hk

variable (env : Env)

theorem verifyExecution (hwalk : Spec.Walk.Execution.spec env (liftProg fns) Idx.Verifier.Walk Needs.Verifier.Walk) :
    Spec.Walk.Execution.spec env (liftProg fns) Idx.Verifier.VerifyExecution Needs.Verifier.VerifyExecution :=
  Proof.Walk.VerifyExecution.ok env _ Idx.Verifier.VerifyExecution _ Verifier.VerifyExecution.tmpl_eq Verifier.VerifyExecution.wf hwalk

kernel_eq need_main : decide (Needs.Main ≤ Rv64mc.need) = true

/-- **The end theorem from `main`'s contract at the stack it needs.** -/
theorem rv64_sound_of_main (hmain : MainSpec Rv64mc.env (liftProg fns) Idx.Main Needs.Main) :
    AllDecode image ∧ Sound image :=
  rv64_sound fun words ↦ holds_need_mono (hmain words) (by simpa using need_main)

end Rv64mc.Table.Walk
