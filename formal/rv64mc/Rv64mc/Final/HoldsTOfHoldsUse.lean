/-
  Rv64mc.Final.HoldsTOfHoldsUse

  `HoldsT.of_holds_post` (`Core/HoldsTOfHolds.lean`) at the image, guarding that it applies and is
  not vacuous: `Input::word`'s total contract, weakened to safety and termination alone
  (`inputWord_safe`, postcondition `True`, memory frame `True`), and its partial contract
  (`Table.Runtime.inputWord`) give the total contract with the partial one's postcondition `WordPost`
  (the word returned and the reader advanced) and memory frame `WordOut` (`inputWord_total`).

  ## Main results

  * `inputWord_safe`, `inputWord_total`
-/

import Rv64mc.Core.HoldsTOfHolds
import Rv64mc.Proof.Runtime.InputWordT
import Rv64mc.Table.Runtime

namespace Rv64mc.Final.HoldsTOfHoldsUse

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Spec.Runtime Rv64mc.Proof.Runtime
  Rv64mc.Proof.Runtime.InputWordT

/-- **`Input::word` is safe and terminates** at the image: its total contract with the postcondition
    `True` and the memory frame `True` (`NEXT` grows within the heap, any word may change). -/
theorem inputWord_safe (env : Env) :
    HoldsT env (liftProg fns) Idx.VerifierRv64.Input.Word Needs.VerifierRv64.Input.Word (WordPreT env)
      (fun _ _ _ _ => True) (fun _ _ _ => True) WordStop :=
  ((InputWordT.total VerifierRv64.Input.Word.link VerifierRv64.Input.Word.tmpl_eq VerifierRv64.Input.Word.wf
      (halt_aborts env _ Idx.VerifierRv64.Halt VerifierRv64.Halt.link VerifierRv64.Halt.tmpl_eq)).mono_need
      (Nat.zero_le _)).contract.mono (fun _ _ _ _ h => h)
    (fun _ _ _ _ _ _ _ ⟨⟨ha, ⟨hg, he, _⟩, hs, _⟩, hc⟩ =>
      ⟨⟨ha, ⟨hg, he, fun _ h => (h (.inr (.inr (.inr trivial)))).elim⟩, hs, trivial⟩, hc⟩)
    fun _ _ _ _ _ _ _ h => h

/-- **`Input::word`'s total contract at the image**, its postcondition and memory frame from the partial
    contract. -/
theorem inputWord_total (env : Env) :
    InputWordSpecT env (liftProg fns) Idx.VerifierRv64.Input.Word Needs.VerifierRv64.Input.Word :=
  (inputWord_safe env).of_holds_post (Table.Runtime.inputWord env) fun _ _ h => h.1

end Rv64mc.Final.HoldsTOfHoldsUse

/-- info: 'Rv64mc.Final.HoldsTOfHoldsUse.inputWord_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Final.HoldsTOfHoldsUse.inputWord_total
