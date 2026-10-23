/-
  LeanVM.Guest.EndFinal

  The soundness end theorem for the deployed guest bytecode, with nothing assumed: checker K's B2
  (`b2_step`, `b2_main`) and B1's callees (`b1Sound`, `vsKnown_proved`) plugged into
  `guest_sound_of_b2`.
-/

module

public import LeanVM.Guest.EndSound
public import LeanVM.Guest.Sound

namespace LeanVM.Guest.End

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Node
open LeanVM.Protocol LeanVM.Protocol.EndToEnd
open scoped ENNReal

@[expose] public section

/-- **B2, proved**: checker K's two contracts for the deployed bytecode. -/
theorem b2Sound : B2Sound := ⟨b2_step vsKnown_proved, b2_main⟩

/-- **Soundness of the deployed guest** (GOAL.txt, checkpoint 5): a valid execution of the guest on
public input `statementDigest seed s` gives `seed'`, `s'` with the same digest, `s'.defer` shaped,
and `NodeRel seed' s'`. -/
theorem guest_sound : GuestSound := guest_sound_of_b2 b2Sound

/-- **The aggregate's soundness against the random oracle**, from `guest_sound`'s pieces. -/
theorem aggregate_sound {A : Adversary} {Q : ℕ} (hA : A.IsTotalQueryBound Q) :
    Pr{let z ← experiment A}[z.1.2 = true ∧ z.1.1.1.1 = guest ∧
      ¬ ∃ seed s, statementDigest seed s = publicDigest z.1.1.1.2 ∧ s.defer.Shaped bytecode ∧
        NodeSpec bytecode seed s] ≤ soundnessError Q :=
  aggregate_sound_of_b2 b2Sound hA

end

end LeanVM.Guest.End
