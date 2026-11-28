/-
  LeanVM.Prover.Complete

  leanVM's completeness, reduced to the honest script's phases, and its axioms.
-/

module

public import LeanVM.Prover.Complete.Assemble
public import LeanVM.Prover.Complete.KeccakPhase
public import LeanVM.Prover.Complete.Witness
public import LeanVM.Prover.Complete.CostEnd
public import LeanVM.Prover.Complete.RingSwitch
public import LeanVM.Prover.Complete.Link.Open
public import LeanVM.Prover.Complete.Link.Index
public import LeanVM.Prover.Complete.Link.Column
public import LeanVM.Prover.Complete.Link.RowId
public import LeanVM.Prover.Complete.Link.TailRow

/-!
# leanVM's completeness

`LeanVM.Completeness` (`Statement/LeanVm.lean`) for the statement's honest prover
`LeanVM.Prover.prove`, which runs `honestScript` against the verifier's own program:

* `Wins.lean`, `Replay.lean`: a script that wins the program (`Wins`) makes proofs the verifier
  accepts, for every hash and permutation (`runProof_of_wins`);
* `Pow.lean`, `Rom.lean`, `Rpm.lean`, `Numbers.lean`: in the random-oracle model the winning
  script's proof is rejected only when a proof-of-work search runs out of fuel (`romComplete`), the
  transfer to the random permutation adds `rpmError` (`rpmComplete`), and the numbers stay below
  `2^-256` (`completenessBound_le`);
* `End.lean`: `LeanVM.completeness_of : WitnessExists → HonestWins → HonestCosts → Completeness`;
* `Witness.lean`: `witnessExists`; `Prefix.lean`, `Public.lean`: the announced sizes, the
  out-of-domain sample and the public input win; `KeccakPhase.lean`: `keccakWins`;
* `Assemble.lean`: `LeanVM.completeness_of_phases : CommitOpenWins → LinkWins → KeccakWins →
  HonestCosts → Completeness`; `Cost*.lean`: `honestCosts`; so
  `LeanVM.completeness_of_open_phases : CommitOpenWins → LinkWins → Completeness`;
* `Link/*.lean`: the link's four identities on the honest witness (`linkIndexIdentity_honest`,
  `rowIdentity_of`, `columnSplit_of`, `linkTailHolds_honest`), so `LeanVM.completeness_holds`.
-/

public section

namespace LeanVM

open LeanVM.Semantics

/-- **Completeness from the two open phases**: the commitment and opening (`CommitOpenWins`) and the
link (`LinkWins`); the witness, the Keccak reduction and the costs are proved. -/
theorem completeness_of_open_phases (hco : Prover.CommitOpenWins) (hlink : Prover.LinkWins) :
    Completeness :=
  completeness_of_phases hco hlink Prover.Complete.Keccak.keccakWins Prover.Complete.Cost.honestCosts

/-- **Completeness from the link**: every other phase and the costs are proved
(`commitOpenWins`, `keccakWins`, `honestCosts`, `witnessExists`). -/
theorem completeness_of_link (hlink : Prover.LinkWins) : Completeness :=
  completeness_of_open_phases Prover.commitOpenWins hlink

/-- **Completeness from the link's four arithmetic facts** (`LinkCore`, `Link/Core.lean`). -/
theorem completeness_of_linkCore
    (h : ∀ (prog : LeanIsaProgram) (input : PublicInput) (t : Execution prog) (ρ : ℕ)
      (W : Prover.Witness), Prover.Admitted prog input t ρ W → Prover.Complete.LinkCore W) :
    Completeness :=
  completeness_of_link (Prover.Complete.linkWins_of_core h)

/-- **Completeness from the link's four identities on the honest witness** (`Link/Open.lean`):
`LinkIndexIdentity`, `RowIdentity`, `ColumnSplit`, `LinkTailHolds`. -/
theorem completeness_of_linkIdentities
    (h : ∀ (prog : LeanIsaProgram) (input : PublicInput) (t : Execution prog) (ρ : ℕ)
      (W : Prover.Witness), Prover.Admitted prog input t ρ W →
        Prover.Complete.LinkIndexIdentity W ∧ Prover.Complete.RowIdentity W ∧
          Prover.Complete.ColumnSplit W ∧ Prover.Complete.LinkTailHolds W) :
    Completeness :=
  completeness_of_linkCore fun prog input t ρ W hA ↦
    let hh := h prog input t ρ W hA
    Prover.Complete.linkCore_of hA.witness hh.1 hh.2.1 hh.2.2.1 hh.2.2.2

/-- **Completeness from the row side's identity and the link's tail**: the index side's identity
(`linkIndexIdentity_honest`) and the pointer columns' split (`columnSplit_of`) are proved. -/
theorem completeness_of_rowTail
    (h : ∀ (prog : LeanIsaProgram) (input : PublicInput) (t : Execution prog) (ρ : ℕ)
      (W : Prover.Witness), Prover.Admitted prog input t ρ W →
        Prover.Complete.RowIdentity W ∧ Prover.Complete.LinkTailHolds W) :
    Completeness :=
  completeness_of_linkIdentities fun prog input t ρ W hA ↦
    ⟨Prover.Complete.linkIndexIdentity_honest hA, (h prog input t ρ W hA).1,
      Prover.Complete.columnSplit_of hA, (h prog input t ρ W hA).2⟩

/-- **Completeness from the link's tail**: the row side's identity (`rowIdentity_of`) is proved. -/
theorem completeness_of_tail
    (h : ∀ (prog : LeanIsaProgram) (input : PublicInput) (t : Execution prog) (ρ : ℕ)
      (W : Prover.Witness), Prover.Admitted prog input t ρ W → Prover.Complete.LinkTailHolds W) :
    Completeness :=
  completeness_of_rowTail fun prog input t ρ W hA ↦
    ⟨Prover.Complete.rowIdentity_of hA, h prog input t ρ W hA⟩

/-- **leanVM is complete** for its honest prover, `LeanVM.Prover.prove`. -/
theorem completeness_holds : Completeness :=
  completeness_of_tail fun _ _ _ _ _ hA ↦ Prover.Complete.linkTailHolds_honest hA.witness

end LeanVM

end

/-- info: 'LeanVM.completeness_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.completeness_holds

/-- info: 'LeanVM.completeness_of_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.completeness_of_tail

/-- info: 'LeanVM.completeness_of_rowTail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.completeness_of_rowTail

/-- info: 'LeanVM.completeness_of_linkIdentities' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.completeness_of_linkIdentities

/-- info: 'LeanVM.completeness_of_linkCore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.completeness_of_linkCore

/-- info: 'LeanVM.Prover.commitOpenWins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Prover.commitOpenWins

/-- info: 'LeanVM.completeness_of_open_phases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.completeness_of_open_phases

/-- info: 'LeanVM.Prover.Complete.Cost.honestCosts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Prover.Complete.Cost.honestCosts

/-- info: 'LeanVM.completeness_of_phases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.completeness_of_phases

/-- info: 'LeanVM.Prover.witnessExists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Prover.witnessExists

/-- info: 'LeanVM.Prover.Complete.Keccak.keccakWins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Prover.Complete.Keccak.keccakWins

/-- info: 'LeanVM.Prover.runProof_of_wins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Prover.runProof_of_wins

/-- info: 'LeanVM.Prover.rpmComplete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Prover.rpmComplete

/-- info: 'LeanVM.Prover.completenessBound_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Prover.completenessBound_le
