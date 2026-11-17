/-
  LeanVM.Guest.EndExecFinal

  The executor's completeness on the guest and the composed prover's proof accepted: every proved
  part wired into `ExecGaps`. No open fact is left (`openGaps`).
-/

import LeanVM.Guest.EndExecHonest
import LeanVM.Guest.ProverGuest
import LeanVM.Guest.EndExecR
import LeanVM.Guest.Mode.Certs
import LeanVM.Guest.Res.SubCerts
import LeanVM.Guest.Res.TermCerts
import LeanVM.Guest.EndExecRLce
import LeanVM.Guest.EndExecYDeployed
import LeanVM.Guest.EndExecYWitCells
import LeanVM.Guest.EndExecYShape
import LeanVM.Guest.EndExecACur
import LeanVM.Guest.EndExecAKeep
import LeanVM.Guest.EndExecAGaps
import LeanVM.Guest.EndExecAUsed
import LeanVM.Guest.EndExecAExtra
import LeanVM.Guest.EndExecCAlign
import LeanVM.Guest.Budget.MainExact
import LeanVM.Guest.EndExecW
import LeanVM.Guest.EndExecRCld
import LeanVM.Guest.EndExecRCp
import LeanVM.Guest.EndExecRGkrC

/-!
# The end theorem

The certificates are the mode walk's (`Mode.guestCerts`, `main`'s, `Mode.guestE0`), the alignment
the deployed one (`Bridge.alignA`), and the hint tracks' invariant `YFin`: the witness streams'
cursor (`YCur`) and the bump pointer (`YAlloc`), each kept by a step given the other's premises
(`KeepY.and`, `InitY.and`: `XOf` is monotone in its hint invariant).

`execGaps_of : OpenGaps → ExecGaps …` is `ExecGaps.ofR` with every proved part: the certificates
(`Mode.modeCerts_guest`, `Mode.mainOk_guestCerts`, `Mode.guestCerts_entry_ne`), `main`'s exactness
(`Budget.mainExactHyp`), the alignment and its jumps (`Bridge.progAl`, `Bridge.alignA_main`,
`alLayout_alignA`, `jumpCells_at`), the `DEREF` pointers (`derefPow_all`), the computed hints
(`hintComputed_alignA`, `extraRef_alignA`), the witness hints (`hintWitness_alignA`,
`witCells_alignA`, `pushShape`), the allocation hints (`hintAlloc_alignA`, on `allocGaps_guest`), the cells the hints use
(`hintsUsed_alignA`), the tracks kept
(`keepY_alignA`, `keepY_allocA_guest`) and started (`initY_cur`, `initY_alloc`), the residuals
(`resTop_guestF`) and the termination facts (`termNode_guest`). `guest_prover_complete_of` is
`guest_prover_complete` from `OpenGaps`, which `openGaps` proves: the kernel checks every walk.
`guestExecution_complete_holds` is `Statement/`'s `GuestExecutionComplete`, the statement's
witness generation (`Prover.guestExecution`) being `guestRun guestAdvice` (`prover_guestExecution_eq`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Node
open LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Guest.Completeness
open LeanVM.Guest.Bridge (alignA)
open LeanVM.Prover.Exec
open scoped ENNReal

/-! ## Hint invariants in conjunction -/

theorem XOf.mono {Y Y' : Ref → St → Prop} (h : ∀ r s, Y r s → Y' r s) {r : Ref} {s : St}
    (hX : XOf Y r s) : XOf Y' r s :=
  ⟨hX.1, hX.2.1, h r s hX.2.2⟩

theorem OnRun.mono {Y Y' : Ref → St → Prop} (h : ∀ r s, Y r s → Y' r s) {r : Ref} {s : St}
    (hon : OnRun (XOf Y) r s) : OnRun (XOf Y') r s :=
  ⟨XOf.mono h hon.1, hon.2.1, hon.2.2⟩

/-- **Two hint invariants kept are kept together.** -/
theorem KeepY.and {Y₁ Y₂ : Ref → St → Prop} (h₁ : KeepY Y₁) (h₂ : KeepY Y₂) :
    KeepY fun r s ↦ Y₁ r s ∧ Y₂ r s := fun r hr C hC s op s1 s' hon hop e1 hm e ↦
  ⟨h₁ r hr C hC s op s1 s' (hon.mono fun _ _ h ↦ h.1) hop e1 hm e,
    h₂ r hr C hC s op s1 s' (hon.mono fun _ _ h ↦ h.2) hop e1 hm e⟩

/-- **Two hint invariants holding initially hold together.** -/
theorem InitY.and {Y₁ Y₂ : Ref → St → Prop} (h₁ : InitY Y₁) (h₂ : InitY Y₂) :
    InitY fun r s ↦ Y₁ r s ∧ Y₂ r s := fun r hr C m hC hm ↦ ⟨h₁ r hr C m hC hm, h₂ r hr C m hC hm⟩

/-- **The hint tracks' invariant on the deployed alignment**: the witness streams' cursor and the
bump pointer. -/
abbrev YFin (r : Ref) (s : St) : Prop := YCur alignA r s ∧ YAlloc alignA r s

/-! ## The open facts (none left) -/

/-- **The facts the executor's completeness on the guest still rests on.** -/
structure OpenGaps : Prop where
  /-- Mode walk track: the walks (`walk … = true`) the kernel does not check (`Mode.ModeHyps`,
  generated from `infer.py`'s `HELD_NS`, now empty). -/
  modeHyps : Mode.ModeHyps

/-- **No open fact is left**: the kernel checks every walk, so `Mode.ModeHyps` has no field. -/
theorem openGaps : OpenGaps := ⟨⟨⟩⟩

/-! ## The assembly -/

/-- **`ExecGaps` from the open facts**, every proved part wired in. -/
theorem execGaps_of (O : OpenGaps) :
    ExecGaps Mode.guestCerts Fn.«main».modeCert Mode.guestE0 (XOf YFin) (fun _ ↦ ProAt) :=
  ExecGaps.ofR (A := alignA) (Mode.modeCerts_guest O.modeHyps) Mode.mainOk_guestCerts Budget.mainExactHyp
    (hintAlloc_alignA sizesAt_guest allocReady_guest fun _ _ h ↦ h.2)
    (hintWitness_alignA (witCells_alignA witPtrRes_guest) pushShape fun _ _ h ↦ h.1)
    (hintComputed_alignA extraRef_alignA)
    (resTop_guestF (fun K hK ↦ by
      simp only [Res.resExc, List.mem_cons, List.not_mem_nil, or_false] at hK
      rcases hK with rfl | rfl | rfl | rfl | rfl
      · exact resCld_alignA
      · exact resCp_alignA
      · exact resLce0_alignA
      · exact resLce16_alignA
      · exact resLy_alignA))
    termNode_guest Bridge.progAl Bridge.alignA_main alLayout_alignA jumpCells_at Mode.guestCerts_entry_ne
    (derefPow_all _)
    (hintsUsed_alignA sizesAt_guest allocReady_guest (witCells_alignA witPtrRes_guest) fun _ _ h ↦ h)
    (KeepY.and (keepY_alignA (derefPow_all _) fun _ _ h ↦ h) keepY_allocA_guest)
    (InitY.and (initY_cur alignA) (initY_alloc alignA))

/-- **The executor runs the guest program to completion on the guest's advice**, given the open
facts. -/
theorem guestExecution_complete_of (O : OpenGaps) : AdviceComplete guestAdvice :=
  guestExecution_complete_on_honest_children (execGaps_of O)

open OracleComp OracleSpec in
/-- **The composed prover's proof is accepted**, given the open facts: `guest_prover_complete`. -/
theorem guest_prover_complete_of (O : OpenGaps) (statement : NodeStatement) (witness : NodeWitness)
    (hrel : NodeRelation (bytecodeWords guestProgram) (deployedSeed guestProgram) statement witness)
    (hlim : DeployedLimits statement witness) (hon : ∀ child ∈ witness.children, HonestChild child) :
    ∃ t, guestRun guestAdvice statement witness = .ok t ∧ ∀ ρ, 1 ≤ ρ ∧ ρ ≤ 4 →
      Pr{let v ← completenessExperiment leanVmHonestProver guestProgram
          (PublicInput.ofDigest (statementDigest (deployedSeed guestProgram) statement)) t ρ (2 ^ 35)}[
          v = false] ≤ (2 : ℝ≥0∞)⁻¹ ^ 256 ∧
      Pr{let accepted ← Common.runWithRandomPermutation (do
          match ← LeanVM.leanVmHonestProver Common.queryPermutation guestProgram
              (PublicInput.ofDigest (statementDigest (deployedSeed guestProgram) statement)) t ρ
              (2 ^ 35) with
          | none => pure false
          | some proof =>
            verifierRefusingZero Common.queryPermutation guestProgram
              (PublicInput.ofDigest (statementDigest (deployedSeed guestProgram) statement)) proof)}[
          accepted = false] ≤ (2 : ℝ≥0∞)⁻¹ ^ 100 :=
  guest_prover_complete (execGaps_of O) statement witness hrel hlim hon

/-! ## The statement's witness generation -/

/-- **The statement's advice is `guestAdvice`**, on a bytecode of the guest's length. -/
theorem prover_guestAdvice_eq {bytecode : List K} (h : bytecode.length = 2 ^ 23) (seed : Digest)
    (s : NodeStatement) (w : NodeWitness) :
    Prover.guestAdvice bytecode seed s w = guestAdvice seed s w := by
  rw [Prover.guestAdvice, guestAdvice, Prover.guestStreams, ProverGuest.honestPushes_eq,
    Hints.honestStreams,
    honestPushes_len (b' := bytecodeShape) (by rw [h, bytecodeShape, List.length_replicate])]
  rfl

/-- **The statement's execution of the guest is `guestRun guestAdvice`.** -/
theorem prover_guestExecution_eq (s : NodeStatement) (w : NodeWitness) :
    Prover.guestExecution guestProgram s w = guestRun guestAdvice s w := by
  simp only [Prover.guestExecution, guestRun]
  rw [prover_guestAdvice_eq (bytecode := bytecodeWords guestProgram) End.bytecode_length]

/-- **The executor runs the guest program to completion on the statement's advice**: `Statement/`'s
`GuestExecutionComplete`, the field `guestExecutionComplete` of `Statement.Theorems`. -/
theorem guestExecution_complete_holds : Completeness.GuestExecutionComplete :=
  fun s w hrel hlim hon ↦
    let ⟨t, he, hv, hsz⟩ := guestExecution_complete_of openGaps s w hrel hlim hon
    ⟨t, (prover_guestExecution_eq s w).trans he, hv, hsz⟩

open OracleComp OracleSpec in
/-- **The guest's prover makes the honest prover's proof of its execution**: where `guestExecution`
returns `t`, `guestProve`'s proof is rejected, refused or not made exactly as the honest prover's
proof of `t` (`Completeness`, `HonestProofRarelyRefused`), for any program `guest`. -/
theorem guestProve_complete {guest : LeanIsaProgram} {s : NodeStatement} {w : NodeWitness}
    {t : Execution guest} (he : Prover.guestExecution guest s w = .ok t)
    (hv : ValidExecution guest (PublicInput.ofDigest (statementDigest (deployedSeed guest) s)) t)
    (hsz : t.committedSize ≤ 2 ^ 30) {ρ : ℕ} (hρ : 1 ≤ ρ ∧ ρ ≤ 4) (hC : LeanVM.Completeness)
    (hR : HonestProofRarelyRefused) :
    let input := PublicInput.ofDigest (statementDigest (deployedSeed guest) s)
    Pr{let accepted ← Common.runWithRandomPermutation (do
        match ← Prover.guestProve Common.queryPermutation guest s w ρ (2 ^ 35) with
        | none => pure false
        | some proof => leanVmVerifier Common.queryPermutation guest input proof)}[
        accepted = false] ≤ (2 : ℝ≥0∞)⁻¹ ^ 256 ∧
    Pr{let accepted ← Common.runWithRandomPermutation (do
        match ← Prover.guestProve Common.queryPermutation guest s w ρ (2 ^ 35) with
        | none => pure false
        | some proof => verifierRefusingZero Common.queryPermutation guest input proof)}[
        accepted = false] ≤ (2 : ℝ≥0∞)⁻¹ ^ 100 := by
  have hp : Prover.guestProve Common.queryPermutation guest s w ρ (2 ^ 35) =
      leanVmHonestProver Common.queryPermutation guest
        (PublicInput.ofDigest (statementDigest (deployedSeed guest) s)) t ρ (2 ^ 35) := by
    simp only [Prover.guestProve, he]
    rfl
  intro input
  rw [hp]
  exact ⟨hC _ _ t ρ hv hsz hρ, hR _ _ t ρ hv hsz hρ⟩

end LeanVM.Guest.EndExec
