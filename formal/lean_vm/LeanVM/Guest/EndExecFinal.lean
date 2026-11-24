/-
  LeanVM.Guest.EndExecFinal

  The executor's completeness on the guest: every proved part wired into `ExecGaps`.
-/

module

public import LeanVM.Guest.EndExecHonest
public import LeanVM.Guest.ProverGuest
public import LeanVM.Guest.CoreMode.Fam.Res
public import LeanVM.Guest.EndExecCore
public import LeanVM.Guest.CoreMode.Gen.Certs
public import LeanVM.Guest.CoreMode.Gen.AnyLinkOk
public import LeanVM.Guest.EndExecYDeployed
public import LeanVM.Guest.EndExecYWitCells
public import LeanVM.Guest.EndExecYShape
public import LeanVM.Guest.EndExecACur
public import LeanVM.Guest.EndExecAKeep
public import LeanVM.Guest.EndExecAGaps
public import LeanVM.Guest.EndExecAUsed
public import LeanVM.Guest.EndExecAExtra
public import LeanVM.Guest.EndExecCAlign
public import LeanVM.Guest.Budget.MainExact
public import LeanVM.Guest.EndExecW

@[expose] public section

/-!
# The end theorem

`execGaps : ExecGaps …` is `ExecGaps.ofR` with every proved part: the core route's certificates (`allCerts`, every
function's `CoreMode.coreCerts`, closed by `assemble` from `CoreMode.coreFacts`: `assembled`, `CoreMode.mainOk_core`,
with their residuals and termination facts), `main`'s exactness (`Budget.mainExactHyp`), the deployed alignment
and its jumps (`Bridge.alignA`, `Bridge.progAl`, `Bridge.alignA_main`, `alLayout_alignA`, `jumpCells_at`), the
`DEREF` pointers (`derefPow_all`), the computed, witness and allocation hints (`hintComputed_alignA`,
`extraRef_alignA`, `hintWitness_alignA`, `witCells_alignA`, `pushShape`, `hintAlloc_alignA` on `allocGaps_guest`),
the cells the hints use (`hintsUsed_alignA`), the hint tracks' invariant `YFin` (the witness streams' cursor
`YCur` and the bump pointer `YAlloc`, kept, `keepY_alignA`, `keepY_allocA_guest`, and started, `initY_cur`,
`initY_alloc`, each given the other's premises by `KeepY.and`, `InitY.and`), and each frame an honest instance
(`coreHonAll_X`). From it `honestAdvice_complete`, and `guestExecution_complete_holds` is `Statement/`'s
`GuestExecutionComplete`, the statement's witness generation (`guestExecution`) being `guestRun honestAdvice`
(`prover_guestExecution_eq`).
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

/-! ## The assembly -/

/-- **The end theorem's certificates**: the core route's, every function's. -/
noncomputable abbrev allCerts : List Mode.Cert := CoreMode.coreCerts

/-- **The certificates closed**, with their residuals and termination facts. -/
theorem assembled :
    ModeCerts allCerts Fn.«main».modeCert Mode.guestE0 ∧ (∀ K ∈ allCerts, K.F.entry ≠ 0) ∧
      ResTop allCerts alignA ∧ TermNode allCerts :=
  assemble (A := alignA) CoreMode.coreFacts

/-- **`ExecGaps`**, every proved part wired in. -/
theorem execGaps :
    ExecGaps allCerts Fn.«main».modeCert Mode.guestE0 (XOf YFin) (fun _ ↦ ProAt) :=
  have h := assembled
  ExecGaps.ofR (A := alignA) h.1 CoreMode.mainOk_core Budget.mainExactHyp
    (hintAlloc_alignA sizesAt_guest allocReady_guest fun _ _ h ↦ h.2)
    (hintWitness_alignA (witCells_alignA witPtrRes_guest) pushShape fun _ _ h ↦ h.1)
    (hintComputed_alignA extraRef_alignA)
    h.2.2.1 h.2.2.2 Bridge.progAl Bridge.alignA_main alLayout_alignA jumpCells_at h.2.1
    (derefPow_all _)
    (hintsUsed_alignA sizesAt_guest allocReady_guest (witCells_alignA witPtrRes_guest) fun _ _ h ↦ h)
    (KeepY.and (keepY_alignA (derefPow_all _) fun _ _ h ↦ h) keepY_allocA_guest)
    (InitY.and (initY_cur alignA) (initY_alloc alignA))
    (coreHonAll_X h.1 h.2.1 Bridge.progAl Bridge.alignA_main
      jumpCells_at alLayout_alignA (fun _ _ h ↦ by rw [Bridge.alignA_of h]; rfl) anyLink_ok)

/-- **The executor runs the guest program to completion on the guest's advice**, unless a child's
proof exhibits a Keccak-256 collision. -/
theorem honestAdvice_complete : AdviceComplete honestAdvice :=
  honestExecution_complete_on_accepted_children execGaps

/-! ## The statement's witness generation -/

/-- **The statement's advice is `honestAdvice`**, on a bytecode of the guest's length. -/
theorem prover_guestAdvice_eq {bytecode : List K} (h : bytecode.length = 2 ^ 23) (seed : Digest)
    (s : NodeStatement) (w : NodeWitness) :
    guestAdvice bytecode seed s w = honestAdvice seed s w := by
  rw [guestAdvice, honestAdvice, guestStreams, ProverGuest.honestPushes_eq,
    Hints.honestStreams,
    honestPushes_len (b' := bytecodeShape) (by rw [h, bytecodeShape, List.length_replicate])]
  rfl

/-- **The statement's execution of the guest is `guestRun honestAdvice`.** -/
theorem prover_guestExecution_eq (s : NodeStatement) (w : NodeWitness) :
    guestExecution guestProgram s w = guestRun honestAdvice s w := by
  simp only [guestExecution, guestRun]
  rw [prover_guestAdvice_eq (bytecode := bytecodeWords guestProgram) End.bytecode_length]

/-- **The executor runs the guest program to completion on the statement's advice**, unless a
child's proof exhibits a Keccak-256 collision: `Statement/`'s `GuestExecutionComplete`, the field
`guestExecutionComplete` of `Statement.Theorems`. -/
theorem guestExecution_complete_holds : Completeness.GuestExecutionComplete :=
  fun s w hrel hlim ↦ (honestAdvice_complete s w hrel hlim).imp_left
    fun ⟨t, he, hv, hsz⟩ ↦ ⟨t, (prover_guestExecution_eq s w).trans he, hv, hsz⟩

/-- **The executor runs the guest program to completion on the statement's advice on honest
children**, with no collision alternative: a node within the deployed limits whose children carry
honest proofs (`HonestChild`) has acceptable children (`acceptableChildren_of_honest`). -/
theorem guestExecution_complete_on_honest_children (s : NodeStatement) (w : NodeWitness)
    (hrel : NodeRelation (bytecodeWords guestProgram) (deployedSeed guestProgram) s w)
    (hlim : DeployedLimits s w) (hon : ∀ child ∈ w.children, HonestChild child) :
    ∃ execution, guestExecution guestProgram s w = .ok execution ∧
      ValidExecution guestProgram
        (PublicInput.ofDigest (statementDigest (deployedSeed guestProgram) s)) execution ∧
      execution.committedSize ≤ 2 ^ 30 :=
  let ⟨t, he, hv, hsz⟩ := honestExecution_complete_of_childrenOk execGaps s w hrel hlim
    (acceptableChildren_of_honest hrel hon)
  ⟨t, (prover_guestExecution_eq s w).trans he, hv, hsz⟩

/-- **The executor runs the guest program to completion on the statement's advice on children
carrying the honest prover's proofs that the deployed verifier accepts**, with no collision
alternative: each child's fresh claim is true (`freshClaim_holds_of_leanVmVerifier`), so it is a
`HonestChild`. -/
theorem guestExecution_complete_on_verified_honest_children (s : NodeStatement) (w : NodeWitness)
    (hrel : NodeRelation (bytecodeWords guestProgram) (deployedSeed guestProgram) s w)
    (hlim : DeployedLimits s w)
    (hon : ∀ child ∈ w.children,
      let input := PublicInput.ofDigest (statementDigest (deployedSeed guestProgram) child.statement)
      (∃ (execution : Execution guestProgram) (ρ : ℕ),
        LeanVM.Prover.prove (m := Id) keccakF1600 guestProgram input execution ρ (2 ^ 35) =
          some child.proof) ∧
      leanVmVerifier (m := Id) keccakF1600 guestProgram input child.proof = true) :
    ∃ execution, guestExecution guestProgram s w = .ok execution ∧
      ValidExecution guestProgram
        (PublicInput.ofDigest (statementDigest (deployedSeed guestProgram) s)) execution ∧
      execution.committedSize ≤ 2 ^ 30 :=
  guestExecution_complete_on_honest_children s w hrel hlim fun child hc ↦
    ⟨freshClaim_holds_of_leanVmVerifier hrel hc (hon child hc).2, (hon child hc).1⟩

open OracleComp OracleSpec in
/-- **The guest's prover makes the honest prover's proof of its execution**: where `guestExecution`
returns `t`, `guestProve`'s proof is rejected or not made exactly as the honest prover's proof of
`t` (`Completeness`), for any program `guest`. -/
theorem guestProve_complete {guest : LeanIsaProgram} {s : NodeStatement} {w : NodeWitness}
    {t : Execution guest} (he : guestExecution guest s w = .ok t)
    (hv : ValidExecution guest (PublicInput.ofDigest (statementDigest (deployedSeed guest) s)) t)
    (hsz : t.committedSize ≤ 2 ^ 30) {ρ : ℕ} (hρ : 1 ≤ ρ ∧ ρ ≤ 4) (hC : LeanVM.Completeness) :
    let input := PublicInput.ofDigest (statementDigest (deployedSeed guest) s)
    Pr{let accepted ← Common.runWithRandomPermutation (do
        match ← guestProve Common.queryPermutation guest s w ρ (2 ^ 35) with
        | none => pure false
        | some proof => leanVmVerifier Common.queryPermutation guest input proof)}[
        accepted = false] ≤ (2 : ℝ≥0∞)⁻¹ ^ 256 := by
  have hp : guestProve Common.queryPermutation guest s w ρ (2 ^ 35) =
      LeanVM.Prover.prove Common.queryPermutation guest
        (PublicInput.ofDigest (statementDigest (deployedSeed guest) s)) t ρ (2 ^ 35) := by
    simp only [guestProve, he]
  intro input
  rw [hp]
  exact hC _ _ t ρ hv hsz hρ

end LeanVM.Guest.EndExec

end
