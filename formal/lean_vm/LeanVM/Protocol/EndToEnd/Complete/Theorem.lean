/-
  LeanVM.Protocol.EndToEnd.Complete.Theorem

  Perfect completeness of the deployed leanVM verifier: from a witness satisfying leanISA's
  constraint system at admissible sizes, an honest strategy makes the interactive run of the
  verifier program accept against every challenge function, and the compiled honest prover
  produces a proof the compiled verifier accepts, for every hash function and permutation, when
  the proof-of-work searches succeed.
-/

module

public import LeanVM.Protocol.EndToEnd.Complete.Assemble
public import LeanVM.Protocol.EndToEnd.Complete.Bus
public import LeanVM.Protocol.EndToEnd.Complete.BusDepth
public import LeanVM.Protocol.EndToEnd.Sound.Moves
public import LeanVM.Protocol.EndToEnd.Complete.Table
public import LeanVM.Protocol.EndToEnd.Complete.Ring
public import LeanVM.Protocol.LeanIsa.Complete
public import LeanVM.Arithmetization.Completeness.Theorem
public import LeanVM.Protocol.WithHash

/-!
# Perfect completeness of the leanVM verifier

The verifier is the program `leanVmVerifierProgram` (`LeanVM.Protocol.Verifier`), the transcription
(`Statement/LeanVmVerifier.lean`) of `verify_execution`, `crates/verifier/src/lib.rs:243-363` at
leanVM `f128`. Its honest prover (`honestStrategy`) is assembled
(`Complete.Assemble`) from the phases' honest scripts: the announcement, the commitment and its
out-of-domain sample (`Complete.Sizes`), the bus (`Complete.Bus`, its depth below `64` by
`Complete.BusDepth`), the table sumcheck (`Complete.Table`), the public input
(`Complete.Public`), the Keccak phase (`Complete.KeccakPhase`, the Keccak reduction's honest
prover `KeccakGkr.hKeccak`), ring switching (`Complete.Ring`) and the WHIR opening
(`Whir.Complete.Opening`, its completeness `Whir.Complete.openingComplete`).

* `runI_leanVmProgram`: from a stack satisfying `M3Honest` of the leanISA instance (`M3Holds`,
  and every padding row holds its table's public padding row) at admissible sizes, for a valid
  rate, the honest strategy wins every interactive run with well-shaped words.
* `leanVm_complete`: from a witness `w` satisfying leanISA's constraint system (`SatisfiedBy`) at
  admissible sizes, through the adaptor's completeness (`m3Honest_stackOf`).
* `exists_prove_verifyWith`: for every hash function `H` and permutation `F` the compiled honest
  prover produces a proof the compiled verifier accepts from the seed of the program and the
  public digest, as soon as every proof-of-work search finds its nonce below `fuel`
  (`exists_prove_runProof`); at Keccak-256 and Keccak-f[1600] this is the deployed verifier
  `verify` (`exists_prove_verify`).
* `leanVm_complete_of_execution`: a valid execution of at most `2^32` steps
  (`constraintCompleteness`) has a witness representing it, at sizes for which, when they are
  admissible, the honest strategy wins.

The honest prover's public statement is the public input's digest `publicInputDigest input`, whose
halves are the input's two memory words (`digestScalars_publicDigest`). No phase but the opening
carries a hypothesis.
-/

namespace LeanVM.Protocol.EndToEnd.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.Whir.Complete LeanVM.Protocol.KeccakHash
open Air.Flat (EnsembleWitness)

@[expose] public section

/-- The honest phases of the leanVM verifier for the stack `q`. -/
noncomputable def leanVmPhases (prog : LeanIsaProgram) (s : Sizes) (q : Column (leanIsaμ prog s)) :
    Phases :=
  ⟨hBus prog s q, hTable prog s q, hKeccakPhase prog s q, hRing⟩

attribute [local irreducible] Follows in
/-- The phases are honest for a stack satisfying `M3Honest` at admissible sizes. -/
theorem leanVmPhases_honest {prog : LeanIsaProgram} {s : Sizes} {input : PublicInput}
    {q : Column (leanIsaμ prog s)} (hs : s.Admissible prog) (hq : M3Honest (inst prog s) input q) :
    (leanVmPhases prog s q).Honest prog s q := by
  have hD : busDepth prog s < 64 := by have := busDepth_le hs; omega
  refine ⟨fun cs ↦ ?_, fun bus hb cs ↦ ?_, fun _ htrue z hl cs ↦ ?_, fun r hr cs ↦ ?_⟩
  · dsimp only [leanVmPhases]
    exact follows_verifyBusBalance hD hq cs
  · exact follows_tablePhase hq.1 bus hb cs
  · exact follows_keccakPhase prog s q hq.1 htrue z hl cs
  · exact follows_ringSwitch_leanIsa r hr cs

/-- The honest strategy of the leanVM verifier for the stack `q` and the rate `ρ`. -/
noncomputable def leanVmProver (prog : LeanIsaProgram) (s : Sizes) (ρ : ℕ)
    (q : Column (leanIsaμ prog s)) : Strategy :=
  honestStrategy prog s ρ q (leanVmPhases prog s q)

/-- **Interactive perfect completeness from the relation.** For sizes admissible for the program,
a valid rate and a stack satisfying `M3Honest` of the leanISA instance on the input, the honest
strategy makes the verifier program accept against every challenge function, committing
well-shaped words. -/
theorem runI_leanVmProgram {prog : LeanIsaProgram} {s : Sizes}
    {input : PublicInput} {ρ : ℕ}
    {q : Column (leanIsaμ prog s)} (hs : s.Admissible prog) (hρ : validRate ρ)
    (hq : M3Honest (inst prog s) input q) (chal : List Ev → E) :
    runI (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input)) (leanVmProver
        prog s ρ q)
        chal = some true ∧
      shapedI (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input)) (leanVmProver
          prog s ρ q)
        chal :=
  runI_leanVmProgram_of hs hρ hq.1 _ (leanVmPhases_honest hs hq) chal

/-- **Perfect completeness of the leanVM verifier, interactively.** A witness satisfying
leanISA's constraint system on the input, at admissible sizes, gives, for every valid rate, a
strategy that makes the verifier program on the program's bytecode and the input's digest
accept against every challenge function, with well-shaped words. -/
theorem leanVm_complete {prog : LeanIsaProgram} {input : PublicInput}
    {κ : ℕ} {w : EnsembleWitness (leanIsaEnsemble prog κ)} {s : Sizes} {ρ : ℕ}
    (h : SatisfiedBy prog input w) (hsz : Sizes.ofWitness w = some s) (hs : s.Admissible prog)
    (hρ : validRate ρ) :
    ∃ S : Strategy, ∀ chal : List Ev → E,
      runI (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input)) S chal =
          some true ∧
        shapedI (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input)) S chal :=
  ⟨_, runI_leanVmProgram hs hρ (m3Honest_stackOf h hsz)⟩

/-- **Perfect completeness of the compiled leanVM verifier.** A witness satisfying leanISA's
constraint system at admissible sizes and a valid rate give, for every hash function `H` and
permutation `F`, a strategy whose compiled proof the compiled verifier accepts, from the seed of
the bytecode and the public digest, as soon as every proof-of-work search finds its nonce below
`fuel`. -/
theorem exists_prove_verifyWith (H : Bytes → Digest)
    (F : KeccakState → KeccakState) {prog : LeanIsaProgram}
    {input : PublicInput} {κ : ℕ} {w : EnsembleWitness (leanIsaEnsemble prog κ)} {s : Sizes} {ρ : ℕ}
    (h : SatisfiedBy prog input w) (hsz : Sizes.ofWitness w = some s) (hs : s.Admissible prog)
    (hρ : validRate ρ) (fuel : ℕ)
    (hg : ∀ hist bits k sp,
      (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input)).after hist = some
          (.grind bits k) →
        findNonce F bits sp fuel ≠ none) :
    ∃ S π, prove H F (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input)) S
        (Id.run (seedWithHash (m := Id) H F (bytecodeWords prog) (publicInputDigest input))) fuel =
          some π ∧
      Id.run (verifyWithHash (m := Id) H F (bytecodeWords prog) (publicInputDigest input) π) =
          true := by
  obtain ⟨S, hS⟩ := leanVm_complete h hsz hs hρ
  obtain ⟨π, hπ, hacc⟩ := exists_prove_runProof H F _ S _ fuel
    (Sound.grindThenSample_leanVmProgram _ _) (fun chal ↦ (hS chal).1) (fun chal ↦ (hS chal).2) hg
  exact ⟨S, π, hπ, hacc⟩

/-- **The deployed verifier accepts the honest proof**: `exists_prove_verifyWith` at Keccak-256
and Keccak-f[1600]. -/
theorem exists_prove_verify {prog : LeanIsaProgram} {input : PublicInput}
    {κ : ℕ} {w : EnsembleWitness (leanIsaEnsemble prog κ)} {s : Sizes} {ρ : ℕ}
    (h : SatisfiedBy prog input w) (hsz : Sizes.ofWitness w = some s) (hs : s.Admissible prog)
    (hρ : validRate ρ) (fuel : ℕ)
    (hg : ∀ hist bits k sp,
      (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input)).after hist = some
          (.grind bits k) →
        findNonce keccakF1600 bits sp fuel ≠ none) :
    ∃ S π, prove keccak256 keccakF1600 (leanVmVerifierProgram (bytecodeWords prog)
        (publicInputDigest input)) S
        (seed (bytecodeWords prog) (publicInputDigest input)) fuel = some π ∧
      Verifier.verify (bytecodeWords prog) (publicInputDigest input) π = true :=
  exists_prove_verifyWith keccak256 keccakF1600 h hsz hs hρ fuel hg

/-- **From an execution.** A valid execution of at most `2^32` steps has a witness representing
it at some sizes; when those sizes are admissible, for every valid rate the honest strategy makes
the verifier program accept against every challenge function. -/
theorem leanVm_complete_of_execution {prog : LeanIsaProgram}
    {input : PublicInput} {t : Execution prog}
    (hv : ValidExecution prog input t) (hsteps : t.stepCount ≤ 2 ^ maxLogRows) :
    ∃ (w : EnsembleWitness (leanIsaEnsemble prog t.logMemorySize)) (s : Sizes),
      SatisfiedBy prog input w ∧ AssignmentRepresents w t ∧ Sizes.ofWitness w = some s ∧
      (s.Admissible prog → ∀ ρ, validRate ρ → ∃ S : Strategy, ∀ chal : List Ev → E,
        runI (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input)) S chal =
            some true ∧
          shapedI (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input)) S
              chal) := by
  obtain ⟨w, hw, hrep⟩ := constraintCompleteness hv hsteps
  obtain ⟨s, hsz⟩ := sizes_of_satisfiedBy hw
  exact ⟨w, s, hw, hrep, hsz, fun hs ρ hρ ↦ leanVm_complete hw hsz hs hρ⟩

end
end LeanVM.Protocol.EndToEnd.Complete
