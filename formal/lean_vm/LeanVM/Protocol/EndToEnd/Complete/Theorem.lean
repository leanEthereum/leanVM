/-
  LeanVM.Protocol.EndToEnd.Complete.Theorem

  Perfect completeness of the deployed leanVM verifier: from a witness satisfying leanISA's
  constraint system at admissible sizes, an honest strategy makes the interactive run of the
  verifier program accept against every challenge function, and the compiled honest prover
  produces a proof the compiled verifier accepts, for every hash function, when the proof-of-work
  searches succeed.
-/

module

public import LeanVM.Protocol.EndToEnd.Complete.Assemble
public import LeanVM.Protocol.EndToEnd.Complete.Bus
public import LeanVM.Protocol.EndToEnd.Complete.Table
public import LeanVM.Protocol.EndToEnd.Complete.Flock
public import LeanVM.Protocol.EndToEnd.Complete.Ring
public import LeanVM.Protocol.EndToEnd.Front.FlockTerminal
public import LeanVM.Protocol.LeanIsa.Complete
public import LeanVM.Arithmetization.Completeness.Theorem

/-!
# Perfect completeness of the leanVM verifier

The verifier is the program `leanVmProgram` (`LeanVM.Protocol.Verifier`), the
transcription of `verify_execution` of `python-verifier/verifier.py` at leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`. Its honest prover (`honestStrategy`) is assembled
(`Complete.Assemble`) from the phases' honest scripts: the announcement and the commitment
(`Complete.Sizes`), the bus (`Complete.Bus`), the table sumcheck (`Complete.Table`), the public
input (`Complete.Public`), Flock (`Complete.Flock`), ring switching (`Complete.Ring`) and the WHIR
opening (`Whir.Complete.Opening`).

* `runI_leanVmProgram`: from a stack satisfying `M3Honest` of the leanISA instance (`M3Holds`,
  and every padding row holds its table's public padding row) at admissible sizes, for a valid rate, the honest strategy wins every interactive run with well-shaped words.
* `leanVm_complete`: from a witness `w` satisfying leanISA's constraint system (`SatisfiedBy`) at
  admissible sizes, through the adaptor's completeness (`m3Honest_stackOf`).
* `exists_prove_verifyWith`: for every hash function the compiled honest prover produces a proof
  the compiled verifier accepts from the seed of the program and the public digest, as soon as
  every proof-of-work search finds its nonce below `fuel` (`exists_prove_runProof`); at BLAKE2s
  this is the deployed verifier `verify`.
* `leanVm_complete_of_execution`: a valid execution of at most `2^32` steps
  (`constraintCompleteness`) has a witness representing it, at sizes for which, when they are
  admissible, the honest strategy wins.

The honest prover's public statement is the public input's digest `publicDigest input`, whose
halves are the input's two memory words (`digestScalars_publicDigest`).

## The one open hypothesis

Every theorem here takes `WalkFaithful blake2sFlockSpec` (`Front.FlockTerminal`): the verifier's
forward walk of the BLAKE2s circuit (`blake2sRowValues`, `verifier.py:1179-1288`) computes the left
and right products of the R1CS of `blake2sCircuit`. The lincheck's terminal check passes for the
honest prover exactly when the program's terminal value is ArkLib's (`TerminalFaithful`), which
`Front.terminalFaithful` derives from it. It is a fidelity fact of the transcription, shared with
the soundness side, and not a property of the honest prover; it was checked numerically on all
`2^14` rows of both products at a pseudo-random weight vector, without a mismatch. Everything
else is proved: the phases carry no other hypothesis.
-/

namespace LeanVM.Protocol.EndToEnd.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.Whir.Complete LeanVM.Protocol.Blake2sHash
open Air.Flat (EnsembleWitness)

@[expose] public section

/-- The honest phases of the leanVM verifier for the stack `q`. -/
noncomputable def leanVmPhases (prog : Program) (s : Sizes) (q : Column (leanIsaμ prog s)) :
    Phases :=
  ⟨hBus prog s q, hTable prog s q, hFlock prog s q, hRing⟩

attribute [local irreducible] Follows in
/-- The phases are honest for a stack satisfying `M3Honest` at admissible sizes. -/
theorem leanVmPhases_honest {prog : Program} {s : Sizes} {input : PublicInput}
    {q : Column (leanIsaμ prog s)} (hs : s.Admissible prog) (hq : M3Honest (inst prog s) input q)
    (hwalk : WalkFaithful Blake2sFlock.blake2sFlockSpec) :
    (leanVmPhases prog s q).Honest prog s q where
  bus cs := follows_verifyBusBalance hs hq cs
  table bus hb cs := follows_tablePhase hq.1 bus hb cs
  flock cs := follows_verifyFlock hq.1 (terminalFaithful _ prog s hwalk) cs
  ring r hr cs := follows_ringSwitch r hr cs

/-- The honest strategy of the leanVM verifier for the stack `q` and the rate `ρ`. -/
noncomputable def leanVmProver (prog : Program) (s : Sizes) (ρ : ℕ)
    (q : Column (leanIsaμ prog s)) : Strategy :=
  honestStrategy prog s ρ q (leanVmPhases prog s q)

/-- **Interactive perfect completeness from the relation.** For sizes admissible for the program,
a valid rate and a stack satisfying `M3Honest` of the leanISA instance on the input, the honest
strategy makes the verifier program accept against every challenge function, committing
well-shaped words. -/
theorem runI_leanVmProgram {prog : Program} {s : Sizes} {input : PublicInput} {ρ : ℕ}
    {q : Column (leanIsaμ prog s)} (hs : s.Admissible prog) (hρ : validRate ρ)
    (hq : M3Honest (inst prog s) input q) (hwalk : WalkFaithful Blake2sFlock.blake2sFlockSpec)
    (chal : List Ev → E) :
    runI (leanVmProgram (bytecodeWords prog) (publicDigest input)) (leanVmProver prog s ρ q)
        chal = some true ∧
      shapedI (leanVmProgram (bytecodeWords prog) (publicDigest input)) (leanVmProver prog s ρ q)
        chal :=
  runI_leanVmProgram_of hs hρ hq.1 _ (leanVmPhases_honest hs hq hwalk) chal

/-- **Perfect completeness of the leanVM verifier, interactively.** A witness satisfying
leanISA's constraint system on the input, at admissible sizes, gives, for every valid rate, a
strategy that makes the verifier program on the program's bytecode and the input's digest
accept against every challenge function, with well-shaped words. -/
theorem leanVm_complete {prog : Program} {input : PublicInput}
    {w : EnsembleWitness (leanIsaEnsemble prog)} {s : Sizes} {ρ : ℕ}
    (h : SatisfiedBy prog input w) (hsz : Sizes.ofWitness w = some s) (hs : s.Admissible prog)
    (hρ : validRate ρ) (hwalk : WalkFaithful Blake2sFlock.blake2sFlockSpec) :
    ∃ S : Strategy, ∀ chal : List Ev → E,
      runI (leanVmProgram (bytecodeWords prog) (publicDigest input)) S chal = some true ∧
        shapedI (leanVmProgram (bytecodeWords prog) (publicDigest input)) S chal :=
  ⟨_, runI_leanVmProgram hs hρ (m3Honest_stackOf h hsz padLimbs_compress) hwalk⟩

/-- **Perfect completeness of the compiled leanVM verifier.** A witness satisfying leanISA's
constraint system at admissible sizes and a valid rate give, for every hash function `H`, a
strategy whose compiled proof the compiled verifier accepts, from the seed of the bytecode and the
public digest, as soon as every proof-of-work search finds its nonce below `fuel`. -/
theorem exists_prove_verifyWith (H : Bytes → Digest) {prog : Program} {input : PublicInput}
    {w : EnsembleWitness (leanIsaEnsemble prog)} {s : Sizes} {ρ : ℕ}
    (h : SatisfiedBy prog input w) (hsz : Sizes.ofWitness w = some s) (hs : s.Admissible prog)
    (hρ : validRate ρ) (hwalk : WalkFaithful Blake2sFlock.blake2sFlockSpec) (fuel : ℕ)
    (hg : ∀ hist bits k cv,
      (leanVmProgram (bytecodeWords prog) (publicDigest input)).after hist = some (.grind bits k) →
        findNonce H bits cv fuel ≠ none) :
    ∃ S π, prove H (leanVmProgram (bytecodeWords prog) (publicDigest input)) S
        (Id.run (seedWith H (bytecodeWords prog) (publicDigest input))) fuel = some π ∧
      Id.run (verifyWith (m := Id) H (bytecodeWords prog) (publicDigest input) π) = true := by
  obtain ⟨S, hS⟩ := leanVm_complete h hsz hs hρ hwalk
  obtain ⟨π, hπ, hacc⟩ := exists_prove_runProof H _ S _ fuel (fun chal ↦ (hS chal).1)
    (fun chal ↦ (hS chal).2) hg
  exact ⟨S, π, hπ, hacc⟩

/-- **The deployed verifier accepts the honest proof**: `exists_prove_verifyWith` at BLAKE2s. -/
theorem exists_prove_verify {prog : Program} {input : PublicInput}
    {w : EnsembleWitness (leanIsaEnsemble prog)} {s : Sizes} {ρ : ℕ}
    (h : SatisfiedBy prog input w) (hsz : Sizes.ofWitness w = some s) (hs : s.Admissible prog)
    (hρ : validRate ρ) (hwalk : WalkFaithful Blake2sFlock.blake2sFlockSpec) (fuel : ℕ)
    (hg : ∀ hist bits k cv,
      (leanVmProgram (bytecodeWords prog) (publicDigest input)).after hist = some (.grind bits k) →
        findNonce blake2sBytes bits cv fuel ≠ none) :
    ∃ S π, prove blake2sBytes (leanVmProgram (bytecodeWords prog) (publicDigest input)) S
        (seed (bytecodeWords prog) (publicDigest input)) fuel = some π ∧
      Verifier.verify (bytecodeWords prog) (publicDigest input) π = true :=
  exists_prove_verifyWith blake2sBytes h hsz hs hρ hwalk fuel hg

/-- **From an execution.** A valid execution of at most `2^32` steps has a witness representing
it at some sizes; when those sizes are admissible, for every valid rate the honest strategy makes
the verifier program accept against every challenge function. -/
theorem leanVm_complete_of_execution {prog : Program} {input : PublicInput} {t : Trace prog}
    (hv : ValidExecution prog input t) (hsteps : t.steps ≤ 2 ^ maxLogRows)
    (hwalk : WalkFaithful Blake2sFlock.blake2sFlockSpec) :
    ∃ w s, SatisfiedBy prog input w ∧ AssignmentRepresents w t ∧ Sizes.ofWitness w = some s ∧
      (s.Admissible prog → ∀ ρ, validRate ρ → ∃ S : Strategy, ∀ chal : List Ev → E,
        runI (leanVmProgram (bytecodeWords prog) (publicDigest input)) S chal = some true ∧
          shapedI (leanVmProgram (bytecodeWords prog) (publicDigest input)) S chal) := by
  obtain ⟨w, hw, hrep⟩ := constraintCompleteness hv hsteps
  obtain ⟨s, hsz⟩ := sizes_of_satisfiedBy hw
  exact ⟨w, s, hw, hrep, hsz, fun hs ρ hρ ↦ leanVm_complete hw hsz hs hρ hwalk⟩

end
end LeanVM.Protocol.EndToEnd.Complete
