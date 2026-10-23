/-
  LeanVM.Protocol.EndToEnd.Completeness

  End-to-end completeness of the deployed leanVM verifier, unconditionally: the BLAKE2s walk's
  fidelity discharged.
-/

module

public import LeanVM.Protocol.EndToEnd.Complete.Theorem
public import LeanVM.Protocol.EndToEnd.Front.WalkFaithful

/-!
# End-to-end completeness

The deployed verifier is `Verifier.verify` (`Verifier.lean`), the
compiled reading at BLAKE2s of `leanVmProgram`, a transcription of `python-verifier/verifier.py`
at leanVM `127510d14c98ade4e8a97646c44fa7f1ff5e752d`. The statements here are those of
`EndToEnd.Complete` with their one fidelity hypothesis, that the verifier's walk of the BLAKE2s
circuit computes the Flock R1CS's rows, discharged by `walkFaithful_blake2sFlockSpec`.

* `leanVm_interactiveComplete`: from a witness satisfying leanISA's constraint system at
  admissible sizes, for a valid rate, an honest strategy makes the verifier program accept
  against every challenge function, committing well-shaped words.
* `leanVm_complete`: for every hash function, the compiled honest prover produces a proof the
  compiled verifier accepts, as soon as its proof-of-work searches find nonces below the fuel;
  `leanVm_complete_blake2s` is the deployed instance.
* `leanVm_complete_of_execution`: from a valid execution of at most `2^32` steps, a witness
  representing it, accepted as above when its sizes are admissible.

Completeness is perfect: the only way the honest prover fails is a proof-of-work search that finds
no nonce below the fuel, a search over BLAKE2s outputs about which nothing is claimed.
-/

namespace LeanVM.Protocol.EndToEnd

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.Blake2sHash
open Air.Flat (EnsembleWitness)

@[expose] public section

/-- **Interactive perfect completeness of the deployed verifier program.** -/
theorem leanVm_interactiveComplete {prog : Program} {input : PublicInput}
    {w : EnsembleWitness (leanIsaEnsemble prog)} {s : Sizes} {ρ : ℕ}
    (h : SatisfiedBy prog input w) (hsz : Sizes.ofWitness w = some s) (hs : s.Admissible prog)
    (hρ : validRate ρ) :
    ∃ S : Strategy, ∀ chal : List Ev → E,
      runI (leanVmProgram (bytecodeWords prog) (Complete.publicDigest input)) S chal = some true ∧
        shapedI (leanVmProgram (bytecodeWords prog) (Complete.publicDigest input)) S chal :=
  Complete.leanVm_complete h hsz hs hρ walkFaithful_blake2sFlockSpec

/-- **Completeness of the compiled verifier, for every hash function.** -/
theorem leanVm_complete (H : Bytes → Digest) {prog : Program} {input : PublicInput}
    {w : EnsembleWitness (leanIsaEnsemble prog)} {s : Sizes} {ρ : ℕ}
    (h : SatisfiedBy prog input w) (hsz : Sizes.ofWitness w = some s) (hs : s.Admissible prog)
    (hρ : validRate ρ) (fuel : ℕ)
    (hg : ∀ hist bits k cv,
      (leanVmProgram (bytecodeWords prog) (Complete.publicDigest input)).after hist =
          some (.grind bits k) → findNonce H bits cv fuel ≠ none) :
    ∃ S π, prove H (leanVmProgram (bytecodeWords prog) (Complete.publicDigest input)) S
        (Id.run (seedWith H (bytecodeWords prog) (Complete.publicDigest input))) fuel = some π ∧
      Id.run (verifyWith (m := Id) H (bytecodeWords prog) (Complete.publicDigest input) π) =
        true :=
  Complete.exists_prove_verifyWith H h hsz hs hρ walkFaithful_blake2sFlockSpec fuel hg

/-- **Completeness of the deployed verifier**: the BLAKE2s instance of `leanVm_complete`. -/
theorem leanVm_complete_blake2s {prog : Program} {input : PublicInput}
    {w : EnsembleWitness (leanIsaEnsemble prog)} {s : Sizes} {ρ : ℕ}
    (h : SatisfiedBy prog input w) (hsz : Sizes.ofWitness w = some s) (hs : s.Admissible prog)
    (hρ : validRate ρ) (fuel : ℕ)
    (hg : ∀ hist bits k cv,
      (leanVmProgram (bytecodeWords prog) (Complete.publicDigest input)).after hist =
          some (.grind bits k) → findNonce blake2sBytes bits cv fuel ≠ none) :
    ∃ S π, prove blake2sBytes (leanVmProgram (bytecodeWords prog) (Complete.publicDigest input)) S
        (seed (bytecodeWords prog) (Complete.publicDigest input)) fuel = some π ∧
      Verifier.verify (bytecodeWords prog) (Complete.publicDigest input) π = true :=
  Complete.exists_prove_verify h hsz hs hρ walkFaithful_blake2sFlockSpec fuel hg

/-- **Completeness from an execution.** -/
theorem leanVm_complete_of_execution {prog : Program} {input : PublicInput} {t : Trace prog}
    (hv : ValidExecution prog input t) (hsteps : t.steps ≤ 2 ^ maxLogRows) :
    ∃ w s, SatisfiedBy prog input w ∧ AssignmentRepresents w t ∧ Sizes.ofWitness w = some s ∧
      (s.Admissible prog → ∀ ρ, validRate ρ → ∃ S : Strategy, ∀ chal : List Ev → E,
        runI (leanVmProgram (bytecodeWords prog) (Complete.publicDigest input)) S chal =
            some true ∧
          shapedI (leanVmProgram (bytecodeWords prog) (Complete.publicDigest input)) S chal) :=
  Complete.leanVm_complete_of_execution hv hsteps walkFaithful_blake2sFlockSpec

end
end LeanVM.Protocol.EndToEnd
