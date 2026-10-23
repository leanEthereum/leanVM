import LeanVM.Protocol.EndToEnd.Complete.Theorem

/-!
# Perfect completeness of the leanVM verifier: statement locks

Locks of the phases' simulations (`follows_verifyBusBalance`, `follows_tablePhase`,
`follows_verifyFlock`, `follows_ringSwitch`, `follows_verifyGkrGrandProducts` is locked in
`Complete/Gkr.lean`'s test) and of the assembled theorems (`leanVm_complete`,
`exists_prove_verifyWith`, `exists_prove_verify`, `leanVm_complete_of_execution`): a change of a
hypothesis or of the conclusion fails here. The fidelity facts the bus and the table phase rest
on are locked too (`pyFlush_eval`, `pyCountColumns`, `pyNConstraints`): they are what makes the
Python tables' bus and constraints the instance's.
-/

namespace LeanVMTests.Protocol.EndToEnd.Complete.Theorem

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.Verifier LeanVM.Protocol.LeanIsa LeanVM.Protocol.Compile
open LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Complete
open LeanVM.Protocol.Whir.Complete LeanVM.Protocol.Blake2sHash
open Air.Flat (EnsembleWitness)

-- Matching a statement against a theorem must not unfold the simulation into the scripts.
attribute [local irreducible] Follows

/-! ## The phases -/

example : ∀ {prog : Program} {s : Sizes} {input : PublicInput} {q : Column (leanIsaμ prog s)},
    s.Admissible prog → M3Honest (inst prog s) input q → ∀ (cs : Commits),
    Follows (fun cs' a b ↦ cs' = cs ∧ a = b ∧ BusGood prog s q b) (hBus prog s q)
      (verifyBusBalance .computed (verifierLayout prog s)) cs :=
  follows_verifyBusBalance

example : ∀ {prog : Program} {s : Sizes} {q : Column (leanIsaμ prog s)} {input : PublicInput},
    M3Holds (inst prog s) input q → ∀ (bus : BusResult), BusGood prog s q bus → ∀ (cs : Commits),
    Follows (fun cs' a b ↦ cs' = cs ∧ a = b ∧ TrueClaims prog s q b) (hTable prog s q bus)
      (tablePhase (verifierLayout prog s) bus) cs :=
  follows_tablePhase

example : ∀ {prog : Program} {s : Sizes} {input : PublicInput} {q : Column (leanIsaμ prog s)},
    M3Holds (inst prog s) input q → TerminalFaithful Blake2sFlock.blake2sFlockSpec prog s →
    ∀ (cs : Commits),
    Follows (fun cs' a b ↦ cs' = cs ∧ a = b ∧ FlockGood prog s q b) (hFlock prog s q)
      (verifyFlock .computed (blake2sR1csLogSize +
        (verifierLayout prog s).tableLogHeights.getD opBlake2s 0)) cs :=
  follows_verifyFlock

example : ∀ {prog : Program} {s : Sizes} {q : Column (leanIsaμ prog s)} (r : List E × List E),
    FlockGood prog s q r → ∀ (cs : Commits),
    Follows (fun cs' a b ↦ cs' = cs ∧ a = b ∧
        StackClaim.Holds (leanIsaμ prog s) (ringSwitchClaim (verifierLayout prog s) b.1 b.2) q ∧
        IsMultilinearFn (leanIsaμ prog s) (ringSwitchClaim (verifierLayout prog s) b.1 b.2).1)
      (hRing r.1 r.2) (ringSwitch r.1 r.2) cs :=
  follows_ringSwitch

/-! ## The fidelity of the Python tables -/

example : ∀ (t : Fin 6) (side : Side) (row : Fin (width (opIdx t)) → K),
    ((pySide t side).map fun coords ↦
        (List.range 16).map fun k ↦ (coords.getD k {}).evaluate (rowFn row)) =
      (((LeanIsa.flushes (opIdx t)).filter fun f ↦ decide (f.1 = side)).map
        fun f ↦ f.2.toList.map fun P ↦ ofK (P.eval row)) :=
  pyFlush_eval

example : ∀ t : Fin 6,
    (tables.getD t default).countColumns = (LeanIsa.counts (opIdx t)).map (·.val) :=
  pyCountColumns

example : tables.map Table.nConstraints = [0, 0, 0, 0, 2, 0] := pyNConstraints

/-! ## The assembled theorems -/

example : ∀ {prog : Program} {input : PublicInput} {w : EnsembleWitness (leanIsaEnsemble prog)}
    {s : Sizes} {ρ : ℕ}, SatisfiedBy prog input w → Sizes.ofWitness w = some s →
    s.Admissible prog → validRate ρ → WalkFaithful Blake2sFlock.blake2sFlockSpec →
    ∃ S : Strategy, ∀ chal : List Ev → E,
      runI (leanVmProgram (bytecodeWords prog) (publicDigest input)) S chal = some true ∧
        shapedI (leanVmProgram (bytecodeWords prog) (publicDigest input)) S chal :=
  leanVm_complete

example : ∀ (H : Bytes → Digest) {prog : Program} {input : PublicInput}
    {w : EnsembleWitness (leanIsaEnsemble prog)} {s : Sizes} {ρ : ℕ},
    SatisfiedBy prog input w → Sizes.ofWitness w = some s → s.Admissible prog → validRate ρ →
    WalkFaithful Blake2sFlock.blake2sFlockSpec → ∀ (fuel : ℕ),
    (∀ hist bits k cv,
      (leanVmProgram (bytecodeWords prog) (publicDigest input)).after hist = some (.grind bits k) →
        findNonce H bits cv fuel ≠ none) →
    ∃ S π, prove H (leanVmProgram (bytecodeWords prog) (publicDigest input)) S
        (Id.run (seedWith H (bytecodeWords prog) (publicDigest input))) fuel = some π ∧
      Id.run (verifyWith (m := Id) H (bytecodeWords prog) (publicDigest input) π) = true :=
  exists_prove_verifyWith

example : ∀ {prog : Program} {input : PublicInput} {w : EnsembleWitness (leanIsaEnsemble prog)}
    {s : Sizes} {ρ : ℕ}, SatisfiedBy prog input w → Sizes.ofWitness w = some s →
    s.Admissible prog → validRate ρ → WalkFaithful Blake2sFlock.blake2sFlockSpec → ∀ (fuel : ℕ),
    (∀ hist bits k cv,
      (leanVmProgram (bytecodeWords prog) (publicDigest input)).after hist = some (.grind bits k) →
        findNonce blake2sBytes bits cv fuel ≠ none) →
    ∃ S π, prove blake2sBytes (leanVmProgram (bytecodeWords prog) (publicDigest input)) S
        (seed (bytecodeWords prog) (publicDigest input)) fuel = some π ∧
      verify (bytecodeWords prog) (publicDigest input) π = true :=
  exists_prove_verify

example : ∀ {prog : Program} {input : PublicInput} {t : Trace prog},
    ValidExecution prog input t → t.steps ≤ 2 ^ maxLogRows →
    WalkFaithful Blake2sFlock.blake2sFlockSpec →
    ∃ w s, SatisfiedBy prog input w ∧ AssignmentRepresents w t ∧ Sizes.ofWitness w = some s ∧
      (s.Admissible prog → ∀ ρ, validRate ρ → ∃ S : Strategy, ∀ chal : List Ev → E,
        runI (leanVmProgram (bytecodeWords prog) (publicDigest input)) S chal = some true ∧
          shapedI (leanVmProgram (bytecodeWords prog) (publicDigest input)) S chal) :=
  leanVm_complete_of_execution

end LeanVMTests.Protocol.EndToEnd.Complete.Theorem
