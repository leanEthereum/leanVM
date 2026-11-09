/-
# Committed soundness games

The abstract security experiment isolating the main technical difficulty of
the code-binding proof. An adversary receives a vector-commitment key, commits
to some value `com`, obtains check randomness `l` *derived from `com`*, and
must produce a vector `c` that (i) is not a codeword, (ii) passes the code
check on `l`, and (iii) commits to `com`. The argument system plays no role
here: the game captures exactly the gap between the code checker's soundness
(which requires the non-codeword to be fixed *before* the randomness is
sampled) and the power of an adversary who may correlate its opened vector
with the randomness.

Two variants:
* the *non-interactive* game (`niCommittedSoundnessExp`): the adversary has
  access to a random oracle, and the check randomness is `H(com)`. This is the
  variant consumed by the code-binding proof.
* the *interactive* game (`intCommittedSoundnessExp`): a two-stage adversary
  without a random oracle; the game samples the check randomness uniformly
  after the adversary commits. This variant makes the rewinding analysis
  transparent: rerunning the second stage twice with independent randomness
  either produces two distinct vectors committing to the same commitment
  (breaking binding of the deterministic commit) or the same vector twice
  (fixed before fresh randomness, so the checker's soundness applies).

The two are related by the standard argument that guesses which random-oracle
query determined the challenge, at a multiplicative loss in the number of
queries; alternatively, the non-interactive game can be analyzed directly with
a forking lemma.

Benedikt Wagner's formalization (https://github.com/b-wagn/fv-pq-da), ported at 4475179c and
modified for VCVio afa6593.
-/
module

public import PqDas.Assumptions.ErasureCode
public import PqDas.Assumptions.VectorCommitment
public import PqDas.Assumptions.CodeChecker
public import PqDas.RomRuntime
public import PqDas.Defs

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace PqDas

variable {Γ Λ : Type} {k n : ℕ} {CkVC ComVC Opn L : Type}

/-! ### The non-interactive game -/

/-- The non-interactive committed soundness game: the adversary outputs
`(com, c)`; with `l := H(com)` (evaluated through the same oracle cache the
adversary interacted with), it wins if `c` is not a codeword, passes the code
check on `l`, and commits to `com`. -/
noncomputable def niCommittedSoundnessExp [Fintype Γ] [DecidableEq Λ]
    [DecidableEq ComVC] [SampleableType L]
    (C : ErasureCode Γ Λ k n) (vc : VectorCommitment Λ n CkVC ComVC Opn)
    (chk : CodeChecker Λ n L) (A : NiCsAdv Λ n CkVC ComVC L) : MeasureTheory.Measure Bool :=
  (roRuntime ComVC L).evalDist do
    let ckVC ← liftM vc.setup
    let (com, c) ← A ckVC
    let l ← HasQuery.query (spec := (ComVC →ₒ L)) com
    return (decide (c ∉ C.code) && chk.check l c && decide (vc.commit ckVC c = com))

/-- The winning probability of the non-interactive game is at most one. -/
lemma niCommittedSoundnessExp_le_one [Fintype Γ] [DecidableEq Λ]
    [DecidableEq ComVC] [SampleableType L]
    (C : ErasureCode Γ Λ k n) (vc : VectorCommitment Λ n CkVC ComVC Opn)
    (chk : CodeChecker Λ n L) (A : NiCsAdv Λ n CkVC ComVC L) (s : Set Bool) :
    niCommittedSoundnessExp C vc chk A s ≤ 1 :=
  (MeasureTheory.measure_mono (Set.subset_univ _)).trans
    (ProbCompRuntime.evalDist_apply_univ_le_one _ _)

/-! ### The interactive game -/

/-- A two-stage adversary against the interactive committed soundness game:
the first stage produces a commitment and private state; the second stage
answers uniformly sampled check randomness with a vector. Neither stage has
oracle access. The explicit `State` makes rewinding (rerunning the second
stage on the same state with fresh randomness) a plain program transformation. -/
structure IntCsAdv (Λ : Type) (n : ℕ) (CkVC ComVC L : Type) where
  /-- Private state passed between the two stages. -/
  State : Type
  /-- First stage: commit. -/
  stage1 : CkVC → ProbComp (ComVC × State)
  /-- Second stage: answer the check randomness with a vector. -/
  stage2 : State → L → ProbComp (Fin n → Λ)

/-- The interactive committed soundness game: after the adversary commits, the
game samples the check randomness `l` uniformly; the adversary then answers
with a vector `c` and wins under the same condition as the non-interactive
game. -/
def intCommittedSoundnessExp [Fintype Γ] [DecidableEq Λ]
    [DecidableEq ComVC] [SampleableType L]
    (C : ErasureCode Γ Λ k n) (vc : VectorCommitment Λ n CkVC ComVC Opn)
    (chk : CodeChecker Λ n L) (A : IntCsAdv Λ n CkVC ComVC L) : ProbComp Bool := do
  let ckVC ← vc.setup
  let (com, st) ← A.stage1 ckVC
  let l ← $ᵗ L
  let c ← A.stage2 st l
  return (decide (c ∉ C.code) && chk.check l c && decide (vc.commit ckVC c = com))

end PqDas
