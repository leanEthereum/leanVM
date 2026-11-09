module

public import Statement.LeanDa
public import Common.HashOracle
public import LeanDa.WithHash

@[expose] public section

/-!
# LeanDA's games with a Keccak-256 oracle, a proof device

The statement's model has coins, `π` and `π⁻¹` and nothing else (`Common.RandomPermutationOracles`): the adversary,
the argument's prover and verifier and LeanDA's verifier hash with Keccak-256 over `π`
(`Common.keccak256OverPermutation`). The proofs of this project reason with Keccak-256 as one more oracle
(`Common.KSpecH`, `Common.HashOracle`): these are the statement's arguments, games and end
statements in that model, as the statement stated them before (`NarkRpmH`, `posBindingGameH`,
`codeBindingGameH`, `ksGameH`, `PositionBindingRpmH`, …). `LeanDa.PiOnly` proves that each game of
the statement is the game here with each hash call expanded into its permutation calls, and
carries the end theorems over.

This module is part of the instantiation of Benedikt Wagner's framework for erasure code
commitments (`PqDas`, ported from https://github.com/b-wagn/fv-pq-da) with LeanDA.
-/

open Polynomial OracleComp OracleSpec ENNReal Common MeasureTheory

namespace LeanDa

open PqDas
open LeanVM.Semantics (KeccakState)


/-- Keccak-256 among the oracles of the random-permutation model. -/
abbrev hK (a : List UInt8) : OracleComp KSpecH DigestBytes := liftM (KSpecH.query (.inr (.inl a)))

/-- A call `π x` of the permutation among the oracles. -/
abbrev pK (x : KeccakState) : OracleComp KSpecH KeccakState := liftM (KSpecH.query (.inr (.inr (.forward x))))

/-- **An argument in the random-permutation model** (Wagner's arguments of knowledge, Foundations
Definition 18, with oracle access): its prover and verifier query the model's oracles (`KSpecH`:
coins, Keccak-256, `π` and `π⁻¹`), the oracles the adversary and LeanDA's verifier query. -/
structure NarkRpmH (Stmt Wit Crs Proof : Type) where
  /-- Sample a common reference string. -/
  setup : ProbComp Crs
  /-- Produce a proof for `stmt` from witness `wit`, querying the oracles. -/
  prove : Crs → Stmt → Wit → OracleComp KSpecH Proof
  /-- Verify a proof, querying the oracles. -/
  verify : Crs → Stmt → Proof → OracleComp KSpecH Bool

/-- A transcript: the queries of the model's oracles with their answers, in order (VCVio's
`QueryLog`). -/
abbrev TranscriptH := QueryLog KSpecH

/-- **A straight-line extractor in the random-permutation model**: a witness from the crs, the
statement, the proof and the transcript of the adversary's queries. -/
abbrev ExtractorRpmH (Stmt Wit Crs Proof : Type) := Crs → Stmt → Proof → TranscriptH → Wit

/-- **The model's oracles answered by a permutation `π`**: coins uniform, Keccak-256 over `π`,
`π` and `π⁻¹`. -/
noncomputable def permImplH (π : Equiv.Perm KeccakState) : QueryImpl KSpecH ProbComp
  | .inl n => (unifSpec.query n : ProbComp (Fin (n + 1)))
  | .inr (.inl a) => pure (keccak256WithPermutation π a)
  | .inr (.inr (.forward x)) => pure (π x)
  | .inr (.inr (.inverse y)) => pure (π.symm y)

/-- **Perfect completeness for every permutation**: with the oracles answered by any permutation
`π`, an honest proof of a statement the relation `rel π` holds for verifies with probability
one. -/
def NarkRpmH.PerfectlyComplete {Stmt Wit Crs Proof : Type} (ps : NarkRpmH Stmt Wit Crs Proof)
    (rel : Equiv.Perm KeccakState → Stmt → Wit → Bool) : Prop :=
  ∀ (π : Equiv.Perm KeccakState), ∀ crs ∈ support ps.setup, ∀ stmt wit, rel π stmt wit = true →
    Pr{let b ← simulateQ (permImplH π) (ps.prove crs stmt wit >>= ps.verify crs stmt)}[b = true] = 1

/-- An argument for LeanDA's relation: the statement a root, the witness the cells. -/
abbrev ArgumentRpmH (r : ℕ) (Crs Proof : Type) := NarkRpmH DigestBytes (Fin (r * 128) → Cell) Crs Proof

/-! ## The games in the random-permutation model

Every party queries the same oracles (`KSpecH`): the adversary, the argument's prover and verifier
Keccak-256, `π` and `π⁻¹`; LeanDA's verifier Keccak-256. A game is run against the lazily sampled
permutation (`runKH`), and its cost counts every party's calls (`permCallsH`). LeanDA's verifier
verifies the argument's proof for the commitment's root once, and each opening's path. -/

variable (r : ℕ) {Crs Proof : Type} (ps : ArgumentRpmH r Crs Proof)
  (ext : ExtractorRpmH DigestBytes (Fin (r * 128) → Cell) Crs Proof)

/-- A position-binding adversary: from the commitment key, a commitment, a position, and two cells
with their openings. -/
abbrev PosBindingAdvRpmH (Crs Proof : Type) :=
  Unit × Crs → OracleComp KSpecH ((DigestBytes × Proof) × Fin (r * 128) × Cell × CellOpening × Cell × CellOpening)

/-- **The position-binding game**: the argument's setup, the adversary, then the verifications:
the argument's of the root's proof and the two openings'; it wins when all verify, at two
different cells. -/
def posBindingGameH (A : PosBindingAdvRpmH r Crs Proof) : OracleComp KSpecH Bool := do
  let crs ← liftM ps.setup
  let (com, p, x, τ, x', τ') ← A ((), crs)
  let ok ← ps.verify crs com.1 com.2
  let b ← verifyCellMWithHash hK r com.1 p x τ
  let b' ← verifyCellMWithHash hK r com.1 p x' τ'
  pure (decide (x ≠ x') && ok && b && b')

/-- A code-binding adversary: from the commitment key, a commitment and a list of opened
positions. -/
abbrev CodeBindingAdvRpmH (Crs Proof : Type) :=
  Unit × Crs → OracleComp KSpecH ((DigestBytes × Proof) × List (Fin (r * 128) × Cell × CellOpening))

/-- **The code-binding game**: the argument's setup, the adversary, then the verifications; it wins
when the root's proof and every opening verify and no codeword agrees with the opened cells. -/
noncomputable def codeBindingGameH (A : CodeBindingAdvRpmH r Crs Proof) : OracleComp KSpecH Bool := do
  let crs ← liftM ps.setup
  let (com, opened) ← A ((), crs)
  let ok ← ps.verify crs com.1 com.2
  let verdicts ← opened.mapM fun o ↦ verifyCellMWithHash hK r com.1 o.1 o.2.1 o.2.2
  pure (ok && verdicts.all id && !decide ((leanDaErasureCode r).Consistent (opened.map fun o ↦ (o.1,
      o.2.1))))

/-- **The adversary's oracles, logged**: each query asked, and appended with its answer to the
transcript. -/
def loggedKH : QueryImpl KSpecH (StateT TranscriptH (OracleComp KSpecH)) := fun t ↦ do
  let u ← liftM (KSpecH.query t)
  modify (· ++ [⟨t, u⟩])
  pure u

/-- A knowledge-soundness adversary: from the crs, a root and a proof. -/
abbrev KsAdvRpmH (Crs Proof : Type) := Crs → OracleComp KSpecH (DigestBytes × Proof)

/-- **The argument's knowledge-soundness game** (Wagner's, Foundations Definition 18, in the
random-permutation model with a straight-line extractor): the argument's setup, the adversary with
its queries logged, the argument's verification, then the relation's check on the cells the
extractor reads off the proof and the adversary's transcript; it wins when the proof verifies and
the extracted cells do not satisfy the relation (`relationWith` over Keccak-256 and `π`). -/
noncomputable def ksGameH (B : KsAdvRpmH Crs Proof) : OracleComp KSpecH Bool := do
  let crs ← liftM ps.setup
  let ((root, proof), log) ← (simulateQ loggedKH (B crs)).run []
  let v ← ps.verify crs root proof
  let ok ← relationMWithHash hK pK root (ext crs root proof log)
  pure (v && !ok)

/-- **The completeness experiment for a permutation `π`** (Wagner's, Foundations Definition 8,
with the hash and the oracles answered by `π`): the argument's setup; the honest commitment to the
message `msg`, the root of its encoding's cells hashed with Keccak-256 over `π`; the argument's
honest proof for the root and its verification, both with the oracles answered by `π`; and the
verification of the encoding's cell at `p` with its honest opening. -/
noncomputable def completenessExpRpmH (π : Equiv.Perm KeccakState) (ps : ArgumentRpmH r Crs Proof)
    (msg : Fin r → Payload) (p : Fin (r * 128)) : ProbComp Bool := do
  let crs ← ps.setup
  let c := (leanDaErasureCode r).encode msg
  let root := commitCellsWithHash (keccak256WithPermutation π) c
  let ok ← simulateQ (permImplH π) (ps.prove crs root c >>= ps.verify crs root)
  pure (ok && Id.run (verifyCellMWithHash (fun a ↦ pure (keccak256WithPermutation π a)) r root p (c p)
    (openCellWithHash (keccak256WithPermutation π) c p)))

/-! ### The end statements, in the model with the hash oracle -/

/-- **LeanDA is perfectly complete in the random-permutation model, for every permutation.**
For any number `r` of rows, every permutation `π` of the Keccak state, and every argument `ps`
perfectly complete for LeanDA's relation for every permutation (`relationForPermutation`, the hash
Keccak-256 over `π` and the challenges the deployed duplex over `π`; the argument's prover and
verifier answered by `π`): every position `p` of the honest commitment to every message `msg`
opens and verifies with probability one (`completenessExpRpmH`). Holding for each `π`, it holds
for every outcome of the binding statements' uniformly random permutation. The proof is Wagner's
completeness proof, transferred. Proved by `LeanDa.leanDa_perfectlyComplete_rpmH`. -/
abbrev PerfectlyCompleteRpmH : Prop :=
  ∀ (r : ℕ) (π : Equiv.Perm KeccakState) {Crs Proof : Type} (ps : ArgumentRpmH r Crs Proof),
    ps.PerfectlyComplete (relationForPermutationWithHash r) →
      ∀ (msg : Fin r → Payload) (p : Fin (r * 128)),
        Pr{let b ← completenessExpRpmH r π ps msg p}[b = true] = 1

/-- **LeanDA is position binding in the random-permutation model.** For every argument `ps` (any
prover and verifier) and every adversary whose game, verifications included, makes at most `Q`
calls of the permutation on every path (`permCallsH`: a hash of `n` bytes costs `⌊n / 136⌋ + 1`, a
call of `π` or `π⁻¹` one, the argument's verifier's included), the probability of opening a
position to two different cells is at most `(Q + 1)² · 2^-256`, for every `Q` (past `2^128` the
bound exceeds one). Proved by
`LeanDa.leanDa_positionBinding_rpmH`. -/
abbrev PositionBindingRpmH : Prop :=
  ∀ (r : ℕ) {Crs Proof : Type} (ps : ArgumentRpmH r Crs Proof) (A : PosBindingAdvRpmH r Crs Proof)
    (Q : ℕ), QueryCostAtMost (posBindingGameH r ps A) permCallsH Q →
      Pr{let b ← runKH (posBindingGameH r ps A)}[b = true] ≤
        ((Q : ℝ≥0∞) + 1) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256

/-- **LeanDA is code binding in the random-permutation model, for an argument knowledge sound in
it** (Benedikt Wagner's framework and games, moved to the random-permutation model, with a
straight-line argument in place of his forking lemma). For `1 ≤ r ≤ 1024` rows (`maxRows`, the
crate's bound), every argument `ps` (its prover and verifier querying the model's oracles) and
straight-line extractor `ext` (reading the adversary's transcript): if every adversary whose
knowledge-soundness game (`ksGameH`, the argument's verifier and the relation's check included)
makes at most `q ≤ 2^128` permutation calls (`permCallsH`) wins it with probability at most
`(q + c) · 2^-k`, then every adversary whose code-binding game, verifications included, makes at
most `Q` calls breaks code binding with probability at most

`(Q + c + 2^22) · 2^-k + (Q + 2^22) · 2^-178 + (Q + 2^22)² · 2^-247`.

The first term is the argument's knowledge soundness against the code-binding adversary itself,
its transcript handed to the extractor (at most `Q + 2^22` calls with the relation's check). The
second is the membership test's soundness, `(2^14 - 1) / 2^192` for each of at most `Q + 2` roots
whose challenge is drawn. The third gathers the transfer to the two-oracle model and the duplex
lemma, of the two games, and the hash's bad events among at most `2 Q + 2^20` hash and challenge
queries: a collision, or a fresh answer that is a digest an earlier input or a root with drawn
challenges already carries; it exceeds one before `Q = 2^124`.

The argument queries the oracles the adversary does, so its knowledge soundness here is the
usual one of an argument in the random-permutation model, with a straight-line extractor reading
the adversary's queries, as leanVM's (`LeanVM.KnowledgeSoundness`); an argument may satisfy it and
be perfectly complete for every permutation (`PerfectlyCompleteRpmH`). Proved by
`LeanDa.leanDa_codeBinding_rpm_boundH`. -/
abbrev CodeBindingRpmH : Prop :=
  ∀ (r : ℕ) {Crs Proof : Type} (ps : ArgumentRpmH r Crs Proof)
    (ext : ExtractorRpmH DigestBytes (Fin (r * 128) → Cell) Crs Proof) (c k : ℕ),
    (∀ (B : KsAdvRpmH Crs Proof) (q : ℕ), QueryCostAtMost (ksGameH r ps ext B) permCallsH q →
      q ≤ 2 ^ 128 → Pr{let b ← runKH (ksGameH r ps ext B)}[b = true] ≤
        ((q : ℝ≥0∞) + c) * (2 : ℝ≥0∞)⁻¹ ^ k) →
    1 ≤ r → r ≤ maxRows →
    ∀ (A : CodeBindingAdvRpmH r Crs Proof) (Q : ℕ),
      QueryCostAtMost (codeBindingGameH r ps A) permCallsH Q →
        Pr{let b ← runKH (codeBindingGameH r ps A)}[b = true] ≤
          ((Q : ℝ≥0∞) + c + 2 ^ 22) * (2 : ℝ≥0∞)⁻¹ ^ k + ((Q : ℝ≥0∞) + 2 ^ 22) * (2 : ℝ≥0∞)⁻¹ ^ 178 +
            ((Q : ℝ≥0∞) + 2 ^ 22) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 247

end LeanDa
