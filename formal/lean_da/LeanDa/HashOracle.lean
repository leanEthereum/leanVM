module

public import Statement.LeanDa
public import Common.HashOracle
public import LeanDa.Defs

@[expose] public section

/-!
# LeanDA's position binding with a Keccak-256 oracle, a proof device

The statement's model has coins, `π` and `π⁻¹` and nothing else (`Common.RandomPermutationOracles`),
and LeanDA's verifier hashes with Keccak-256 over `π` (`Common.keccak256OverPermutation`). The
proofs reason with Keccak-256 as one more oracle (`Common.KSpecH`): here is the position-binding
game in that model, with an argument that queries the oracles and whose verification the game runs
(`NarkRpmH`, `posBindingGameH`, `PositionBindingRpmH`). The statement's game, which has no
argument, is this game for the argument that accepts everything, each hash call expanded into its
permutation calls (`positionBindingGame_eq_expand`, `LeanDa.End`).

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

/-- An argument for LeanDA's relation: the statement a root, the witness the cells. -/
abbrev ArgumentRpmH (r : ℕ) (Crs Proof : Type) := NarkRpmH DigestBytes (Fin (r * 128) → Cell) Crs Proof

/-! ## The position-binding game

Every party queries the same oracles (`KSpecH`): the adversary and the argument's verifier
Keccak-256, `π` and `π⁻¹`; LeanDA's verifier Keccak-256. The game is run against the lazily sampled
permutation (`runKH`), and its cost counts every party's calls (`permCallsH`). -/

variable (r : ℕ) {Crs Proof : Type} (ps : ArgumentRpmH r Crs Proof)

/-- A position-binding adversary: from the commitment key, a commitment, a position, and two cells
with their openings. -/
abbrev PosBindingAdvRpmH (Crs Proof : Type) :=
  Unit × Crs → OracleComp KSpecH ((DigestBytes × Proof) × Fin (r * 128) × Cell × ByteOpening × Cell × ByteOpening)

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

/-! ### The propositions, in the model with the hash oracle -/

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

end LeanDa
