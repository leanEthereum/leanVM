/-
  LeanVM.Protocol.Compile.Rom.Sound

  The random-oracle theorem of the compiled verifier: Fiat-Shamir over a duplex sponge with proof
  of work and Merkle commitments (BCS) turns a doom certificate of a verifier program into a bound
  on the probability that the compiled verifier, run with Keccak-256 and Keccak-f[1600] modelled
  as independent random oracles, accepts a proof whose extracted history passes through doom.
-/

module

public import LeanVM.Protocol.Compile.Rom.Step
public import LeanVM.Protocol.Compile.Rom.Final
public import LeanVM.Protocol.Compile.Rom.Bridge
public import LeanVM.Protocol.WithHash

/-!
# The random-oracle theorem of the compiled verifier

Let `P : VerifierProgram Bool` be a verifier program (`LeanVM.Protocol.Compile.VerifierProgram`)
with a doom certificate `C : Cert P`, and `σ : Seeds X` a family of seedings of the Fiat-Shamir
sponge, one per statement `x : X`, each with the root history `σ.root x` at which its seed puts `P`.
The verifier of a statement and a proof (`verifierFam σ P`, `LeanVM.Protocol.Compile.Rom.Bridge`)
seeds the sponge by `σ.seed x`, then runs `P` from its root node on the proof, every hash a query
to a random oracle `Bytes →ₒ Digest` and every permutation of the sponge a query to an
independent random oracle `KState →ₒ KState` (`HashSpec`).

In the experiment `romExperiment A (verifierFam σ P)` the adversary `A`, an oracle computation
with at most `Q_A` queries to the two oracles together, outputs a statement `x` and a proof `π`;
the verifier, with at most `Q_V` queries on every statement and proof, runs on them against the
same lazily sampled random oracles. `romSound` bounds the probability that the verifier accepts
while some boundary prefix of the *extracted history*, past the root, is doomed:

  `Pr[accept ∧ ∃ h₀, root x ≤ h₀ ≤ extracted history, Boundary h₀ ∧ C.D h₀]`
  `  ≤ (Q_A + Q_V) · (εmax + failBound σ (Q_A + Q_V))`,

where

* `εmax` bounds `2^-min(grindBits h, 64) · C.ε h` for every history `h`: the certificate's
  escape bound of each group of challenges, discounted by the proof of work before it;
* `failBound σ N = (5 + |σ.offs|) · N / 2^256`: the probability that a fresh answer collides
  with or predicts a value the oracles' log already refers to (`Fail`): a hash answer that is an
  earlier hash output, a Merkle child or seeding digest inside an earlier input, a root absorbed
  by a permutation input, or an IV a permutation input carries; a permutation answer whose
  capacity (`576` bits) is an earlier output's or input's, or zero;
* the extracted history (`extractedFrom`) is the interactive history of the verifier's run on
  `π` from the root, every query answered by the final random-oracle cache, every commitment
  holding the word extracted for its root from the hash answers of that cache (`extract`), `[]`
  if the run does not reach a verdict. Its doomed boundary prefixes are what the knowledge
  extractor reads off: a proof accepted with no doomed boundary prefix is one from whose
  extracted words a witness is read.

## The proof

A potential on the oracles' ordered log (`pot`, `LeanVM.Protocol.Compile.Rom.Potential`): `1`
once some answer collided with or predicted a referenced value (`Fail`), otherwise the sum, over
the groups of challenges the log has started from doomed boundaries, of their escape
probabilities conditioned on the challenges drawn so far, capped at `1`. It vanishes on the empty
log (`pot_nil`), rises by at most `εmax + (5 + |σ.offs|)(|ℓ| + 1)/2^256` in expectation at each
fresh query to either oracle (`step_ineqH`, `step_ineqF`), and is `1` on every reachable final
log on which the verifier accepts with a doomed boundary prefix (`final_ineq`, through
`verifyFam_of_mem_support_logExperiment`). The engine
`prEvent_romExperiment_le_of_logFreshStepBelow` (`LeanVM.Protocol.ToVCVio.Rom`) turns this into
the bound. When `εmax ≥ 1` the bound exceeds one (the verifier queries at least once).

## Decisions

* The proof-of-work factor is `2^-min(b, 64)`: the predicate `powOk` tests the third lane of the
  permutation that absorbs the nonce, so for `b > 64` it holds with probability `2^-64`, not
  `2^-b`. leanVM grinds at most `25` bits. That permutation's first two lanes are the group's
  first challenge (`ground`), and its later challenges come from later permutations, whose inputs
  carry the permutation's capacity: the lanes are disjoint, so the proof of work's factor and the
  group's escape probability multiply.
* Keccak-f[1600] is modelled as a random function on states, not a random permutation.
* Each seeding is hash steps then one permutation (`Seed`): leanVM's
  `F(IV ‖ pi ‖ 0)` with `IV = H(tag ‖ bytecode)` is one hash step and the permutation.
* The statement is the adversary's: one program `P` with one certificate covers every statement
  by its root history, and the family's seeds are told apart by their permutation inputs
  (`Seeds.inj`). A fixed statement is a family of one.
* The bad event reads the final random-oracle cache only (`extractedFrom` of `z.2`), so it is a
  statement about VCVio's `randomOracle`; the order of the log is used only in the proof.
-/

namespace LeanVM.Protocol.Compile.Rom

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakHash LeanVM.Protocol.Rom
open OracleComp OracleSpec
open scoped ENNReal

@[expose] public section

/- The enumerations of `Digest` and `KState` must never be unfolded by unification. -/
attribute [local irreducible] instFintypeDigest instFintypeKState

/-- The failure term: `(5 + |σ.offs|) · N / 2^256` bounds the probability that one fresh answer
collides with or predicts one of the values a log of fewer than `N` entries refers to. -/
noncomputable def failBound {X : Type} (σ : Seeds X) (N : ℕ) : ℝ≥0∞ :=
  ((5 + σ.offs.length) * N : ℕ) / 2 ^ 256

/-- Some boundary prefix, past the statement's root, of the extracted history of the verifier's
run on the statement and proof `z`, under the answers of the cache `c`, is doomed. -/
def Doomed {X : Type} {P : VerifierProgram Bool} (C : Cert P) (σ : Seeds X) (z : X × Proof)
    (c : KeccakCalls.QueryCache) : Prop :=
  ∃ h₀, h₀ <+: extractedFrom (fun x ↦ c (.inl x)) (fun s ↦ c (.inr s)) (σ.seed z.1)
      (nodeAt P (σ.root z.1)) (σ.root z.1) z.2 ∧
    (σ.root z.1).length ≤ h₀.length ∧ Boundary h₀ ∧ C.D h₀

/-- The seeded verifier always queries an oracle: it makes at least one query. -/
theorem not_isTotalQueryBound_verifierComp_zero (σ₀ : Seed) (P : VerifierProgram Bool) (π : Proof) :
    ¬ IsTotalQueryBound (verifierComp σ₀ P π) 0 := by
  unfold verifierComp verify Seed.run
  rcases hs : σ₀.hs with _ | ⟨f, fs⟩
  · simp only [Seed.hsRun, pure_bind, callKeccakF1600]
    exact fun h ↦ absurd (isTotalQueryBound_query_bind_iff.mp h).1 (lt_irrefl 0)
  · simp only [Seed.hsRun, callKeccak256, bind_assoc]
    exact fun h ↦ absurd (isTotalQueryBound_query_bind_iff.mp h).1 (lt_irrefl 0)

/-- **The step inequality, packaged for the engine**: below `N` entries, a fresh answer to either
oracle raises the potential by at most `εmax + failBound σ N` in expectation. -/
theorem pot_logStepBelow {X : Type} {P : VerifierProgram Bool} (C : Cert P) (σ : Seeds X) {εmax
    : ℝ≥0∞}
    (hε : ∀ h, (2 : ℝ≥0∞)⁻¹ ^ min (grindBits h) 64 * C.ε h ≤ εmax) (N : ℕ) :
    LogStepBelow N (pot C.D σ P) (εmax + failBound σ N) := by
  refine ⟨fun ℓ x hℓ _ ↦ ?_, fun ℓ s hℓ hs ↦ ?_⟩
  · refine (step_ineqH C.D ℓ x).trans (add_le_add le_rfl ?_)
    refine le_add_left ?_
    rw [failBound]
    refine ENNReal.div_le_div_right ?_ _
    exact_mod_cast Nat.mul_le_mul_left _ hℓ
  · refine (step_ineqF C hε ℓ s ((lookR_eq_none_iff ℓ s).mpr hs)).trans
      (add_le_add le_rfl (add_le_add le_rfl ?_))
    rw [failBound]
    refine ENNReal.div_le_div_right ?_ _
    exact_mod_cast Nat.mul_le_mul_left _ hℓ

/-- **The random-oracle theorem for an event of the log that implies doom** on accepted proofs
without failure, the bad event read off the ordered log. -/
theorem romSound_log {X : Type} (P : VerifierProgram Bool) (C : Cert P) (σ : Seeds X)
    (hroot : ∀ x, RootOk P (σ.root x)) (εmax : ℝ≥0∞)
    (hε : ∀ h, (2 : ℝ≥0∞)⁻¹ ^ min (grindBits h) 64 * C.ε h ≤ εmax)
    (A : OracleComp KeccakCalls (X × Proof)) (QA : ℕ) (hA : IsTotalQueryBound A QA)
    (QV : ℕ) (hV : ∀ z, IsTotalQueryBound (verifierFam σ P z) QV)
    (bad : X × Proof → Log → Prop)
    (hbad : ∀ z ℓ, ¬ Fail σ ℓ →
      verify (lookH ℓ) (lookF ℓ) (σ.seed z.1) (nodeAt P (σ.root z.1)) z.2 = some true →
        bad z ℓ → Doomed C σ z (cacheOf ℓ)) :
    Pr{let z ← logExperiment A (verifierFam σ P)}[z.1.2 = true ∧ bad z.1.1 z.2] ≤
      (QA + QV : ℕ) * (εmax + failBound σ (QA + QV)) := by
  by_cases hlt : εmax < 1
  · have hε1 : ∀ h, grindBits h = 0 → C.ε h < 1 := fun h hg ↦ by
      have := hε h
      rw [hg, Nat.zero_min, pow_zero, one_mul] at this
      exact this.trans_lt hlt
    refine prEvent_logExperiment_le_of_freshStepBelow (QA + QV) (pot_logStepBelow C σ hε _)
      (pot_nil C.D σ P) A (verifierFam σ P) QA QV hA hV le_rfl bad ?_
    intro z hz hacc hb
    by_cases hf : Fail σ z.2
    · simp only [pot, hf, ↓reduceIte, le_refl]
    · have hv := verifyFam_of_mem_support_logExperiment A hz hacc
      exact final_ineq C hf hε1 (hroot _) hv (hbad z.1.1 z.2 hf hv hb)
  · rw [not_lt] at hlt
    by_cases hQ : QA + QV = 0
    · -- no verifier can make no query: there is no outcome
      have hQV : QV = 0 := by omega
      refine le_of_eq_of_le (prEvent_eq_zero_of_forall_mem_support _ _ fun z _ _ ↦ ?_) bot_le
      exact not_isTotalQueryBound_verifierComp_zero _ _ _ (hQV ▸ hV z.1.1)
    · refine (prEvent_le_one _).trans ?_
      calc (1 : ℝ≥0∞) = 1 * 1 := (one_mul 1).symm
        _ ≤ (QA + QV : ℕ) * (εmax + failBound σ (QA + QV)) :=
          mul_le_mul' (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hQ) (hlt.trans le_self_add)

/-- **The random-oracle theorem for an event that implies doom**: if, for every statement and
proof the statement's seeded verifier accepts with the queries answered by the cache, the event
`bad` implies that a boundary prefix of the extracted history is doomed, the probability that the
verifier accepts while `bad` holds is at most `romSound`'s bound. -/
theorem romSound_of_imp {X : Type} (P : VerifierProgram Bool) (C : Cert P) (σ : Seeds X)
    (hroot : ∀ x, RootOk P (σ.root x)) (εmax : ℝ≥0∞)
    (hε : ∀ h, (2 : ℝ≥0∞)⁻¹ ^ min (grindBits h) 64 * C.ε h ≤ εmax)
    (A : OracleComp KeccakCalls (X × Proof)) (QA : ℕ) (hA : IsTotalQueryBound A QA)
    (QV : ℕ) (hV : ∀ z, IsTotalQueryBound (verifierFam σ P z) QV)
    (bad : X × Proof → KeccakCalls.QueryCache → Prop)
    (hbad : ∀ z c, verify (fun x ↦ c (.inl x)) (fun s ↦ c (.inr s)) (σ.seed z.1)
      (nodeAt P (σ.root z.1)) z.2 = some true → bad z c → Doomed C σ z c) :
    Pr{let z ← romExperiment A (verifierFam σ P)}[z.1.2 = true ∧ bad z.1.1 z.2] ≤
      (QA + QV : ℕ) * (εmax + failBound σ (QA + QV)) := by
  rw [prEvent_romExperiment_eq_logExperiment A (verifierFam σ P)
    fun r c ↦ r.2 = true ∧ bad r.1 c]
  exact romSound_log P C σ hroot εmax hε A QA hA QV hV (fun z ℓ ↦ bad z (cacheOf ℓ))
    fun z ℓ _ hv hb ↦ hbad z (cacheOf ℓ) hv hb

/-- **The random-oracle theorem of the compiled verifier.** For a verifier program `P` with a
doom certificate `C`, a family of seedings `σ` whose roots are roots of `P`, an adversary `A`
making at most `QA` queries that outputs a statement and a proof, and a compiled verifier making
at most `QV` queries on every statement and proof, the probability that the verifier accepts
while some boundary prefix of its extracted history is doomed is at most
`(QA + QV) · (εmax + failBound σ (QA + QV))`, where `εmax` bounds every escape bound of the
certificate discounted by the proof of work before it. -/
theorem romSound {X : Type} (P : VerifierProgram Bool) (C : Cert P) (σ : Seeds X)
    (hroot : ∀ x, RootOk P (σ.root x)) (εmax : ℝ≥0∞)
    (hε : ∀ h, (2 : ℝ≥0∞)⁻¹ ^ min (grindBits h) 64 * C.ε h ≤ εmax)
    (A : OracleComp KeccakCalls (X × Proof)) (QA : ℕ) (hA : IsTotalQueryBound A QA)
    (QV : ℕ) (hV : ∀ z, IsTotalQueryBound (verifierFam σ P z) QV) :
    Pr{let z ← romExperiment A (verifierFam σ P)}[z.1.2 = true ∧ Doomed C σ z.1.1 z.2] ≤
      (QA + QV : ℕ) * (εmax + failBound σ (QA + QV)) :=
  romSound_of_imp P C σ hroot εmax hε A QA hA QV hV (Doomed C σ) fun _ _ _ h ↦ h

end
end LeanVM.Protocol.Compile.Rom
