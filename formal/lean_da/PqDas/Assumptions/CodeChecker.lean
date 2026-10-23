/-
# Code checkers

A code checker is a probabilistic test of code membership: `check l c` takes a
domain element `l : L` and an alleged codeword `c`, and deterministically
accepts or rejects. Completeness requires that codewords are accepted for every
`l`; `δ`-soundness requires that any *fixed* non-codeword is accepted with
probability at most `δ` over a uniformly random `l`. The intended instantiation
is a Reed-Solomon membership check via an inner product of the codeword with a
random vector of the dual code, where `l` is the randomness determining that
vector.

Note the order of quantifiers in soundness: the non-codeword is fixed *before*
the randomness is sampled. A cheating committer may correlate its committed
vector with the check randomness (which is derived from its commitment by
Fiat-Shamir); bridging this gap is exactly the job of the rewinding analysis in
the code-binding proof, which manufactures a run where the vector is determined
before fresh check randomness is drawn.

Soundness is stated in two equivalent forms: a probabilistic one (consumed by
the security-game analysis) and a counting one (the natural target when
verifying a concrete instantiation, e.g. a barycentric Reed-Solomon check).

Ported from b-wagn/fv-pq-da at 4475179c, modified for VCVio afa6593.
-/
import PqDas.Assumptions.ErasureCode

open OracleComp ENNReal

namespace PqDas

/-- A code checker for vectors in `Fin n → Λ` with check-randomness domain `L`:
a deterministic test `check`, intended to accept exactly-the-codewords with
high probability over `L`. -/
structure CodeChecker (Λ : Type) (n : ℕ) (L : Type) where
  /-- The (deterministic) membership check. -/
  check : L → (Fin n → Λ) → Bool

namespace CodeChecker

variable {Γ Λ L : Type} {k n : ℕ}

/-- Completeness: every codeword passes the check for every `l`. -/
def Complete (cc : CodeChecker Λ n L) (C : ErasureCode Γ Λ k n) : Prop :=
  ∀ c ∈ C.code, ∀ l, cc.check l c = true

/-- `δ`-soundness: any *fixed* non-codeword passes the check with probability
at most `δ` over a uniformly random `l`. -/
def Sound [SampleableType L] (cc : CodeChecker Λ n L) (C : ErasureCode Γ Λ k n)
    (δ : ℝ≥0∞) : Prop :=
  ∀ c ∉ C.code, Pr{let x ← (fun l => cc.check l c) <$> ($ᵗ L)}[x = true] ≤ δ

/-- Counting form of `δ`-soundness: for every fixed non-codeword, the fraction
of the domain accepting it is at most `δ`. Concrete instantiations prove this
form; the game analysis consumes `Sound`. -/
theorem sound_iff_card_le [SampleableType L] [Fintype L]
    (cc : CodeChecker Λ n L) (C : ErasureCode Γ Λ k n) (δ : ℝ≥0∞) :
    cc.Sound C δ ↔ ∀ c ∉ C.code,
      (({l | cc.check l c = true} : Finset L).card : ℝ≥0∞) / Fintype.card L ≤ δ := by
  unfold Sound
  refine forall₂_congr fun c _ => ?_
  rw [prEvent_map, SampleableType.prEvent_uniformSample]

end CodeChecker

end PqDas
