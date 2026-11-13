import LeanVM.Protocol.Verifier.WhirTarget
import LeanVM.Protocol.Whir.Complete.OpeningProof
import LeanVM.Protocol.WithHash

/-!
# Completeness of the WHIR opening: tests

* **Statement locks** of `runFrom_verifyStackedOpening` and `openingComplete`: a change of a
  hypothesis or of the conclusion fails here.
* **The honest round polynomials** (`#guard`, compiled): the sumcheck identity
  `polyEval_roundQuad` on small tables (and its failure on a wrong claim), the derived linear
  coefficient, linearity in the weight table; the equality kernel, the partial fold and the
  multilinear extension against their sums.
-/

namespace LeanVMTests.Protocol.Whir.Complete.Opening

open LeanVM.Prover (Script)

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd
  LeanVM.Protocol.Compile LeanVM.Protocol.Whir LeanVM.Protocol.Whir.Complete

/-! ## Statement locks -/

example : OpeningComplete → ∀ {μ R : ℕ}, Whir.Admissible μ R → ∀ (q : Column μ)
    (claims : List StackClaim), claims.length ≤ maxStackedClaims →
    (∀ c ∈ claims, StackClaim.Holds μ c q) → (∀ c ∈ claims, IsMultilinearFn μ c.1) →
    ∀ (h : List Ev), commits h = [stackCommit μ R q] → ∀ (S : Strategy),
    (∀ e, S.msg (h ++ e) = (honestOpening μ R q claims).msgAt e ∧
      S.word (h ++ e) = (honestOpening μ R q claims).wordAt e) →
    ∀ (chal : List Ev → E),
      S.runFrom chal (verifyStackedOpening μ R claims) h = some () ∧
        S.ShapedFrom chal (verifyStackedOpening μ R claims) h :=
  @runFrom_verifyStackedOpening

example : OpeningComplete := openingComplete

/-- info: 'LeanVM.Protocol.Whir.Complete.openingComplete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms openingComplete

/-- The stack's commitment is opened at level `0` with the shape `commitStack` announces. -/
example : stackCommit 15 1 ⟨Vector.replicate _ 0⟩ = (10, 64, stackWord 15 1 ⟨Vector.replicate _ 0⟩) :=
  rfl

/-! ## The honest round polynomials -/

/-- A field element from three words (the last two summed into the upper limb). -/
def eK (a b c : ℕ) : E := E.ofLimbs (K.ofBits a) (K.ofBits (b + c))

/-- A pseudo-random table of `n` entries. -/
def tbl (seed n : ℕ) : List E :=
  (List.range n).map fun i ↦ eK (i * 0x9E3779B97F4A7C15 + seed) (i * i + 3 * seed) (seed + 7 * i)

-- The sumcheck round: the polynomial built from the two scalars sent and the claim `Σ W·g` is,
-- at `c`, the sum of the folded product.
#guard (List.range 4).all fun k ↦
  let W := tbl 1 (2 ^ (k + 1))
  let g := tbl 2 (2 ^ (k + 1))
  let c := eK 5 6 7
  decide (polyEval (roundQuad (dot W g) W g) c = dot (foldPairs c W) (foldPairs c g))

-- Negative: with a claim off by one the identity fails (the claim is load-bearing).
#guard
  let W := tbl 1 8
  let g := tbl 2 8
  let c := eK 5 6 7
  polyEval (roundQuad (dot W g + 1) W g) c ≠ dot (foldPairs c W) (foldPairs c g)

-- `h(0) + h(1)` is the claim: the linear coefficient the verifier derives is the honest one.
#guard
  let W := tbl 3 16
  let g := tbl 4 16
  let h := roundQuad (dot W g) W g
  polyEval h 0 + polyEval h 1 = dot W g

-- The round polynomial is linear in the weight table (gluing).
#guard
  let W := tbl 1 8
  let T := tbl 9 8
  let g := tbl 2 8
  let s := eK 11 0 1
  roundC0 (axpy s W T) g = roundC0 W g + s * roundC0 T g ∧
    roundC2 (axpy s W T) g = roundC2 W g + s * roundC2 T g

-- The equality kernel is `eq(j, p)` entrywise, and pairing with it is the multilinear extension.
#guard
  let p := [eK 1 2 3, eK 4 5 6, eK 7 8 9]
  let t := tbl 6 8
  (List.range 8).all (fun j ↦ decide ((eqKernel p).getD j 0 = eqEval (boolPoint 3 j) p)) &&
    decide (dot t (eqKernel p) = multilinearEval t p)

-- Partial folding: fixing the first two of four coordinates.
#guard
  let t := tbl 8 16
  let r := [eK 2 3 5, eK 7 11 13]
  (List.range 4).all fun x ↦
    decide ((foldAll t r).getD x 0 =
      ((List.range 4).map fun j ↦ eqEval (boolPoint 2 j) r * t.getD (j + 4 * x) 0).sum)

end LeanVMTests.Protocol.Whir.Complete.Opening
