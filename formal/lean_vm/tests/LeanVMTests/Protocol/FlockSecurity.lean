import LeanVM.Protocol.Flock
import LeanVMTests.Protocol.Flock

/-!
# Flock knowledge soundness tests

The Flock argument's knowledge soundness rests on two facts about its constants that completeness
does not use. Each is load-bearing, and the counterexamples here show what goes wrong without it:

* **The fixed coordinates' weights are `F_2`-independent.** With the fixed coordinate `0`, a
  nonzero Boolean residual vanishes at every completion of the fixed coordinates, so the zero
  test on the point misses it; the weights `eq(0, ·)` have a nonzero `0/1` combination that
  vanishes.
* **Ring switching is injective.** With the generator `1`, the errors `(1, 1)` are nonzero and
  every sum `Σ_i g^i · δ_i^(2^k)` vanishes in characteristic two, so wrong slices would give a
  true weighted claim for every coefficient.

Two of the verifier's checks, on the tiny argument of the definition's tests:

* **The zeros on the skip nodes.** A batch with a wrong gate has a residual whose extension at the
  point is not zero. The verifier, interpolating the honest coset values with zeros, starts the
  zerocheck at a false claim; interpolating `P`'s own values on the skip nodes instead would give
  the true one.
* **The constant position's `α³` term.** The zero batch satisfies every constraint and fails only
  at the constant position. At its true terminal values the lincheck sum is
  `v_a + α v_b + α² v_c`, so the batched claim without the `α³` term would be true; with it, it is
  false.

At leanVM's constants both hold (`fixedWeights_independent`, `ringSwitch_injective`), and the
phase's security is stated at the slot's errors, which dominate the proved ones challenge by
challenge (`flockErrorsT_le_flockErrorsOf`).

A plain file, so `#guard` evaluates the compiled definitions.
-/

namespace LeanVMTests.Protocol.FlockSecurity

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Flock CompPoly CMlPolynomialEval

/-! ## A Boolean fixed coordinate -/

def one : E := 1

/-- One fixed coordinate, `0`, and one drawn; two within-block and batch coordinates in all. -/
def zeroFixed : Flock.Params E where
  s := 0
  m := 1
  κ := 1
  nodes := SkipDomain.ofPts #v[0, one]
  nFix := 1
  nRand := 1
  fixed := #v[0]
  hpoint := rfl
  cpos := 0

/-- A nonzero Boolean residual: `1` at the entry whose fixed coordinate is `1`. -/
def residual : CMlPolynomialEval E (zeroFixed.m + zeroFixed.κ) := #v[0, 1, 0, 0]

#guard residual.toList ≠ [0, 0, 0, 0]
-- It vanishes at every completion of the fixed coordinate `0`.
#guard RestrictedZero residual (zeroFixed.pointPartial (#v[] : Vector E 0))

/-- A nonzero `0/1` combination of the fixed weights. -/
def comb : Fin (2 ^ zeroFixed.nFix) → E := ![0, 1]

#guard ∑ v, (lagrangeBasis zeroFixed.fixed)[v] * comb v = 0
#guard comb 1 ≠ 0

/-! ## Ring switching with the generator `1` -/

/-- The errors `(1, 1)`. -/
def δ : Fin 2 → E := fun _ ↦ 1

-- Every `π_k`, `k < 2`, vanishes: with one stage, the last coefficient is free.
#guard (List.range 2).all fun k ↦ frobPair Finset.univ (fun i : Fin 2 ↦ one ^ i.val) δ k = 0
#guard δ 0 ≠ 0

/-! ## The zeros on the skip nodes -/

open LeanVMTests.Protocol.Flock in
-- The wrong gate shows at the point: a residual's extension there is not zero.
#guard ∃ i : Fin 2, evalMle (errTable toyC (badZ noO) i) (toyP.point s1.2) ≠ 0

open LeanVMTests.Protocol.Flock in
/-- The honest coset values of the batch with a wrong gate. -/
def msgB : Vector E 2 := skipHonest toyP toyC badZ ((s1, noO), ())

open LeanVMTests.Protocol.Flock in
def stB : SumcheckRound.Stmt (ZcX Unit E (toyP.m + toyP.κ)) E 0 := skipNext toyP (s1, msgB) zs

open LeanVMTests.Protocol.Flock in
-- With the zeros assumed, the zerocheck starts at a false claim.
#guard ((stB, noO), ()) ∉ SumcheckRound.rel (zcFamily toyP toyC badZ side0) 0

open LeanVMTests.Protocol.Flock in
/-- `P` of the batch with a wrong gate, at the point, as a function of the skip value. -/
def pB (Y : E) : E := pValue toyP.nodes toyC (badZ noO) (toyP.point s1.2) Y

open LeanVMTests.Protocol.Flock in
-- With `P`'s own values on the skip nodes in place of the zeros, the claim would be true.
#guard interpolateAt toyP.nodes.pts (Vector.ofFn fun j ↦ pB toyP.nodes.pts[j]) zs = pB zs

/-! ## The constant position's `α³` term -/

open LeanVMTests.Protocol.Flock in
/-- The zero batch's true terminal statement: every table is zero, so are its extensions. -/
def tZ : TermStmt Unit E (toyP.m + toyP.κ) := (((), toyP.point s1.2, zs), #v[c0, c1], 0, 0, 0)

open LeanVMTests.Protocol.Flock in
-- The lincheck sum is `v_a + α v_b + α² v_c`, here zero: without the `α³` term the batched claim
-- would be true.
#guard (linFamily toyP toyC zeroZ side0 (W := Unit)).claim (((tZ, α0), noO), ()) 0 #v[] = 0

open LeanVMTests.Protocol.Flock in
-- With it, the lincheck starts at a false claim.
#guard ((alphaNext tZ α0, noO), ()) ∉ SumcheckRound.rel (linFamily toyP toyC zeroZ side0) 0

/-! ## leanVM's constants -/

-- The two facts at leanVM's constants, in the form the generic argument takes them.
example (c : Fin (2 ^ (flockParams 3).nFix) → E) (hc : ∀ v, c v = 0 ∨ c v = 1)
    (h : ∑ v, (lagrangeBasis (flockParams 3).fixed)[v] * c v = 0) : ∀ v, c v = 0 :=
  fixedWeights_independent c hc h

example (δ : Fin (2 ^ (flockParams 3).s) → E)
    (h : ∀ k < 2 ^ (5 + 1), frobPair Finset.univ (fun i ↦ algebraMap K E (g ^ i.val)) δ k = 0) :
    ∀ i, δ i = 0 :=
  ringSwitch_injective δ h

-- The slot's errors dominate the proved ones, challenge by challenge.
example (k : ℕ) : Typed.Errors.Le (flockSlotOf k).tree (flockSlotOf k).roles
    (Flock.flockErrorsT (flockParams k) 5) (flockErrorsOf k) :=
  flockErrorsT_le_flockErrorsOf k

end LeanVMTests.Protocol.FlockSecurity
