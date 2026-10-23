import LeanVM.Protocol.ToArkLib.GrandProduct
import LeanVM.Protocol.ToArkLib.Oracles
import LeanVM.Protocol.Field
import LeanVM.Protocol.Spine.Errors
import LeanVM.Protocol.Spine.Slots
import LeanVM.Protocol.Spine.Toy

/-!
# Grand-product tests

Over `E`, with no public data and no oracle, on trees of four, eight and sixteen leaves.

* **The slot.** `gkr 3 4` is typed at `gkrSlot E 3 4`, and the errors `gkrErrors` charges along
  every path are within their closed form. The bus slot takes the component at its type: the bus
  phase's shape around `gkr 3 toy.μBus` is at `busSlot toy`.
* **An honest run of `gkr 1 2`, by hand.** The roots satisfy the input relation; the combined
  claim, the descendants' check, the two combination challenges and the output relation.
* **An honest run of `gkr 3 4`, by hand.** On three trees of sixteen leaves: the first step from
  the roots, then the second from two variables to four, where the combined claim is the family's
  first claim, each honest round polynomial passes the verifier's normalized check and evaluates
  to the family's next claim at the challenge, the honest descendants pass the final check, and
  the new point is `(u_0, u_1, c_0, c_1)`; the output relation holds.
* **An honest run of `gkr 3 3`, by hand.** The binary step first, two values per tree and one
  combination challenge, then a radix-four step with one sumcheck round.
* **What is rejected.** The polynomial of a prover holding other leaves, a wrong claim, and
  descendants of other leaves.
* **Riders.** A nonzero rider fails the input relation, a zero one passes; at the final point the
  output relation holds for a nonzero rider exactly when the point's low coordinate is a root of
  its extension, the escape its challenge is charged for. A nonzero rider on no variable fails
  both relations at every point.
* **Completeness** has an inhabitant, with a zero rider and without riders.

A plain file, so `#guard` evaluates the compiled definitions. Values of `E` written with numerals
are named as definitions before a guard uses them.
-/

namespace LeanVMTests.Protocol.GrandProduct

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Gkr LeanVM.Protocol.Toy CompPoly
  CMlPolynomialEval
open scoped NNReal

/-- No oracle. -/
def noO : ∀ i, NoOracle i := fun i ↦ i.elim0

/-- Three values of `E`. -/
def a : E := y
def b : E := y + 1
def c : E := y * y + y

/-- One tree of four leaves. -/
def four : Unit → (∀ i, NoOracle i) → Fin 1 → CMlPolynomialEval E 2 :=
  fun _ _ _ ↦ #v[a, b, c, 1]

/-- Three trees of sixteen leaves. -/
def sixteen : Unit → (∀ i, NoOracle i) → Fin 3 → CMlPolynomialEval E 4 := fun _ _ s ↦
  ![#v[a, b, c, 1, a, a, b, b, c, c, 1, 1, a, b, c, a],
    #v[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    #v[b, c, a, b, c, a, b, c, a, b, c, a, b, c, a, 1]] s

/-- No rider. -/
def noRiders {μ : ℕ} : Unit → (∀ i, NoOracle i) → List (Σ τ : Fin (μ + 1), CMlPolynomialEval E τ) :=
  fun _ _ ↦ []

/-! ## The slot -/

-- The errors of `gkr 3 4` from a unit `u` along every path: `(nside - 1)·u` on each of the two
-- combiners, `4·u` on each of the two sumcheck rounds of radix four, `u` on each of the four
-- combination challenges, within the closed form `((μ + 1)(nside - 1) + 2μ² + 3μ + 3)·u`.
example (u : ℝ≥0) : Typed.Errors.Bounded (Typed.gkrSlot E 3 4).tree (Typed.gkrSlot E 3 4).roles
    (Typed.gkrErrors E u 3 4) ((((4 + 1) * (3 - 1) + 2 * 4 * 4 + 3 * 4 + 3 : ℕ) : ℝ≥0) * u) :=
  Typed.gkrErrors_bounded E u 3 4

-- The component is typed at the slot.
example : Typed.Def NoOracle (Unit × (Fin 3 → E)) Unit (LayerStmt Unit E 3 4) Unit
    (Typed.gkrSlot E 3 4) :=
  gkr 3 4 sixteen

/-- The public data of the bus phase's argument: the statement and the fingerprint challenges. -/
abbrev BusX : Type := toy.Stmt × ((Fin 4 → E) × E)

/-- The bus phase's shape around the argument: the fingerprint challenges, the two roots, the
argument for three trees of `2 ^ μ_bus` leaves read from the stack, and the boundary values. The
bus slot takes it at the slot's type, by definitional equality of the slots. -/
def busShape : Typed.Def (TheOracle toy) toy.Stmt Unit
    (LayerStmt BusX E 3 toy.μBus × Vector E toy.busClaims) Unit (busSlot toy) :=
  (((Typed.sampleChallenge (TheOracle toy) ((Fin 4 → E) × E) (fun _ ↦ true)
      fun s ab ↦ (s, ab)).append
    (Typed.sendChecked (TheOracle toy) (E × E) (fun _ ↦ (0, 0)) (fun _ _ ↦ true)
      fun s r ↦ ((s, ![r.1, r.1, r.2]) : BusX × (Fin 3 → E)))).append
    (gkr 3 toy.μBus fun _ _ _ ↦ Vector.replicate _ 1)).append
    (Typed.sendChecked (TheOracle toy) (Vector E toy.busClaims) (fun _ ↦ Vector.replicate _ 0)
      (fun _ _ ↦ true) fun s v ↦ (s, v))

/-! ## The relations, decided by evaluation -/

-- The quantifier over the riders is decided along the list: instance search would otherwise
-- enumerate every table over `E`, through the noncomputable `Fintype K`.
instance {μ : ℕ} (rd : Unit → (∀ i, NoOracle i) → List (Σ τ : Fin (μ + 1), CMlPolynomialEval E τ))
    (x : Unit) (o : ∀ i, NoOracle i) : Decidable (RidersZero μ rd x o) :=
  List.decidableBAll _ _

instance {nside μ : ℕ} (l : Unit → (∀ i, NoOracle i) → Fin nside → CMlPolynomialEval E μ)
    (rd : Unit → (∀ i, NoOracle i) → List (Σ τ : Fin (μ + 1), CMlPolynomialEval E τ)) (p) :
    Decidable (p ∈ relIn nside μ l rd) :=
  inferInstanceAs (Decidable (RidersZero μ rd p.1.1.1 p.1.2 ∧
    ∀ s, p.1.1.2 s = ∏ i : Fin (2 ^ μ), (l p.1.1.1 p.1.2 s)[i]))

instance {nside μ : ℕ} (l : Unit → (∀ i, NoOracle i) → Fin nside → CMlPolynomialEval E μ)
    (rd : Unit → (∀ i, NoOracle i) → List (Σ τ : Fin (μ + 1), CMlPolynomialEval E τ)) (p) :
    Decidable (p ∈ relOut nside μ l rd) :=
  @instDecidableAnd _ _
    (inferInstanceAs (Decidable (∀ s, evalMle (l p.1.1.1 p.1.2 s) p.1.1.2.1 = p.1.1.2.2 s)))
    (List.decidableBAll _ _)

/-! ## An honest run of `gkr 1 2`, by hand -/

/-- The root of the four-leaf tree. -/
def root : Fin 1 → E := fun _ ↦ a * b * c

/-- A wrong root. -/
def root' : Fin 1 → E := fun _ ↦ a * b * c + 1

#guard ((((), root), noO), ()) ∈ relIn 1 2 four noRiders
#guard ((((), root'), noO), ()) ∉ relIn 1 2 four noRiders

/-- After the combiner `λ = b`: no round to run, the point empty. -/
def t0 : SumcheckRound.Stmt (LayerX Unit E 1 0) E 0 := lambdaNext 1 0 (rootStmt 1 ((), root)) b

/-- The honest descendants at the empty point: the leaves themselves. -/
def leafVals : Fin 1 → CMlPolynomialEval E 2 := children 1 2 four 2 0 () noO #v[]

#guard (leafVals 0).toList = [a, b, c, 1]
#guard combineCheck 1 2 0 t0 leafVals
#guard ¬ combineCheck 1 2 0 (lambdaNext 1 0 (rootStmt 1 ((), root')) b) leafVals

/-- The statement after `u_0 = c`, `u_1 = a`. -/
def t1 : LayerStmt Unit E 1 (0 + 2) :=
  interpDone 1 2 0 (interpNext 1 2 0 (interpNext 1 2 0 (childNext 1 2 0 t0 leafVals) c) a)

#guard t1.2.1.toList = [c, a]
#guard ((t1, noO), ()) ∈ relOut 1 2 four noRiders

/-! ## An honest run of `gkr 3 4`, by hand -/

/-- The roots of the three sixteen-leaf trees. -/
def roots16 : Fin 3 → E := fun s ↦ ∏ i : Fin 16, (sixteen () noO s)[i]

#guard ((((), roots16), noO), ()) ∈ relIn 3 4 sixteen noRiders

/-- The first step, from the roots: the combiner `c`, no sumcheck round. -/
def a0 : SumcheckRound.Stmt (LayerX Unit E 3 0) E 0 := lambdaNext 3 0 (rootStmt 3 ((), roots16)) c

/-- The honest descendants of the roots: the second level. -/
def ch0 : Fin 3 → CMlPolynomialEval E 2 := children 3 4 sixteen 2 0 () noO #v[]

#guard combineCheck 3 2 0 a0 ch0

/-- After `u_0 = a`, `u_1 = c`: the statement at layer `2`. -/
def mid : LayerStmt Unit E 3 (0 + 2) :=
  interpDone 3 2 0 (interpNext 3 2 0 (interpNext 3 2 0 (childNext 3 2 0 a0 ch0) a) c)

-- It is in the relation at layer `2`: each value is the second level's extension at the point.
#guard ∀ s, evalMle (layerTable (sixteen () noO s) 2) mid.2.1 = mid.2.2 s

/-- The point the second step starts from. -/
def r : Vector E 2 := mid.2.1

/-- The trees' values at `r` on the second level. -/
def vals : Fin 3 → E := mid.2.2

#guard r.toList = [a, c]

/-- The combiner. -/
def lam : E := b

/-- The step's context: the layer statement, the combiner, no oracle, no witness. -/
def lctx : LayerCtx Unit E NoOracle 3 2 := (((((), (r, vals)), lam), noO), ())

/-- The combined claim. -/
def claim0 : E := (lambdaNext 3 2 ((), (r, vals)) lam).2.2

-- The combined claim is the family's claim with nothing fixed: the layer identity at `r`.
#guard claim0 = partialSum (summand 3 4 sixteen 2 2 lctx) r 0 #v[]
-- The combination is by the powers `1, λ, λ²`, tree `s` taking `λ^s`.
#guard claim0 = vals 0 + lam * vals 1 + lam * lam * vals 2

/-- The two sumcheck challenges. -/
def c0 : E := c
def c1 : E := a + c

/-- The honest polynomials: five coefficients each. -/
def q0 : SumcheckRound.Message E 4 := roundPoly 3 4 sixteen 2 2 lctx 0 #v[]
def q1 : SumcheckRound.Message E 4 := roundPoly 3 4 sixteen 2 2 lctx 1 #v[c0]

/-- The statements before each round. -/
def s0 : SumcheckRound.Stmt (LayerX Unit E 3 2) E 0 := ((((), (r, vals)), lam), (#v[], claim0))
def s1 : SumcheckRound.Stmt (LayerX Unit E 3 2) E 1 :=
  SumcheckRound.next 0 s0 (SumcheckRound.evaluate 4 q0 c0) c0
def s2 : SumcheckRound.Stmt (LayerX Unit E 3 2) E 2 :=
  SumcheckRound.next 1 s1 (SumcheckRound.evaluate 4 q1 c1) c1

-- Each honest polynomial passes the normalized check, `(1 - r_j) q(0) + r_j q(1)` against the
-- running claim, and the running claim is the family's.
#guard SumcheckRound.check 0 (weights 3 2) s0 q0
#guard (1 - a) * SumcheckRound.evaluate 4 q0 0 + a * SumcheckRound.evaluate 4 q0 1 = claim0
#guard s1.2.2 = partialSum (summand 3 4 sixteen 2 2 lctx) r 1 #v[c0]
#guard SumcheckRound.check 1 (weights 3 2) s1 q1
#guard s2.2.2 = partialSum (summand 3 4 sixteen 2 2 lctx) r 2 #v[c0, c1]
-- The final claim is the summand at the challenges, with no equality factor.
#guard s2.2.2 = summand 3 4 sixteen 2 2 lctx #v[c0, c1]
-- A polynomial of degree four is not a product of five affine factors: its top coefficient is
-- what the cofactor's degree allows, and the message carries no sixth.
example : SumcheckRound.Message E 4 = Vector E 5 := rfl

/-- The honest descendants. -/
def ch : Fin 3 → CMlPolynomialEval E 2 := children 3 4 sixteen 2 2 () noO #v[c0, c1]

-- The final check passes on the honest descendants.
#guard combineCheck 3 2 2 s2 ch
-- What it checks, written out: the final claim is `Σ_s λ^s ∏_c (ch s)[c]`.
#guard s2.2.2 = (∏ c : Fin 4, (ch 0)[c]) + lam * (∏ c : Fin 4, (ch 1)[c]) +
  lam * lam * (∏ c : Fin 4, (ch 2)[c])

/-- The next layer statement, after `u_0 = b`, `u_1 = a`. -/
def next : LayerStmt Unit E 3 (2 + 2) :=
  interpDone 3 2 2 (interpNext 3 2 2 (interpNext 3 2 2 (childNext 3 2 2 s2 ch) b) a)

-- The new point is `(u_0, u_1, c_0, c_1)`, the combination challenges first.
#guard next.2.1.toList = [b, a, c0, c1]
-- The output relation holds: each tree's new value is its leaves' extension at the new point.
#guard ((next, noO), ()) ∈ relOut 3 4 sixteen noRiders

/-! ## An honest run of `gkr 3 3`, by hand -/

/-- Three trees of eight leaves. -/
def eight : Unit → (∀ i, NoOracle i) → Fin 3 → CMlPolynomialEval E 3 :=
  fun x o s ↦ contract (sixteen x o s)

/-- Their roots. -/
def roots8 : Fin 3 → E := fun s ↦ ∏ i : Fin 8, (eight () noO s)[i]

#guard ((((), roots8), noO), ()) ∈ relIn 3 3 eight noRiders

/-- The binary step: the combiner `a`, no sumcheck round. -/
def e0 : SumcheckRound.Stmt (LayerX Unit E 3 0) E 0 := lambdaNext 3 0 (rootStmt 3 ((), roots8)) a

/-- Two values per tree: the first level. -/
def chb : Fin 3 → CMlPolynomialEval E 1 := children 3 3 eight 1 0 () noO #v[]

#guard combineCheck 3 1 0 e0 chb

/-- After the one combination challenge `u_0 = b`: the statement at layer `1`. -/
def p1 : LayerStmt Unit E 3 (0 + 1) :=
  interpDone 3 1 0 (interpNext 3 1 0 (childNext 3 1 0 e0 chb) b)

/-- The radix-four step from one variable: the combiner `c`, one sumcheck round. -/
def ctx1 : LayerCtx Unit E NoOracle 3 1 := (((p1, c), noO), ())
def e1 : SumcheckRound.Stmt (LayerX Unit E 3 1) E 0 := lambdaNext 3 1 p1 c
def h0 : SumcheckRound.Message E 4 := roundPoly 3 3 eight 2 1 ctx1 0 #v[]

#guard SumcheckRound.check 0 (weights 3 1) e1 h0

/-- After the round's challenge `a`. -/
def e2 : SumcheckRound.Stmt (LayerX Unit E 3 1) E 1 :=
  SumcheckRound.next 0 e1 (SumcheckRound.evaluate 4 h0 a) a

/-- The honest descendants. -/
def ch1 : Fin 3 → CMlPolynomialEval E 2 := children 3 3 eight 2 1 () noO #v[a]

#guard combineCheck 3 2 1 e2 ch1

/-- After `u_0 = c`, `u_1 = b`: the final statement. -/
def fin3 : LayerStmt Unit E 3 (1 + 2) :=
  interpDone 3 2 1 (interpNext 3 2 1 (interpNext 3 2 1 (childNext 3 2 1 e2 ch1) c) b)

#guard fin3.2.1.toList = [c, b, a]
#guard ((fin3, noO), ()) ∈ relOut 3 3 eight noRiders

/-! ## What is rejected -/

/-- The trees with one leaf changed. -/
def tampered : Unit → (∀ i, NoOracle i) → Fin 3 → CMlPolynomialEval E 4 :=
  fun x o s ↦ (sixteen x o s).set 0 (a + 1)

/-- The first polynomial of a prover who holds the tampered trees. -/
def q0' : SumcheckRound.Message E 4 := roundPoly 3 4 tampered 2 2 lctx 0 #v[]

-- It differs from the honest one and fails the check against the honest claim.
#guard q0'.toList ≠ q0.toList
#guard ¬ SumcheckRound.check 0 (weights 3 2) s0 q0'
-- A wrong running claim.
#guard ¬ SumcheckRound.check 0 (weights 3 2) (s0.1, (s0.2.1, claim0 + 1)) q0
-- Descendants of other leaves.
#guard ¬ combineCheck 3 2 2 s2 (children 3 4 tampered 2 2 () noO #v[c0, c1])
-- The descendants' products are checked against the claim: a wrong claim is rejected.
#guard ¬ combineCheck 3 2 2 (s2.1, (s2.2.1, s2.2.2 + 1)) ch

/-! ## Riders -/

/-- A rider on one variable whose table is `(1, 0)`: its extension `1 - x` vanishes at `1`
only. -/
def rider : Unit → (∀ i, NoOracle i) → List (Σ τ : Fin 3, CMlPolynomialEval E τ) :=
  fun _ _ ↦ [⟨1, #v[1, 0]⟩]

/-- A rider whose table is zero. -/
def zeroRider : Unit → (∀ i, NoOracle i) → List (Σ τ : Fin 3, CMlPolynomialEval E τ) :=
  fun _ _ ↦ [⟨1, #v[0, 0]⟩]

#guard ((((), root), noO), ()) ∈ relIn 1 2 four zeroRider
#guard ((((), root), noO), ()) ∉ relIn 1 2 four rider

/-- The final statement at a point whose low coordinate is `1`, the root of the rider. -/
def one : E := 1
def atRoot : LayerStmt Unit E 1 2 := ((), (#v[one, a], fun _ ↦ evalMle (four () noO 0) #v[one, a]))

-- The honest run's final statement: the leaf claim holds, the rider's extension is `1 - c ≠ 0`.
#guard ((t1, noO), ()) ∈ relOut 1 2 four zeroRider
#guard ((t1, noO), ()) ∉ relOut 1 2 four rider
-- At the rider's root the output relation holds although the rider is not zero: the escape
-- charged to that challenge.
#guard ((atRoot, noO), ()) ∈ relOut 1 2 four rider

/-- A rider on no variable whose one value is `1`: a condition that fails. -/
def constRider : Unit → (∀ i, NoOracle i) → List (Σ τ : Fin 3, CMlPolynomialEval E τ) :=
  fun _ _ ↦ [⟨0, #v[1]⟩]

-- A rider on no variable fails the output relation at every point, the rider's root included.
#guard ((((), root), noO), ()) ∉ relIn 1 2 four constRider
#guard ((t1, noO), ()) ∉ relOut 1 2 four constRider
#guard ((atRoot, noO), ()) ∉ relOut 1 2 four constRider

/-! ## Completeness -/

/-- The completeness half of the whole argument, without riders. -/
example : Typed.Complete (gkr 3 4 sixteen) (relIn 3 4 sixteen noRiders)
    (relOut 3 4 sixteen noRiders) :=
  gkrComplete 3 4 sixteen noRiders

/-- The completeness half with a rider that is zero, so that the input relation is inhabited (a
nonzero rider, such as `rider`, leaves it empty). -/
example : Typed.Complete (gkr 1 2 four) (relIn 1 2 four zeroRider)
    (relOut 1 2 four zeroRider) :=
  gkrComplete 1 2 four zeroRider

end LeanVMTests.Protocol.GrandProduct
