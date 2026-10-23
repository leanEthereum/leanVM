import LeanVM.Protocol.ToArkLib.GrandProductSecurity
import LeanVM.Protocol.ToArkLib.Oracles
import LeanVM.Protocol.Spine.Errors
import LeanVMTests.Protocol.GrandProduct

/-!
# Grand-product knowledge-soundness tests

Over `E`, on the trees of the grand-product tests.

* **The theorem has an inhabitant that computes** at the slot's errors: `gkrSecurity 3 4 sixteen
  noRiders`, raised from the unit `1 / |E|` to the slot's `overE 1` (`overE_one`), is a `def`
  without `noncomputable`, and so is its extractor; so are the instances with a zero rider, whose
  input relation is inhabited, with a nonzero rider, whose input relation is empty, and for an
  odd `μ`.
* **The riders are tracked.** At the last layer of `gkr 1 2`, the rider `1 - x` is zero on the
  coordinates fixed so far exactly when the first combination challenge is its root.
* **The round check is load-bearing.** Without it, the challenge of the second step's first
  round is not knowledge sound below error one, whatever the extractor:
  from a statement whose running claim is the family's plus one, the honest polynomial lands in
  the next relation at every challenge.
* **The descendants' check is load-bearing.** Without it, no security exists for the
  descendants' message, at any error and whatever the extractor: from a statement whose final claim is the
  family's plus one, the honest descendants are accepted into the relation after the message.
* **Partial points.** The coordinates the state function tracks: the sumcheck challenges fill
  `ρ, …, ρ + j − 1`, the combination challenges `0, …, i − 1`, and together the whole new point.

The refutations take their statement at a variable layer statement and point: a statement
built from the hand run's values puts the trees' evaluation over `E` into a definitional
comparison, which does not finish. They are stated at the completeness
half's relations, `family` and `childRel`: with no riders these are the security half's,
`familyT` at `constTrack` definitionally and `childRelT … 0` by agreement on no challenge being
equality, so the verifier refuted is the one `gkrSecurity` is proved for.
-/

namespace LeanVMTests.Protocol.GrandProductSecurity

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Gkr LeanVM.Protocol.SumcheckRound
  LeanVMTests.Protocol.GrandProduct CompPoly CMlPolynomialEval
open scoped NNReal

/-! ## The theorem has an inhabitant -/

/-- Knowledge soundness of `gkr 3 4` at the slot's errors, without riders. -/
def security34 : Typed.Security (gkr 3 4 sixteen) (relIn 3 4 sixteen noRiders)
    (relOut 3 4 sixteen noRiders) (Typed.gkrErrors E (overE 1) 3 4) :=
  (gkrSecurity 3 4 sixteen noRiders).mono (Typed.Errors.Le.of_eq (by rw [overE_one]))

/-- Its extractor at a statement, which a slot reads. -/
def extractor34 := security34.extractor

/-- With a zero rider: the input relation is inhabited. -/
example : Typed.Security (gkr 1 2 four) (relIn 1 2 four zeroRider)
    (relOut 1 2 four zeroRider) (Typed.gkrErrors E (overE 1) 1 2) :=
  (gkrSecurity 1 2 four zeroRider).mono (Typed.Errors.Le.of_eq (by rw [overE_one]))

/-- With a nonzero rider: no statement is in the input relation, and every one escapes at each
challenge with at most the error charged to it. -/
example : Typed.Security (gkr 1 2 four) (relIn 1 2 four rider) (relOut 1 2 four rider)
    (Typed.gkrErrors E (overE 1) 1 2) :=
  (gkrSecurity 1 2 four rider).mono (Typed.Errors.Le.of_eq (by rw [overE_one]))

/-- For an odd `μ`, where the binary layer comes first. -/
example : Typed.Security (gkr 3 3 eight) (relIn 3 3 eight noRiders)
    (relOut 3 3 eight noRiders) (Typed.gkrErrors E (overE 1) 3 3) :=
  (gkrSecurity 3 3 eight noRiders).mono (Typed.Errors.Le.of_eq (by rw [overE_one]))

/-! ## The riders are tracked -/

instance {n : ℕ} (t : CMlPolynomialEval E n) (σ : Partial E) : Decidable (RestrictedZero t σ) :=
  inferInstanceAs (Decidable (∀ b : Fin (2 ^ n), evalMle t (σ.point b) = 0))

instance (rd : Unit → (∀ i, NoOracle i) → List (Σ τ : Fin 3, CMlPolynomialEval E τ))
    (σ : Partial E) : Decidable (RidersZeroOn 2 rd () noO σ) :=
  List.decidableBAll _ _

-- At the last layer of `gkr 1 2` there is no sumcheck round, and the combination challenges fix
-- the coordinates from `0` up. Before any, the rider is not zero; after the first, it is zero
-- on the coordinates fixed exactly when the challenge is `1`, the root of `1 - x`.
#guard ¬ RidersZeroOn 2 rider () noO (interpPartial 2 (#v[] : Vector E 0) (#v[] : Vector E 0))
#guard RidersZeroOn 2 rider () noO (interpPartial 2 (#v[] : Vector E 0) (#v[one] : Vector E 1))
#guard ¬ RidersZeroOn 2 rider () noO (interpPartial 2 (#v[] : Vector E 0) (#v[a] : Vector E 1))

/-! ## The round check is load-bearing -/

/-- The second step's family, on the tests' three sixteen-leaf trees. -/
def Φ : SumcheckRound.Family E (LayerX Unit E 3 2) NoOracle Unit 4 :=
  family 3 4 sixteen noRiders 2 2

/-- The map of the first round's challenge: the polynomial's value at it is the next claim. -/
def nextClaim (p : MidStmt (LayerX Unit E 3 2) E 0 4) (c : E) :
    SumcheckRound.Stmt (LayerX Unit E 3 2) E 1 :=
  SumcheckRound.next 0 p.1 (SumcheckRound.evaluate 4 p.2 c) c

/-- A verifier that draws the first round's challenge without checking the polynomial has no
knowledge error below one, whatever the extractor: from a running claim off by one, the honest
polynomial is accepted at every challenge. -/
theorem unchecked_round_one_le {e : ℝ≥0}
    (S : Typed.Security (Typed.sampleChallenge NoOracle E (fun _ ↦ true) nextClaim)
      (relMid Φ 0) (rel Φ 1) (Typed.drawErrors E e)) : 1 ≤ e := by
  obtain ⟨x⟩ : Nonempty (LayerX Unit E 3 2) := ⟨(((), (#v[0, 0], fun _ ↦ 0)), 0)⟩
  exact Typed.sampleChallenge_one_le S
    ((x, (#v[], Φ.claim ((x, noO), ()) 0 #v[] + 1)), Φ.poly ((x, noO), ()) 0 #v[]) noO
    (fun _ h ↦ one_ne_zero (add_eq_left.mp h.1.2)) rfl fun c ↦
      ⟨(), fun r hr ↦ absurd hr List.not_mem_nil,
        (family_honest 3 4 sixteen noRiders 2 2).next ((x, noO), ()) 0 #v[] c (by decide)⟩

/-! ## The descendants' check is load-bearing -/

/-- A verifier that reads the descendants without checking them has no security from the
sumcheck's final relation to the relation after the message, at any error and whatever the
extractor: from a final claim off by one, the honest descendants are accepted. -/
theorem unchecked_children_no_security
    {hp : (SumcheckRound.Stmt (LayerX Unit E 3 2) E 2 × ∀ i, NoOracle i) × Unit →
      (Fin 3 → Vector E 4)}
    {err : Typed.Errors (Typed.sayTree (Fin 3 → Vector E 4)) (Typed.sayRoles _)}
    (S : Typed.Security (Typed.sendChecked NoOracle (Fin 3 → Vector E 4) hp (fun _ _ ↦ true)
      (childNext 3 2 2)) (rel Φ 2) (childRel 3 4 sixteen noRiders 2 2 0) err) : False := by
  obtain ⟨x⟩ : Nonempty (LayerX Unit E 3 2) := ⟨(((), (#v[0, 0], fun _ ↦ 0)), 0)⟩
  obtain ⟨cv⟩ : Nonempty (Vector E 2) := ⟨#v[0, 0]⟩
  exact Typed.sendChecked_no_security S (x, (cv, Φ.claim ((x, noO), ()) 2 cv + 1)) noO
    (fun w hmem ↦ by
      cases w
      exact one_ne_zero (add_eq_left.mp hmem.2))
    (children 3 4 sixteen 2 2 x.1.1 noO cv) rfl () ⟨fun r hr ↦ absurd hr List.not_mem_nil, rfl⟩

/-! ## Partial points -/

/-- Two sumcheck challenges of a radix-four layer. -/
def χ : Vector E 2 := #v[a, b]

/-- Two combination challenges. -/
def u : Vector E 2 := #v[c, one]

-- The sumcheck challenges fill coordinates `2` and `3`; nothing else is fixed.
#guard (List.range 6).map (roundsPartial 2 χ) = [none, none, some a, some b, none, none]
-- One combination challenge fills coordinate `0` as well.
#guard (List.range 6).map (interpPartial 2 χ (#v[c] : Vector E 1)) =
  [some c, none, some a, some b, none, none]
-- Both fill the whole new point `(u, χ)`.
#guard (List.range 6).map (interpPartial 2 χ u) = [some c, some one, some a, some b, none, none]
-- The descendants' coordinates, by the combination challenges alone.
#guard (List.range 3).map (combPartial u) = [some c, some one, none]

end LeanVMTests.Protocol.GrandProductSecurity
