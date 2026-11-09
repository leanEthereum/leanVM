/-
  LeanVM.Protocol.BusSecurity

  Round-by-round knowledge soundness of the bus phase at the slot's error: the fingerprint
  challenges at `4·2^{μ_bus}/|E|`, the grand-product argument at its own errors, the roots and
  the boundary values at none.
-/

module

public import LeanVM.Protocol.Bus
public import LeanVM.Protocol.ToArkLib.GrandProductSecurity

/-!
# Knowledge soundness of the bus phase

`busSecurity I h` is the security half of `busPhase I h` at the slot's errors `busErrors I`, from
`Seam.commit` to `Seam.bus`. The stack is the oracle and every witness is trivial, so it is
round-by-round soundness: a stack outside `M3Holds` reaches `Seam.bus` only through a bad
challenge. It is composed from the four steps' halves, at the same intermediate relations as
`busComplete`, so every challenge keeps the error the slot assigns it:

* **The challenges `(α, β)`** (`challengeSecurity`), at `4·2^{μ_bus}/|E|` (Theorem 5.1 and
  Proposition `prop:pad`, `doc/leanvm/body/08-end-to-end-protocol.tex` at leanVM `3a37fb6e1`).
  The state after them is `afterChallenge`: the push and pull products agree at `(α, β)`, the
  count product is nonzero, every constraint vanishes, and the public lines and the Keccak
  predicate hold. It asks the products to agree, not the multisets, since a collision of the
  products could be charged to no later challenge. A stack outside `M3Holds` whose executed count
  cells are nonzero and that meets the clauses no challenge touches is unbalanced: its executed
  rows' two multisets differ. Each side's product is then its executed tuples' product times its
  padding leaves, the fingerprints of nonzero tuples whatever the padding rows hold, so the two
  sides of at most `2^{μ_bus}` leaves collide at no more than `4·2^{μ_bus}·|E|⁴` of the `|E|⁵`
  challenges (`card_paddedSideProduct_collision_le`). A zero executed count cell makes the count
  product zero at every challenge (`countsNonzero_of_prod`).
* **The roots** (`rootsSecurity`), at no error: a root that passes the check `R_c ≠ 0` and is
  the product of its leaves makes the count product nonzero, and one root for push and pull makes
  their products agree. This is where the check is load-bearing: a zero count is otherwise
  balanced on the bus (§6.2, `06-bus-interactions.tex:78`; the deployed verifier's check is
  `crates/verifier/src/bus.rs:117-119`).
* **The grand-product argument** (`gkrSecurity`), at `Typed.gkrErrors` from the unit `1/|E|`. Its riders
  carry the constraints and the public lines with the Keccak predicate, so its state function
  carries the zerocheck: a constraint that does not vanish on the cube has a nonzero extension
  restricted to the coordinates of `ζ` drawn so far, which a coordinate makes zero at one value at
  most, inside the argument's own bound.
* **The boundary values** (`valuesSecurity`), at no error: the claims of `Seam.bus` force the
  values sent to be the boundary columns' extensions, and then the forms sum to the totals
  exactly when the leaf claims hold (`sum_forms_eq_total_iff`); the zerocheck clause gives the
  riders' vanishing.

Every part takes no real number and no `Fintype` instance as an argument, and the compositions
are inlined, so the security computes, its extractor included. The count of bad challenges is a
number the compiled security holds, so `|E|` is written `2^192` there (`card_E`): `Nat.card E` does
not compute.

Written from the specification and the protocol's relations; nothing is transcribed.
-/

namespace LeanVM.Protocol

open LeanVM.Parameters CompPoly CMlPolynomialEval OracleComp OracleSpec
open scoped NNReal

@[expose] public section

namespace Bus

variable {I : M3Instance}

/-! ## The challenges -/

/-- `|E| = 2^192`, counted with `Nat.card`. -/
private theorem natCard_E : Nat.card E = 2 ^ 192 := by
  rw [Nat.card_eq_fintype_card, card_E]

/-- From a stack outside `M3Holds`, at most `4·2^{μ_bus}·|E|⁴` challenges `(α, β)` lead into
`afterChallenge`: none if an executed count cell is zero (the count product is then zero) or a
clause no challenge touches fails, a collision of the two products otherwise, whatever the padding
rows hold (Proposition `prop:pad`). -/
private theorem card_afterChallenge_le (h : Conditions I) (s : I.Stmt) (o : ∀ i, TheOracle I i)
    (hs : ¬ M3Holds I s (theStack o)) :
    Nat.card {ab : (Fin 4 → E) × E // (((s, ab), o), ()) ∈ afterChallenge I} ≤
      4 * 2 ^ I.μBus * (2 ^ 192) ^ 4 := by
  rw [← natCard_E]
  by_cases hrest : I.CountsNonzero (theStack o) ∧ I.ConstraintsVanish (theStack o) ∧
      I.PublicLinesHold s (theStack o) ∧ I.aux (theStack o)
  · have hb : ¬ I.Balanced (theStack o) := fun hb ↦
      hs ⟨hrest.2.1, hb, hrest.1, hrest.2.2.1, hrest.2.2.2⟩
    have hne : (I.tuples (theStack o) .push : Multiset (Vector K 16)) ≠
        (I.tuples (theStack o) .pull : Multiset (Vector K 16)) :=
      fun he ↦ hb (Multiset.coe_eq_coe.mp he)
    have hP : (sidePadTuples I (theStack o) .push : Multiset (Vector K 16)).card +
        (I.tuples (theStack o) .push : Multiset (Vector K 16)).card ≤ 2 ^ I.μBus := by
      rw [Multiset.coe_card, Multiset.coe_card, length_side (k := 0) rfl, ← blocks_total]
      exact push_fits I
    have hQ : (sidePadTuples I (theStack o) .pull : Multiset (Vector K 16)).card +
        (I.tuples (theStack o) .pull : Multiset (Vector K 16)).card ≤ 2 ^ I.μBus := by
      rw [Multiset.coe_card, Multiset.coe_card, length_side (k := 1) rfl]
      exact h.pull_fits
    refine (Finite.card_le_of_embedding (Subtype.impEmbedding _ _ fun ab hab ↦ ?_)).trans
      (card_paddedSideProduct_collision_le hne (fun u hu ↦ padTuple_ne_zero h hu)
        (fun u hu ↦ padTuple_ne_zero h hu) hP hQ)
    have hprod := hab.1
    change ∏ x : Fin (2 ^ I.μBus), (pushLeaves I ab.1 ab.2 (theStack o))[x] =
      ∏ x : Fin (2 ^ I.μBus), (pullLeaves I ab.1 ab.2 (theStack o))[x] at hprod
    rw [prod_pushLeaves, prod_pullLeaves h] at hprod
    exact hprod
  · have : IsEmpty {ab : (Fin 4 → E) × E // (((s, ab), o), ()) ∈ afterChallenge I} :=
      ⟨fun ab ↦ hrest ⟨countsNonzero_of_prod h _ _ _ ab.2.2.1, ab.2.2.2⟩⟩
    rw [Nat.card_of_isEmpty]
    exact Nat.zero_le _

/-- The challenges' count over their number is the slot's error, `4·2^{μ_bus}/|E|`. -/
private theorem challenge_error_eq :
    ((4 * 2 ^ I.μBus * (2 ^ 192) ^ 4 : ℕ) : ℝ≥0) / (Nat.card ((Fin 4 → E) × E) : ℝ≥0) =
      overE (4 * 2 ^ I.μBus) := by
  rw [← natCard_E]
  have hE : (Nat.card E : ℝ≥0) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast Fintype.card_ne_zero
  rw [overE, ← Nat.card_eq_fintype_card, Nat.card_prod, Nat.card_fun, Nat.card_fin]
  push_cast
  rw [mul_comm ((Nat.card E : ℝ≥0) ^ 4) (Nat.card E : ℝ≥0),
    mul_div_mul_right _ _ (pow_ne_zero 4 hE)]

/-- The challenges' typed security half, at `4·2^{μ_bus}/|E|` (Theorem 5.1). -/
def challengeSecurity (h : Conditions I) :
    Typed.Security (challengeStep I) (Seam.commit I) (afterChallenge I)
      (Typed.drawErrors _ (overE (4 * 2 ^ I.μBus))) :=
  (Typed.sampleChallengeSecurity (4 * 2 ^ I.μBus * (2 ^ 192) ^ 4) fun s o _ ↦
    Typed.card_badChallenge_le_of_unit _ s o fun hs ↦
      by exact card_afterChallenge_le h s o hs).mono
      (by exact ⟨le_of_eq challenge_error_eq, fun _ ↦ trivial⟩)

/-! ## The roots -/

/-- A root that passes the check `R_c ≠ 0` and is the product of its leaves makes the count
product nonzero, and one root for push and pull makes their products agree. -/
theorem roots_reflect (h : Conditions I) (x : Data I) (o : ∀ i, TheOracle I i) (w : Unit)
    (r : E × E) (hc : decide (r.2 ≠ 0) = true)
    (hout : (((x, ![r.1, r.1, r.2]), o), w) ∈ Gkr.relIn 3 I.μBus (leaves I) (riders I)) :
    ((x, o), w) ∈ afterChallenge I := by
  cases w
  obtain ⟨hz, hroots⟩ := hout
  obtain ⟨hcons, hl, ha⟩ := (ridersZero_iff h x o).mp hz
  have h0 : r.1 = ∏ i : Fin (2 ^ I.μBus), (leaves I x o 0)[i] := hroots 0
  have h1 : r.1 = ∏ i : Fin (2 ^ I.μBus), (leaves I x o 1)[i] := hroots 1
  have h2 : r.2 = ∏ i : Fin (2 ^ I.μBus), (leaves I x o 2)[i] := hroots 2
  have hnz : r.2 ≠ 0 := of_decide_eq_true hc
  rw [h2] at hnz
  exact ⟨h0.symm.trans h1, hnz, hcons, hl, ha⟩

/-- The roots' typed security half, at no error. -/
def rootsSecurity (h : Conditions I) :
    Typed.Security (rootsStep I) (afterChallenge I)
      (Gkr.relIn 3 I.μBus (leaves I) (riders I)) (Typed.sayErrors _) :=
  Typed.sendCheckedSecurity (roots_reflect h)

/-! ## The boundary values -/

/-- The boundary claims force the values sent, the forms summing to the totals then force the
leaf claims, and the zerocheck clause the riders' vanishing. -/
theorem values_reflect (h : Conditions I) (ℓ : Gkr.LayerStmt (Data I) E 3 I.μBus)
    (o : ∀ i, TheOracle I i) (w : Unit) (vals : Vector E I.busClaims)
    (_ : (fun (_ : Gkr.LayerStmt (Data I) E 3 I.μBus) (_ : Vector E I.busClaims) ↦ true) ℓ vals
      = true)
    (hout : (((ℓ.1.1, busOut h ℓ vals), o), w) ∈ Seam.bus I) :
    ((ℓ, o), w) ∈ Gkr.relOut 3 I.μBus (leaves I) (riders I) := by
  cases w
  obtain ⟨hzero, hforms, hclaims, hl, ha⟩ := hout
  have hvals : ∀ i : Fin I.busClaims, vals[i] = eval₂Mle
      (I.column (theStack o) I.boundaryColumns[i]).values (algebraMap K E)
      (columnPoint h ℓ.2.1 i) := fun i ↦
    (hclaims ⟨I.boundaryColumns[i], columnPoint h ℓ.2.1 i, vals[i]⟩
      (by simp only [busOut, Vector.toList_ofFn, List.mem_ofFn]; exact ⟨i, rfl⟩)).symm
  refine ⟨fun k ↦ (sum_forms_eq_total_iff h k _ _ _ _ _ _ hvals).mp (hforms k),
    (riders_vanish_iff ℓ.1 o ℓ.2.1).mpr ⟨fun j hj C hC ↦ ?_, hl, ha⟩⟩
  have := hzero ⟨j, Or.inl (List.ne_nil_of_mem hC)⟩ C hC
  rwa [show (busOut h ℓ vals).point = point h ℓ.2.1 from rfl, lowPoint_point] at this

/-- The values' typed security half, at no error. -/
def valuesSecurity (h : Conditions I) :
    Typed.Security (valuesStep I h) (Gkr.relOut 3 I.μBus (leaves I) (riders I))
      (Seam.bus I) (Typed.sayErrors _) :=
  Typed.sendCheckedSecurity (values_reflect h)

end Bus

/-- **Knowledge soundness of the bus phase on the typed framework**, at the slot's errors
`busErrors I`, from `Seam.commit` to `Seam.bus`, with the extractor that keeps the trivial
witness. It computes, extractor included. -/
def busSecurity (I : M3Instance) (h : Bus.Conditions I) :
    Typed.Security (busPhase I h) (Seam.commit I) (Seam.bus I) (busErrors I) :=
  (((Bus.challengeSecurity h).append (Bus.rootsSecurity h)).append
    ((gkrSecurity 3 I.μBus (Bus.leaves I) (Bus.riders I)).mono (by
      rw [overE_one]
      exact Typed.Errors.Le.refl _ _ _))).append
    (Bus.valuesSecurity h)

end
end LeanVM.Protocol
