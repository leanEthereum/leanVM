/-
  LeanVM.Protocol.ToArkLib.GrandProductSecurity

  Round-by-round knowledge soundness of the batched grand-product argument, at the errors its
  schedule charges: a combiner, a sumcheck round or a combination challenge turns a false claim
  into a true one at few values, and the riders are tracked on the coordinates drawn so far.
  Candidate for ArkLib.
-/

module

public import LeanVM.Protocol.ToArkLib.GrandProduct
public import LeanVM.Protocol.ToCompPoly.Restriction

/-!
# Knowledge soundness of the grand product

`gkrSecurity nside μ leaves riders` is the security half of `gkr` at the errors
`Typed.gkrErrors F (1 / |F|) nside μ`, with the extractor that keeps the trivial witness. With
the witness `Unit` throughout, it is round-by-round soundness of the language `Gkr.relIn`:
nothing is extracted. It is composed, like the completeness half, from the parts' through
`Typed.Security.append`, so every challenge keeps the error its slot assigned it:

* the combiner: batching by powers (`Typed.batchSecurity`): a statement outside the layer
  relation combines into the family's first claim at `nside − 1` combiners at most, since two
  different value vectors combine to the same scalar at the roots of a polynomial of degree
  `nside − 1`;
* the sumcheck rounds: `SumcheckRound.roundsSecurity` on the layer's family, whose honest
  polynomials are consistent (`familyT_consistent`) and whose invariant is sound
  (`familyT_sound`);
* the descendants: their check is sound at error zero (`combineCheck_sound`): values that pass
  it and are the honest ones make the final claim the summand at the point;
* the combination challenges: a wrong value vector agrees with the honest one on one more
  coordinate at one challenge at most (`card_interpNext_le`), by
  `card_filter_restrictedZero_update_le` on the difference of the two tables.

*The riders.* The output relation asks each rider's extension to vanish at the low coordinates
of the final point, which are the last layer's combination challenges and then its sumcheck
challenges. Inside the argument the riders stay zero tables (`constTrack`): nothing of a layer's
point survives the next layer. At the last layer the state tracks them on the coordinates drawn
so far (`progTrack`, through `RestrictedZero` on a `Partial` point: `roundsPartial` during the
rounds, `interpPartial` during the combination challenges, both a challenge vector placed at its
coordinates by `Partial.ofVector`), and a rider that is not zero on the
coordinates so far is zero on one more at one challenge at most. A `RiderTrack` is what a step's
security needs of either: the predicates during the rounds, during the combination challenges
and at the new point, how each hands over to the next, and the one-escape bounds. The escape of
a rider at a challenge is dominated by the claim's at the same challenge, so the riders add
nothing to `Typed.gkrErrors`.

The step from layer `m` with `k` radix-four steps to follow uses the progressive tracker when
`k = 0` and the constant one otherwise (`layerStepsSecurity` splits on `k`); so does the first
step when `μ` is odd (`oddSecurity`). The relations between steps are `stepsIn`: the layer
relation, or, with no step left, the output relation read at the layer.
-/

namespace LeanVM.Protocol

open CompPoly CMlPolynomialEval OracleComp OracleSpec
open scoped NNReal ENNReal

@[expose] public section

namespace Gkr

variable {F : Type}

/-! ## The partial points of a step -/

/-- The coordinates of a layer's new point fixed by its first `j` sumcheck challenges: the
coordinates `ρ` to `ρ + j - 1`, the combination challenges coming first. -/
abbrev roundsPartial (ρ : ℕ) {j : ℕ} (χ : Vector F j) : Partial F := Partial.ofVector ρ χ

/-- The first `i` combination challenges as a partial point of the descendants' `ρ`
coordinates. -/
abbrev combPartial {i : ℕ} (u : Vector F i) : Partial F := Partial.ofVector 0 u

/-- The coordinates fixed by the sumcheck challenges and the first `i` combination
challenges. -/
abbrev interpPartial (ρ : ℕ) {m : ℕ} (χ : Vector F m) {i : ℕ} (u : Vector F i) : Partial F :=
  (combPartial u).or (roundsPartial ρ χ)

/-- With all `ρ` combination challenges drawn, every coordinate of the new point `(u, χ)` is
fixed. -/
private theorem interpPartial_full (ρ : ℕ) {m : ℕ} (χ : Vector F m) (u : Vector F ρ) (k : ℕ)
    (hk : k < m + ρ) :
    interpPartial ρ χ u k = some ((Vector.cast (Nat.add_comm ρ m) (u ++ χ))[k]) := by
  simp only [interpPartial, combPartial, roundsPartial, Partial.or, Partial.ofVector,
    Vector.getElem_cast, Vector.getElem_append]
  split_ifs <;> first | rfl | omega

variable [Field F] [Finite F] [BEq F] [LawfulBEq F] [DecidableEq F]
  [SampleableType F] {X : Type} {ι : Type} {O : ι → Type} [∀ i, OracleInterface (O i)]
  (nside μ : ℕ) (leaves : X → (∀ i, O i) → Fin nside → CMlPolynomialEval F μ)
  (riders : X → (∀ i, O i) → List (Σ τ : Fin (μ + 1), CMlPolynomialEval F τ))

/-! ## Riders on partial points -/

/-- Every rider is zero on the partial point. -/
def RidersZeroOn (x : X) (o : ∀ i, O i) (σ : Partial F) : Prop :=
  ∀ r ∈ riders x o, RestrictedZero r.2 σ

omit [Finite F] [BEq F] [LawfulBEq F] [DecidableEq F] [SampleableType F]
  [∀ i, OracleInterface (O i)] in
private theorem ridersZeroOn_empty_iff (x : X) (o : ∀ i, O i) :
    RidersZeroOn μ riders x o Partial.empty ↔ RidersZero μ riders x o := by
  simp only [RidersZeroOn, RidersZero, restrictedZero_empty_iff]

omit [BEq F] [LawfulBEq F] [DecidableEq F] [SampleableType F] [∀ i, OracleInterface (O i)] in
/-- Riders not all zero on a partial point are all zero on it with one more coordinate fixed
for at most one value. -/
private theorem card_ridersZeroOn_update_le (x : X) (o : ∀ i, O i) (σ : Partial F) (k : ℕ)
    (hne : ¬ RidersZeroOn μ riders x o σ) :
    Nat.card {c // RidersZeroOn μ riders x o (Function.update σ k (some c))} ≤ 1 := by
  have := Fintype.ofFinite F
  classical
  rw [natCard_subtype_eq_card_filter]
  simp only [RidersZeroOn, not_forall] at hne
  obtain ⟨r, hr, hne⟩ := hne
  refine (Finset.card_le_card fun c hc ↦ ?_).trans
    (card_filter_restrictedZero_update_le r.2 σ k hne)
  rw [Finset.mem_filter] at hc ⊢
  exact ⟨Finset.mem_univ _, hc.2 r hr⟩

/-! ## How a step tracks the riders -/

/-- How a step's knowledge state tracks the riders: a predicate during the sumcheck rounds
(`inv`), one during the combination challenges (`invU`), one at the new point (`out`); the
first is the riders' zeroness at the start, each hands over to the next, and each challenge
restores a broken predicate at one value at most. The field is finite: a `Nat.card` count of an
infinite set is `0`, which would make the two escape bounds hold of any predicate. -/
structure RiderTrack [Finite F] (ρ m : ℕ) where
  /-- During the rounds, after `j` challenges. -/
  inv : X → (∀ i, O i) → (j : ℕ) → Vector F j → Prop
  /-- During the combination challenges, after `i` of them, at the sumcheck's point. -/
  invU : X → (∀ i, O i) → Vector F m → (i : ℕ) → Vector F i → Prop
  /-- At the new point. -/
  out : X → (∀ i, O i) → Vector F (m + ρ) → Prop
  /-- Before the first round, the riders are zero. -/
  inv_zero : ∀ x o (v : Vector F 0), inv x o 0 v ↔ RidersZero μ riders x o
  /-- A round's challenge restores the predicate at one value at most. -/
  inv_escape : ∀ x o j (χ : Vector F j), ¬ inv x o j χ →
    Nat.card {c // inv x o (j + 1) (χ.push c)} ≤ 1
  /-- The rounds hand over to the combination challenges. -/
  invU_zero : ∀ x o (χ : Vector F m) (v : Vector F 0), invU x o χ 0 v ↔ inv x o m χ
  /-- A combination challenge restores the predicate at one value at most. -/
  invU_escape : ∀ x o (χ : Vector F m) i (u : Vector F i), ¬ invU x o χ i u →
    Nat.card {c // invU x o χ (i + 1) (u.push c)} ≤ 1
  /-- At the new point, the predicate is the one after all combination challenges. -/
  out_iff : ∀ x o (χ : Vector F m) (u : Vector F ρ),
    out x o (Vector.cast (Nat.add_comm ρ m) (u ++ χ)) ↔ invU x o χ ρ u

omit [Field F] [Finite F] [BEq F] [LawfulBEq F] [DecidableEq F] [SampleableType F]
  [∀ i, OracleInterface (O i)] in
/-- A predicate that does not depend on the challenge, false, is restored at no value. -/
private theorem card_const_le {P : Prop} (hP : ¬ P) : Nat.card {_c : F // P} ≤ 1 := by
  have : IsEmpty {_c : F // P} := ⟨fun c ↦ hP c.2⟩
  rw [Nat.card_of_isEmpty]
  exact zero_le_one

/-- Inside the argument, the riders stay zero tables: nothing of a layer's point survives. -/
def constTrack (ρ m : ℕ) : RiderTrack μ riders ρ m where
  inv := fun x o _ _ ↦ RidersZero μ riders x o
  invU := fun x o _ _ _ ↦ RidersZero μ riders x o
  out := fun x o _ ↦ RidersZero μ riders x o
  inv_zero := fun _ _ _ ↦ Iff.rfl
  inv_escape := fun _ _ _ _ h ↦ by exact card_const_le h
  invU_zero := fun _ _ _ _ ↦ Iff.rfl
  invU_escape := fun _ _ _ _ _ h ↦ by exact card_const_le h
  out_iff := fun _ _ _ _ ↦ Iff.rfl

/-- At the last layer, whose point is the final one, the riders are zero on the coordinates
drawn so far, and at the end vanish at the low coordinates of the final point. -/
def progTrack (ρ m : ℕ) (h : m + ρ = μ) : RiderTrack μ riders ρ m where
  inv := fun x o _ χ ↦ RidersZeroOn μ riders x o (roundsPartial ρ χ)
  invU := fun x o χ _ u ↦ RidersZeroOn μ riders x o (interpPartial ρ χ u)
  out := fun x o ζ ↦ ∀ r ∈ riders x o, evalMle r.2 (lowPoint (Vector.cast h ζ) r.1) = 0
  inv_zero := fun x o v ↦ by
    simp only [roundsPartial, Partial.ofVector_zero, ridersZeroOn_empty_iff]
  inv_escape := fun x o j χ hne ↦ by
    simp only [roundsPartial, Partial.ofVector_push]
    exact card_ridersZeroOn_update_le μ riders x o (roundsPartial ρ χ) (ρ + j) hne
  invU_zero := fun x o χ v ↦ by
    simp only [interpPartial, combPartial, Partial.ofVector_zero, Partial.empty_or]
  invU_escape := fun x o χ i u hne ↦ by
    simp only [interpPartial, combPartial, Partial.ofVector_push, Partial.update_or,
      Nat.zero_add]
    exact card_ridersZeroOn_update_le μ riders x o (interpPartial ρ χ u) i hne
  out_iff := fun x o χ u ↦ by
    simp only [RidersZeroOn]
    refine forall₂_congr fun r hr ↦ ?_
    rw [restrictedZero_of_all r.2 _ (lowPoint (Vector.cast h (Vector.cast (Nat.add_comm ρ m)
      (u ++ χ))) r.1)]
    intro k hk
    rw [interpPartial_full ρ χ u k (by have := r.1.isLt; omega)]
    simp [lowPoint, Vector.getElem_cast]

/-! ## The layer's family with a tracker -/

section Layer

variable (ρ m : ℕ)

/-- The layer's family of claims, the riders tracked by `T`: the same claims, polynomials and
domain as `family`, so the same rounds; `family` is this family at `constTrack`. -/
def familyT (T : RiderTrack μ riders ρ m) :
    SumcheckRound.Family F (LayerX X F nside m) O Unit (2 ^ ρ) where
  claim := fun ctx j cv ↦ partialSum (summand nside μ leaves ρ m ctx) (pointOf ctx) j cv
  poly := roundPoly nside μ leaves ρ m
  weight := weights nside m
  inv := fun ctx j cv ↦ T.inv (dataOf ctx) (oraclesOf ctx) j cv

omit [DecidableEq F] [SampleableType F] [∀ i, OracleInterface (O i)] in
/-- The honest polynomials of the tracked family are consistent: the same as `family`'s. -/
private theorem familyT_consistent (T : RiderTrack μ riders ρ m) :
    (familyT nside μ leaves riders ρ m T).Consistent m :=
  ⟨(family_honest nside μ leaves riders ρ m).check, (family_honest nside μ leaves riders ρ m).next⟩

omit [DecidableEq F] [SampleableType F] [∀ i, OracleInterface (O i)] in
/-- The tracked family's invariant is sound: a round's challenge restores it at one value at
most, within the polynomial degree. -/
private theorem familyT_sound (T : RiderTrack μ riders ρ m) :
    (familyT nside μ leaves riders ρ m T).Sound m :=
  fun _ _ cv _ hinv ↦ (T.inv_escape _ _ _ cv hinv).trans Nat.one_le_two_pow

/-! ## The combiner -/

variable {S : Type} (inp : S → LayerStmt X F nside m)

omit [DecidableEq F] [SampleableType F] [∀ i, OracleInterface (O i)] in
/-- After the combiner, the family's first relation is the riders' condition and the combined
claim being the combination, by the same powers, of the trees' levels at the layer's point. -/
private theorem mem_rel_lambdaNext (T : RiderTrack μ riders ρ m) (hm : m + ρ ≤ μ)
    (s : LayerStmt X F nside m) (o : ∀ i, O i) (l : F) :
    ((lambdaNext nside m s l, o), ()) ∈
        SumcheckRound.rel (familyT nside μ leaves riders ρ m T) 0 ↔
      RidersZero μ riders s.1 o ∧
        powerBatch s.2.2 l =
          powerBatch (fun t ↦ evalMle (layerTable (leaves s.1 o t) m) s.2.1) l := by
  change T.inv s.1 o 0 #v[] ∧ (lambdaNext nside m s l).2.2 =
    partialSum (summand nside μ leaves ρ m (((s, l), o), ())) s.2.1 0 #v[] ↔ _
  rw [T.inv_zero, partialSum_summand_zero nside μ leaves ρ m hm s o l]
  exact Iff.rfl

omit [DecidableEq F] [SampleableType F] [∀ i, OracleInterface (O i)] in
/-- The combiner's batching hypothesis: a statement outside the relation has the levels' values
as true values, fixed before the combiner, which a combiner landing in the family's first relation
makes the combined claim's, and which differ from the claimed values. -/
theorem lambda_batch (T : RiderTrack μ riders ρ m) (hm : m + ρ ≤ μ)
    {relS : Set ((S × ∀ i, O i) × Unit)}
    (hinp : ∀ s o, ((s, o), ()) ∈ relS ↔ ((inp s, o), ()) ∈ layerRel nside μ leaves riders m)
    (s : S) (o : ∀ i, O i) :
    ∃ a : Fin nside → F, ∀ w ρ', ((s, o), w) ∉ relS →
      (((((inp s, ρ'), (#v[], powerBatch (inp s).2.2 ρ')) :
          SumcheckRound.Stmt (LayerX X F nside m) F 0), o), w) ∈
        SumcheckRound.rel (familyT nside μ leaves riders ρ m T) 0 →
        a ≠ (inp s).2.2 ∧ powerBatch (inp s).2.2 ρ' = powerBatch a ρ' :=
  ⟨fun t ↦ evalMle (layerTable (leaves (inp s).1 o t) m) (inp s).2.1, fun w l hs hl ↦ by
    cases w
    obtain ⟨hz, hval⟩ := (mem_rel_lambdaNext nside μ leaves riders ρ m T hm (inp s) o l).mp hl
    exact ⟨fun he ↦ hs ((hinp s o).mpr ⟨hz, fun t ↦ congrFun he t⟩), hval⟩⟩

/-- The typed security half of the combiner at `(nside − 1) / |F|`. -/
def lambdaSecurity (T : RiderTrack μ riders ρ m) (hm : m + ρ ≤ μ)
    {relS : Set ((S × ∀ i, O i) × Unit)}
    (hinp : ∀ s o, ((s, o), ()) ∈ relS ↔ ((inp s, o), ()) ∈ layerRel nside μ leaves riders m) :
    Typed.Security (lambdaStep nside m inp) relS
      (SumcheckRound.rel (familyT nside μ leaves riders ρ m T) 0)
      (Typed.drawErrors F (((nside - 1 : ℕ) : ℝ≥0) / (Nat.card F : ℝ≥0))) :=
  Typed.batchSecurity (lambda_batch nside μ leaves riders ρ m inp T hm hinp)

/-! ## The descendants -/

/-- After the descendants' message with `i` combination challenges drawn: the riders by the
tracker, and each tree's values agree with the honest ones on the challenges drawn so far. At
`i = 0` and `constTrack` it is `childRel 0`: agreement on no challenge is equality. -/
def childRelT (T : RiderTrack μ riders ρ m) (i : ℕ) :
    Set ((InterpStmt X F nside m ρ i × ∀ j, O j) × Unit) :=
  {p | T.invU p.1.1.1.1 p.1.2 p.1.1.1.2.1 i p.1.1.2 ∧
    ∀ t, RestrictedZero
      (diffTable (p.1.1.1.2.2 t) (children nside μ leaves ρ m p.1.1.1.1 p.1.2 p.1.1.1.2.1 t))
      (combPartial p.1.1.2)}

omit [SampleableType F] [∀ i, OracleInterface (O i)] in
/-- The descendants' check is sound: values that pass it and are the honest ones make the final
claim the summand at the point. -/
private theorem combineCheck_sound (T : RiderTrack μ riders ρ m)
    (s : SumcheckRound.Stmt (LayerX X F nside m) F m) (o : ∀ i, O i)
    (ch : Fin nside → CMlPolynomialEval F ρ) (hc : combineCheck nside ρ m s ch = true)
    (hout : ((childNext nside ρ m s ch, o), ()) ∈ childRelT nside μ leaves riders ρ m T 0) :
    ((s, o), ()) ∈ SumcheckRound.rel (familyT nside μ leaves riders ρ m T) m := by
  obtain ⟨hinv, hch⟩ := hout
  refine ⟨(T.invU_zero _ _ _ _).mp hinv, ?_⟩
  have hch' : ∀ t, ch t = children nside μ leaves ρ m s.1.1.1 o s.2.1 t := fun t ↦ by
    have := hch t
    simp only [combPartial, Partial.ofVector_zero] at this
    exact (diffTable_restrictedZero_empty_iff _ _).mp this
  change s.2.2 = partialSum (summand nside μ leaves ρ m ((s.1, o), ())) s.1.1.2.1 m s.2.1
  rw [partialSum_self]
  rw [combineCheck, decide_eq_true_eq] at hc
  rw [hc, powerBatch]
  unfold summand
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun c _ ↦ ?_
  simp [hch', children, below]

/-- The typed security half of the descendants' message: no challenge. -/
def childrenSecurity (T : RiderTrack μ riders ρ m) :
    Typed.Security (sendChildren nside μ leaves ρ m)
      (SumcheckRound.rel (familyT nside μ leaves riders ρ m T) m)
      (childRelT nside μ leaves riders ρ m T 0) (Typed.sayErrors _) :=
  Typed.sendCheckedSecurity fun s o w ch hc hout ↦ by
    cases w
    exact combineCheck_sound nside μ leaves riders ρ m T s o ch hc hout

/-! ## The combination challenges -/

omit [BEq F] [LawfulBEq F] [DecidableEq F] [SampleableType F] [∀ i, OracleInterface (O i)] in
/-- A statement outside the relation after `i` combination challenges is inside it after one
more at one challenge at most: the riders' predicate or some tree's agreement was broken, and
each is restored at one value at most. -/
private theorem card_interpNext_le (T : RiderTrack μ riders ρ m) {i : ℕ}
    (s : InterpStmt X F nside m ρ i) (o : ∀ j, O j)
    (hs : ((s, o), ()) ∉ childRelT nside μ leaves riders ρ m T i) :
    Nat.card {c // ((interpNext nside ρ m s c, o), ()) ∈
      childRelT nside μ leaves riders ρ m T (i + 1)} ≤ 1 := by
  have := Fintype.ofFinite F
  classical
  rw [natCard_subtype_eq_card_filter]
  by_cases hinv : T.invU s.1.1 o s.1.2.1 i s.2
  · have hne : ∃ t, ¬ RestrictedZero
        (diffTable (s.1.2.2 t) (children nside μ leaves ρ m s.1.1 o s.1.2.1 t))
        (combPartial s.2) := by
      by_contra h
      exact hs ⟨hinv, fun t ↦ by_contra fun ht ↦ h ⟨t, ht⟩⟩
    obtain ⟨t, ht⟩ := hne
    refine (Finset.card_le_card fun c hc ↦ ?_).trans
      (card_filter_restrictedZero_update_le _ (combPartial s.2) i ht)
    rw [Finset.mem_filter] at hc ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    have := hc.2.2 t
    simp only [show (interpNext nside ρ m s c).2 = s.2.push c from rfl, combPartial,
      Partial.ofVector_push, Nat.zero_add] at this
    exact this
  · refine (Finset.card_le_card fun c hc ↦ ?_).trans
      ((natCard_subtype_eq_card_filter _).symm.trans_le
        (T.invU_escape _ _ _ i s.2 hinv))
    rw [Finset.mem_filter] at hc ⊢
    exact ⟨Finset.mem_univ _, hc.2.1⟩

/-- The typed security half of the first `i` combination challenges, at `1 / |F|` each. -/
def interpPrefixSecurity (T : RiderTrack μ riders ρ m) : (i : ℕ) →
    Typed.Security (interpPrefix nside ρ m i) (childRelT nside μ leaves riders ρ m T 0)
      (childRelT nside μ leaves riders ρ m T i) (Typed.drawsErrors F (1 / Nat.card F : ℝ≥0) i)
  | 0 => Typed.passThroughSecurityOfIff (f := id) fun _ _ ↦ Iff.rfl
  | i + 1 =>
    (interpPrefixSecurity T i).append
      ((Typed.sampleChallengeSecurity 1 fun s o _ ↦
        Typed.card_badChallenge_le_of_unit _ s o fun hs ↦
          by exact card_interpNext_le nside μ leaves riders ρ m T s o hs).mono (by
            refine ⟨?_, fun _ ↦ trivial⟩
            show ((1 : ℕ) : ℝ≥0) / (Nat.card F : ℝ≥0) ≤ 1 / Nat.card F
            rw [Nat.cast_one]))

/-- The step's output relation, the riders by the tracker: the new values are the level below
at the new point. -/
def stepOutT (T : RiderTrack μ riders ρ m) :
    Set ((LayerStmt X F nside (m + ρ) × ∀ i, O i) × Unit) :=
  {p | T.out p.1.1.1 p.1.2 p.1.1.2.1 ∧
    ∀ s, evalMle (layerTable (leaves p.1.1.1 p.1.2 s) (m + ρ)) p.1.1.2.1 = p.1.1.2.2 s}

omit [BEq F] [LawfulBEq F] [DecidableEq F] [SampleableType F] [∀ i, OracleInterface (O i)] in
/-- The interpolated statement is in the step's output relation exactly when the statement before
it is in the relation after all `ρ` combination challenges. -/
private theorem interpDone_mem_stepOutT_iff (T : RiderTrack μ riders ρ m)
    (s : InterpStmt X F nside m ρ ρ) (o : ∀ i, O i) :
    ((interpDone nside ρ m s, o), ()) ∈ stepOutT nside μ leaves riders ρ m T ↔
      ((s, o), ()) ∈ childRelT nside μ leaves riders ρ m T ρ := by
  show (T.out s.1.1 o (Vector.cast (Nat.add_comm ρ m) (s.2 ++ s.1.2.1)) ∧
    ∀ t, evalMle (layerTable (leaves s.1.1 o t) (m + ρ))
      (Vector.cast (Nat.add_comm ρ m) (s.2 ++ s.1.2.1)) = evalMle (s.1.2.2 t) s.2) ↔
    (T.invU s.1.1 o s.1.2.1 ρ s.2 ∧ ∀ t, RestrictedZero
      (diffTable (s.1.2.2 t) (children nside μ leaves ρ m s.1.1 o s.1.2.1 t)) (combPartial s.2))
  rw [T.out_iff]
  refine and_congr Iff.rfl (forall_congr' fun t ↦ ?_)
  rw [restrictedZero_of_all _ (combPartial s.2) s.2
      (fun k hk ↦ by simp [combPartial, Partial.ofVector, hk]), evalMle_diffTable,
    sub_eq_zero, evalMle_cast_append, eq_comm]
  exact Iff.rfl

/-- The typed security half of the combination challenges, at `1 / |F|` each. -/
def interpolateSecurity (T : RiderTrack μ riders ρ m) :
    Typed.Security (interpolate nside ρ m) (childRelT nside μ leaves riders ρ m T 0)
      (stepOutT nside μ leaves riders ρ m T) (Typed.drawsErrors F (1 / Nat.card F : ℝ≥0) ρ) :=
  match ρ, T with
  | 0, T =>
    Typed.passThroughSecurityOfIff (f := interpDone nside 0 m) fun s o ↦
      by exact interpDone_mem_stepOutT_iff nside μ leaves riders 0 m T s o
  | ρ' + 1, T =>
    (interpPrefixSecurity nside μ leaves riders (ρ' + 1) m T ρ').append
      ((Typed.sampleChallengeSecurity 1 fun s o _ ↦
        Typed.card_badChallenge_le_of_unit _ s o fun hs ↦ by
          exact (Finite.card_le_of_embedding (Subtype.impEmbedding _ _ fun c hc ↦
            (interpDone_mem_stepOutT_iff nside μ leaves riders (ρ' + 1) m T _ o).mp hc)).trans
            (card_interpNext_le nside μ leaves riders (ρ' + 1) m T s o hs)).mono (by
          refine ⟨?_, fun _ ↦ trivial⟩
          show ((1 : ℕ) : ℝ≥0) / (Nat.card F : ℝ≥0) ≤ 1 / Nat.card F
          rw [Nat.cast_one]))

/-! ## A step down -/

/-- The typed security half of a step whose level below exists, at the unit `1 / |F|`. -/
def layerStepSecurity (T : RiderTrack μ riders ρ m) (hm : m + ρ ≤ μ)
    {relS : Set ((S × ∀ i, O i) × Unit)}
    (hinp : ∀ s o, ((s, o), ()) ∈ relS ↔ ((inp s, o), ()) ∈ layerRel nside μ leaves riders m) :
    Typed.Security (layerStep nside μ leaves ρ m inp) relS
      (stepOutT nside μ leaves riders ρ m T)
      (Typed.stepErrors F nside ρ m (((nside - 1 : ℕ) : ℝ≥0) * (1 / Nat.card F))
        (1 / Nat.card F : ℝ≥0)) :=
  ((((lambdaSecurity nside μ leaves riders ρ m inp T hm hinp).mono
      (by exact ⟨(div_eq_mul_one_div _ _).le, fun _ ↦ trivial⟩)).append
    ((SumcheckRound.roundsSecurity (familyT nside μ leaves riders ρ m T) m
      (by exact familyT_consistent nside μ leaves riders ρ m T)
      (by exact familyT_sound nside μ leaves riders ρ m T) m 0 (Nat.zero_add m)).mono
      (by exact Typed.roundsErrors_le F (2 ^ ρ) (div_eq_mul_one_div _ _).le m))).append
    (childrenSecurity nside μ leaves riders ρ m T)).append
    (interpolateSecurity nside μ leaves riders ρ m T)

end Layer

/-! ## The whole argument -/

/-- The input relation of `k` radix-four steps from layer `m`: the layer relation, or, with no
step left, the output relation read at layer `m`. -/
def stepsIn : (k m : ℕ) → m + 2 * k = μ →
    Set ((LayerStmt X F nside m × ∀ i, O i) × Unit)
  | 0, m, h =>
    {p | (∀ r ∈ riders p.1.1.1 p.1.2, evalMle r.2 (lowPoint (Vector.cast h p.1.1.2.1) r.1) = 0) ∧
      ∀ s, evalMle (layerTable (leaves p.1.1.1 p.1.2 s) m) p.1.1.2.1 = p.1.1.2.2 s}
  | _ + 1, m, _ => layerRel nside μ leaves riders m

omit [Finite F] [BEq F] [LawfulBEq F] [DecidableEq F] [SampleableType F]
  [∀ i, OracleInterface (O i)] in
/-- With no step left, the input relation is the output relation across the equality of
layers. -/
private theorem stepsIn_zero_iff (m : ℕ) (h : m + 2 * 0 = μ) (s : LayerStmt X F nside m)
    (o : ∀ i, O i) :
    ((s, o), ()) ∈ stepsIn nside μ leaves riders 0 m h ↔
      (((s.1, (Vector.cast (by omega) s.2.1, s.2.2)), o), ()) ∈ relOut nside μ leaves riders := by
  have hm : m = μ := by omega
  subst hm
  simp only [stepsIn, relOut, Vector.cast_rfl, layerTable_self, Set.mem_ofPred_eq]
  exact and_comm

/-- The typed security half of the radix-four steps from layer `m`. -/
def layerStepsSecurity : (k m : ℕ) → (h : m + 2 * k = μ) →
    Typed.Security (layerSteps nside μ leaves k m h) (stepsIn nside μ leaves riders k m h)
      (relOut nside μ leaves riders) (Typed.stepsErrors F nside (1 / Nat.card F : ℝ≥0) k m)
  | 0, m, h =>
    Typed.passThroughSecurityOfIff fun s o ↦
      by exact (stepsIn_zero_iff nside μ leaves riders m h s o).symm
  | 1, m, h =>
    (layerStepSecurity nside μ leaves riders 2 m id (progTrack μ riders 2 m (by omega))
      (by omega) fun _ _ ↦ Iff.rfl).append (layerStepsSecurity 0 (m + 2) (by omega))
  | k + 2, m, h =>
    (layerStepSecurity nside μ leaves riders 2 m id (constTrack μ riders 2 m)
      (by omega) fun _ _ ↦ Iff.rfl).append (layerStepsSecurity (k + 1) (m + 2) (by omega))

omit [Finite F] [BEq F] [LawfulBEq F] [DecidableEq F] [SampleableType F]
  [∀ i, OracleInterface (O i)] in
/-- With no layer at all, the roots are in the output relation read at layer `0` exactly when
they are in the input relation: a rider on no variable is one value, its extension at the empty
point. -/
private theorem relIn_iff_stepsIn_zero (h : 0 + 2 * 0 = μ) (s : X × (Fin nside → F))
    (o : ∀ i, O i) :
    ((s, o), ()) ∈ relIn nside μ leaves riders ↔
      ((rootStmt nside s, o), ()) ∈ stepsIn nside μ leaves riders 0 0 h := by
  have hμ : μ = 0 := by omega
  subst hμ
  simp only [stepsIn, Set.mem_ofPred_eq]
  refine and_congr ?_ (forall_congr' fun t ↦ ?_)
  · refine forall₂_congr fun r hr ↦ ?_
    obtain ⟨⟨τ, hτ⟩, t⟩ := r
    have hτ0 : τ = 0 := by omega
    subst hτ0
    refine ⟨fun h ↦ ?_, fun h i ↦ ?_⟩
    · rw [evalMle_zero]
      exact h ⟨0, Nat.one_pos⟩
    · rw [evalMle_zero] at h
      obtain ⟨i, hi⟩ := i
      have hi0 : i = 0 := by
        have : i < 1 := hi
        omega
      subst hi0
      exact h
  · show s.2 t = ∏ i : Fin (2 ^ 0), (leaves s.1 o t)[i] ↔
      evalMle (layerTable (leaves s.1 o t) 0) #v[] = s.2 t
    constructor
    · intro h
      rw [evalMle_zero, h, ← layerTable_zero_getElem]
      rfl
    · intro h
      rw [evalMle_zero] at h
      rw [← h, ← layerTable_zero_getElem]
      rfl

/-- The typed security half of the first step. -/
def oddSecurity : (r : ℕ) → (hr : r ≤ 1) → (k : ℕ) → (hk : r + 2 * k = μ) →
    Typed.Security (odd nside μ leaves r hr) (relIn nside μ leaves riders)
      (stepsIn nside μ leaves riders k r hk) (Typed.oddErrors F nside (1 / Nat.card F : ℝ≥0) r)
  | 0, _, 0, hk =>
    Typed.passThroughSecurityOfIff (f := rootStmt nside) fun s o ↦
      by exact (relIn_iff_stepsIn_zero nside μ leaves riders hk s o).symm
  | 0, _, k + 1, hk =>
    Typed.passThroughSecurityOfIff (f := rootStmt nside) fun s o ↦
      by exact (relIn_iff_layerRel_zero nside μ leaves riders s o).symm
  | 1, _, 0, hk =>
    layerStepSecurity nside μ leaves riders 1 0 (rootStmt nside)
      (progTrack μ riders 1 0 (by omega)) (by omega)
      (relIn_iff_layerRel_zero nside μ leaves riders)
  | 1, _, k + 1, hk =>
    layerStepSecurity nside μ leaves riders 1 0 (rootStmt nside) (constTrack μ riders 1 0)
      (by omega) (relIn_iff_layerRel_zero nside μ leaves riders)
  | _ + 2, h, _, _ => absurd h (by omega)

end Gkr

variable {F : Type} [Field F] [Finite F] [BEq F] [LawfulBEq F] [DecidableEq F]
  [SampleableType F] {X : Type} {ι : Type} {O : ι → Type} [∀ i, OracleInterface (O i)]
  (nside μ : ℕ) (leaves : X → (∀ i, O i) → Fin nside → CMlPolynomialEval F μ)
  (riders : X → (∀ i, O i) → List (Σ τ : Fin (μ + 1), CMlPolynomialEval F τ))

/-- **Knowledge soundness** of the grand-product argument on the typed framework, at the errors
`Typed.gkrErrors` its slot charges from the unit `1 / |F|`, with the extractor that keeps the
trivial witness. It computes, extractor included. -/
def gkrSecurity :
    Typed.Security (gkr nside μ leaves) (Gkr.relIn nside μ leaves riders)
      (Gkr.relOut nside μ leaves riders) (Typed.gkrErrors F (1 / Nat.card F : ℝ≥0) nside μ) :=
  (Gkr.oddSecurity nside μ leaves riders (μ % 2) _ (μ / 2) (Nat.mod_add_div μ 2)).append
    (Gkr.layerStepsSecurity nside μ leaves riders (μ / 2) (μ % 2) (Nat.mod_add_div μ 2))

end
end LeanVM.Protocol
