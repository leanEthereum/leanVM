/-
  LeanVM.Protocol.ToArkLib.Flock.Security

  The knowledge soundness of the Flock argument: each component's round-by-round knowledge
  soundness at the count of its bad challenges, and their composition. Candidate for ArkLib.
-/

module

public import LeanVM.Protocol.ToArkLib.Flock.Reduction
import LeanVM.Protocol.ToCompPoly.PowerBatching

/-!
# Knowledge soundness of the Flock argument

Every component keeps the trivial witness, so its knowledge state is its input relation and a
challenge is bad when it carries a statement outside the input relation into the output
relation. The counts, per challenge, over `|F|`:

* a drawn coordinate of the point: `1`. A residual that is not zero on the coordinates fixed so far
  is zero with one more fixed for one value at most (`natCard_restrictedZero_update_le`).
* `z_skip`: `2 · 2 ^ s - 1`. If a residual is not zero at the point, or the message is not `P` on
  the coset, the interpolated polynomial is not `P`, and two polynomials of degree below
  `2 · 2 ^ s` agree at `2 · 2 ^ s - 1` points at most (`card_interpolateAt_eq_le`).
* a zerocheck round: `2`, the sumcheck round's count. The invariant's constant-position track
  escapes at one value at most, and only where the claim is true.
* `α`: `3`. If one of the three values or the constant position is wrong, the batched claim and
  the lincheck sum are distinct cubics in `α` (`card_false_batch_le`), by the block-diagonal
  identity.
* a lincheck round: `2`.
* a ring-switching coefficient: `1`. A family whose `π`s do not all vanish keeps a nonzero `π`
  after a stage for every coefficient but one (`card_stage_zero_le_one`).

Soundness needs two facts about the constants that completeness does not. They are hypotheses
here, discharged for each instance:
* the fixed coordinates of the point carry `F_2`-independent weights (`hfixed`); with
  characteristic two and Boolean tables, a residual zero on the fixed coordinates alone is zero
  (`eq_zero_of_restrictedZero_fixed`);
* ring switching is injective (`hinj`): a family whose `π`s all vanish is zero.

The messages, which check nothing or check what the next relation reads, have error zero.

Three of the verifier's checks come with refutations, whatever the extractor: without the
lincheck's terminal check the slices have no security at any error
(`linEnd_unchecked_no_security`); interpolating values sent at every node instead of assuming
zeros on the skip nodes (`skipDraw_unzeroed_one_le`), or batching without the constant position's
`α³` term (`alphaDraw_noConst_one_le`), leaves a challenge with no knowledge error below one.

Nothing here transcribes a source.
-/

namespace LeanVM.Protocol

namespace Flock

open CompPoly CMlPolynomialEval OracleComp OracleSpec SumcheckRound BlockR1CS
open scoped NNReal

@[expose] public section

/-! ## Errors -/

variable {F : Type}

/-- `N / |F|`, with `|F|` counted by `Nat.card`. -/
noncomputable abbrev overF (F : Type) (N : ℕ) : ℝ≥0 := (N : ℝ≥0) / (Nat.card F : ℝ≥0)

/-- A predicate that implies another holds of fewer elements. -/
theorem natCard_subtype_mono {α : Type} [Finite α] {p q : α → Prop} (h : ∀ a, p a → q a) :
    Nat.card {a // p a} ≤ Nat.card {a // q a} :=
  Nat.card_le_card_of_injective (fun a ↦ ⟨a.1, h a.1 a.2⟩) fun _ _ hab ↦
    Subtype.ext (congrArg Subtype.val hab :)

/-- A predicate that holds of nothing holds of no element. -/
theorem natCard_subtype_eq_zero {α : Type} {p : α → Prop} (h : ∀ a, ¬ p a) :
    Nat.card {a // p a} = 0 := by
  have : IsEmpty {a // p a} := ⟨fun a ↦ h a.1 a.2⟩
  exact Nat.card_of_isEmpty

/-! ## The fixed coordinates and Boolean residuals -/

section Lemmas

variable [Field F] (P : Params F)

/-- A completion of the fixed coordinates alone: the fixed coordinates, then a cube point. -/
theorem point_pointPartial_empty (h : Fin (2 ^ P.nRand)) :
    (P.pointPartial (#v[] : Vector F 0)).point
        (Fin.cast (congrArg (2 ^ ·) P.hpoint) (cubeIndex (0 : Fin (2 ^ P.nFix)) h)) =
      Vector.cast P.hpoint (P.fixed ++ (boolVec h : Vector F P.nRand)) := by
  apply Vector.ext
  intro k hk
  have hk' : k < P.nFix + P.nRand := P.hpoint ▸ hk
  simp only [Partial.point, Params.pointPartial, Partial.ofVector, Vector.getElem_ofFn,
    Vector.getElem_cast, Vector.getElem_append]
  by_cases hkf : k < P.nFix
  · rw [dite_eq_left ⟨Nat.zero_le _, by simpa using hkf⟩, dite_eq_left hkf]
    simp [hkf]
  · rw [dite_eq_right (by simp; omega), dite_eq_right hkf]
    simp [boolVec, Fin.getElem_fin, Nat.testBit_two_pow_mul, show P.nFix ≤ k by omega]

/-- **The fixed coordinates.** If the weights `eq(fixed, v)` of the fixed coordinates are
`F_2`-independent, a Boolean table zero on the fixed coordinates alone is zero. -/
theorem eq_zero_of_restrictedZero_fixed
    (hfixed : ∀ c : Fin (2 ^ P.nFix) → F, (∀ v, c v = 0 ∨ c v = 1) →
      ∑ v, (lagrangeBasis P.fixed)[v] * c v = 0 → ∀ v, c v = 0)
    (t : CMlPolynomialEval F (P.m + P.κ))
    (hbool : ∀ u : Fin (2 ^ (P.m + P.κ)), t[u] = 0 ∨ t[u] = 1)
    (h : RestrictedZero t (P.pointPartial (#v[] : Vector F 0))) (u : Fin (2 ^ (P.m + P.κ))) :
    t[u] = 0 := by
  set t' : CMlPolynomialEval F (P.nFix + P.nRand) :=
    Vector.cast (congrArg (2 ^ ·) P.hpoint.symm) t with ht'
  have ht : ∀ u' : Fin (2 ^ (P.nFix + P.nRand)),
      t'[u'] = t[Fin.cast (congrArg (2 ^ ·) P.hpoint) u'] := fun u' ↦ by
    simp [t']
  have hslice : ∀ (hi : Fin (2 ^ P.nRand)) v, t'[cubeIndex v hi] = 0 := by
    intro hi
    refine hfixed (fun v ↦ t'[cubeIndex v hi]) (fun v ↦ by rw [ht]; exact hbool _) ?_
    have h0 := h (Fin.cast (congrArg (2 ^ ·) P.hpoint) (cubeIndex (0 : Fin (2 ^ P.nFix)) hi))
    rw [point_pointPartial_empty, ← evalMle_cast P.hpoint.symm t, Vector.cast_cast,
      Vector.cast_rfl, ← ht', evalMle_append_boolVec, evalMle_eq_sum] at h0
    simp only [slice_getElem] at h0
    rw [← h0]
    exact Finset.sum_congr rfl fun v _ ↦ mul_comm _ _
  obtain ⟨⟨v, hi⟩, hvh⟩ := (cubeSplit P.nFix P.nRand).surjective
    (Fin.cast (congrArg (2 ^ ·) P.hpoint.symm) u)
  have := hslice hi v
  rw [ht, ← cubeSplit_apply, hvh] at this
  simpa using this

variable [CharP F 2] {s m κ : ℕ}

/-- In characteristic two, the residuals of a Boolean batch are Boolean. -/
theorem isBool_errTable (C : BlockR1CS F (s + m)) {z : Fin (2 ^ s) → CMlPolynomialEval F (m + κ)}
    (hz : ∀ i (u : Fin (2 ^ (m + κ))), (z i)[u] = 0 ∨ (z i)[u] = 1) (i : Fin (2 ^ s))
    (u : Fin (2 ^ (m + κ))) : (errTable C z i)[u] = 0 ∨ (errTable C z i)[u] = 1 := by
  obtain ⟨⟨jin, t⟩, rfl⟩ := (cubeSplit m κ).surjective u
  rw [cubeSplit_apply, errTable_getElem, leftTable_cubeIndex, rightTable_cubeIndex]
  have hb : ∀ j : Fin (2 ^ (s + m)), IsBool (batchBlock z t)[j] := fun j ↦ by
    obtain ⟨⟨jsk, jin'⟩, rfl⟩ := (cubeSplit s m).surjective j
    rw [cubeSplit_apply, batchBlock_cubeIndex]
    exact hz _ _
  rcases isBool_rows_fst C hb (cubeIndex i jin) with ha | ha <;>
    rcases isBool_rows_snd C hb (cubeIndex i jin) with hb' | hb' <;>
    rcases hz i (cubeIndex jin t) with hc | hc <;>
    simp [ha, hb', hc, CharTwo.sub_eq_add]

end Lemmas

variable [Field F] [DecidableEq F] [SampleableType F] [Finite F] (P : Params F)
  {ι : Type} {O : ι → Type} [∀ i, OracleInterface (O i)]
  (C : BlockR1CS F (P.s + P.m))
  (z : (∀ i, O i) → Fin (2 ^ P.s) → CMlPolynomialEval F (P.m + P.κ))
  {S : Type} (side : S → (∀ i, O i) → Prop)

/-! ## The point -/

omit [∀ i, OracleInterface (O i)] [SampleableType F] in
/-- The count behind `drawPointSecurity`. -/
theorem drawPoint_card (j : ℕ) (s : PointStmt S F j) (o : ∀ i, O i)
    (hin : ((s, o), ()) ∉ pointRel P C z side j) :
    Nat.card {x : F // (((s.1, s.2.push x), o), ()) ∈ pointRel P C z side (j + 1)} ≤ 1 := by
  by_cases hall : side s.1 o ∧ ∀ t : Fin (2 ^ P.κ), (constTable P.cpos (z o))[t] = 0
  · -- Some residual is not zero on the point so far: it is zero after one value at most.
    have hres : ¬ ∀ i, RestrictedZero (errTable C (z o) i) (P.pointPartial s.2) :=
      fun h ↦ hin ⟨hall.1, h, hall.2⟩
    obtain ⟨i₀, hi₀⟩ := not_forall.mp hres
    refine (natCard_subtype_mono fun x hx ↦ ?_).trans
      (natCard_restrictedZero_update_le _ _ (P.nFix + j) hi₀)
    have := hx.2.1 i₀
    rwa [show (s.1, s.2.push x).2 = s.2.push x from rfl, P.pointPartial_push] at this
  · -- The side condition or the constant position fails, and no challenge restores it.
    rw [natCard_subtype_eq_zero fun x hx ↦ hall ⟨hx.1, hx.2.2⟩]
    exact zero_le_one

/-- One coordinate of the point, typed. -/
def drawPointSecurity (j : ℕ) :
    Typed.Security (drawPoint (S := S) (F := F) (O := O) (W := Unit) j)
      (pointRel P C z side j) (pointRel P C z side (j + 1)) (Typed.drawErrors F (overF F 1)) :=
  Typed.sampleChallengeSecurity _ fun s o _ ↦
    Typed.card_badChallenge_le_of_unit _ s o (drawPoint_card P C z side j s o)

/-- The point's draws, typed. -/
def pointDrawsSecurity (relIn : Set ((S × ∀ i, O i) × Unit))
    (hIn : ∀ s o, ((s, o), ()) ∈ relIn → (((s, #v[]), o), ()) ∈ pointRel P C z side 0)
    (hOut : ∀ s o, (((s, #v[]), o), ()) ∈ pointRel P C z side 0 → ((s, o), ()) ∈ relIn) :
    (j : ℕ) → Typed.Security (pointDraws (S := S) (F := F) (O := O) (W := Unit) j) relIn
      (pointRel P C z side j) (Typed.drawsErrors F (overF F 1) j)
  | 0 => Typed.passThroughSecurityOfIff fun s o ↦ ⟨hOut s o, hIn s o⟩
  | j + 1 => (pointDrawsSecurity relIn hIn hOut j).append (drawPointSecurity P C z side j)

/-! ## The univariate skip -/

/-- The skip message, typed. -/
def skipMsgSecurity :
    Typed.Security (skipMsg P C z (S := S) (O := O) (W := Unit)) (pointRel P C z side P.nRand)
      (skipRel P C z side) (Typed.sayErrors _) :=
  Typed.sendCheckedSecurity fun _ _ _ _ _ h ↦ h.1

omit [DecidableEq F] [SampleableType F] [Finite F] [∀ i, OracleInterface (O i)] in
/-- The zerocheck's first claim is `P` at `z_skip`. -/
theorem zcFamily_claim_zero {W : Type} (ctx : Ctx (ZcX S F (P.m + P.κ)) O W) :
    (zcFamily P C z side).claim ctx 0 #v[] =
      pValue P.nodes C (z ctx.1.2) ctx.1.1.2.1 ctx.1.1.2.2 := by
  rw [pValue_eq]
  show partialSum _ _ 0 #v[] = _
  rw [partialSum_zero]
  rfl

omit [DecidableEq F] [SampleableType F] [Finite F] [∀ i, OracleInterface (O i)] in
/-- If a residual is not zero at the point or the message is not `P` on the coset, the values
the verifier interpolates, zeros then the message, are not those of `P`. -/
theorem skipValues_ne
    (hnodes : Function.Injective fun j : Fin (2 ^ P.s + 2 ^ P.s) ↦ P.nodes.pts[j])
    (s : PointStmt S F P.nRand × Vector F (2 ^ P.s)) (o : ∀ i, O i)
    (hpre : side s.1.1 o ∧ ∀ t : Fin (2 ^ P.κ), (constTable P.cpos (z o))[t] = 0)
    (hin : ((s, o), ()) ∉ skipRel P C z side) :
    Vector.replicate (2 ^ P.s) (0 : F) ++ s.2 ≠
      Vector.ofFn fun j ↦ (pPoly P.nodes C (z o) (P.point s.1.2)).eval P.nodes.pts[j] := by
  intro heq
  have hent : ∀ (j : ℕ) (hj : j < 2 ^ P.s + 2 ^ P.s),
      (Vector.replicate (2 ^ P.s) (0 : F) ++ s.2)[j] =
        pValue P.nodes C (z o) (P.point s.1.2) P.nodes.pts[j] := fun j hj ↦ by
    rw [heq, Vector.getElem_ofFn, eval_pPoly]
    rfl
  apply hin
  refine ⟨⟨hpre.1, fun i ↦ ?_, hpre.2⟩, ?_⟩
  · rw [restrictedZero_of_all _ _ _ (P.pointPartial_all s.1.2)]
    have h0 := hent i.val (by omega)
    rw [Vector.getElem_append_left i.isLt, Vector.getElem_replicate,
      pValue_skipNode P.nodes hnodes] at h0
    exact h0.symm
  · apply Vector.ext
    intro k hk
    have h1 := hent (2 ^ P.s + k) (by omega)
    rw [Vector.getElem_append_right (by omega) (by omega)] at h1
    simp only [Nat.add_sub_cancel_left] at h1
    rw [h1]
    simp only [skipHonest, skipMessage, Vector.getElem_ofFn]

omit [∀ i, OracleInterface (O i)] [SampleableType F] in
/-- The count behind `skipDrawSecurity`. -/
theorem skipDraw_card
    (hnodes : Function.Injective fun j : Fin (2 ^ P.s + 2 ^ P.s) ↦ P.nodes.pts[j])
    (s : PointStmt S F P.nRand × Vector F (2 ^ P.s)) (o : ∀ i, O i)
    (hin : ((s, o), ()) ∉ skipRel P C z side) :
    Nat.card {x : F // ((skipNext P s x, o), ()) ∈ rel (zcFamily P C z side) 0} ≤
      2 ^ P.s + 2 ^ P.s - 1 := by
  have := Fintype.ofFinite F
  classical
  by_cases hpre : side s.1.1 o ∧ ∀ t : Fin (2 ^ P.κ), (constTable P.cpos (z o))[t] = 0
  · rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    refine (Finset.card_le_card fun Y hY ↦ ?_).trans
      (card_interpolateAt_eq_le P.nodes.pts hnodes _ _
        (degree_pPoly_lt P.nodes C (z o) (P.point s.1.2))
        (skipValues_ne P C z side hnodes s o hpre hin))
    rw [Finset.mem_filter] at hY ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    have hc : skipClaim P.nodes s.2 Y =
        (zcFamily P C z side).claim (((s.1.1, P.point s.1.2, Y), o), ()) 0 #v[] := hY.2.2
    rw [zcFamily_claim_zero, skipClaim, P.nodes.allInv_eq, interpolateWith_lagrangeInv] at hc
    rw [hc, eval_pPoly]
  · rw [natCard_subtype_eq_zero fun Y hY ↦ hpre ⟨hY.1.1, by
      have hres := hY.1.2
      change RestrictedZero _ (Partial.ofSuffix P.m (#v[] : Vector F 0)) at hres
      rwa [Partial.ofSuffix_of_le _ _ (Nat.zero_le _), restrictedZero_empty_iff] at hres⟩]
    exact Nat.zero_le _

/-- `z_skip`, typed. -/
def skipDrawSecurity
    (hnodes : Function.Injective fun j : Fin (2 ^ P.s + 2 ^ P.s) ↦ P.nodes.pts[j]) :
    Typed.Security (skipDraw P (S := S) (O := O) (W := Unit)) (skipRel P C z side)
      (rel (zcFamily P C z side) 0) (Typed.drawErrors F (overF F (2 ^ P.s + 2 ^ P.s - 1))) :=
  Typed.sampleChallengeSecurity _ fun s o _ ↦
    Typed.card_badChallenge_le_of_unit _ s o (skipDraw_card P C z side hnodes s o)

/-! ## The zerocheck's rounds -/

omit [DecidableEq F] [SampleableType F] [∀ i, OracleInterface (O i)] in
/-- The zerocheck's family is sound: on the within-block coordinates its invariant does not move;
on the batch coordinates a challenge restores the constant position's track at one value at
most. -/
theorem zcFamily_sound {W : Type} : (zcFamily P C z side (W := W)).Sound (P.m + P.κ) := by
  intro ctx j c _ hinv
  by_cases hside : side ctx.1.1.1 ctx.1.2
  · have hres : ¬ RestrictedZero (constTable P.cpos (z ctx.1.2)) (Partial.ofSuffix P.m c) :=
      fun h ↦ hinv ⟨hside, h⟩
    by_cases hj : j < P.m
    · rw [natCard_subtype_eq_zero fun x hx ↦ hres (by
        have := hx.2
        rwa [Partial.ofSuffix_push_of_lt _ _ _ hj] at this)]
      exact Nat.zero_le _
    · refine (natCard_subtype_mono fun x hx ↦ ?_).trans
        ((natCard_restrictedZero_update_le _ _ (j - P.m) hres).trans (by norm_num))
      have := hx.2
      rwa [Partial.ofSuffix_push_of_le _ _ _ (by omega)] at this
  · rw [natCard_subtype_eq_zero fun x hx ↦ hside hx.1]
    exact Nat.zero_le _

/-- The rounds on the within-block coordinates, typed. -/
def zcRoundsLowSecurity :
    Typed.Security (zcRoundsLow P C z side (O := O) (W := Unit))
      (rel (zcFamily P C z side) 0) (rel (zcFamily P C z side) P.m)
      (Typed.roundsErrors F 2 (overF F 2) P.m) :=
  roundsSecurity (zcFamily P C z side) P.m
    { check := fun ctx j c hj ↦ (zcFamily_honest P C z side).check ctx j c (by omega)
      next := fun ctx j c x hj ↦ (zcFamily_honest P C z side).next ctx j c x (by omega) }
    (fun ctx j c hj ↦ zcFamily_sound P C z side ctx j c (by omega))
    P.m 0 (Nat.zero_add _)

/-- The rounds on the batch coordinates, typed. -/
def zcRoundsHighSecurity :
    Typed.Security (zcRoundsHigh P C z side (O := O) (W := Unit))
      (rel (zcFamily P C z side) P.m) (rel (zcFamily P C z side) (P.m + P.κ))
      (Typed.roundsErrors F 2 (overF F 2) P.κ) :=
  roundsSecurity (zcFamily P C z side) (P.m + P.κ) (zcFamily_honest P C z side).toConsistent
    (zcFamily_sound P C z side) P.κ P.m rfl

omit [DecidableEq F] [∀ i, OracleInterface (O i)] [SampleableType F] [Finite F] in
/-- The reflection behind `zcEndSecurity`. -/
theorem zcEnd_reflect (s : Stmt (ZcX S F (P.m + P.κ)) F (P.m + P.κ)) (o : ∀ i, O i) (w : Unit)
    (v : Vector F 2)
    (_ : (fun (_ : Stmt (ZcX S F (P.m + P.κ)) F (P.m + P.κ)) (_ : Vector F 2) ↦ true) s v = true)
    (h : ((termNext s v, o), w) ∈ termRel P C z side) :
    ((s, o), w) ∈ rel (zcFamily P C z side) (P.m + P.κ) := by
  cases w
  obtain ⟨hside, hconst, ha, hb, hc⟩ := h
  refine ⟨⟨hside, hconst⟩, ?_⟩
  change evalMle (zcA P C z o s.1.2.2) s.2.1 = v[0] at ha
  change evalMle (zcB P C z o s.1.2.2) s.2.1 = v[1] at hb
  change evalMle (zcC P z o s.1.2.2) s.2.1 = v[0] * v[1] - s.2.2 at hc
  show s.2.2 = (zcFamily P C z side).claim ((s.1, o), ()) (P.m + P.κ) s.2.1
  simp only [zcFamily, partialSum_self, prodSub]
  rw [ha, hb, hc]
  ring

/-- The terminal values, typed. -/
def zcEndSecurity :
    Typed.Security (zcEnd P C z (S := S) (O := O) (W := Unit))
      (rel (zcFamily P C z side) (P.m + P.κ)) (termRel P C z side) (Typed.sayErrors _) :=
  Typed.sendCheckedSecurity (zcEnd_reflect P C z side)

/-! ## The lincheck -/

omit [DecidableEq F] [SampleableType F] [Finite F] [∀ i, OracleInterface (O i)] in
/-- The lincheck's first claim: the three values and the constant position batched by `α`, by
the block-diagonal identity. -/
theorem linFamily_claim_zero {W : Type} (t : TermStmt S F (P.m + P.κ)) (α : F) (o : ∀ i, O i)
    (w : W) :
    (linFamily P C z side).claim (((t, α), o), w) 0 #v[] =
      evalMle (zcA P C z o t.1.2.2) t.2.1 + α * evalMle (zcB P C z o t.1.2.2) t.2.1 +
        α ^ 2 * evalMle (zcC P z o t.1.2.2) t.2.1 +
        α ^ 3 * (1 - evalMle (constTable P.cpos (z o)) (highVec t.2.1)) := by
  show highSum (linFun (linM P C (t, α)) (linZ P z o (t, α))) 0 #v[] = _
  rw [highSum_zero, sum_linFun_boolVec, linM, linZ, sum_mTable_zTable, lowVec_append_highVec]
  rfl

/-- Two different coefficient vectors give the same polynomial value at `n - 1` points at most. -/
private theorem card_filter_powerSum_eq_le {G : Type*} [Field G] [Fintype G] [DecidableEq G]
    {n : ℕ} (a b : Fin n → G) (hne : a ≠ b) :
    (Finset.univ.filter fun l : G ↦ ∑ t, l ^ t.val * a t = ∑ t, l ^ t.val * b t).card ≤
      n - 1 := by
  refine le_trans (le_of_eq (congrArg Finset.card (Finset.filter_congr fun l _ ↦ ?_)))
    (card_false_batch_le a b (Function.ne_iff.mp hne))
  simp only [powerBatch, mul_comm]

omit [DecidableEq F] [SampleableType F] [Finite F] [∀ i, OracleInterface (O i)] in
/-- A cubic in `α` by its four coefficients. -/
private theorem sum_four (l a₀ a₁ a₂ a₃ : F) :
    ∑ t : Fin 4, l ^ t.val * ![a₀, a₁, a₂, a₃] t = a₀ + l * a₁ + l ^ 2 * a₂ + l ^ 3 * a₃ := by
  simp [Fin.sum_univ_four]

omit [∀ i, OracleInterface (O i)] [SampleableType F] in
/-- The count behind `alphaDrawSecurity`. -/
theorem alphaDraw_card (t : TermStmt S F (P.m + P.κ)) (o : ∀ i, O i)
    (hin : ((t, o), ()) ∉ termRel P C z side) :
    Nat.card {x : F // ((alphaNext t x, o), ()) ∈ rel (linFamily P C z side) 0} ≤ 3 := by
  have := Fintype.ofFinite F
  classical
  by_cases hside : side t.1.1 o
  · have hne : (![t.2.2.1, t.2.2.2.1, t.2.2.2.2, 1] : Fin 4 → F) ≠
        ![evalMle (zcA P C z o t.1.2.2) t.2.1, evalMle (zcB P C z o t.1.2.2) t.2.1,
          evalMle (zcC P z o t.1.2.2) t.2.1,
          1 - evalMle (constTable P.cpos (z o)) (highVec t.2.1)] := by
      intro hab
      have h0 : t.2.2.1 = evalMle (zcA P C z o t.1.2.2) t.2.1 := congrFun hab 0
      have h1 : t.2.2.2.1 = evalMle (zcB P C z o t.1.2.2) t.2.1 := congrFun hab 1
      have h2 : t.2.2.2.2 = evalMle (zcC P z o t.1.2.2) t.2.1 := congrFun hab 2
      have h3 : (1 : F) = 1 - evalMle (constTable P.cpos (z o)) (highVec t.2.1) :=
        congrFun hab 3
      refine hin ⟨hside, ?_, h0.symm, h1.symm, h2.symm⟩
      rw [restrictedZero_of_all _ _ (highVec t.2.1) fun k hk ↦ by
        rw [Partial.ofSuffix_all _ t.2.1 k hk]
        simp [highVec]]
      linear_combination h3
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    refine (Finset.card_le_card fun l hl ↦ ?_).trans (card_filter_powerSum_eq_le _ _ hne)
    rw [Finset.mem_filter] at hl ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    have hc : t.2.2.1 + l * t.2.2.2.1 + l ^ 2 * t.2.2.2.2 + l ^ 3 =
        (linFamily P C z side).claim (((t, l), o), ()) 0 #v[] := hl.2.2
    rw [linFamily_claim_zero] at hc
    rw [sum_four, sum_four, mul_one]
    exact hc
  · rw [natCard_subtype_eq_zero fun l hl ↦ hside hl.1]
    exact Nat.zero_le _

/-- `α`, typed. -/
def alphaDrawSecurity :
    Typed.Security (alphaDraw P (S := S) (O := O) (W := Unit)) (termRel P C z side)
      (rel (linFamily P C z side) 0) (Typed.drawErrors F (overF F 3)) :=
  Typed.sampleChallengeSecurity _ fun t o _ ↦
    Typed.card_badChallenge_le_of_unit _ t o (alphaDraw_card P C z side t o)

omit [DecidableEq F] [SampleableType F] [∀ i, OracleInterface (O i)] in
/-- The lincheck's family is sound: its invariant does not move. -/
theorem linFamily_sound {W : Type} : (linFamily P C z side (W := W)).Sound P.m := by
  intro ctx j c _ hinv
  rw [natCard_subtype_eq_zero (p := fun x ↦ (linFamily P C z side).inv ctx (j + 1) (c.push x))
    fun x hx ↦ hinv hx]
  exact Nat.zero_le _

/-- The lincheck's rounds, typed. -/
def linRoundsSecurity :
    Typed.Security (linRounds P C z side (O := O) (W := Unit))
      (rel (linFamily P C z side) 0) (rel (linFamily P C z side) P.m)
      (Typed.roundsErrors F 2 (overF F 2) P.m) :=
  roundsSecurity (linFamily P C z side) P.m (linFamily_honest P C z side).toConsistent
    (linFamily_sound P C z side) P.m 0 (Nat.zero_add _)

omit [∀ i, OracleInterface (O i)] [SampleableType F] [Finite F] in
/-- The reflection behind `linEndSecurity`. -/
theorem linEnd_reflect (st : Stmt (LinX S F (P.m + P.κ)) F P.m) (o : ∀ i, O i) (w : Unit)
    (sv : Vector F (2 ^ P.s)) (hcheck : linCheck P C st sv = true)
    (hout : ((linNext P st sv, o), w) ∈ outRel P z side) :
    ((st, o), w) ∈ rel (linFamily P C z side) P.m := by
  cases w
  refine ⟨hout.1, ?_⟩
  rw [linCheck, decide_eq_true_eq] at hcheck
  show st.2.2 = highSum (linFun (linM P C st.1) (linZ P z o st.1)) P.m st.2.1
  rw [hcheck, linTerminal_eq, highSum_self, linFun]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  congr 1
  have hsv : sv[i] = evalMle (z o i) (linPoint P st) := hout.2 i
  rw [hsv, linPoint, linZ, evalMle_sliceLow_zTable]

/-- The slices, typed. -/
def linEndSecurity :
    Typed.Security (linEnd P C z (S := S) (O := O) (W := Unit)) (rel (linFamily P C z side) P.m)
      (outRel P z side) (Typed.sayErrors _) :=
  Typed.sendCheckedSecurity (linEnd_reflect P C z side)

/-- The verifier's claim from values at every node, the skip nodes' among them: `z_skip` with the
zeros not assumed. -/
def skipNextAll (s : PointStmt S F P.nRand × Vector F (2 ^ P.s + 2 ^ P.s)) (Y : F) :
    Stmt (ZcX S F (P.m + P.κ)) F 0 :=
  ((s.1.1, P.point s.1.2, Y), (#v[], interpolateWith P.nodes.pts P.nodes.allInv s.2 Y))

/-- The verifier's batched claim without the constant position's term. -/
def alphaNextNoConst {n : ℕ} (t : TermStmt S F n) (α : F) : Stmt (LinX S F n) F 0 :=
  ((t, α), (#v[], t.2.2.1 + α * t.2.2.2.1 + α ^ 2 * t.2.2.2.2))

/-! ## The checks are load-bearing -/

omit [DecidableEq F] [SampleableType F] [Finite F] [∀ i, OracleInterface (O i)] in
/-- Without the lincheck's terminal check, the slices have no security at any error, whatever
the extractor: from a running claim off the family's, the honest slices are accepted. -/
theorem linEnd_unchecked_no_security
    {err : Typed.Errors (Typed.sayTree (Vector F (2 ^ P.s))) (Typed.sayRoles _)}
    (Sec : Typed.Security (Typed.sendChecked O _ (linHonest P z) (fun _ _ ↦ true)
      (linNext P (S := S))) (rel (linFamily P C z side (W := Unit)) P.m) (outRel P z side) err)
    (st : Stmt (LinX S F (P.m + P.κ)) F P.m) (o : ∀ i, O i) (hside : side st.1.1.1.1 o)
    (hclaim : st.2.2 ≠ (linFamily P C z side (W := Unit)).claim ((st.1, o), ()) P.m st.2.1) :
    False :=
  Typed.sendChecked_no_security Sec st o (fun w h ↦ hclaim (by cases w; exact h.2))
    (linHonest P z ((st, o), ())) rfl () ⟨hside, fun i ↦ by simp [linHonest, linNext]⟩

omit [DecidableEq F] [Finite F] [∀ i, OracleInterface (O i)] in
/-- Interpolating values sent at every node, the skip nodes' included, instead of assuming zeros
on the skip nodes, leaves `z_skip` with no knowledge error below one, whatever the extractor:
from a residual not zero at the point, the honest coset values carry the true claim. -/
theorem skipDraw_unzeroed_one_le
    (hnodes : Function.Injective fun j : Fin (2 ^ P.s + 2 ^ P.s) ↦ P.nodes.pts[j])
    {relIn : Set (((PointStmt S F P.nRand × Vector F (2 ^ P.s + 2 ^ P.s)) × ∀ i, O i) × Unit)}
    (hrel : ∀ s msg o, (((s, msg), o), ()) ∈ relIn → ((s, o), ()) ∈ pointRel P C z side P.nRand)
    {e : ℝ≥0}
    (Sec : Typed.Security (Typed.sampleChallenge O F (fun _ ↦ true) (skipNextAll P (S := S)))
      relIn (rel (zcFamily P C z side) 0) (Typed.drawErrors F e))
    (s : PointStmt S F P.nRand) (o : ∀ i, O i) (hside : side s.1 o)
    (hconst : ∀ t : Fin (2 ^ P.κ), (constTable P.cpos (z o))[t] = 0) (i : Fin (2 ^ P.s))
    (hres : evalMle (errTable C (z o) i) (P.point s.2) ≠ 0) : 1 ≤ e :=
  Typed.sampleChallenge_one_le Sec
    (s, Vector.ofFn fun j ↦ pValue P.nodes C (z o) (P.point s.2) P.nodes.pts[j]) o
    (fun w hw ↦ by
      cases w
      exact hres ((restrictedZero_of_all _ _ _ (P.pointPartial_all s.2)).mp
        ((hrel _ _ _ hw).2.1 i)))
    rfl fun Y ↦ ⟨(), ⟨hside, by
      show RestrictedZero _ (Partial.ofSuffix P.m (#v[] : Vector F 0))
      rw [Partial.ofSuffix_of_le _ _ (Nat.zero_le _), restrictedZero_empty_iff]
      exact hconst⟩, by
      show interpolateWith P.nodes.pts P.nodes.allInv
          (Vector.ofFn fun j ↦ pValue P.nodes C (z o) (P.point s.2) P.nodes.pts[j]) Y =
        (zcFamily P C z side).claim (((s.1, P.point s.2, Y), o), ()) 0 #v[]
      rw [zcFamily_claim_zero, P.nodes.allInv_eq, interpolateWith_lagrangeInv]
      simp only [← eval_pPoly]
      exact interpolateAt_eval P.nodes.pts hnodes _ (degree_pPoly_lt P.nodes C (z o) _) Y⟩

omit [DecidableEq F] [Finite F] [∀ i, OracleInterface (O i)] in
/-- Batching the lincheck's claims without the constant position's `α³` term leaves `α_lc` with
no knowledge error below one, whatever the extractor: at true terminal values of a batch whose
constant position fails, the batched claim is true at every `α`. -/
theorem alphaDraw_noConst_one_le
    {relIn : Set ((TermStmt S F (P.m + P.κ) × ∀ i, O i) × Unit)}
    (hrel : ∀ t o, ((t, o), ()) ∈ relIn → ((t, o), ()) ∈ termRel P C z side) {e : ℝ≥0}
    (Sec : Typed.Security (Typed.sampleChallenge O F (fun _ ↦ true)
      (alphaNextNoConst (S := S) (n := P.m + P.κ))) relIn (rel (linFamily P C z side) 0)
      (Typed.drawErrors F e))
    (t : TermStmt S F (P.m + P.κ)) (o : ∀ i, O i) (hside : side t.1.1 o)
    (ha : t.2.2.1 = evalMle (zcA P C z o t.1.2.2) t.2.1)
    (hb : t.2.2.2.1 = evalMle (zcB P C z o t.1.2.2) t.2.1)
    (hc : t.2.2.2.2 = evalMle (zcC P z o t.1.2.2) t.2.1)
    (hconst : evalMle (constTable P.cpos (z o)) (highVec t.2.1) = 1) : 1 ≤ e :=
  Typed.sampleChallenge_one_le Sec t o
    (fun w hw ↦ by
      cases w
      have hrz := (hrel t o hw).2.1
      rw [restrictedZero_of_all _ _ (highVec t.2.1) fun k hk ↦ by
        rw [Partial.ofSuffix_all _ t.2.1 k hk]
        simp [highVec]] at hrz
      rw [hrz] at hconst
      exact zero_ne_one hconst)
    rfl fun α ↦ ⟨(), hside, by
      show t.2.2.1 + α * t.2.2.2.1 + α ^ 2 * t.2.2.2.2 =
        (linFamily P C z side).claim (((t, α), o), ()) 0 #v[]
      rw [linFamily_claim_zero, hconst, ← ha, ← hb, ← hc]
      ring⟩

/-! ## Ring switching -/

section Ring

variable [CharP F 2] (s' : ℕ) {K : Type} [CommRing K] (φ : K →+* F) (g : K)

/-- With no stage, typed. -/
def ringStartSecurity
    (hinj : ∀ δ : Fin (2 ^ P.s) → F,
      (∀ k < 2 ^ (s' + 1), frobPair Finset.univ (fun i ↦ φ (g ^ i.val)) δ k = 0) → ∀ i, δ i = 0) :
    Typed.Security (ringDraws P (S := S) (O := O) (W := Unit) 0) (outRel P z side)
      (ringRel P z side s' φ g 0) (Typed.drawsErrors F (overF F 1) 0) :=
  Typed.passThroughSecurity fun st o _ ↦
    ⟨fun h ↦ ⟨h.1, fun i ↦ by
      have herr := hinj _ (fun k hk ↦ h.2 k (by simpa using hk)) i
      simp only [ringStages, List.ofFn_zero, frobMap, sliceError, sub_eq_zero] at herr
      exact herr⟩,
    fun h ↦ ⟨h.1, fun k _ ↦ by
      have herr : ∀ i, sliceError P z o st i = 0 := fun i ↦ by
        rw [sliceError, h.2 i, sub_self]
      simp only [ringStages, List.ofFn_zero, frobMap, frobPair, herr]
      simp⟩⟩

omit [DecidableEq F] [SampleableType F] [Finite F] [∀ i, OracleInterface (O i)] [CharP F 2] in
/-- Before the last stage the `π`s run below `2 · 2 ^ (s' - p)`. -/
private theorem two_pow_succ_sub {p : ℕ} (hp : p ≤ s') : 2 ^ (s' + 1 - p) = 2 * 2 ^ (s' - p) := by
  rw [show s' + 1 - p = (s' - p) + 1 by omega, pow_succ, mul_comm]

omit [∀ i, OracleInterface (O i)] [SampleableType F] in
/-- The count behind `ringDrawSecurity`. -/
theorem ringDraw_card (p : ℕ) (hp : p ≤ s') (st : RingStmt S F (P.m + P.κ) P.s p)
    (o : ∀ i, O i) (hin : ((st, o), ()) ∉ ringRel P z side s' φ g p) :
    Nat.card {x : F // (((st.1, st.2.push x), o), ()) ∈ ringRel P z side s' φ g (p + 1)} ≤ 1 := by
  have := Fintype.ofFinite F
  classical
  by_cases hside : side st.1.1 o
  · have hne : ∃ k < 2 * 2 ^ (s' - p), frobPair Finset.univ
        (fun i : Fin (2 ^ P.s) ↦ φ (g ^ i.val))
        (fun i ↦ frobMap (ringStages s' st.2) (sliceError P z o st.1 i)) k ≠ 0 := by
      by_contra hall
      refine hin ⟨hside, fun k hk ↦ ?_⟩
      by_contra hk0
      exact hall ⟨k, two_pow_succ_sub s' hp ▸ hk, hk0⟩
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    refine (Finset.card_le_card fun x hx ↦ ?_).trans
      (card_stage_zero_le_one Finset.univ _ _ (2 ^ (s' - p)) hne)
    rw [Finset.mem_filter] at hx ⊢
    refine ⟨Finset.mem_univ _, fun k hk ↦ ?_⟩
    have := hx.2.2 k (by rwa [show s' + 1 - (p + 1) = s' - p by omega])
    simpa only [frobMap_ringStages_push] using this
  · rw [natCard_subtype_eq_zero fun x hx ↦ hside hx.1]
    exact zero_le_one

/-- One coefficient, typed. -/
def ringDrawSecurity (p : ℕ) (hp : p ≤ s') :
    Typed.Security (ringDraw P (S := S) (O := O) (W := Unit) p) (ringRel P z side s' φ g p)
      (ringRel P z side s' φ g (p + 1)) (Typed.drawErrors F (overF F 1)) :=
  Typed.sampleChallengeSecurity _ fun st o _ ↦
    Typed.card_badChallenge_le_of_unit _ st o (ringDraw_card P z side s' φ g p hp st o)

/-- The first `p` coefficients, typed. -/
def ringDrawsSecurity
    (hinj : ∀ δ : Fin (2 ^ P.s) → F,
      (∀ k < 2 ^ (s' + 1), frobPair Finset.univ (fun i ↦ φ (g ^ i.val)) δ k = 0) → ∀ i, δ i = 0) :
    (p : ℕ) → p ≤ s' →
      Typed.Security (ringDraws P (S := S) (O := O) (W := Unit) p) (outRel P z side)
        (ringRel P z side s' φ g p) (Typed.drawsErrors F (overF F 1) p)
  | 0, _ => ringStartSecurity P z side s' φ g hinj
  | p + 1, hp =>
    (ringDrawsSecurity hinj p (by omega)).append (ringDrawSecurity P z side s' φ g p (by omega))

variable {μ : ℕ} (lift : Vector F (P.m + P.κ) → Vector F μ)
  (col : (∀ i, O i) → CMlPolynomialEval K (P.m + P.κ))
  (stack : (∀ i, O i) → CMlPolynomialEval K μ)

omit [∀ i, OracleInterface (O i)] [SampleableType F] in
/-- The count behind `ringFinalSecurity`. -/
theorem ringFinal_card {StmtOut : Type} (finish : S → Weight F μ → F → StmtOut)
    (relOut : Set ((StmtOut × ∀ i, O i) × Unit))
    (hOut : ∀ sIn o (Wt : Weight F μ) T, ((finish sIn Wt T, o), ()) ∈ relOut →
      side sIn o ∧ Wt.pair φ (stack o) = T)
    (hcell : ∀ o (u : Fin (2 ^ (P.m + P.κ))),
      φ (col o)[u] = ∑ i : Fin (2 ^ P.s), φ (g ^ i.val) * (z o i)[u])
    (hbool : ∀ o i (u : Fin (2 ^ (P.m + P.κ))), (z o i)[u] = 0 ∨ (z o i)[u] = 1)
    (hread : ∀ o p, eval₂Mle (col o) φ p = eval₂Mle (stack o) φ (lift p))
    (st : RingStmt S F (P.m + P.κ) P.s s') (o : ∀ i, O i)
    (hin : ((st, o), ()) ∉ ringRel P z side s' φ g s') :
    Nat.card {x : F // ((finish st.1.1 (ringWeight P s' lift st.1.2.1 (st.2.push x))
      (ringTarget P s' φ g st.1.2.2 (st.2.push x)), o), ()) ∈ relOut} ≤ 1 := by
  have := Fintype.ofFinite F
  classical
  by_cases hside : side st.1.1 o
  · have hne : ∃ k < 2 * 1, frobPair Finset.univ (fun i : Fin (2 ^ P.s) ↦ φ (g ^ i.val))
        (fun i ↦ frobMap (ringStages s' st.2) (sliceError P z o st.1 i)) k ≠ 0 := by
      by_contra hall
      refine hin ⟨hside, fun k hk ↦ ?_⟩
      by_contra hk0
      exact hall ⟨k, by simpa using hk, hk0⟩
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    refine (Finset.card_le_card fun x hx ↦ ?_).trans
      (card_stage_zero_le_one Finset.univ _ _ 1 hne)
    rw [Finset.mem_filter] at hx ⊢
    refine ⟨Finset.mem_univ _, fun k hk ↦ ?_⟩
    obtain rfl : k = 0 := by omega
    have hpair := (hOut _ _ _ _ hx.2).2
    rw [pair_ringWeight P z s' φ g lift col stack hcell hbool hread, ringTarget] at hpair
    have hΦ : ∀ a, frobMap (ringStages s' (st.2.push x)) a =
        frobMap (ringStages s' st.2) a + x * frobMap (ringStages s' st.2) a ^ 2 ^ 1 :=
      fun a ↦ by rw [frobMap_ringStages_push, Nat.sub_self, pow_zero]
    have key : ∀ i : Fin (2 ^ P.s),
        (frobMap (ringStages s' st.2) (sliceError P z o st.1 i) +
          x * frobMap (ringStages s' st.2) (sliceError P z o st.1 i) ^ 2 ^ 1) ^ 2 ^ 0 =
        frobMap (ringStages s' (st.2.push x)) st.1.2.2[i] -
          frobMap (ringStages s' (st.2.push x)) (evalMle (z o i) st.1.2.1) := fun i ↦ by
      rw [pow_zero, pow_one, ← hΦ, sliceError]
      exact map_sub (frobMapHom (ringStages s' (st.2.push x))) _ _
    rw [frobPair]
    simp only [key, mul_sub, Finset.sum_sub_distrib]
    rw [← hpair, sub_self]
  · rw [natCard_subtype_eq_zero fun x hx ↦ hside (hOut _ _ _ _ hx).1]
    exact zero_le_one

/-- The last coefficient, typed. -/
def ringFinalSecurity {StmtOut : Type} (finish : S → Weight F μ → F → StmtOut)
    (relOut : Set ((StmtOut × ∀ i, O i) × Unit))
    (hOut : ∀ sIn o (Wt : Weight F μ) T, ((finish sIn Wt T, o), ()) ∈ relOut →
      side sIn o ∧ Wt.pair φ (stack o) = T)
    (hcell : ∀ o (u : Fin (2 ^ (P.m + P.κ))),
      φ (col o)[u] = ∑ i : Fin (2 ^ P.s), φ (g ^ i.val) * (z o i)[u])
    (hbool : ∀ o i (u : Fin (2 ^ (P.m + P.κ))), (z o i)[u] = 0 ∨ (z o i)[u] = 1)
    (hread : ∀ o p, eval₂Mle (col o) φ p = eval₂Mle (stack o) φ (lift p)) :
    Typed.Security (ringFinal P s' φ g lift finish (O := O) (W := Unit))
      (ringRel P z side s' φ g s') relOut (Typed.drawErrors F (overF F 1)) :=
  Typed.sampleChallengeSecurity _ fun st o _ ↦ Typed.card_badChallenge_le_of_unit _ st o
    (ringFinal_card P z side s' φ g lift col stack finish relOut hOut hcell hbool hread st o)

/-- Ring switching, typed. -/
def ringSwitchSecurity {StmtOut : Type} (finish : S → Weight F μ → F → StmtOut)
    (relOut : Set ((StmtOut × ∀ i, O i) × Unit))
    (hinj : ∀ δ : Fin (2 ^ P.s) → F,
      (∀ k < 2 ^ (s' + 1), frobPair Finset.univ (fun i ↦ φ (g ^ i.val)) δ k = 0) → ∀ i, δ i = 0)
    (hOut : ∀ sIn o (Wt : Weight F μ) T, ((finish sIn Wt T, o), ()) ∈ relOut →
      side sIn o ∧ Wt.pair φ (stack o) = T)
    (hcell : ∀ o (u : Fin (2 ^ (P.m + P.κ))),
      φ (col o)[u] = ∑ i : Fin (2 ^ P.s), φ (g ^ i.val) * (z o i)[u])
    (hbool : ∀ o i (u : Fin (2 ^ (P.m + P.κ))), (z o i)[u] = 0 ∨ (z o i)[u] = 1)
    (hread : ∀ o p, eval₂Mle (col o) φ p = eval₂Mle (stack o) φ (lift p)) :
    Typed.Security (ringSwitch P s' φ g lift finish (O := O) (W := Unit)) (outRel P z side)
      relOut (Typed.drawsErrors F (overF F 1) (s' + 1)) :=
  (ringDrawsSecurity P z side s' φ g hinj s' le_rfl).append
    (ringFinalSecurity P z side s' φ g lift col stack finish relOut hOut hcell hbool hread)

/-! ## The argument -/

/-- The typed errors of the Flock argument, challenge by challenge, as `flockError`. -/
noncomputable abbrev flockErrorsT :
    Typed.Errors (flockSlot F P.s P.m P.κ P.nRand s').tree (flockSlot F P.s P.m P.κ P.nRand s').roles :=
  Typed.Errors.append _ _ (Typed.Errors.append _ _ (Typed.Errors.append _ _ (Typed.Errors.append _ _
    (Typed.Errors.append _ _ (Typed.Errors.append _ _ (Typed.Errors.append _ _
    (Typed.Errors.append _ _ (Typed.Errors.append _ _
    (Typed.drawsErrors F (overF F 1) P.nRand) (Typed.sayErrors _))
    (Typed.drawErrors F (overF F (2 ^ P.s + 2 ^ P.s - 1)))) (Typed.roundsErrors F 2 (overF F 2) P.m))
    (Typed.roundsErrors F 2 (overF F 2) P.κ)) (Typed.sayErrors _)) (Typed.drawErrors F (overF F 3)))
    (Typed.roundsErrors F 2 (overF F 2) P.m)) (Typed.sayErrors _))
    (Typed.drawsErrors F (overF F 1) (s' + 1))

/-- **Knowledge soundness of the Flock argument on the typed framework**, at `flockErrorsT`. -/
def flockSecurity {StmtOut : Type} (finish : S → Weight F μ → F → StmtOut)
    (hnodes : Function.Injective fun j : Fin (2 ^ P.s + 2 ^ P.s) ↦ P.nodes.pts[j])
    (hfixed : ∀ c : Fin (2 ^ P.nFix) → F, (∀ v, c v = 0 ∨ c v = 1) →
      ∑ v, (lagrangeBasis P.fixed)[v] * c v = 0 → ∀ v, c v = 0)
    (hinj : ∀ δ : Fin (2 ^ P.s) → F,
      (∀ k < 2 ^ (s' + 1), frobPair Finset.univ (fun i ↦ φ (g ^ i.val)) δ k = 0) → ∀ i, δ i = 0)
    (relIn : Set ((S × ∀ i, O i) × Unit)) (relOut : Set ((StmtOut × ∀ i, O i) × Unit))
    (hIn : ∀ s o, ((s, o), ()) ∈ relIn ↔ side s o ∧ BatchHolds C P.cpos (z o))
    (hOut : ∀ sIn o (Wt : Weight F μ) T, ((finish sIn Wt T, o), ()) ∈ relOut →
      side sIn o ∧ Wt.pair φ (stack o) = T)
    (hcell : ∀ o (u : Fin (2 ^ (P.m + P.κ))),
      φ (col o)[u] = ∑ i : Fin (2 ^ P.s), φ (g ^ i.val) * (z o i)[u])
    (hbool : ∀ o i (u : Fin (2 ^ (P.m + P.κ))), (z o i)[u] = 0 ∨ (z o i)[u] = 1)
    (hread : ∀ o p, eval₂Mle (col o) φ p = eval₂Mle (stack o) φ (lift p)) :
    Typed.Security (flock P C z side s' φ g lift finish (W := Unit)) relIn relOut
      (flockErrorsT P s') :=
  (pointDrawsSecurity P C z side relIn
      (fun s o h ↦ by
        obtain ⟨hside, hholds⟩ := (hIn s o).mp h
        obtain ⟨herr, hconst⟩ := (batchHolds_iff C P.cpos (z o)).mp hholds
        refine ⟨hside, fun i b ↦ ?_, hconst⟩
        rw [evalMle_eq_sum]
        exact Finset.sum_eq_zero fun u _ ↦ by rw [herr i u, zero_mul])
      (fun s o h ↦ (hIn s o).mpr ⟨h.1, (batchHolds_iff C P.cpos (z o)).mpr ⟨fun i u ↦
        eq_zero_of_restrictedZero_fixed P hfixed _ (isBool_errTable C (hbool o) i) (h.2.1 i) u,
        h.2.2⟩⟩)
      P.nRand).append (skipMsgSecurity P C z side) |>.append
    (skipDrawSecurity P C z side hnodes) |>.append (zcRoundsLowSecurity P C z side) |>.append
    (zcRoundsHighSecurity P C z side) |>.append (zcEndSecurity P C z side) |>.append
    (alphaDrawSecurity P C z side) |>.append (linRoundsSecurity P C z side) |>.append
    (linEndSecurity P C z side) |>.append
    (ringSwitchSecurity P z side s' φ g lift col stack finish relOut hinj hOut hcell hbool hread)

end Ring

end

end Flock

end LeanVM.Protocol
