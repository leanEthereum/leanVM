import Whir.InteractiveSoundness
import Whir.ExecutableOOD
import Whir.RingMapBatching

namespace Whir.CommitmentAnchor
open Concrete Protocol CausalGame ParameterBounds
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
noncomputable local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Identity is the entire immutable record, not its Merkle root alone. The
anchor point is sampled once after this root/shape and before its value and any
opening statements. Every session reuses the same point and value. This ideal
record does not claim that the deployed keyed transcript realizes that game. -/
structure Commitment (p : Profile) where
  lanes : Nat
  root : BaseOracle
  point : Fin (config p).logN → E
  value : E
  occupied : 0 < lanes ∧ lanes ≤ 2^(config p).folds[0]!

/-- The anchor's public linear weight has exactly the occupied-lane support.
Missing zero-tail coefficients are not treated as alternative witnesses. -/
def weight (c : Config) (lanes : Nat) (point : Array E) : Array E :=
  tab (2^c.logN) fun i =>
    if i < lanes*2^(c.logN-c.folds[0]!) then (eqTable point)[i]! else E.zero

def value (c : Config) (lanes : Nat) (w : Witness c lanes) (point : Array E) : E :=
  Concrete.mle (paddedWitness c lanes w) point

/-- Zero-tail truncation preserves the claimed MLE on an actual supported
witness. This is the linear claim every later session must additionally check;
using a full-cube weight would violate the existing occupied-lane guards. -/
theorem weight_value (c : Config) (lanes : Nat) (w : Witness c lanes)
    (point : Array E) (point_size : point.size = c.logN) :
    dot (paddedWitness c lanes w) (weight c lanes point) = value c lanes w point := by
  classical
  simp only [value, Concrete.mle, ArrayAlgebra.dot_eq_sum, weight,
    ArrayLayout.size_tab, TerminalRefinement.size_eqTable, point_size,
    paddedWitness, ArrayLayout.size_tab, min_self]
  apply Finset.sum_congr rfl
  intro i hi
  have hif : i < 2^c.logN := Finset.mem_range.mp hi
  simp only [ArrayLayout.getElem!_tab _ _ _ hif]
  by_cases occupied : i < lanes*2^(c.logN-c.folds[0]!)
  · simp only [occupied, ite_eq_left]
  · have outside : ¬ i < (Array.ofFn w).size := by
      simpa only [Array.size_ofFn, Fintype.card_fin] using occupied
    simp [occupied]

def claim (p : Profile) (commitment : Commitment p) : Claim :=
  ⟨weight (config p) commitment.lanes (Array.ofFn commitment.point), commitment.value⟩

def claims (p : Profile) (commitment : Commitment p) (opening : Array Claim) : Array Claim :=
  opening.push (claim p commitment)

def input (p : Profile) (commitment : Commitment p) (opening : Array Claim) : Public :=
  ExecutionShapes.Input p commitment.lanes commitment.root (claims p commitment opening)

/-- Candidate list is fixed solely by the original root and shape, before the
anchor point or malicious choice of its advertised value. -/
noncomputable def selected (p : Profile) (lanes : Nat) (root : BaseOracle)
    (point : Fin (config p).logN → E) (v : E) : Finset (Witness (config p) lanes) := by
  classical
  exact (InitialCandidates.witnesses (config p) lanes root).filter
    (fun w => value (config p) lanes w (Array.ofFn point) = v)

noncomputable def Ambiguous (p : Profile) (lanes : Nat) (root : BaseOracle)
    (point : Fin (config p).logN → E) : Prop :=
  ∃ a ∈ InitialCandidates.witnesses (config p) lanes root,
    ∃ b ∈ InitialCandidates.witnesses (config p) lanes root, a ≠ b ∧
      value (config p) lanes a (Array.ofFn point) =
        value (config p) lanes b (Array.ofFn point)

/-- Supported padding is injective. Only literal occupied base words are
witnesses; arbitrary differences in the mandated zero tail are excluded. -/
theorem padded_injective (c : Config) (lanes : Nat)
    (fits : lanes*2^(c.logN-c.folds[0]!) ≤ 2^c.logN) :
    Function.Injective (paddedWitness c lanes) := by
  intro a b same
  funext i
  apply FieldModel.ofK_injective
  have hi : i.val < 2^c.logN := lt_of_lt_of_le i.isLt fits
  have he := congrArg (fun xs : Array E => xs[i.val]!) same
  simpa [paddedWitness, tab, getElem!_pos, i.isLt, hi] using he

/-- Outside the point-only ambiguity event, EVERY advertised anchor value,
including one chosen maliciously after seeing the point, selects at most one
root-fixed candidate. This quantifier is simultaneous over all later sessions. -/
theorem selected_unique (p : Profile) (lanes : Nat) (root : BaseOracle)
    (point : Fin (config p).logN → E) (clean : ¬ Ambiguous p lanes root point)
    (v : E) : (selected p lanes root point v).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro a ha b hb
  obtain ⟨ha,hav⟩ := Finset.mem_filter.mp ha
  obtain ⟨hb,hbv⟩ := Finset.mem_filter.mp hb
  by_contra different
  exact clean ⟨a,ha,b,hb,different,hav.trans hbv.symm⟩

/-- Cross-session uniqueness for a single immutable anchored commitment. Claims
and strategies can differ between sessions; satisfying the same anchor forces
the same supported root candidate. No honest-commitment premise is present. -/
theorem cross_session (p : Profile) (commitment : Commitment p)
    (clean : ¬ Ambiguous p commitment.lanes commitment.root commitment.point)
    (a b : Witness (config p) commitment.lanes)
    (ha : a ∈ selected p commitment.lanes commitment.root commitment.point commitment.value)
    (hb : b ∈ selected p commitment.lanes commitment.root commitment.point commitment.value) : a = b :=
  Finset.card_le_one.mp (selected_unique p _ _ _ clean _) a ha b hb

/-- A binding selector fixed before any opening statements or session strategy.
This uses classical choice for a mathematical binding definition, NOT an
algorithm or a claimed knowledge extractor. -/
noncomputable def boundWitness (p : Profile) (commitment : Commitment p) :
    Option (Witness (config p) commitment.lanes) :=
  if h : ∃ w, w ∈ selected p commitment.lanes commitment.root commitment.point commitment.value
  then some h.choose else none

theorem boundWitness_eq (p : Profile) (commitment : Commitment p)
    (clean : ¬ Ambiguous p commitment.lanes commitment.root commitment.point)
    (w : Witness (config p) commitment.lanes)
    (hw : w ∈ selected p commitment.lanes commitment.root commitment.point commitment.value) :
    boundWitness p commitment = some w := by
  have hasCandidate : ∃ w, w ∈ selected p commitment.lanes commitment.root commitment.point commitment.value := ⟨w,hw⟩
  rw [boundWitness, dite_eq_left hasCandidate]
  exact congrArg some (cross_session p commitment clean _ _ hasCandidate.choose_spec hw)

/-- Consumer-visible failure of the actual causal verifier: acceptance with no explanation by the one immutable commitment's mathematical selector. This predicate does not assert knowledge extraction. -/
def openingFailure (p : Profile) (commitment : Commitment p)
    (opening : Array Claim) (strategy : Strategy) (tape : Tape (config p)) : Prop :=
  experiment (ExecutionShapes.Input p commitment.lanes commitment.root (claims p commitment opening)) strategy tape = true ∧
    ¬ ∃ w, boundWitness p commitment = some w ∧
      ∀ c ∈ opening.toList,
        dot (paddedWitness (config p) commitment.lanes w) c.weight = c.value

attribute [local irreducible] openingFailure

/-- Every later actual causal verifier session additionally checks the same
immutable anchor. Off the anchor collision event, accepted claims contradicting
the one commitment-fixed witness have only the existing opening error, including
the additional anchor in the initial random batch. -/
theorem unique_opening_probability (p : Profile) (commitment : Commitment p)
    (clean : ¬ Ambiguous p commitment.lanes commitment.root commitment.point)
    (opening : Array Claim) (strategy : Strategy) :
    Soundness.uniformProb (Finset.univ.filter fun tape : Tape (config p) =>
      openingFailure p commitment opening strategy tape) ≤
      GroupedChallenges.interactiveError (config p) (estimates (config p)) (opening.size+1) := by
  classical
  have bound := InteractiveSoundness.opening_probability p commitment.lanes commitment.root
    (claims p commitment opening) strategy
  have subset : (Finset.univ.filter fun tape : Tape (config p) =>
      openingFailure p commitment opening strategy tape) ⊆
    Finset.univ.filter fun tape : Tape (config p) =>
      experiment (ExecutionShapes.Input p commitment.lanes commitment.root (claims p commitment opening)) strategy tape = true ∧
      ¬ ∃ w ∈ InitialCandidates.witnesses (config p) commitment.lanes commitment.root,
        ∀ c ∈ (claims p commitment opening).toList,
          dot (paddedWitness (config p) commitment.lanes w) c.weight = c.value := by
    intro tape
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, openingFailure]
    rintro ⟨accepted,contradicts⟩
    constructor
    · exact accepted
    rintro ⟨w,hw,allClaims⟩
    have anchor := allClaims (claim p commitment)
      (by simp [claims])
    have selected : w ∈ selected p commitment.lanes commitment.root commitment.point commitment.value := by
      apply Finset.mem_filter.mpr
      refine ⟨hw,?_⟩
      simpa only [claim, weight_value, Array.size_ofFn, Fintype.card_fin] using anchor
    apply contradicts
    exact ⟨w,boundWitness_eq p commitment clean w selected,fun c hc =>
      allClaims c (by simp only [claims, Array.toList_push, List.mem_append, List.mem_singleton]; exact Or.inl hc)⟩
  apply le_trans ?_ (by simpa only [claims, Array.size_push] using bound)
  unfold Soundness.uniformProb
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast (Finset.card_le_card subset)

set_option maxRecDepth 100000 in
private theorem production_size : ∀ p : Profile,
    (config p).logN ≤ 28 ∧
    2^(config p).folds[0]! * 2^((config p).logN-(config p).folds[0]!) =
      2^(config p).logN := by
  decide +kernel

/-- Exact anchor ambiguity term for the actual commitment-fixed supported list.
The point is genuinely independent uniform E randomness after the root/shape;
this theorem is not a Fiat--Shamir or whole-PCS security bound. -/
theorem ambiguity_probability (p : Profile) (lanes : Nat) (root : BaseOracle)
    (occupied : lanes ≤ 2^(config p).folds[0]!) :
    Soundness.uniformProb (Finset.univ.filter fun point : Fin (config p).logN → E =>
      Ambiguous p lanes root point) ≤
      ((InitialCandidates.witnesses (config p) lanes root).card.choose 2 : ℚ) *
        ((config p).logN : ℚ) / 2^192 := by
  classical
  let candidates := InitialCandidates.witnesses (config p) lanes root
  let arrays := candidates.image (paddedWitness (config p) lanes)
  have fits : lanes*2^((config p).logN-(config p).folds[0]!) ≤ 2^(config p).logN := by
    calc
      _ ≤ 2^(config p).folds[0]! * 2^((config p).logN-(config p).folds[0]!) :=
        Nat.mul_le_mul_right _ occupied
      _ = _ := (production_size p).2
  have inj := padded_injective (config p) lanes fits
  have sz : ∀ a ∈ arrays, a.size = 2^(config p).logN := by
    intro a ha
    obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp ha
    simp [paddedWitness, tab]
  have bound := ExecutableOOD.candidate_separation arrays sz
  have event : ∀ point,
      Ambiguous p lanes root point ↔
      ∃ a ∈ arrays, ∃ b ∈ arrays, a ≠ b ∧
        Concrete.mle a (Array.ofFn point) = Concrete.mle b (Array.ofFn point) := by
    intro point
    constructor
    · rintro ⟨a,ha,b,hb,different,same⟩
      exact ⟨_,Finset.mem_image.mpr ⟨a,ha,rfl⟩,
        _,Finset.mem_image.mpr ⟨b,hb,rfl⟩,fun e => different (inj e),same⟩
    · rintro ⟨a,ha,b,hb,different,same⟩
      obtain ⟨wa,hwa,rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨wb,hwb,rfl⟩ := Finset.mem_image.mp hb
      exact ⟨wa,hwa,wb,hwb,fun e => different (congrArg _ e),same⟩
  simp_rw [← event] at bound
  rw [Finset.card_image_of_injective _ inj, FieldModel.card_E] at bound
  simpa only [candidates, mul_div_assoc, Nat.cast_pow, Nat.cast_ofNat] using bound

/-- One anchor costs at most 2^-124 of list-selection ambiguity at the proved
2^32 list cap and dimension at most 28. Opening, adaptation, Merkle, FS and
concrete cryptographic terms are separate and must still be composed. -/
theorem ambiguity_probability_numeric (p : Profile) (lanes : Nat) (root : BaseOracle)
    (occupied : lanes ≤ 2^(config p).folds[0]!) :
    Soundness.uniformProb (Finset.univ.filter fun point : Fin (config p).logN → E =>
      Ambiguous p lanes root point) ≤ (1 : ℚ)/2^124 := by
  classical
  apply (ambiguity_probability p lanes root occupied).trans
  have cards := InitialCandidates.production_witnesses_card p lanes root
  have dims := (production_size p).1
  have num : ((InitialCandidates.witnesses (config p) lanes root).card.choose 2 : ℚ) *
      ((config p).logN : ℚ) ≤ ((2^32 : Nat).choose 2 : ℚ)*28 := by
    apply mul_le_mul
    · exact_mod_cast Nat.choose_le_choose 2 cards
    · exact_mod_cast dims
    · exact Nat.cast_nonneg _
    · exact Nat.cast_nonneg _
  apply (div_le_div_of_nonneg_right num (by positivity)).trans
  norm_num [Nat.choose_two_right]

/-- The root, supported lane count and profile are fixed before sampling this point. Only the advertised value depends on the point; the record is reused unchanged in every opening session. -/
def sampledCommitment (p : Profile) (lanes : Nat) (root : BaseOracle)
    (occupied : 0 < lanes ∧ lanes ≤ 2^(config p).folds[0]!)
    (advertised : (Fin (config p).logN → E) → E)
    (point : Fin (config p).logN → E) : Commitment p :=
  ⟨lanes, root, point, advertised point, occupied⟩

private theorem ledger_mono (p : Profile) {a b : Nat} (h : a ≤ b) :
    GroupedChallenges.interactiveError (config p) (estimates (config p)) a ≤
      GroupedChallenges.interactiveError (config p) (estimates (config p)) b := by
  unfold GroupedChallenges.interactiveError
  exact add_le_add (add_le_add (initialBatch_mono _ h) le_rfl) le_rfl

/-- Finite product averaging charges the exceptional outer event once, while retaining the actual nonconstant inner ledger. Events may depend arbitrarily on both coordinates. -/
private theorem exceptional_product_average {A B : Type*}
    [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (bad : A → Prop) (event : A × B → Prop) (ledger : A → ℚ)
    (nonnegative : ∀ x, 0 ≤ ledger x)
    (good : ∀ x, ¬ bad x →
      Soundness.uniformProb (Finset.univ.filter fun y : B => event (x,y)) ≤ ledger x) :
    Soundness.uniformProb (Finset.univ.filter event) ≤
      Soundness.uniformProb (Finset.univ.filter bad) +
        (∑ x : A, ledger x) / Fintype.card A := by
  classical
  have fiber (x : A) :
      Soundness.uniformProb (Finset.univ.filter fun y : B => event (x,y)) ≤
        (if bad x then 1 else 0) + ledger x := by
    by_cases hx : bad x
    · have one : Soundness.uniformProb
          (Finset.univ.filter fun y : B => event (x,y)) ≤ 1 := by
        unfold Soundness.uniformProb
        apply (div_le_one (by positivity)).mpr
        exact_mod_cast Finset.card_le_univ _
      simpa [hx] using one.trans (le_add_of_nonneg_right (nonnegative x))
    · simpa [hx] using good x hx
  rw [RingMapBatching.uniform_product]
  calc
    _ ≤ (∑ x : A, ((if bad x then 1 else 0 : ℚ) + ledger x)) / Fintype.card A :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum fun x _ => fiber x) (by positivity)
    _ = _ := by
      simp only [Finset.sum_add_distrib, Soundness.uniformProb, Finset.card_filter,
        Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      rw [add_div]

/-- Actual joint ideal game: one uniform anchor point followed by an independent uniform session tape. Every malicious value, opening and causal strategy is allowed to depend on the point. The candidate list remains fixed by the original root and supported shape. -/
theorem joint_opening_probability (p : Profile) (lanes : Nat) (root : BaseOracle)
    (occupied : 0 < lanes ∧ lanes ≤ 2^(config p).folds[0]!)
    (advertised : (Fin (config p).logN → E) → E)
    (opening : (Fin (config p).logN → E) → Array Claim)
    (strategy : (Fin (config p).logN → E) → Strategy) :
    Soundness.uniformProb (Finset.univ.filter
      fun sample : (Fin (config p).logN → E) × Tape (config p) =>
        openingFailure p (sampledCommitment p lanes root occupied advertised sample.1)
          (opening sample.1) (strategy sample.1) sample.2) ≤
      ((InitialCandidates.witnesses (config p) lanes root).card.choose 2 : ℚ) *
        ((config p).logN : ℚ) / 2^192 +
      (∑ point : Fin (config p).logN → E,
        GroupedChallenges.interactiveError (config p) (estimates (config p))
          ((opening point).size+1)) / Fintype.card (Fin (config p).logN → E) := by
  classical
  let ledger := fun point : Fin (config p).logN → E =>
    GroupedChallenges.interactiveError (config p) (estimates (config p))
      ((opening point).size+1)
  calc
    _ ≤ Soundness.uniformProb (Finset.univ.filter (Ambiguous p lanes root)) +
        (∑ point : Fin (config p).logN → E, ledger point) /
          Fintype.card (Fin (config p).logN → E) := by
      apply exceptional_product_average (Ambiguous p lanes root) _ ledger
        (fun point => InteractiveSoundness.error_nonneg _ _)
      intro point clean
      exact unique_opening_probability p
        (sampledCommitment p lanes root occupied advertised point) clean
        (opening point) (strategy point)
    _ ≤ _ := by
      dsimp only [ledger]
      exact add_le_add (ambiguity_probability p lanes root occupied.2) le_rfl

/-- A uniform cap on later opening statements gives the actual opening ledger at maxClaimSize plus the single immutable anchor claim. The pair-collision charge is not multiplied by the number of sessions or openings. -/
theorem joint_opening_probability_capped (p : Profile) (lanes : Nat) (root : BaseOracle)
    (occupied : 0 < lanes ∧ lanes ≤ 2^(config p).folds[0]!)
    (advertised : (Fin (config p).logN → E) → E)
    (opening : (Fin (config p).logN → E) → Array Claim)
    (strategy : (Fin (config p).logN → E) → Strategy)
    (maxClaimSize : Nat) (opening_cap : ∀ point, (opening point).size ≤ maxClaimSize) :
    Soundness.uniformProb (Finset.univ.filter
      fun sample : (Fin (config p).logN → E) × Tape (config p) =>
        openingFailure p (sampledCommitment p lanes root occupied advertised sample.1)
          (opening sample.1) (strategy sample.1) sample.2) ≤
      ((InitialCandidates.witnesses (config p) lanes root).card.choose 2 : ℚ) *
        ((config p).logN : ℚ) / 2^192 +
      GroupedChallenges.interactiveError (config p) (estimates (config p)) (maxClaimSize+1) := by
  classical
  apply RingMapBatching.conditional_error (Ambiguous p lanes root) _ _ _
    (InteractiveSoundness.error_nonneg _ _) (ambiguity_probability p lanes root occupied.2)
  intro point clean
  exact (unique_opening_probability p
    (sampledCommitment p lanes root occupied advertised point) clean
    (opening point) (strategy point)).trans
    (ledger_mono p (Nat.add_le_add_right (opening_cap point) 1))

/-- The supported production profiles have dimension at most 28 and a proved root-fixed list cap of 2^32. With the anchor included in the 2^64 claim cap, the composed ideal-interactive bound is exactly stated as 2^-124 plus 2^-73, not rounded to a whole-system 128-bit claim. -/
theorem joint_opening_probability_numeric (p : Profile) (lanes : Nat) (root : BaseOracle)
    (occupied : 0 < lanes ∧ lanes ≤ 2^(config p).folds[0]!)
    (advertised : (Fin (config p).logN → E) → E)
    (opening : (Fin (config p).logN → E) → Array Claim)
    (strategy : (Fin (config p).logN → E) → Strategy)
    (opening_cap : ∀ point, (opening point).size+1 ≤ 2^64) :
    Soundness.uniformProb (Finset.univ.filter
      fun sample : (Fin (config p).logN → E) × Tape (config p) =>
        openingFailure p (sampledCommitment p lanes root occupied advertised sample.1)
          (opening sample.1) (strategy sample.1) sample.2) ≤
      (1 : ℚ)/2^124 + (1 : ℚ)/2^73 := by
  classical
  apply RingMapBatching.conditional_error (Ambiguous p lanes root) _ _ _
    (by positivity) (ambiguity_probability_numeric p lanes root occupied.2)
  intro point clean
  exact (unique_opening_probability p
    (sampledCommitment p lanes root occupied advertised point) clean
    (opening point) (strategy point)).trans
    (production_interactive p _ (opening_cap point))

/-- Two fresh independent session tapes share one point and one malicious advertised value. The second opening and strategy may depend on the entire first tape. Failure means either accepted session lacks an explanation by the same commitment-fixed selector. Finite fiber averaging charges the anchor collision once and both opening ledgers. -/
theorem joint_two_session_probability (p : Profile) (lanes : Nat) (root : BaseOracle)
    (occupied : 0 < lanes ∧ lanes ≤ 2^(config p).folds[0]!)
    (advertised : (Fin (config p).logN → E) → E)
    (opening₁ : (Fin (config p).logN → E) → Array Claim)
    (strategy₁ : (Fin (config p).logN → E) → Strategy)
    (opening₂ : (Fin (config p).logN → E) → Tape (config p) → Array Claim)
    (strategy₂ : (Fin (config p).logN → E) → Tape (config p) → Strategy)
    (maxClaimSize₁ maxClaimSize₂ : Nat)
    (cap₁ : ∀ point, (opening₁ point).size ≤ maxClaimSize₁)
    (cap₂ : ∀ point tape₁, (opening₂ point tape₁).size ≤ maxClaimSize₂) :
    Soundness.uniformProb (Finset.univ.filter
      fun sample : (Fin (config p).logN → E) × (Tape (config p) × Tape (config p)) =>
        openingFailure p (sampledCommitment p lanes root occupied advertised sample.1)
          (opening₁ sample.1) (strategy₁ sample.1) sample.2.1 ∨
        openingFailure p (sampledCommitment p lanes root occupied advertised sample.1)
          (opening₂ sample.1 sample.2.1) (strategy₂ sample.1 sample.2.1) sample.2.2) ≤
      ((InitialCandidates.witnesses (config p) lanes root).card.choose 2 : ℚ) *
        ((config p).logN : ℚ) / 2^192 +
      (GroupedChallenges.interactiveError (config p) (estimates (config p)) (maxClaimSize₁+1) +
        GroupedChallenges.interactiveError (config p) (estimates (config p)) (maxClaimSize₂+1)) := by
  classical
  apply RingMapBatching.conditional_error (Ambiguous p lanes root) _ _ _
    (add_nonneg (InteractiveSoundness.error_nonneg _ _) (InteractiveSoundness.error_nonneg _ _))
    (ambiguity_probability p lanes root occupied.2)
  intro point clean
  apply RingMapBatching.conditional_error
    (openingFailure p (sampledCommitment p lanes root occupied advertised point)
      (opening₁ point) (strategy₁ point)) _ _ _
    (InteractiveSoundness.error_nonneg _ _)
    ((unique_opening_probability p
      (sampledCommitment p lanes root occupied advertised point) clean
      (opening₁ point) (strategy₁ point)).trans
      (ledger_mono p (Nat.add_le_add_right (cap₁ point) 1)))
  intro tape₁ first_clean
  simp only [first_clean, false_or]
  exact (unique_opening_probability p
    (sampledCommitment p lanes root occupied advertised point) clean
    (opening₂ point tape₁) (strategy₂ point tape₁)).trans
    (ledger_mono p (Nat.add_le_add_right (cap₂ point tape₁) 1))

/-- Numeric two-session bound in the same ideal game, allowing adaptation to the first tape and retaining one anchor charge. No Fiat-Shamir or concrete keyed-transcript realization is asserted. -/
theorem joint_two_session_probability_numeric (p : Profile) (lanes : Nat) (root : BaseOracle)
    (occupied : 0 < lanes ∧ lanes ≤ 2^(config p).folds[0]!)
    (advertised : (Fin (config p).logN → E) → E)
    (opening₁ : (Fin (config p).logN → E) → Array Claim)
    (strategy₁ : (Fin (config p).logN → E) → Strategy)
    (opening₂ : (Fin (config p).logN → E) → Tape (config p) → Array Claim)
    (strategy₂ : (Fin (config p).logN → E) → Tape (config p) → Strategy)
    (cap₁ : ∀ point, (opening₁ point).size+1 ≤ 2^64)
    (cap₂ : ∀ point tape₁, (opening₂ point tape₁).size+1 ≤ 2^64) :
    Soundness.uniformProb (Finset.univ.filter
      fun sample : (Fin (config p).logN → E) × (Tape (config p) × Tape (config p)) =>
        openingFailure p (sampledCommitment p lanes root occupied advertised sample.1)
          (opening₁ sample.1) (strategy₁ sample.1) sample.2.1 ∨
        openingFailure p (sampledCommitment p lanes root occupied advertised sample.1)
          (opening₂ sample.1 sample.2.1) (strategy₂ sample.1 sample.2.1) sample.2.2) ≤
      (1 : ℚ)/2^124 + ((1 : ℚ)/2^73 + (1 : ℚ)/2^73) := by
  classical
  apply RingMapBatching.conditional_error (Ambiguous p lanes root) _ _ _
    (by positivity) (ambiguity_probability_numeric p lanes root occupied.2)
  intro point clean
  apply RingMapBatching.conditional_error
    (openingFailure p (sampledCommitment p lanes root occupied advertised point)
      (opening₁ point) (strategy₁ point)) _ _ _ (by positivity)
    ((unique_opening_probability p
      (sampledCommitment p lanes root occupied advertised point) clean
      (opening₁ point) (strategy₁ point)).trans
      (production_interactive p _ (cap₁ point)))
  intro tape₁ first_clean
  simp only [first_clean, false_or]
  exact (unique_opening_probability p
    (sampledCommitment p lanes root occupied advertised point) clean
    (opening₂ point tape₁) (strategy₂ point tape₁)).trans
    (production_interactive p _ (cap₂ point tape₁))

end Whir.CommitmentAnchor

#print axioms Whir.CommitmentAnchor.joint_opening_probability
#print axioms Whir.CommitmentAnchor.joint_opening_probability_capped
#print axioms Whir.CommitmentAnchor.joint_opening_probability_numeric
#print axioms Whir.CommitmentAnchor.joint_two_session_probability
#print axioms Whir.CommitmentAnchor.joint_two_session_probability_numeric
