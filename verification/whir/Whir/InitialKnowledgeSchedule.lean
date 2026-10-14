import Whir.SupportedCandidateClaims
import Whir.SupportedCandidateMCA
import Whir.CausalFolds

/-! SAME-target backward induction over the actual causal fold kernels. The
fresh-scalar guards concern incoming prefixes, never future acceptance. -/
namespace Whir.InitialKnowledgeSchedule
open Concrete Protocol CausalGame CausalExecution CausalProbability ExecutionShapes
open CandidateFolding SupportedCandidateExtraction ParameterBounds

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
attribute [local irreducible] ParameterBounds.config

noncomputable def paired (input : Public) (strategy : Strategy) (t : Tape input.config)
    (i : Fin input.config.folds.size) (j : Fin input.config.folds[i.val]!) :=
  OracleReplay.pairedOracle (i.val == 0) input.config.folds[i.val]!
    (levelAt input strategy t i).oracle (challenges input.config t).levels[i.val]!.folds
    j.val j.isLt (N := 2 ^ (remaining input.config i + input.config.rates[i.val]!))

noncomputable def RawMCA (input : Public) (strategy : Strategy)
    (i : Fin input.config.folds.size) (j : Fin input.config.folds[i.val]!)
    (t : Tape input.config) : Prop :=
  MutualAgreement.RowBad MutualAgreement.foldGenerator
    (LinearMap.range (concreteEncoder (remaining input.config i) input.config.rates[i.val]!))
    (threshold input.config i)
    ![fun lane => paired input strategy t i j (evenLane lane),
      fun lane => paired input strategy t i j (oddLane lane)]
    (challenges input.config t).levels[i.val]!.folds[j.val]!

noncomputable def ClaimEscape (input : Public) (strategy : Strategy)
    (i : Fin input.config.folds.size) (j : Fin input.config.folds[i.val]!)
    (t : Tape input.config) : Prop :=
  (challenges input.config t).levels[i.val]!.folds[j.val]! ∈
    candidateRoundEscape (foldCandidates input strategy t i j)
      (foldAt input strategy t i j).state (block input.config i)

/-- Chronological coefficient folds, with the verifier's actual physical block.
The compact prover messages are not coefficient tables and do not occur here. -/
def foldFrom (input : Public) (t : Tape input.config) (i start count : Nat)
    (a : Array E) : Array E :=
  (List.range count).foldl (fun a j => foldValues a (block input.config i)
    (challenges input.config t).levels[i]!.folds[start+j]!) a

@[simp] theorem foldFrom_zero (input : Public) (t : Tape input.config) (i start : Nat)
    (a : Array E) : foldFrom input t i start 0 a = a := rfl

theorem foldFrom_succ (input : Public) (t : Tape input.config) (i start count : Nat)
    (a : Array E) : foldFrom input t i start (count+1) a =
      foldFrom input t i (start+1) count
        (foldValues a (block input.config i)
          (challenges input.config t).levels[i]!.folds[start]!) := by
  unfold foldFrom
  rw [List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
  congr 1
  funext a j
  congr 2
  omega

/-- The SAME chosen final candidate inherits every actual incoming claim. This
is an actual trajectory theorem; no abstract safe-schedule premise is supplied. -/
theorem same_target_lifts (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (strategy : Strategy) (t : Tape (config p))
    (i : Fin (config p).folds.size) (start count : Nat)
    (bound : start + count ≤ (config p).folds[i.val]!)
    (mca : ∀ j : Fin (config p).folds[i.val]!, start ≤ j.val → j.val < start+count →
      ¬ RawMCA (Input p lanes root claims) strategy i j t)
    (guard : ∀ j : Fin (config p).folds[i.val]!, start ≤ j.val → j.val < start+count →
      ¬ ClaimEscape (Input p lanes root claims) strategy i j t)
    (target : Array E)
    (member : target ∈ foldCandidates (Input p lanes root claims) strategy t i (start+count))
    (truth : dot target (foldAt (Input p lanes root claims) strategy t i (start+count)).state.weight =
      (foldAt (Input p lanes root claims) strategy t i (start+count)).state.claim) :
    ∃ original ∈ foldCandidates (Input p lanes root claims) strategy t i start,
      foldFrom (Input p lanes root claims) t i start count original = target ∧
      dot original (foldAt (Input p lanes root claims) strategy t i start).state.weight =
        (foldAt (Input p lanes root claims) strategy t i start).state.claim := by
  induction count generalizing start with
  | zero => exact ⟨target, member, rfl, truth⟩
  | succ count ih =>
    let input := Input p lanes root claims
    let j : Fin (config p).folds[i.val]! := ⟨start, by omega⟩
    obtain ⟨middle, hm, he, ht⟩ := ih (start+1) (by omega)
      (by intro j hj hk; exact mca j (by omega) (by omega))
      (by intro j hj hk; exact guard j (by omega) (by omega))
      (by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using member)
      (by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using truth)
    have nextMember : middle ∈ arrayCandidates (i.val == 0)
        (concreteEncoder (remaining input.config i) input.config.rates[i.val]!)
        (foldOracle (paired input strategy t i j)
          (challenges input.config t).levels[i.val]!.folds[start]!)
        (threshold input.config i) := by
      unfold foldCandidates at hm
      rw [OracleReplay.oracleAt_succ _ _ _ _ start j.isLt] at hm
      exact hm
    obtain ⟨original, ho, hf⟩ := array_lifts (i.val == 0) _ _ rfl _ _ _
      (mca j le_rfl (by change start < start+(count+1); omega)) middle nextMember
    have pairedEq := OracleReplay.paired_candidates (i.val == 0) input.config.folds[i.val]!
      (remaining input.config i) input.config.rates[i.val]! start (threshold input.config i)
      (levelAt input strategy t i).oracle (challenges input.config t).levels[i.val]!.folds j.isLt
    have originalMember : original ∈ foldCandidates input strategy t i start := by
      change original ∈ arrayCandidates (i.val == 0)
        (concreteEncoder (remaining input.config i) input.config.rates[i.val]!)
        (OracleReplay.pairedOracle (i.val == 0) input.config.folds[i.val]!
          (levelAt input strategy t i).oracle (challenges input.config t).levels[i.val]!.folds
          start j.isLt) (threshold input.config i) at ho
      rw [pairedEq] at ho
      exact ho
    change middle = foldValues original
      (CandidateFolding.foldBlock (i.val == 0) (dimension input.config i))
      (challenges input.config t).levels[i.val]!.folds[start]! at hf
    refine ⟨original, originalMember, ?_, ?_⟩
    · rw [foldFrom_succ, CausalFolds.block_eq, ← hf]
      exact he
    · have shape := OracleReplay.candidate_round_shape (i.val == 0) input.config.folds[i.val]!
        (remaining input.config i) input.config.rates[i.val]! start (threshold input.config i)
        (levelAt input strategy t i).oracle (challenges input.config t).levels[i.val]!.folds
        j.isLt original ho
      apply backward_claim _ (foldAt input strategy t i start).state
        (CandidateFolding.foldBlock (i.val == 0) (dimension input.config i))
        (if i.val == 0 then 2 ^ (input.config.folds[i.val]! - (start+1))
          else 2 ^ (input.config.folds[i.val]! - (start+1)) * 2 ^ remaining input.config i)
        (challenges input.config t).levels[i.val]!.folds[start]!
        (proof input strategy t).levels[i.val]!.afterFold[start]!
        original originalMember shape
        (candidate_weight_size p lanes root claims strategy t i start (by omega) original originalMember)
        (by simpa only [ClaimEscape, CausalFolds.block_eq, j] using
          guard j le_rfl (by change start < start+(count+1); omega))
      rw [← hf]
      simpa only [foldAt_succ, foldStep, CausalFolds.block_eq] using ht

/-- Both raw knowledge exclusions are incoming-prefix measurable. -/
theorem paired_set (input : Public) (strategy : Strategy) (t : Tape input.config)
    (i : Fin input.config.folds.size) (j : Fin input.config.folds[i.val]!)
    (q : Coordinate input.config) (x : Sample q)
    (before : levelStart (challenges input.config t) i.val+j.val ≤ position q) :
    paired input strategy (set q t x) i j = paired input strategy t i j :=
  CausalFolds.pairedOracle_set input strategy i j q t x before

theorem knowledgeEvents_set_future (input : Public) (strategy : Strategy)
    (t : Tape input.config) (i : Fin input.config.folds.size)
    (j : Fin input.config.folds[i.val]!) (q : Coordinate input.config) (x : Sample q)
    (before : levelStart (challenges input.config t) i.val+j.val+1 ≤ position q) :
    (RawMCA input strategy i j (set q t x) ↔ RawMCA input strategy i j t) ∧
      (ClaimEscape input strategy i j (set q t x) ↔ ClaimEscape input strategy i j t) := by
  have scalar : (challenges input.config (set q t x)).levels[i.val]!.folds[j.val]! =
      (challenges input.config t).levels[i.val]!.folds[j.val]! := by
    rw [CausalStateCausality.challenge_fold, CausalStateCausality.challenge_fold]
    apply get_set_ne
    intro same
    have hp := congrArg position same
    rw [CausalPositions.position_fold i j t] at hp
    omega
  constructor
  · unfold RawMCA
    rw [paired_set input strategy t i j q x (by omega), scalar]
  · unfold ClaimEscape
    rw [scalar,
      CausalStateCausality.foldCandidates_set input strategy q t x i j.val j.isLt.le (by omega),
      CausalStateCausality.foldAt_set input strategy q t x i j.val j.isLt.le (by omega)]

open Classical in
theorem rawMCA_fiber_bound (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (strategy : Strategy) (t : Tape (config p))
    (i : Fin (config p).folds.size) (j : Fin (config p).folds[i.val]!) :
    Soundness.uniformProb (Finset.univ.filter fun r : E =>
      RawMCA (Input p lanes root claims) strategy i j (set (.fold i j) t r)) ≤
      (2 ^ 108 : ℚ) / 2 ^ 192 := by
  let input := Input p lanes root claims
  have event : (Finset.univ.filter fun r : E =>
      RawMCA input strategy i j (set (.fold i j) t r)) =
      mcaSeeds p i (paired input strategy t i j) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, RawMCA, mcaSeeds,
      paired_set input strategy t i j (.fold i j) r
        (CausalPositions.position_fold i j t).symm.le,
      CausalStateCausality.challenge_fold, get_set]
    rfl
  rw [event]
  exact mcaSeeds_probability p i _

open Classical in
theorem claimEscape_fiber_bound (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (strategy : Strategy) (t : Tape (config p))
    (i : Fin (config p).folds.size) (j : Fin (config p).folds[i.val]!) :
    Soundness.uniformProb (Finset.univ.filter fun r : E =>
      ClaimEscape (Input p lanes root claims) strategy i j (set (.fold i j) t r)) ≤
      (2 ^ 33 : ℚ) / 2 ^ 192 := by
  let input := Input p lanes root claims
  have before := (CausalPositions.position_fold i j t).symm.le
  have events : (Finset.univ.filter fun r : E =>
      ClaimEscape input strategy i j (set (.fold i j) t r)) =
      candidateRoundEscape (foldCandidates input strategy t i j)
        (foldAt input strategy t i j).state (block input.config i) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ClaimEscape,
      CausalStateCausality.challenge_fold, get_set,
      CausalStateCausality.foldCandidates_set input strategy (.fold i j) t r i j.val j.isLt.le before,
      CausalStateCausality.foldAt_set input strategy (.fold i j) t r i j.val j.isLt.le before]
  rw [events]
  have bound := candidateRoundEscape_probability (foldCandidates input strategy t i j)
    (foldAt input strategy t i j).state (block input.config i)
  have cap : ((foldCandidates input strategy t i j).card : ℚ) ≤ 2 ^ 32 := by
    exact_mod_cast ConcreteCandidates.production_arrayCandidates_card (i.val == 0) p i
      (OracleReplay.oracleAt (i.val == 0) input.config.folds[i.val]!
        (levelAt input strategy t i).oracle (challenges input.config t).levels[i.val]!.folds j.val)
  rw [FieldModel.card_E] at bound
  simp only [Nat.cast_pow, Nat.cast_ofNat] at bound
  calc
    _ ≤ (2 ^ 32 : ℚ) * (2 / 2 ^ 192) :=
      bound.trans (mul_le_mul_of_nonneg_right cap (by positivity))
    _ = _ := by norm_num

open Classical in
theorem rawMCA_probability (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (strategy : Strategy)
    (i : Fin (config p).folds.size) (j : Fin (config p).folds[i.val]!) :
    Soundness.uniformProb (Finset.univ.filter (RawMCA (Input p lanes root claims) strategy i j)) ≤
      (2 ^ 108 : ℚ) / 2 ^ 192 := by
  apply fiber_event_bound (.fold i j)
  intro rest
  exact rawMCA_fiber_bound p lanes root claims strategy rest.val i j

open Classical in
theorem claimEscape_probability (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (strategy : Strategy)
    (i : Fin (config p).folds.size) (j : Fin (config p).folds[i.val]!) :
    Soundness.uniformProb (Finset.univ.filter (ClaimEscape (Input p lanes root claims) strategy i j)) ≤
      (2 ^ 33 : ℚ) / 2 ^ 192 := by
  apply fiber_event_bound (.fold i j)
  intro rest
  exact claimEscape_fiber_bound p lanes root claims strategy rest.val i j

/-- All 56 profiles use the physical six-fold initial ladder. -/
theorem production_initial_six : ∀ p : Profile, (config p).folds[0]! = 6 := by
  decide +kernel

open Classical in
noncomputable def InitialFoldBad (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (strategy : Strategy) (t : Tape (config p)) : Prop :=
  ∃ j : Fin (config p).folds[0]!,
    RawMCA (Input p lanes root claims) strategy ⟨0, (production_config_valid p).2.1⟩ j t ∨
    ClaimEscape (Input p lanes root claims) strategy ⟨0, (production_config_valid p).2.1⟩ j t

open scoped BigOperators in
open Classical in
theorem uniform_or_family_bound {Ω I : Type*} [Fintype Ω] [Fintype I]
    (event : Ω → Prop) (P Q : I → Ω → Prop)
    [DecidablePred event] [∀ i, DecidablePred (P i)] [∀ i, DecidablePred (Q i)]
    (cover : ∀ t, event t ↔ ∃ i, P i t ∨ Q i t) (ep eq : ℚ)
    (hp : ∀ i, Soundness.uniformProb (Finset.univ.filter (P i)) ≤ ep)
    (hq : ∀ i, Soundness.uniformProb (Finset.univ.filter (Q i)) ≤ eq) :
    Soundness.uniformProb (Finset.univ.filter event) ≤
      (Fintype.card I : ℚ) * (ep+eq) := by
  let events (j : I × Bool) : Finset Ω :=
    Finset.univ.filter fun t => if j.2 then P j.1 t else Q j.1 t
  let errors (j : I × Bool) : ℚ := if j.2 then ep else eq
  have equality : Finset.univ.filter event =
      Finset.univ.biUnion events := by
    ext t
    simp [events, cover, exists_or, or_comm]
  rw [equality]
  calc
    _ ≤ ∑ j, Soundness.uniformProb (events j) := Soundness.union_bound events
    _ ≤ ∑ j, errors j := by
      apply Finset.sum_le_sum
      rintro ⟨j, b⟩ _
      cases b
      · exact hq j
      · exact hp j
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp [errors, mul_add]

open Classical in
theorem uniform_or_bound {Ω : Type*} [Fintype Ω] (P Q : Ω → Prop)
    [DecidablePred P] [DecidablePred Q] (ep eq : ℚ)
    (hp : Soundness.uniformProb (Finset.univ.filter P) ≤ ep)
    (hq : Soundness.uniformProb (Finset.univ.filter Q) ≤ eq) :
    Soundness.uniformProb (Finset.univ.filter fun t => P t ∨ Q t) ≤ ep+eq := by
  have bound := uniform_or_family_bound (fun t => P t ∨ Q t)
    (fun _ : Unit => P) (fun _ : Unit => Q) (by intro t; simp)
    ep eq (fun _ => hp) (fun _ => hq)
  simpa using bound

open scoped BigOperators in
open Classical in
theorem initialFoldBad_probability (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (strategy : Strategy) :
    Soundness.uniformProb (Finset.univ.filter (InitialFoldBad p lanes root claims strategy)) ≤
      6 * ((2 ^ 108 : ℚ) / 2 ^ 192 + 2 ^ 33 / 2 ^ 192) := by
  have bound := @uniform_or_family_bound (Tape (config p)) (Fin (config p).folds[0]!)
    inferInstance inferInstance
    (InitialFoldBad p lanes root claims strategy)
    (fun j t => RawMCA (Input p lanes root claims) strategy
      ⟨0, (production_config_valid p).2.1⟩ j t)
    (fun j t => ClaimEscape (Input p lanes root claims) strategy
      ⟨0, (production_config_valid p).2.1⟩ j t)
    inferInstance inferInstance inferInstance
    (fun _ => Iff.rfl)
    ((2 ^ 108 : ℚ) / 2 ^ 192) ((2 ^ 33 : ℚ) / 2 ^ 192)
    (fun j => rawMCA_probability p lanes root claims strategy ⟨0, (production_config_valid p).2.1⟩ j)
    (fun j => claimEscape_probability p lanes root claims strategy ⟨0, (production_config_valid p).2.1⟩ j)
  rw [Fintype.card_fin] at bound
  calc
    _ ≤ ((config p).folds[0]! : ℚ) *
        ((2 ^ 108 : ℚ) / 2 ^ 192 + 2 ^ 33 / 2 ^ 192) := bound
    _ = 6 * ((2 ^ 108 : ℚ) / 2 ^ 192 + 2 ^ 33 / 2 ^ 192) :=
      congrArg (fun n : Nat => (n : ℚ) * ((2 ^ 108 : ℚ) / 2 ^ 192 + 2 ^ 33 / 2 ^ 192))
        (production_initial_six p)

#print axioms same_target_lifts
#print axioms initialFoldBad_probability
end Whir.InitialKnowledgeSchedule
