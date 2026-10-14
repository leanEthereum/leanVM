import Whir.InteractiveSoundness
import Mathlib.LinearAlgebra.Lagrange
import Whir.ConcreteRowExtraction

/-! Knowledge games, actual unique-radius row decoding, and the information required by record interpolation.

The rewind interface counts black-box response calls exactly. Its fuel is an abstract interaction bound, not a proof of machine running time: Lean continuations, output construction, and the prover itself are not unit-cost. `ConcreteRowExtraction` supplies executable Gao decoding with a concrete dense-encoder correspondence. It requires a full received row inside the unique radius and does not establish that verifier acceptance supplies such a row. No knowledge-soundness theorem is asserted.

The extraction integration is split by access and algebra: `RewindRowExtraction` parses real fixed-public reset answers and composes the source decoder/counter; `PCSRewindExtraction` assembles the occupied witness and states the actual accepted-without-explaining-output cover. `RewindCoverage` proves stratified query-coordinate coverage, not availability of valid replies from an adversarial prover. `RewindTrajectory`, `RewindBatchTarget` and `RewindRadiusExtraction` track generic-E next-root candidates and the OOD-selected fixed projection target, with actual authentication and an explicit nonzero batching-collision event. `TraceBasisExtraction`, `ShoupTraceExtraction` and `PCSListExtraction` provide a non-enumerating source-extension list-decoder path. These pieces do not supply a Fiat–Shamir reset reduction, a common-lane reconstruction theorem for every accepted prefix, or a complete knowledge-error bound.

The checked obstruction concerns record-only interpolation. The dense causal game exposes the entire root; a hashed commitment or an authenticated query log needs a separate access reduction. These results do not assert impossibility of rewindable knowledge extraction. -/
namespace Whir.KnowledgeExtraction
open Concrete Protocol CausalGame Polynomial
open scoped BigOperators

/-- A commitment and its claims are chosen before the verifier tape. -/
structure CommittedProver where
  input : Public
  respond : Strategy

/-- The relation is the actual commitment-fixed list relation, not unique
opening and not merely truth of claims about an unrelated witness. -/
def Explains (input : Public) (w : Witness input.config input.lanes) : Prop :=
  w ∈ InitialCandidates.witnesses input.config input.lanes input.root ∧
  ∀ claim ∈ input.claims.toList,
    dot (paddedWitness input.config input.lanes w) claim.weight = claim.value

/-- Rewinding resets the deterministic causal prover and replays a selected
challenge prefix. The extractor cannot invent past prover replies. This models
fixed prover coins; randomized provers need their coins fixed across rewinds. -/
inductive RewindProgram (c : Config) (lanes : Nat) where
  | finish (output : Option (Witness c lanes))
  | query (batches : List Batch) (message : Batch)
      (next : Reply → RewindProgram c lanes)

/-- Every response in this history is obtained from the black box itself.
Challenge schedules are typed `Batch` messages; this is the total `Strategy`
interface, not a claim about reset access to the deployed Fiat--Shamir prover. -/
def replayPast (input : Public) (strategy : Strategy) :
    History → List Batch → History
  | past, [] => past
  | past, message :: rest =>
      replayPast input strategy ((message, strategy input past message) :: past) rest

structure RewindResult (c : Config) (lanes : Nat) where
  output : Option (Witness c lanes)
  responseCalls : Nat

/-- Each round replays at most `maxReplay` messages before its new response.
Exhausted round fuel or an oversized prefix fails, rather than granting free
oracle access. Local Lean evaluation and prover running time are not unit-cost. -/
def runRewind (input : Public) (strategy : Strategy) (maxReplay : Nat) :
    Nat → RewindProgram input.config input.lanes → RewindResult input.config input.lanes
  | _, .finish w => ⟨w, 0⟩
  | 0, .query _ _ _ => ⟨none, 0⟩
  | fuel + 1, .query batches message next =>
      if batches.length ≤ maxReplay then
        let past := replayPast input strategy [] batches
        let result := runRewind input strategy maxReplay fuel
          (next (strategy input past message))
        ⟨result.output, result.responseCalls + batches.length + 1⟩
      else ⟨none, 0⟩

theorem responseCalls_le (input : Public) (strategy : Strategy) (maxReplay fuel : Nat)
    (program : RewindProgram input.config input.lanes) :
    (runRewind input strategy maxReplay fuel program).responseCalls ≤
      fuel * (maxReplay + 1) := by
  induction fuel generalizing program with
  | zero => cases program <;> simp [runRewind]
  | succ fuel ih =>
    cases program with
    | finish w => simp [runRewind]
    | query batches message next =>
      simp only [runRewind]
      split_ifs with within
      · have bound := ih (next (strategy input (replayPast input strategy [] batches) message))
        simp only
        rw [Nat.succ_mul]
        omega
      · simp

/-- Extraction randomness is independent of the verifier tape. Bounds count
rewind rounds and replay messages; value-connected local arithmetic is measured
separately by the concrete extractor instrumentation. -/
structure Extractor (Seed : Type*) where
  program : (input : Public) → Seed → RewindProgram input.config input.lanes
  rewindRounds : Nat
  maxReplay : Nat


def extractionSuccess {Seed : Type*} (extractor : Extractor Seed)
    (prover : CommittedProver) (seed : Seed) : Prop :=
  ∃ w, (runRewind prover.input prover.respond extractor.maxReplay extractor.rewindRounds
    (extractor.program prover.input seed)).output = some w ∧ Explains prover.input w

/-- A joint independent uniform experiment, using the actual causal verifier.
No acceptance probability or extraction relation is assumed by a theorem here. -/
noncomputable def knowledgeFailureProbability {Seed : Type*} [Fintype Seed] [Nonempty Seed]
    (extractor : Extractor Seed) (prover : CommittedProver) : ℚ := by
  classical
  exact Soundness.uniformProb (Finset.univ.filter fun sample : Tape prover.input.config × Seed =>
    experiment prover.input prover.respond sample.1 = true ∧
    ¬ extractionSuccess extractor prover sample.2)


section Records
variable {F I : Type*} [Field F] [CharP F 2]

/-- Interpolation can identify a novel coefficient row from `2^n` distinct
correct evaluations. This is uniqueness, not an algorithm finding a correct
common agreement set inside an adversarial commitment. -/
theorem records_determine_row (basis : Nat → F) (n : Nat)
    (independent : AdditiveCode.Independent basis n)
    (records : Finset I) (domain : I → F) (distinct : Set.InjOn domain records)
    (enough : 2 ^ n ≤ records.card) (a b : Fin (2 ^ n) → F)
    (same : ∀ i ∈ records,
      (CandidateFolding.novelEncoder basis n domain) a i =
        (CandidateFolding.novelEncoder basis n domain) b i) : a = b := by
  apply AdditiveCode.polynomial_injective independent
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq records distinct
    ((AdditiveCode.polynomial_degree_lt independent a).trans_le (by exact_mod_cast enough))
    ((AdditiveCode.polynomial_degree_lt independent b).trans_le (by exact_mod_cast enough))
  exact same

/-- With fewer records there is a nonzero novel coefficient row vanishing on
all observations. This uses the explicit product of their linear factors; it
holds even without distinctness of the observed field points. -/
theorem sparse_records_have_kernel (basis : Nat → F) (n : Nat)
    (independent : AdditiveCode.Independent basis n)
    (records : Finset I) (domain : I → F) (few : records.card < 2 ^ n) :
    ∃ a : Fin (2 ^ n) → F, a ≠ 0 ∧
      ∀ i ∈ records, (CandidateFolding.novelEncoder basis n domain) a i = 0 := by
  classical
  let p : F[X] := ∏ i ∈ records, (Polynomial.X - Polynomial.C (domain i))
  have nonzero : p ≠ 0 := (Polynomial.monic_prod_X_sub_C domain records).ne_zero
  have degree : p.degree < 2 ^ n := by
    rw [Polynomial.degree_eq_natDegree nonzero]
    dsimp [p]
    rw [Polynomial.natDegree_finsetProd_X_sub_C_eq_card]
    exact_mod_cast few
  obtain ⟨a, ha⟩ := (AdditiveCode.polynomial_surjective independent p).mpr degree
  refine ⟨a, ?_, ?_⟩
  · intro hz
    subst a
    have : p = 0 := by simpa [AdditiveCode.polynomial] using ha.symm
    exact nonzero this
  · intro i hi
    change (AdditiveCode.polynomial basis n a).eval (domain i) = 0
    rw [ha]
    simp only [p, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C]
    exact Finset.prod_eq_zero hi (sub_self _)

/-- No deterministic record-only decoder is correct for every coefficient row
below the interpolation threshold. This is an information lower bound, not a
claim that acceptance or rewinding cannot reveal additional information. -/
theorem no_sparse_record_decoder (basis : Nat → F) (n : Nat)
    (independent : AdditiveCode.Independent basis n)
    (records : Finset I) (domain : I → F) (few : records.card < 2 ^ n) :
    ¬ ∃ decode : (records → F) → (Fin (2 ^ n) → F),
      ∀ a, decode (fun i => (CandidateFolding.novelEncoder basis n domain) a i) = a := by
  obtain ⟨a, nonzero, vanishes⟩ := sparse_records_have_kernel basis n independent records domain few
  rintro ⟨decode, correct⟩
  have observations : (fun i : records =>
      (CandidateFolding.novelEncoder basis n domain) a i) =
      (fun i : records => (CandidateFolding.novelEncoder basis n domain) 0 i) := by
    funext i
    rw [vanishes i i.property, map_zero]
    rfl
  exact nonzero ((correct a).symm.trans ((congrArg decode observations).trans (correct 0)))
end Records

/-- The exact initial row observation, computed by the verifier's dense encoder.
These are occupied base-field coefficients, not arbitrary extension witnesses. -/
def rowRecords (n rate : Nat) (records : Finset (Fin (2 ^ (n + rate))))
    (words : Fin (2 ^ n) → K) : records → E :=
  fun q => (encode n rate (Array.ofFn fun j => E.ofK (words j)))[q.val.val]!

/-- The matching upper threshold for actual base rows: `2^n` distinct machine
query positions identify their coefficients. Finding records belonging to one
candidate, rather than mixing candidates, is not supplied by this theorem. -/
theorem actual_records_determine_row (n rate : Nat) (depth : n + rate ≤ 64)
    (records : Finset (Fin (2 ^ (n + rate)))) (enough : 2 ^ n ≤ records.card)
    (a b : Fin (2 ^ n) → K) (same : rowRecords n rate records a = rowRecords n rate records b) :
    a = b := by
  have encoded : ∀ q ∈ records,
      (CandidateFolding.novelEncoder (AdditiveCode.bitBasis E.ofK) n
        (fun q : Fin (2 ^ (n + rate)) => E.ofK (UInt64.ofNat q.val))) (fun j => E.ofK (a j)) q =
      (CandidateFolding.novelEncoder (AdditiveCode.bitBasis E.ofK) n
        (fun q : Fin (2 ^ (n + rate)) => E.ofK (UInt64.ofNat q.val))) (fun j => E.ofK (b j)) q := by
    intro q hq
    have observed := congrFun same (⟨q, hq⟩ : records)
    unfold rowRecords at observed
    rw [AdditiveCode.concrete_encode_eval n rate _ (by simp) _ q.isLt,
      AdditiveCode.concrete_encode_eval n rate _ (by simp) _ q.isLt] at observed
    simpa [AdditiveCode.concretePolynomial, AdditiveCode.arrayPolynomial,
      AdditiveCode.concreteBaseRepresentation, QueryRefinement.concreteRepresentation,
      CandidateFolding.novelEncoder] using observed
  have coefficientEq := records_determine_row (AdditiveCode.bitBasis E.ofK) n
    (AdditiveCode.concrete_bitBasis_independent n (by omega)) records
    (fun q : Fin (2 ^ (n + rate)) => E.ofK (UInt64.ofNat q.val))
    (AdditiveCode.concreteDomain (n + rate) depth).injective.injOn enough
    (fun j => E.ofK (a j)) (fun j => E.ofK (b j)) encoded
  funext j
  exact FieldModel.ofK_injective (congrFun coefficientEq j)

private noncomputable def baseRepresentation : AdditiveCode.BaseRepresentation FieldModel.BaseQuotient where
  map := FieldModel.toBaseQuotient
  one := FieldModel.toBaseQuotient_one
  add := FieldModel.toBaseQuotient_xor
  mul := FieldModel.toBaseQuotient_kmul
  inv := FieldModel.toBaseQuotient_kinv

/-- Endpoint-connected obstruction: below `2^n` authenticated evaluations,
two distinct literal base-word rows have identical actual dense encodings at
every observed query. No unique commitment or accepting prover is presumed. -/
theorem actual_sparse_rows (n rate : Nat) (depth : n + rate ≤ 64)
    (records : Finset (Fin (2 ^ (n + rate)))) (few : records.card < 2 ^ n) :
    ∃ words : Fin (2 ^ n) → K, words ≠ 0 ∧
      rowRecords n rate records words = rowRecords n rate records 0 := by
  classical
  let basis := AdditiveCode.bitBasis FieldModel.toBaseQuotient
  let domain := fun q : Fin (2 ^ (n + rate)) =>
    FieldModel.toBaseQuotient (UInt64.ofNat q.val)
  have independent : AdditiveCode.Independent basis n :=
    AdditiveCode.bitBasis_independent baseRepresentation
      FieldModel.toBaseQuotient_injective n (by omega)
  obtain ⟨a, nonzero, vanishes⟩ :=
    sparse_records_have_kernel basis n independent records domain few
  choose words hwords using fun j => FieldModel.toBaseQuotient_bijective.2 (a j)
  have nonzeroWords : words ≠ 0 := by
    intro hz
    apply nonzero
    funext j
    simpa [hz] using (hwords j).symm
  refine ⟨words, nonzeroWords, ?_⟩
  have poly :
      AdditiveCode.concretePolynomial n (Array.ofFn fun j => E.ofK (words j)) =
      (AdditiveCode.polynomial basis n a).map FieldModel.baseEmbedding := by
    rw [BaseCandidateDescent.map_polynomial]
    unfold AdditiveCode.concretePolynomial AdditiveCode.arrayPolynomial
    apply congrArg₂ (AdditiveCode.polynomial · n ·)
    · funext j
      simp [basis, AdditiveCode.bitBasis, AdditiveCode.concreteBaseRepresentation,
        FieldModel.baseEmbedding_word]
    · funext j
      simp [QueryRefinement.concreteRepresentation]
      rw [← hwords j, FieldModel.baseEmbedding_word]
  funext q
  unfold rowRecords
  rw [AdditiveCode.concrete_encode_eval n rate _ (by simp) _ q.val.isLt,
    AdditiveCode.concrete_encode_eval n rate _ (by simp) _ q.val.isLt, poly]
  have zeroPoly : AdditiveCode.concretePolynomial n
      (Array.ofFn fun j : Fin (2 ^ n) => E.ofK ((0 : Fin (2 ^ n) → K) j)) = 0 := by
    simp [AdditiveCode.concretePolynomial, AdditiveCode.arrayPolynomial,
      QueryRefinement.concreteRepresentation, AdditiveCode.polynomial, FieldModel.ofK_zero]
  rw [zeroPoly, Polynomial.eval_zero]
  rw [← FieldModel.baseEmbedding_word, Polynomial.eval_map_apply]
  change FieldModel.baseEmbedding
    ((CandidateFolding.novelEncoder basis n domain) a q.val) = 0
  rw [vanishes q.val q.property, map_zero]

/-- In particular, a deterministic interpolation shortcut consuming only these
records cannot recover every production initial row. This is not a lower bound
against an extractor that also consumes a root, claims, or rewind responses. -/
theorem actual_no_sparse_decoder (n rate : Nat) (depth : n + rate ≤ 64)
    (records : Finset (Fin (2 ^ (n + rate)))) (few : records.card < 2 ^ n) :
    ¬ ∃ decode : (records → E) → (Fin (2 ^ n) → K),
      ∀ words, decode (rowRecords n rate records words) = words := by
  obtain ⟨words, nonzero, same⟩ := actual_sparse_rows n rate depth records few
  rintro ⟨decode, correct⟩
  exact nonzero ((correct words).symm.trans ((congrArg decode same).trans (correct 0)))

theorem production_no_sparse_decoder (p : ParameterBounds.Profile)
    (records : Finset (Fin (2 ^ ((ParameterBounds.config p).logN -
      (ParameterBounds.config p).folds[0]! + (ParameterBounds.config p).rates[0]!))))
    (few : records.card < 2 ^ ((ParameterBounds.config p).logN -
      (ParameterBounds.config p).folds[0]!)) :
    ¬ ∃ decode : (records → E) →
        (Fin (2 ^ ((ParameterBounds.config p).logN -
          (ParameterBounds.config p).folds[0]!)) → K),
      ∀ words, decode (rowRecords _ _ records words) = words :=
  actual_no_sparse_decoder _ _ (InitialCandidates.production_initial_facts p).2.2.1 records few

/-- Connection of the game relation to the existing verifier endpoint. Outside
its concrete bad-challenge cover, acceptance implies an explanation exists.
This deliberately does not select it or claim it can be found efficiently. -/
theorem accepted_safe_explanation (p : ParameterBounds.Profile) (lanes : Nat)
    (root : BaseOracle) (claims : Array Claim) (strategy : Strategy)
    (tape : Tape (ParameterBounds.config p))
    (accepted : experiment (ExecutionShapes.Input p lanes root claims) strategy tape = true)
    (safe : ∀ q, ¬ CausalBadEvents.Bad
      (ExecutionShapes.Input p lanes root claims) strategy q tape) :
    ∃ w, Explains (ExecutionShapes.Input p lanes root claims) w := by
  classical
  by_contra noExplanation
  have noWitness : ¬ ∃ w ∈ InitialCandidates.witnesses (ParameterBounds.config p) lanes root,
      ∀ claim ∈ claims.toList,
        dot (paddedWitness (ParameterBounds.config p) lanes w) claim.weight = claim.value := by
    simpa [Explains, ExecutionShapes.Input] using noExplanation
  obtain ⟨q, bad⟩ := InteractiveSoundness.accepted_false_cover
    p lanes root claims strategy tape accepted noWitness
  exact safe q bad

#print axioms responseCalls_le
#print axioms records_determine_row
#print axioms sparse_records_have_kernel
#print axioms no_sparse_record_decoder
#print axioms actual_records_determine_row
#print axioms actual_sparse_rows
#print axioms actual_no_sparse_decoder
#print axioms production_no_sparse_decoder
#print axioms accepted_safe_explanation

end Whir.KnowledgeExtraction
