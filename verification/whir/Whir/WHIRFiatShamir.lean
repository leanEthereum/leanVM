import Whir.CausalBadEvents
import Whir.TypedFiatShamirGame
import Whir.ByteCodec
import Whir.CausalPrefix
import Whir.InteractiveSoundness
import Whir.RingPCSGame

/-! Ordinary classical, dependent-alphabet WHIR allocation bounds. Concrete
prefix events come from actual checked states and commitment-fixed lists.
No homogeneous sigma sampling, future-tape exposure, grinding credit or
numerical 128-bit claim is used. -/
namespace Whir.WHIRFiatShamir
open Concrete Protocol CausalGame CausalProbability ParameterBounds GroupedChallenges
open scoped BigOperators
open Classical

/-- Deterministic public-statement syntax is imposed on every queried branch,
not only on the final accepted proof. -/
structure Statement (p : Profile) where
  lanes : Nat
  root : BaseOracle
  claims : Array Claim
  lane_bound : lanes ≤ 2 ^ (config p).folds[0]!
  claim_shape : ∀ j : Fin claims.size, claims[j].weight.size = 2 ^ (config p).logN
  claim_cap : claims.size ≤ 2^64

abbrev Statement.input {p : Profile} (s : Statement p) : Public :=
  ⟨config p, s.lanes, s.root, s.claims⟩

/-- Only strict-past values exist at this interface. The suffix below is filled
with deterministic zeros, never sampled or disclosed as random future tape. -/
abbrev Prefix {c : Config} (q : Coordinate c) :=
  (r : Coordinate c) → position r < position q → Sample r

noncomputable def Prefix.tape {c : Config} {q : Coordinate c} (past : Prefix q) : Tape c :=
  (coordinates c).symm (fun r => if h : position r < position q then past r h else 0)

/-- A concrete request includes the fixed public commitment and a causal strategy.
The strategy is allowed to choose its pending response after seeing this sample. -/
structure Request (p : Profile) where
  statement : Statement p
  strategy : Strategy
  coordinate : Coordinate (config p)
  past : Prefix coordinate

abbrev Answer {p : Profile} (r : Request p) := Sample r.coordinate

def bad {p : Profile} (r : Request p) (x : Answer r) : Prop :=
  CausalBadEvents.Bad r.statement.input r.strategy r.coordinate
    (set r.coordinate r.past.tape x)

/-- The conservative largest actual grouped error, with the supported claim cap. -/
def eta (p : Profile) : ℚ := groupedMaximum (config p) (estimates (config p)) (2^64)

theorem eta_nonneg (p : Profile) : 0 ≤ eta p := by
  apply le_trans (show (0 : ℚ) ≤ 2 / fieldSize by norm_num [fieldSize])
  exact (le_max_left _ _).trans (le_max_right _ _)

theorem eta_le (p : Profile) : eta p ≤ 1 / 2^79 :=
  production_grouped p (2^64) le_rfl

/-- All five actual prefix-event providers are instantiated here. There is no
PCS/RBR/local-escape premise left for the caller to assume. -/
theorem sparse (p : Profile) (r : Request p) :
    FiatShamirGame.average (fun x : Answer r => if bad r x then 1 else 0) ≤ eta p := by
  have hf := CausalBadEvents.fiber_bound p r.statement.lanes r.statement.root
    r.statement.claims r.statement.lane_bound r.statement.claim_shape
    r.strategy r.coordinate r.past.tape
  have hl := CausalBadEvents.localError_le_groupedMaximum r.statement.input r.coordinate
  have hm : groupedMaximum (config p) (estimates (config p)) r.statement.claims.size ≤ eta p := by
    unfold eta groupedMaximum
    exact max_le_max (initialBatch_mono _ r.statement.claim_cap) le_rfl
  calc
    _ = Soundness.uniformProb (Finset.univ.filter fun x : Answer r => bad r x) := by
      simp only [FiatShamirGame.average, Soundness.uniformProb, Finset.sum_boole]
    _ ≤ eta p := hf.trans (hl.trans hm)

abbrev AllocationGame (p : Profile) (n : Nat) :=
  TypedFiatShamirGame.Game (Request p) Answer n

noncomputable def risk {p : Profile} {n : Nat} (game : AllocationGame p n) : ℚ :=
  TypedFiatShamirGame.risk bad game

/-- Adaptive stopping and arbitrary branches are already inside the game; the
resource cap is the type index of the entire tree, not its successful path. -/
theorem ordinary_bound (p : Profile) (B K : Nat) (game : AllocationGame p (B*(K+1))) :
    risk game ≤ min 1 ((B*(K+1) : Nat) * eta p) :=
  le_min (TypedFiatShamirGame.risk_le_one bad game)
    (TypedFiatShamirGame.risk_bound bad (eta p) (eta_nonneg p) (sparse p) game)

theorem ordinary_bound_numeric (p : Profile) (B K : Nat)
    (game : AllocationGame p (B*(K+1))) :
    risk game ≤ min 1 (((B*(K+1) : Nat) : ℚ) / 2^79) := by
  apply (ordinary_bound p B K game).trans
  apply min_le_min le_rfl
  have h := mul_le_mul_of_nonneg_left (eta_le p) (show (0 : ℚ) ≤ (B*(K+1) : Nat) by positivity)
  simpa only [mul_one_div] using h

/-- The actual codec is bijective; query chunks and lambda stay in one product. -/
abbrev Bytes {c : Config} : Coordinate c → Type
  | .initial => FiatShamirGame.Scalar24
  | .fold _ _ => FiatShamirGame.Scalar24
  | .ood i _ => Fin (remaining c i) → FiatShamirGame.Scalar24
  | .query i => (Fin (queryChunks c i) → FiatShamirGame.Scalar24) × FiatShamirGame.Scalar24
  | .tail _ => FiatShamirGame.Scalar24

instance {c : Config} (q : Coordinate c) : Fintype (Bytes q) := by
  cases q <;> unfold Bytes <;> infer_instance

def scalarCodec : FiatShamirGame.Scalar24 ≃ E where
  toFun := ByteCodec.decodeE
  invFun := ByteCodec.encodeE
  left_inv := ByteCodec.encodeE_decodeE
  right_inv := ByteCodec.decodeE_encodeE

def codec {c : Config} (q : Coordinate c) : Bytes q ≃ Sample q :=
  match q with
  | .initial => scalarCodec
  | .fold _ _ => scalarCodec
  | .ood _ _ => Equiv.piCongrRight (fun _ => scalarCodec)
  | .query _ => Equiv.prodCongr (Equiv.piCongrRight (fun _ => scalarCodec)) scalarCodec
  | .tail _ => scalarCodec

/-- Exact distribution, not an approximation or cardinality-only assertion. -/
theorem codec_average {c : Config} (q : Coordinate c) (f : Sample q → ℚ) :
    FiatShamirGame.average (fun b : Bytes q => f (codec q b)) =
      FiatShamirGame.average f := by
  unfold FiatShamirGame.average
  rw [Fintype.sum_equiv (codec q) _ f (fun _ => rfl), Fintype.card_congr (codec q)]

theorem byte_sparse (p : Profile) (r : Request p) :
    FiatShamirGame.average (fun b : Bytes r.coordinate =>
      if bad r (codec r.coordinate b) then 1 else 0) ≤ eta p := by
  rw [codec_average r.coordinate (fun x => if bad r x then 1 else 0)]
  exact sparse p r

/-- Unused independent padding is integrated out, never returned to the strategy
as an extra challenge and never resampled on a partial-vector cache read. -/
theorem padding_average {X Pad : Type*} [Fintype X] [Fintype Pad] [Nonempty Pad]
    (f : X → ℚ) :
    FiatShamirGame.average (fun pair : X × Pad => f pair.1) = FiatShamirGame.average f := by
  have hp : (Fintype.card Pad : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [FiatShamirGame.average, Fintype.sum_prod_type, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum, Fintype.card_prod, Nat.cast_mul]
  field_simp

/-- Pending coefficients do not enter the truth of the newly folded claim. -/
theorem fold_pending_irrelevant (candidates : Finset (Array E)) (state : VerifierState E)
    (block : Nat) (x : E) (a b : Message E) :
    VerifierInvariant.Lost candidates (state.fold block x a) ↔
      VerifierInvariant.Lost candidates (state.fold block x b) := Iff.rfl

/-- After successful authentication, arbitrary lambda-dependent rows and the
current intro can be replaced by canonical rows and a fixed default intro.
Thus allocation-time truth does not guess the current prover response. -/
theorem canonical_query_restores (n rate count i : Nat) (root : Oracle)
    (cs : LevelChallenges) (p : LevelProof) (state : VerifierState E)
    (candidates : Finset (Array E))
    (rowsAt : LevelBoundary.QueryTape (n+rate) count → E → Oracle)
    (introAt : LevelBoundary.QueryTape (n+rate) count → E → Message E)
    (x : LevelBoundary.QueryTape (n+rate) count × E)
    (h : QueryBatchSoundness.Restores n rate count i root cs p state candidates rowsAt introAt x) :
    QueryBatchSoundness.Restores n rate count i root cs p state candidates
      (fun tape _ => (QueryBatchSoundness.queries (n+rate) count tape).map (fun q => root[q]!))
      (fun _ _ => default) x := by
  obtain ⟨hs, ha, hl⟩ := h
  have rows := BatchingRefinement.checked_rows_eq root
    (QueryBatchSoundness.queries (n+rate) count x.1)
    {p with rows := rowsAt x.1 x.2, intro := introAt x.1 x.2} hs ha
  change rowsAt x.1 x.2 =
    (QueryBatchSoundness.queries (n+rate) count x.1).map (fun q => root[q]!) at rows
  refine ⟨by simp, ?_, ?_⟩
  · have he : authenticateRow root (QueryBatchSoundness.queries (n+rate) count x.1)
        {p with rows := (QueryBatchSoundness.queries (n+rate) count x.1).map (fun q => root[q]!), intro := default} =
        authenticateRow root (QueryBatchSoundness.queries (n+rate) count x.1)
          {p with rows := rowsAt x.1 x.2, intro := introAt x.1 x.2} := by
      funext j u
      simp only [authenticateRow, rows]
    rw [he]
    exact ha
  · have he (ch : LevelChallenges) :
        oodBatch ch {p with rows := rowsAt x.1 x.2, intro := introAt x.1 x.2} state =
        oodBatch ch {p with rows := (QueryBatchSoundness.queries (n+rate) count x.1).map (fun q => root[q]!), intro := default} state := rfl
    dsimp only [queryBatch, VerifierInvariant.Lost, VerifierState.batch] at hl ⊢
    rw [he, rows] at hl
    exact hl

/-- Actual prequery data only: current rows are canonical, current intro ignored. -/
def QueryEnvelope (input : Public) (strategy : Strategy)
    (i : Fin input.config.folds.size) (t : Tape input.config) (x : Sample (.query i)) : Prop :=
  CausalBoundary.QueryPrior input strategy i t ∧
  QueryBatchSoundness.Restores (remaining input.config i) input.config.rates[i.val]!
    input.config.queries[i.val]! i (CausalExecution.levelAt input strategy t i).oracle
    (challenges input.config t).levels[i.val]! (CausalExecution.proof input strategy t).levels[i.val]!
    (CausalBoundary.boundary input strategy t i).state (CausalExecution.followingCandidates input strategy t i)
    (fun tape _ => (QueryBatchSoundness.queries
      (remaining input.config i + input.config.rates[i.val]!) input.config.queries[i.val]! tape).map
      (fun q => (CausalExecution.levelAt input strategy t i).oracle[q]!))
    (fun _ _ => default) x

theorem query_implies_envelope (p : Profile) (s : Statement p) (strategy : Strategy)
    (i : Fin (config p).folds.size) (t : Tape (config p)) (x : Sample (.query i))
    (h : CausalBoundary.QueryEvent s.input strategy i (set (.query i) t x)) :
    QueryEnvelope s.input strategy i t x := by
  have facts := CausalBoundary.production_boundary_facts p i
  obtain ⟨prior, restores⟩ := CausalBoundary.query_event_fiber s.input strategy t i x
    facts.1 facts.2.1 h
  exact ⟨prior, canonical_query_restores _ _ _ _ _ _ _ _ _ _ _ _ restores⟩

theorem query_envelope_bound (p : Profile) (s : Statement p) (strategy : Strategy)
    (i : Fin (config p).folds.size) (t : Tape (config p)) :
    Soundness.uniformProb (Finset.univ.filter (QueryEnvelope s.input strategy i t)) ≤
      queryBatchError (config p) (estimates (config p)) i := by
  classical
  by_cases prior : CausalBoundary.QueryPrior s.input strategy i t
  · have hb := CausalBoundary.actual_transition s.input strategy t p rfl i
      (fun tape _ => (QueryBatchSoundness.queries
        (remaining (config p) i + (config p).rates[i.val]!) (config p).queries[i.val]! tape).map
        (fun q => (CausalExecution.levelAt s.input strategy t i).oracle[q]!))
      (fun _ _ => default) prior.2.1 prior.2.2.1 prior.2.2.2
    unfold QueryEnvelope
    simp only [prior, true_and]
    convert hb using 1
    rfl
  · have he : (Finset.univ.filter (QueryEnvelope s.input strategy i t)) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro x _ hx
      exact prior hx.1
    rw [he]
    simp only [Soundness.uniformProb, Finset.card_empty, Nat.cast_zero, zero_div]
    have alpha := (production_level_facts p i).2.2.2.2.2.2.1
    unfold queryBatchError estimates fieldSize
    split_ifs <;> positivity

/-- Response-independent envelope on the whole typed draw. -/
def Envelope (input : Public) (strategy : Strategy) (q : Coordinate input.config)
    (t : Tape input.config) : Sample q → Prop :=
  match q with
  | .query i => QueryEnvelope input strategy i t
  | q => fun x => CausalBadEvents.Bad input strategy q (set q t x)

theorem bad_implies_envelope (p : Profile) (s : Statement p) (strategy : Strategy)
    (q : Coordinate (config p)) (t : Tape (config p)) (x : Sample q)
    (h : CausalBadEvents.Bad s.input strategy q (set q t x)) :
    Envelope s.input strategy q t x := by
  cases q with
  | query i => exact query_implies_envelope p s strategy i t x h
  | initial => exact h
  | fold i j => exact h
  | ood i j => exact h
  | tail j => exact h

theorem envelope_fiber (p : Profile) (s : Statement p) (strategy : Strategy)
    (q : Coordinate (config p)) (t : Tape (config p)) :
    Soundness.uniformProb (Finset.univ.filter (Envelope s.input strategy q t)) ≤
      CausalBadEvents.localError s.input q := by
  cases q with
  | query i => exact query_envelope_bound p s strategy i t
  | initial => exact CausalBadEvents.fiber_bound p s.lanes s.root s.claims s.lane_bound s.claim_shape strategy .initial t
  | fold i j => exact CausalBadEvents.fiber_bound p s.lanes s.root s.claims s.lane_bound s.claim_shape strategy (.fold i j) t
  | ood i j => exact CausalBadEvents.fiber_bound p s.lanes s.root s.claims s.lane_bound s.claim_shape strategy (.ood i j) t
  | tail j => exact CausalBadEvents.fiber_bound p s.lanes s.root s.claims s.lane_bound s.claim_shape strategy (.tail j) t

def allocationBad {p : Profile} (r : Request p) : Answer r → Prop :=
  Envelope r.statement.input r.strategy r.coordinate r.past.tape

theorem allocation_sparse (p : Profile) (r : Request p) :
    FiatShamirGame.average (fun x : Answer r => if allocationBad r x then 1 else 0) ≤ eta p := by
  have hf := envelope_fiber p r.statement r.strategy r.coordinate r.past.tape
  have hl := CausalBadEvents.localError_le_groupedMaximum r.statement.input r.coordinate
  have hm : groupedMaximum (config p) (estimates (config p)) r.statement.claims.size ≤ eta p := by
    unfold eta groupedMaximum
    exact max_le_max (initialBatch_mono _ r.statement.claim_cap) le_rfl
  calc
    _ = Soundness.uniformProb (Finset.univ.filter fun x : Answer r => allocationBad r x) := by
      simp only [FiatShamirGame.average, Soundness.uniformProb, Finset.sum_boole]
    _ ≤ eta p := hf.trans (hl.trans hm)

theorem bad_implies_allocationBad {p : Profile} (r : Request p) (x : Answer r)
    (h : bad r x) : allocationBad r x :=
  bad_implies_envelope p r.statement r.strategy r.coordinate r.past.tape x h

noncomputable def allocationRisk {p : Profile} {n : Nat} (game : AllocationGame p n) : ℚ :=
  TypedFiatShamirGame.risk allocationBad game

theorem allocation_bound (p : Profile) (B K : Nat) (game : AllocationGame p (B*(K+1))) :
    allocationRisk game ≤ min 1 ((B*(K+1) : Nat) * eta p) :=
  le_min (TypedFiatShamirGame.risk_le_one allocationBad game)
    (TypedFiatShamirGame.risk_bound allocationBad (eta p) (eta_nonneg p) (allocation_sparse p) game)

theorem allocation_byte_sparse (p : Profile) (r : Request p) :
    FiatShamirGame.average (fun b : Bytes r.coordinate =>
      if allocationBad r (codec r.coordinate b) then 1 else 0) ≤ eta p := by
  rw [codec_average r.coordinate (fun x => if allocationBad r x then 1 else 0)]
  exact allocation_sparse p r

/-- Profiles may change between branches/statements. Only the request tag is a
sum; the random answer is always uniform in that request's exact fiber. -/
abbrev AnyRequest := (p : Profile) × Request p
abbrev AnyAnswer (r : AnyRequest) := Answer r.2

def anyAllocationBad (r : AnyRequest) : AnyAnswer r → Prop := allocationBad r.2

theorem any_allocation_sparse (r : AnyRequest) :
    FiatShamirGame.average (fun x : AnyAnswer r => if anyAllocationBad r x then 1 else 0) ≤
      (1 / 2^79 : ℚ) :=
  (allocation_sparse r.1 r.2).trans (eta_le r.1)

theorem all_profiles_allocation_bound (B K : Nat)
    (game : TypedFiatShamirGame.Game AnyRequest AnyAnswer (B*(K+1))) :
    TypedFiatShamirGame.risk anyAllocationBad game ≤
      min 1 (((B*(K+1) : Nat) : ℚ) / 2^79) := by
  refine le_min (TypedFiatShamirGame.risk_le_one anyAllocationBad game) ?_
  have h := TypedFiatShamirGame.risk_bound anyAllocationBad (1/2^79)
    (by positivity) any_allocation_sparse game
  simpa only [mul_one_div] using h

def Prefix.ofTape {c : Config} (q : Coordinate c) (t : Tape c) : Prefix q :=
  fun r _ => get r t

theorem prefix_get {c : Config} (q r : Coordinate c) (t : Tape c)
    (past : position r < position q) :
    get r (Prefix.ofTape q t).tape = get r t := by
  change (coordinates c ((coordinates c).symm _)) r = _
  simp only [Equiv.apply_symm_apply]
  simp only [Prefix.ofTape, dite_eq_left past]

/-- Zero filling does not leak a sampled suffix: every relevant event is
identical on the actual tape and its strict prefix plus current response. -/
theorem bad_prefix (p : Profile) (s : Statement p) (strategy : Strategy)
    (q : Coordinate (config p)) (t : Tape (config p)) :
    CausalBadEvents.Bad s.input strategy q t ↔
      CausalBadEvents.Bad s.input strategy q
        (set q (Prefix.ofTape q t).tape (get q t)) := by
  apply CausalPrefix.bad_congr s.input strategy (production_config_valid p).1
  intro r hr
  by_cases same : r = q
  · subst r
    rw [get_set]
  · rw [get_set_ne q r _ _ same]
    symm
    apply prefix_get
    have ne : position r ≠ position q := fun h => same (CausalPrefix.position_injective _ h)
    omega

def requestOfTape {p : Profile} (s : Statement p) (strategy : Strategy)
    (q : Coordinate (config p)) (t : Tape (config p)) : Request p :=
  ⟨s, strategy, q, Prefix.ofTape q t⟩

/-- The parent actual-verifier cover is instantiated, not left as a soundness
assumption. The list was fixed from the initial commitment before the claims. -/
theorem accepted_false_prefix_cover (p : Profile) (s : Statement p) (strategy : Strategy)
    (t : Tape (config p)) (accepted : experiment s.input strategy t = true)
    (hfalse : ¬ ∃ w ∈ InitialCandidates.witnesses (config p) s.lanes s.root,
      ∀ claim ∈ s.claims.toList,
        dot (paddedWitness (config p) s.lanes w) claim.weight = claim.value) :
    ∃ q, allocationBad (requestOfTape s strategy q t) (get q t) := by
  obtain ⟨q, hq⟩ := InteractiveSoundness.accepted_false_cover p s.lanes s.root
    s.claims strategy t accepted hfalse
  refine ⟨q, bad_implies_allocationBad _ _ ?_⟩
  exact (bad_prefix p s strategy q t).mp hq

/-- The stacked-opening first allocation is eight field elements: gamma, six
map scalars, and lambda. There is no intermediate response or second draw. -/
structure StackInitial (p : Profile) (familyCap : Nat) where
  lanes : Nat
  root : BaseOracle
  lane_bound : lanes ≤ 2 ^ (config p).folds[0]!
  familyCount : Nat
  family : Fin familyCount → RingPCSGame.FamilyClaim
  family_bound : familyCount ≤ familyCap
  points : Array RingPCSGame.PointClaim
  claim_bound : points.size + 1 ≤ 2^64

def ringCharge (familyCap : Nat) : ℚ :=
  (2^32 : ℚ) * (((familyCap-1 : Nat) : ℚ) / 2^192 + 1/2^160)

theorem ringCharge_nonneg (familyCap : Nat) : 0 ≤ ringCharge familyCap := by
  unfold ringCharge
  positivity

theorem ringCharge_mono {a b : Nat} (h : a ≤ b) : ringCharge a ≤ ringCharge b := by
  unfold ringCharge
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add
  · apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast Nat.sub_le_sub_right h 1
  · exact le_rfl

inductive StackRequest (p : Profile) (familyCap : Nat) where
  | initial (data : StackInitial p familyCap)
  | later (request : Request p) (notInitial : request.coordinate ≠ .initial)

abbrev StackAnswer {p : Profile} {cap : Nat} : StackRequest p cap → Type
  | .initial _ => RingPCSGame.Prefix × E
  | .later r _ => Answer r

noncomputable instance {p : Profile} {cap : Nat} (r : StackRequest p cap) : Fintype (StackAnswer r) := by
  cases r <;> unfold StackAnswer <;> infer_instance

instance {p : Profile} {cap : Nat} (r : StackRequest p cap) : Nonempty (StackAnswer r) := by
  cases r <;> unfold StackAnswer <;> infer_instance

def stackBad {p : Profile} {cap : Nat} (r : StackRequest p cap) : StackAnswer r → Prop :=
  match r with
  | .initial d => RingPCSGame.InitialEvent p d.lanes d.root d.family d.points
  | .later r _ => allocationBad r

def stackEta (p : Profile) (familyCap : Nat) : ℚ := eta p + ringCharge familyCap

theorem stack_sparse (p : Profile) (cap : Nat) (r : StackRequest p cap) :
    FiatShamirGame.average (fun x : StackAnswer r => if stackBad r x then 1 else 0) ≤
      stackEta p cap := by
  cases r with
  | later r hn =>
    exact (allocation_sparse p r).trans (le_add_of_nonneg_right (ringCharge_nonneg cap))
  | initial d =>
    have hb := RingPCSGame.initial_event_probability p d.lanes d.root d.lane_bound d.family d.points
    have hi : (d.points.size : ℚ) / 2^160 =
        initialBatch (config p) (estimates (config p)) (d.points.size+1) := by
      unfold initialBatch
      rw [dite_eq_left (production_config_valid p).2.1]
      simp only [estimates, fieldSize, Nat.add_sub_cancel_right]
      norm_num
      ring
    have hp : (d.points.size : ℚ) / 2^160 ≤ eta p := by
      rw [hi]
      exact (initialBatch_mono _ d.claim_bound).trans (le_max_left _ _)
    have hr := ringCharge_mono d.family_bound
    calc
      _ = Soundness.uniformProb (Finset.univ.filter (RingPCSGame.InitialEvent p d.lanes d.root d.family d.points)) := by
        change FiatShamirGame.average (fun x : RingPCSGame.Prefix × E =>
          if RingPCSGame.InitialEvent p d.lanes d.root d.family d.points x then (1 : ℚ) else 0) = _
        simp only [FiatShamirGame.average, Soundness.uniformProb, Finset.sum_boole]
      _ ≤ ringCharge d.familyCount + (d.points.size : ℚ) / 2^160 := hb
      _ ≤ stackEta p cap := by unfold stackEta; linarith

theorem stack_allocation_bound (p : Profile) (familyCap B K : Nat)
    (game : TypedFiatShamirGame.Game (StackRequest p familyCap) StackAnswer (B*(K+1))) :
    TypedFiatShamirGame.risk stackBad game ≤
      min 1 ((B*(K+1) : Nat) * stackEta p familyCap) :=
  le_min (TypedFiatShamirGame.risk_le_one stackBad game)
    (TypedFiatShamirGame.risk_bound stackBad (stackEta p familyCap)
      (add_nonneg (eta_nonneg p) (ringCharge_nonneg familyCap)) (stack_sparse p familyCap) game)

end Whir.WHIRFiatShamir
