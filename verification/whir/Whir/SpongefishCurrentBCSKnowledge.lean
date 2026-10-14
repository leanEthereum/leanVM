import Whir.SpongefishCurrentRoundPackets
import Whir.SpongefishCurrentSourceJoinProbability
import Whir.PCSBCSSourceKnowledgeComposition
import Whir.PCSBCSChallengeOracleEnteredGames
import Whir.PCSBCSPublicPrimitiveOpening
import Whir.PCSBCSNativePhysicalMerkleBad

/-! Basic full-prefix BCS knowledge composition for the current #607 transcript (`remark:bcs-with-basic-fs` of the pinned book source). The basic variant has no hash-chain term, so the final bound `finalBound` has exactly three summands: the additive source RBR term `Q * rbrError` on the round packets, the initialized byte-mode coupling `min(1,(2Q^2-Q)/2^256)` and the complete public Merkle trace alarm `(Q^3+3Q^2-2Q)/2^256`.

The generic part holds for any packet partition and any per-coin node model with a proved conditional hazard. The module also supplies the pointwise reduction to a public good event or the Merkle alarm (`Reduction`, `reduction_union`), the ordinary output collision alarm (`collision_alarm`), the four record-binding message shapes, the deployed opening schedule and the numeric level. The current endpoint for the full source program with the opening walk is `SpongefishCurrentKnowledgeEndpoint.full_knowledge_bound`. -/
namespace Whir.SpongefishCurrentBCSKnowledge
open Concrete FiatShamirGame DuplexModeGame DuplexFraming RawOracleCoupling
open PCSBCSChallengeOracle PCSStateRestoration.Latent TypedOracleCompiler SpongefishPCSRoundFrames
set_option autoImplicit false
set_option maxRecDepth 100000

/-! ## Generic packet composition -/

section Generic
variable {Packet : Type} [Fintype Packet] [DecidableEq Packet] {Block : Packet → Type}
  [∀ x, Fintype (Block x)] {Q : Nat}
  (part : Partition (PublicCompressionCouplingMixed.Key Q) Packet Block)

/-- The compiled source program with one grouped packet allocation at first
physical disclosure, exactly as in the whole-view coupling. -/
noncomputable def source {R : Type} (iv : Digest32) (program : Program R) (counted : Counts Q program) :
    Sampling part.Key (part.Answer (D := Digest32)) (View R) Q :=
  Atomic.program part (PublicCompressionCouplingMixed.compile Q iv [] program Q (by rfl) counted)

/-- Every ideal table on which the observer fires exposes a state path from an
undoomed to a doomed state. -/
def Refines {P R : Type} (model : NodeModel part.Key (part.Answer (D := Digest32)) P)
    (iv : Digest32) (program : Program R) (counted : Counts Q program) (observe : View R → Bool) :
    Prop :=
  ∀ table, observe (Sampling.eval table (source part iv program counted)) = true →
    StatePath model table (Sampling.execute table (source part iv program counted)).2 false true

private theorem average_indicator {T : Type} [Fintype T] (test : T → Bool) :
    average (fun t => if test t then (1 : ℚ) else 0) =
      Soundness.uniformProb (Finset.univ.filter fun t => test t = true) := by
  classical
  simp only [average,Soundness.uniformProb,Finset.card_filter,Nat.cast_sum,
    Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

variable [Fintype part.Key] [DecidableEq part.Key]
  [∀ key, Fintype (part.Answer (D := Digest32) key)] [∀ key, Nonempty (part.Answer (D := Digest32) key)]

open Classical in
/-- Ideal packet experiment: at most `Q * epsilon`, for a node model chosen per attacker coin. -/
theorem ideal_bound {P AdvCoins R : Type} [Fintype AdvCoins] [Nonempty AdvCoins]
    (model : AdvCoins → NodeModel part.Key (part.Answer (D := Digest32)) P) (epsilon : ℚ)
    (nonnegative : 0 ≤ epsilon) (hazard : ∀ a, ConditionalHazard (model a) epsilon) (iv : Digest32)
    (adversary : AdvCoins → Program R) (counted : ∀ a, Counts Q (adversary a))
    (observe : View R → Bool)
    (refines : ∀ a, Refines part (model a) iv (adversary a) (counted a) observe) :
    atomicIdealProbability part iv adversary counted observe ≤ (Q : ℚ) * epsilon := by
  unfold atomicIdealProbability
  have each (a : AdvCoins) :
      Sampling.expectation (fun result => if observe result.1 then (1 : ℚ) else 0)
        (RawOracleCoupling.memo (source part iv (adversary a) (counted a)) (fun _ => none)) ≤
        (Q : ℚ) * epsilon := by
    have tableMemo := RawOracleCoupling.empty_table_eq_memo
      (source part iv (adversary a) (counted a)) (fun view => if observe view then (1 : ℚ) else 0)
    rw [← tableMemo,average_indicator]
    have bound := accepted_path_failure_probability (model a) Q 0 (source part iv (adversary a) (counted a))
      epsilon nonnegative (hazard a)
      (fun table => observe (Sampling.eval table (source part iv (adversary a) (counted a))) = true)
      (refines a)
    simp only [Nat.add_zero] at bound
    convert bound using 2
    ext t
    simp only [Finset.mem_filter]
  have summed := average_mono each
  rw [average_const] at summed
  convert summed using 1
  congr 1
  funext a
  unfold source
  congr 2 <;> exact Subsingleton.elim _ _

/-- Real primitive experiment: ideal packet bound plus the whole-view coupling, for a node model chosen per attacker coin. -/
theorem real_bound {P AdvCoins R : Type} [Fintype AdvCoins] [Nonempty AdvCoins]
    (model : AdvCoins → NodeModel part.Key (part.Answer (D := Digest32)) P) (epsilon : ℚ)
    (nonnegative : 0 ≤ epsilon) (hazard : ∀ a, ConditionalHazard (model a) epsilon) (iv : Digest32)
    (adversary : AdvCoins → Program R) (counted : ∀ a, Counts Q (adversary a))
    (observe : View R → Bool)
    (refines : ∀ a, Refines part (model a) iv (adversary a) (counted a) observe) :
    realProbability iv adversary observe ≤ (Q : ℚ) * epsilon + duplexModeLoss Q := by
  have coupling := actual_source_atomic_game_bound part iv adversary counted observe
  have deviation := (abs_le.mp coupling).2
  have ideal := ideal_bound part model epsilon nonnegative hazard iv adversary counted observe refines
  linarith

end Generic

/-! ## Complete public Merkle trace alarm for an arbitrary root policy -/

noncomputable def merkleProbability {Coins R : Type} [Fintype Coins] {Q : Nat}
    (roots : PublicMerkleProbability.RootPolicy) (iv : Digest32)
    (adversary : Coins → Program R) (counted : ∀ coins, Counts Q (adversary coins)) : ℚ :=
  average fun coins => average fun C : PrimitiveOracle =>
    if PublicMerkleProbability.traceAlarm roots []
      (PublicCompressionProgram.primitiveLog C iv (adversary coins) Q (counted coins)) then 1 else 0

theorem merkle_bound {Coins R : Type} [Fintype Coins] [Nonempty Coins] {Q : Nat}
    (roots : PublicMerkleProbability.RootPolicy)
    (rootCap : ∀ log : PublicMerkleLog.PublicLog, log.length ≤ Q → (roots log).card ≤ Q*(Q+1))
    (iv : Digest32) (adversary : Coins → Program R) (counted : ∀ coins, Counts Q (adversary coins)) :
    merkleProbability roots iv adversary counted ≤ ((Q : ℚ)^3+3*(Q : ℚ)^2-2*(Q : ℚ))/2^256 := by
  unfold merkleProbability
  have each (coins : Coins) := PublicMerkleProbability.random_compression_bound roots Q (Q*(Q+1))
    rootCap (PublicCompressionProgram.compile iv (adversary coins) Q (counted coins))
  simp only [PublicMerkleProbability.alarm_trace] at each
  have bound := average_mono each
  rw [average_const,PCSBCSActualMerkleBound.exact_merkle_loss] at bound
  exact bound

/-- Pointwise reduction of an arbitrary real event to the public good event or
the complete Merkle trace alarm. -/
def Reduction {Coins R : Type} {Q : Nat} (roots : PublicMerkleProbability.RootPolicy) (iv : Digest32)
    (adversary : Coins → Program R) (counted : ∀ coins, Counts Q (adversary coins))
    (event : PrimitiveOracle → Coins → Prop) (good : View R → Bool) : Prop :=
  ∀ C coins, event C coins →
    good (runReal C iv (adversary coins)).view = true ∨
    PublicMerkleProbability.traceAlarm roots []
      (PublicCompressionProgram.primitiveLog C iv (adversary coins) Q (counted coins)) = true

open Classical in
theorem reduction_union {Coins R : Type} [Fintype Coins] [Nonempty Coins] {Q : Nat}
    (roots : PublicMerkleProbability.RootPolicy) (iv : Digest32)
    (adversary : Coins → Program R) (counted : ∀ coins, Counts Q (adversary coins))
    (event : PrimitiveOracle → Coins → Prop) (good : View R → Bool)
    (reduction : Reduction roots iv adversary counted event good) :
    average (fun coins : PrimitiveOracle × Coins => if event coins.1 coins.2 then (1 : ℚ) else 0) ≤
      realProbability iv adversary good + merkleProbability roots iv adversary counted := by
  unfold realProbability
  rw [distinguish_average (inferInstance : Fintype (PrimitiveOracle × Coins))]
  simp only [WHIRObservableSecurity.average_product]
  rw [RawOracleCoupling.average_comm (X := PrimitiveOracle) (Y := Coins),
    RawOracleCoupling.average_comm (X := PrimitiveOracle) (Y := Coins)]
  unfold merkleProbability
  rw [← average_add]
  apply average_mono
  intro coins
  rw [← average_add]
  apply average_mono
  intro C
  by_cases happened : event C coins
  · rcases reduction C coins happened with publicGood | alarm
    · simp only [happened,publicGood,↓reduceIte]
      split <;> norm_num
    · simp only [happened,alarm,↓reduceIte]
      split <;> norm_num
  · simp only [happened,↓reduceIte]
    split <;> split <;> norm_num

/-- Any program: an ordinary output collision in the PUBLIC log of the real view
raises the complete primitive trace alarm, for every root policy. The historical
packet partition is used only as a proof device; it is not part of the claim. -/
theorem collision_alarm {R : Type} (C : PrimitiveOracle) (iv : Digest32) (program : Program R)
    (Q : Nat) (counted : Counts Q program) (roots : PublicMerkleProbability.RootPolicy)
    (collision : PublicMerkleLog.OutputCollision
      (PCSBCSPublicPrimitiveOpening.publicOrdinaryLog Q iv (runReal C iv program).view)) :
    PublicMerkleProbability.traceAlarm roots []
      (PublicCompressionProgram.primitiveLog C iv program Q counted) = true := by
  have ordinary := PCSBCSPublicPrimitiveOpening.publicOrdinaryLog_actual
    (p := (⟨0,by decide⟩,⟨0,by decide⟩)) (iv := iv) (boundary := 0)
    C (WHIRRealSimulator.rawTable Q C) program Q (le_refl Q) counted
  simp only [Atomic.eval_program,Partition.join_split] at ordinary
  have view : Sampling.eval (PublicCompressionCouplingMixed.oracle C (WHIRRealSimulator.rawTable Q C))
      (PublicCompressionCouplingMixed.compile Q iv [] program Q (le_refl Q) counted) =
      (runReal C iv program).view := by
    rw [PublicCompressionCouplingMixed.compile_actual]
    exact WHIRRealSimulator.runIdeal_view C iv _ ⟨rfl,by simp⟩ _ _ (le_refl Q) _
  rw [view] at ordinary
  rw [ordinary] at collision
  exact PCSBCSNativePhysicalMerkleBad.mixed_atomic_collision_alarm
    (p := (⟨0,by decide⟩,⟨0,by decide⟩)) (boundary := 0) C iv program Q (le_refl Q) counted roots
    collision

/-- The three explicit summands of the current endpoint. -/
def finalBound (Q : ℚ) : ℚ :=
  Q * ((17/32 : ℚ)^56 + 1/2^78) + min 1 ((2*Q^2-Q)/2^256) + (Q^3+3*Q^2-2*Q)/2^256

/-! ## Every record-binding message shape -/

/-- Literal binding read calls of a record with `packs` normalized pending E. -/
def bindingCalls (shape : AnchoredHeaderCodec.Shape) (packs : Nat) : List Call :=
  List.replicate 3 (.read .scalar) ++ [.read .root,.read .root] ++ List.replicate 2 (.read .scalar) ++
    List.replicate packs (.read .scalar) ++ List.replicate shape.logN (.read .scalar) ++ [.read .scalar]

theorem messageCalls_binding (r : SpongefishSessionAdapter.Record)
    (pointLength : r.point.length = r.shape.logN) :
    SpongefishCurrentAcceptedJoin.messageCalls r =
      bindingCalls r.shape ((r.context.pending.length+23)/24) := by
  simp only [SpongefishCurrentAcceptedJoin.messageCalls,SpongefishRecordBindingParser.messages,
    SpongefishRecordBindingParser.scalarMessages,List.map_append,List.map_map,List.map_cons,
    List.map_nil,bindingCalls,SpongefishSessionAdapter.constants,SpongefishSessionAdapter.contextScalars,
    SpongefishSessionAdapter.pendingPacks,Function.comp_def,List.map_const',List.length_ofFn,
    pointLength]
  rfl

/-- The received record of an accepted caller path has at most three pending packs. -/
theorem accepted_packs (c : DuplexRefinement.Compression) (iv : Digest32)
    (tag instanceBytes narg : List Byte) (hints : List (List Byte))
    (layout : WHIRCallerClaims.CallerLayout) (before : List Call)
    (r : SpongefishSessionAdapter.Record) (initial pre received : Cursor)
    (setup : SpongefishCurrentObservedSessionEntry.actualSetup c iv tag instanceBytes narg hints =
      some initial)
    (preRun : SpongefishCurrentPrimitiveEventCompiler.actualReplay c initial before = .ok pre)
    (receivedEq : SpongefishCurrentCommitmentReceive.receive c pre
      (AnchoredSourceCaller.shape layout) = some (received,r)) :
    (r.context.pending.length+23)/24 < 4 ∧ r.point.length = r.shape.logN := by
  obtain ⟨shapeEq,contextEq,pointLength,_⟩ :=
    SpongefishCurrentCommitmentReceive.receive_retains c pre received _ r receivedEq
  have bounded := SpongefishCurrentAcceptedJoin.actualReplay_bounded c before initial pre
    (SpongefishCurrentAcceptedJoin.setup_bounded c iv tag instanceBytes narg hints initial setup) preRun
  have pendingBound : r.context.pending.length ≤ 64 := by
    rw [contextEq]
    simpa [SpongefishSessionAdapter.capture] using bounded
  refine ⟨by omega,?_⟩
  rw [shapeEq]
  exact pointLength

/-! ## Concrete level from the deployed parameters -/

/-- For every aggregate budget up to `2^64` primitive-work units the complete
bound is at most `Q / 2^51`: each unit of attacker plus verifier work buys at
most `2^-51` knowledge error, with no proof-of-work credit. -/
theorem finalBound_le (Q : ℚ) (positive : 0 ≤ Q) (cap : Q ≤ 2^64) : finalBound Q ≤ Q / 2^51 := by
  unfold finalBound
  have square : Q^2 ≤ 2^64 * Q := by nlinarith
  have cube : Q^3 ≤ 2^128 * Q := by nlinarith
  have coupling : min 1 ((2*Q^2-Q)/2^256) ≤ (2*Q^2-Q)/2^256 := min_le_right _ _
  have numeric : (17/32 : ℚ)^56 + 1/2^78 + 2*2^64/2^256 + (2^128+3*2^64)/2^256 ≤ 1/2^51 := by
    norm_num
  nlinarith

/-- Concrete levels: `2^20` units give at most `2^-31`, `2^40` units at most `2^-11`. -/
theorem finalBound_levels :
    finalBound (2^20) ≤ 1/2^31 ∧ finalBound (2^40) ≤ 1/2^11 := by
  constructor
  · have h := finalBound_le (2^20) (by norm_num) (by norm_num)
    calc finalBound (2^20) ≤ 2^20/2^51 := h
      _ = 1/2^31 := by norm_num
  · have h := finalBound_le (2^40) (by norm_num) (by norm_num)
    calc finalBound (2^40) ≤ 2^40/2^51 := h
      _ = 1/2^11 := by norm_num

/-- Deployed query grinding: `QUERY_GRINDING_BITS = 17` at every level. -/
def deployedGrinding (p : ParameterBounds.Profile) : Fin (ParameterBounds.config p).folds.size → Fin 64 :=
  fun _ => ⟨17,by decide⟩

deriving instance DecidableEq for WireKind
deriving instance DecidableEq for Call

/-- The predecessor's literal current source loop layout for a configuration. -/
def boundaryOf (c : Protocol.Config) (grinding : Nat → Fin 64) (i : Nat) : Boundary :=
  ⟨CausalGame.remaining c i,CausalGame.oodCount c i,CausalGame.remaining c i + c.rates[i]!,
    c.queries[i]!,grinding i⟩

def layoutOf (c : Protocol.Config) (grinding : Nat → Fin 64) : OpeningLayout where
  initialRounds := c.folds[0]!
  firstBoundary := boundaryOf c grinding 0
  intermediate := (List.range (c.folds.size - 2)).map fun k =>
    (c.folds[k+1]!,boundaryOf c grinding (k+1))
  finalFoldRounds := c.folds[c.folds.size - 1]!
  residualDimension := CausalGame.remaining c (c.folds.size - 1)
  finalDepth := CausalGame.remaining c (c.folds.size - 1) + c.rates[c.folds.size - 1]!
  finalCount := c.queries[c.folds.size - 1]!
  finalGrinding := grinding (c.folds.size - 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel computation for all 56 production profiles at the deployed grinding:
the per-coordinate opening call list is exactly the separately inspected
current source loop layout `SpongefishPCSRoundFrames.OpeningLayout.schedule`. -/
theorem deployed_schedule : ∀ p : ParameterBounds.Profile,
    SpongefishCurrentOpeningAcceptance.openingCalls (p := p) (deployedGrinding p) =
      (layoutOf (ParameterBounds.config p) (fun _ => ⟨17,by decide⟩)).schedule := by
  decide +kernel

/-- Consequently any two verifier draws of the deployed opening are separated
by a nonempty canonical prover payload. -/
theorem deployed_opening_between (p : ParameterBounds.Profile) (pre middle suffix : List Call)
    (first second : Group)
    (scheduled : SpongefishCurrentOpeningAcceptance.openingCalls (p := p) (deployedGrinding p) =
      pre ++ (Call.draw first :: (middle ++ Call.draw second :: suffix))) :
    ∃ kind, Call.read kind ∈ middle ∧ ∀ value : kind.Value, kind.codec.bytes value ≠ [] := by
  rw [deployed_schedule p] at scheduled
  exact SpongefishCurrentRoundSeparation.opening_between _ pre middle suffix first second scheduled

#print axioms ideal_bound
#print axioms real_bound
#print axioms merkle_bound
#print axioms reduction_union
#print axioms finalBound_le
#print axioms finalBound_levels
#print axioms collision_alarm
#print axioms messageCalls_binding
#print axioms deployed_schedule
#print axioms deployed_opening_between

end Whir.SpongefishCurrentBCSKnowledge
