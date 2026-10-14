import Whir.PCSBCSNativeSourceFailure
import Whir.PCSBCSAtomicAllocationTrace
import Whir.PCSBCSConstructionReplayTrace
import Whir.WHIRRealSimulator
import Whir.PCSBCSActualMerkleBound

/-! Historical pre-#607 native physical trace joins. The chosen real raw table
is a deterministic realization, not an independent random oracle. Every
retained opening plan is included in the complete source compression trace.
The global allocation-log collision is included in the very same causal alarm;
it must not be silently identified with a frozen extracted-row mismatch.
The first shape-address/scanner-admission join is deliberately not assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Whir.PCSBCSNativePhysicalMerkleBad
open Concrete Protocol FiatShamirGame DuplexFraming DuplexModeGame TypedOracleCompiler
open RawOracleCoupling PCSBCSChallengeOracle PCSBCSSourceRootCapture
open PublicMerkleLog PublicCompressionProgram
open MerkleTransport MerkleTransport.Commitments
open MerkleBinding

private theorem execute_mixed_map {B n : Nat} {R S : Type}
    (oracle : PublicCompressionCouplingMixed.Key B → Digest32) (f : R → S)
    (program : PublicCompressionCouplingMixed.Computation B R n) :
    (Sampling.execute oracle (PublicCompressionCouplingMixed.Computation.map f program)).2 =
      (Sampling.execute oracle program).2 := by
  induction program with
  | ret => rfl
  | draw key next ih => simp only [PublicCompressionCouplingMixed.Computation.map,Sampling.execute,ih]

/-- A fallback seed draw comes from an actual direct primitive observation.
This holds for arbitrary mixed raw answers and arbitrary initial public logs. -/
theorem mixed_seed_origin {R : Type} (B : Nat) (seed : DuplexPublicSimulator.Seed)
    (ro : RawKey B → Digest32) (iv : Digest32) (log : PublicLog)
    (program : Program R) (remaining : Nat) (limit : remaining ≤ B)
    (counted : Counts remaining program) (n : Node) (d : Digest32)
    (recorded : (⟨.inl n,d⟩ : Sigma (fun _ : PublicCompressionCouplingMixed.Key B => Digest32)) ∈
      (Sampling.execute (PublicCompressionCouplingMixed.oracle seed ro)
        (PublicCompressionCouplingMixed.compile B iv log program remaining limit counted)).2) :
    ∃ purpose, (⟨.primitive purpose n,d⟩ : Observation) ∈
      (Sampling.eval (PublicCompressionCouplingMixed.oracle seed ro)
        (PublicCompressionCouplingMixed.compile B iv log program remaining limit counted)).observations := by
  induction program generalizing log remaining with
  | done value => simp [PublicCompressionCouplingMixed.compile,Sampling.execute] at recorded
  | ask query next ih =>
    cases query with
    | primitive purpose input =>
      simp only [PublicCompressionCouplingMixed.compile,Sampling.execute_pad,Sampling.execute_bind,
        execute_mixed_map,List.mem_append] at recorded
      rcases recorded with first | later
      · unfold PublicCompressionCouplingMixed.primitiveCalls at first
        cases hit : DuplexPublicSimulator.lookup log input with
        | some answer => simp [hit,Sampling.execute] at first
        | none =>
          cases key : DuplexPublicSimulator.privateKey B log input with
          | some raw => simp [hit,key,Sampling.execute] at first
          | none =>
            simp only [hit,key,Sampling.execute,List.mem_cons,List.not_mem_nil,or_false] at first
            cases first
            refine ⟨purpose,?_⟩
            simp [PublicCompressionCouplingMixed.compile,Sampling.eval_pad,Sampling.eval_bind,
              PublicCompressionCouplingMixed.primitiveCalls,hit,key,
              PublicCompressionCouplingMixed.Computation.eval_map,DuplexRawProgram.observe,
              PublicCompressionCouplingMixed.oracle,Sampling.eval]
      · obtain ⟨found,member⟩ := ih _ _ _ _ (counted.2 _) later
        refine ⟨found,?_⟩
        simp only [PublicCompressionCouplingMixed.compile,Sampling.eval_pad,Sampling.eval_bind,
          PublicCompressionCouplingMixed.Computation.eval_map,DuplexRawProgram.observe]
        exact List.mem_cons_of_mem _ member
    | construction coordinate valid =>
      simp only [PublicCompressionCouplingMixed.compile,Sampling.execute_pad,Sampling.execute,
        execute_mixed_map,List.mem_cons] at recorded
      rcases recorded with impossible | later
      · cases impossible
      · obtain ⟨purpose,member⟩ := ih _ log _ _ (counted.2 _) later
        refine ⟨purpose,?_⟩
        simp only [PublicCompressionCouplingMixed.compile,Sampling.eval_pad,Sampling.eval,
          PublicCompressionCouplingMixed.Computation.eval_map,DuplexRawProgram.observe]
        exact List.mem_cons_of_mem _ member

section Allocation
variable {p : ParameterBounds.Profile} {B : Nat} {iv : Digest32} {boundary : Nat}
local notation "part" => EnteredPacket.partition (p := p) (Q := B) (iv := iv) (boundary := boundary)

private theorem allocation_ordinary (seed : DuplexPublicSimulator.Seed) (ro : RawKey B → Digest32)
    (raw : PublicCompressionCouplingMixed.Key B) (record : Node × Digest32)
    (member : record ∈ ordinaryRecord
      (PCSBCSAtomicAllocationTrace.allocation part
        ((part).split (PublicCompressionCouplingMixed.oracle seed ro)) raw)) :
    ∃ n, raw = .inl n ∧ record = (n,seed n) := by
  cases raw with
  | inl n =>
    unfold PCSBCSAtomicAllocationTrace.allocation at member
    split at member
    · rename_i block found
      have impossible := (part).encode_recognize (.inl n) block found
      cases impossible
    · simp only [ordinaryRecord,Partition.split,PublicCompressionCouplingMixed.oracle,List.mem_singleton] at member
      exact ⟨n,rfl,member⟩
  | inr key =>
    unfold PCSBCSAtomicAllocationTrace.allocation at member
    split at member <;> simp [ordinaryRecord] at member

private theorem execute_answers {Key R : Type} {n : Nat} (oracle : Key → Digest32)
    (program : Sampling Key (fun _ => Digest32) R n)
    (event : Sigma (fun _ : Key => Digest32))
    (member : event ∈ (Sampling.execute oracle program).2) : event.2 = oracle event.1 := by
  induction program with
  | ret => simp [Sampling.execute] at member
  | draw key next ih =>
    rcases List.mem_cons.mp member with equal | later
    · cases equal; rfl
    · exact ih (oracle key) later

/-- Ordinary grouped records have literal seed-draw provenance; atomic packet
allocation cannot fabricate a primitive hash record. -/
theorem atomic_ordinary_origin {R : Type} {n : Nat}
    (seed : DuplexPublicSimulator.Seed) (ro : RawKey B → Digest32)
    (program : Sampling (PublicCompressionCouplingMixed.Key B) (fun _ => Digest32) R n)
    (record : Node × Digest32)
    (member : record ∈ ordinaryPrefix (Sampling.execute
      ((part).split (PublicCompressionCouplingMixed.oracle seed ro)) (Atomic.program part program)).2) :
    (⟨.inl record.1,record.2⟩ : Sigma (fun _ : PublicCompressionCouplingMixed.Key B => Digest32)) ∈
      (Sampling.execute (PublicCompressionCouplingMixed.oracle seed ro) program).2 := by
  rw [PCSBCSAtomicAllocationTrace.execute_program,Partition.join_split] at member
  obtain ⟨event,present,ordinary⟩ :=
    (PCSBCSNativeCapturedLogs.ordinaryPrefix_membership _ record).mp member
  obtain ⟨raw,rawPresent,same⟩ := List.mem_map.mp present
  subst event
  obtain ⟨input,equal,recordEqual⟩ := allocation_ordinary seed ro raw.1 record ordinary
  have authentic : raw.2 = PublicCompressionCouplingMixed.oracle seed ro raw.1 :=
    execute_answers _ program raw rawPresent
  have same : (⟨.inl record.1,record.2⟩ : Sigma (fun _ : PublicCompressionCouplingMixed.Key B => Digest32)) = raw := by
    rcases raw with ⟨key,answer⟩
    dsimp only at equal authentic
    subst key
    subst record
    change answer = seed input at authentic
    cases authentic
    rfl
  exact same ▸ rawPresent
end Allocation

/-- Whole attacker-plus-verifier programs are supported here, not just the
native suffix. The chosen raw table and every full-path call belong to the
same primitive C. No allocation/physical-trace identity is supplied. -/
theorem mixed_atomic_ordinary_subset {p : ParameterBounds.Profile} {B boundary : Nat}
    {R : Type} (C : PrimitiveOracle) (iv : Digest32)
    (program : Program R) (A : Nat) (limit : A ≤ B) (counted : Counts A program) :
    let part := EnteredPacket.partition (p := p) (Q := B) (iv := iv) (boundary := boundary)
    ∀ record ∈ ordinaryPrefix (Sampling.execute
      (part.split (PublicCompressionCouplingMixed.oracle C (WHIRRealSimulator.rawTable B C)))
      (Atomic.program part (PublicCompressionCouplingMixed.compile B iv [] program A limit counted))).2,
      record ∈ primitiveLog C iv program A counted := by
  dsimp only
  intro record member
  have raw := atomic_ordinary_origin C (WHIRRealSimulator.rawTable B C)
    (PublicCompressionCouplingMixed.compile B iv [] program A limit counted) record member
  obtain ⟨purpose,observed⟩ := mixed_seed_origin B C (WHIRRealSimulator.rawTable B C)
    iv [] program A limit counted record.1 record.2 raw
  have realView :
      Sampling.eval (PublicCompressionCouplingMixed.oracle C (WHIRRealSimulator.rawTable B C))
        (PublicCompressionCouplingMixed.compile B iv [] program A limit counted) =
        (runReal C iv program).view := by
    rw [PublicCompressionCouplingMixed.compile_actual]
    exact WHIRRealSimulator.runIdeal_view C iv _ ⟨rfl,by simp⟩ _ _ limit _
  rw [realView] at observed
  have included := PCSBCSConstructionReplayTrace.observation_trace_membership C iv
    program A counted _ observed
  have answer := PCSBCSConstructionReplayTrace.observation_answer C iv program _ observed
  change record.2 = C record.1 at answer
  apply included record
  change record ∈ [(record.1,C record.1)]
  exact List.mem_singleton.mpr (Prod.ext rfl answer)

/-- One shared monitor covers global ordinary-allocation collisions, including
collisions unrelated to any returned row. This is pointwise, not a probability
certificate or a converse to `extraction_bad_opening_bad`. -/
theorem mixed_atomic_collision_alarm {p : ParameterBounds.Profile} {B boundary : Nat}
    {R : Type} (C : PrimitiveOracle) (iv : Digest32)
    (program : Program R) (A : Nat) (limit : A ≤ B) (counted : Counts A program)
    (roots : PublicMerkleProbability.RootPolicy) :
    let part := EnteredPacket.partition (p := p) (Q := B) (iv := iv) (boundary := boundary)
    OutputCollision (ordinaryPrefix (Sampling.execute
      (part.split (PublicCompressionCouplingMixed.oracle C (WHIRRealSimulator.rawTable B C)))
      (Atomic.program part (PublicCompressionCouplingMixed.compile B iv [] program A limit counted))).2) →
    PublicMerkleProbability.traceAlarm roots [] (primitiveLog C iv program A counted) = true := by
  dsimp only
  intro bad
  by_contra loud
  have quiet := Bool.eq_false_iff.mpr loud
  have collision := PublicMerkleProbability.collision_mono
    (mixed_atomic_ordinary_subset (p := p) (boundary := boundary) C iv program A limit counted) bad
  have clean := PublicMerkleProbability.traceAlarm_clean C roots [] _
    (by intro n d h; cases h) (primitiveLog_authentic C iv program A counted)
    (by rintro ⟨a,b,d,h,_⟩; cases h) quiet
  apply clean
  apply PublicMerkleProbability.collision_mono _ collision
  exact fun _ member => List.mem_append_left _ (List.mem_reverse.mpr member)


/-- Literal first-shape-address captures are physically observed records, even
for an enclosing attacker-plus-verifier program. This is not yet saturation of
the freeze boundary or scanner root admission. -/
theorem sourceLog_physical_subset {p : ParameterBounds.Profile} {B boundary : Nat}
    {R : Type} (C : PrimitiveOracle) (iv : Digest32)
    (program : Program R) (A : Nat) (limit : A ≤ B) (counted : Counts A program)
    (address : PCSBCSSourceRootCapture.Key (p := p) (Q := B) (iv := iv) (boundary := boundary) →
      List PCSBCSSourceRootReferences.Reference) (ref : PCSBCSSourceRootReferences.Reference) :
    let part := EnteredPacket.partition (p := p) (Q := B) (iv := iv) (boundary := boundary)
    ∀ record ∈ PCSBCSCapturedNativeReplyBridge.sourceLog address ref
      (Atomic.program part (PublicCompressionCouplingMixed.compile B iv [] program A limit counted))
      (part.split (PublicCompressionCouplingMixed.oracle C (WHIRRealSimulator.rawTable B C))),
      record ∈ primitiveLog C iv program A counted := by
  dsimp only
  intro record member
  apply mixed_atomic_ordinary_subset (p := p) (boundary := boundary) C iv program A limit counted
  exact PCSBCSNativeCapturedLogs.sourceLog_subset address ref _ _ record member

/-- Excluding the one complete-trace causal alarm makes EVERY actual frozen
shape-address log clean. No per-reference union bound or row mismatch is used. -/
theorem sourceLog_clean_of_alarm {p : ParameterBounds.Profile} {B boundary : Nat}
    {R : Type} (C : PrimitiveOracle) (iv : Digest32)
    (program : Program R) (A : Nat) (limit : A ≤ B) (counted : Counts A program)
    (address : PCSBCSSourceRootCapture.Key (p := p) (Q := B) (iv := iv) (boundary := boundary) →
      List PCSBCSSourceRootReferences.Reference) (ref : PCSBCSSourceRootReferences.Reference)
    (roots : PublicMerkleProbability.RootPolicy)
    (quiet : PublicMerkleProbability.traceAlarm roots [] (primitiveLog C iv program A counted) = false) :
    let part := EnteredPacket.partition (p := p) (Q := B) (iv := iv) (boundary := boundary)
    ¬ OutputCollision (PCSBCSCapturedNativeReplyBridge.sourceLog address ref
      (Atomic.program part (PublicCompressionCouplingMixed.compile B iv [] program A limit counted))
      (part.split (PublicCompressionCouplingMixed.oracle C (WHIRRealSimulator.rawTable B C)))) := by
  dsimp only
  intro bad
  have global := PCSBCSNativeCapturedLogs.sourceLog_collision address ref _ _ bad
  have alarm := mixed_atomic_collision_alarm (p := p) (boundary := boundary)
    C iv program A limit counted roots global
  rw [quiet] at alarm
  cases alarm

/-- A retained actual real opening's full ordinary plans are in the actual
complete program, even when that program has an adversarial prefix. -/
theorem observed_complete_evaluated {p : ParameterBounds.Profile} {lanes : Nat}
    {proofs : Array PrunedMerklePaths} {R : Type}
    (C : PrimitiveOracle) (iv : Digest32) (program : Program R)
    (A : Nat) (counted : Counts A program) (opening : WHIRPhysicalVerifier.QueryOpening p)
    (observed : WHIRPhysicalOpeningRuns.ObservedOpening lanes proofs
      (runReal C iv program).view.observations opening) :
    ∀ path ∈ opening.result.paths, ∀ bytes ∈ path.opening.inputs (hashing (hash C)),
      bytes.length < 2^56 ∧ ∀ event ∈ PublicMerkleLog.plan C bytes,
        event ∈ primitiveLog C iv program A counted := by
  have answers := fun o h => PCSBCSConstructionReplayTrace.observation_answer C iv program o h
  intro path member bytes input
  obtain ⟨bound,evaluated⟩ := WHIRPhysicalSoundness.observed_evaluated
    observed C iv answers path member bytes input
  refine ⟨bound,?_⟩
  intro event present
  have actual := evaluated event present
  have included := PCSBCSConstructionReplayTrace.observation_trace_membership C iv
    program A counted _ actual
  have answer := PCSBCSConstructionReplayTrace.observation_answer C iv program _ actual
  change event.2 = C event.1 at answer
  apply included event
  change event ∈ [(event.1,C event.1)]
  exact List.mem_singleton.mpr (Prod.ext rfl answer)

/-- Fixed-height raw paths hash the FULL zero-prefixed leaf image, before any
source occupied-lane projection. The actual decoder and geometry are retained. -/
theorem observed_complete_geometry {p : ParameterBounds.Profile} {lanes : Nat}
    {proofs : Array PrunedMerklePaths} {R : Type}
    (C : PrimitiveOracle) (iv : Digest32) (program : Program R)
    (opening : WHIRPhysicalVerifier.QueryOpening p)
    (observed : WHIRPhysicalOpeningRuns.ObservedOpening lanes proofs
      (runReal C iv program).view.observations opening) :
    ∀ path ∈ opening.result.paths, ∃ row : List K,
      row.length = (if opening.level.val = 0 then lanes else WHIRPhysicalVerifier.leafWords p opening.level.val) ∧
      path.leafData = leafImage 0 (WHIRPhysicalVerifier.leafWords p opening.level.val) row ∧
      path.leafData.length = WHIRPhysicalVerifier.leafWords p opening.level.val ∧
      path.path.length = (ParameterBounds.length (ParameterBounds.config p) opening.level.val).log2 ∧
      path.root (hash C) = opening.root := by
  have answers := fun o h => PCSBCSConstructionReplayTrace.observation_answer C iv program o h
  obtain ⟨proof,_,accepted,_⟩ := observed.real C iv answers
  have opened := (WHIRPhysicalVerifier.openRows_real_accepted C iv proof opening.root
    (ParameterBounds.length (ParameterBounds.config p) opening.level.val)
    (WHIRPhysicalVerifier.queryIndices p opening.level opening.sample)
    (if opening.level.val = 0 then lanes else WHIRPhysicalVerifier.leafWords p opening.level.val)
    (WHIRPhysicalVerifier.leafWords p opening.level.val) (opening.level.val == 0)
    opening.result accepted).1
  have refined := open_refines _ _ _ _ _ _ _ _ opened
  intro path member
  obtain ⟨q,_,row,_,width,_,image,full,height,root⟩ := forall₂_mem_right refined member
  exact ⟨row,width,image,full,height,root⟩

section Driver
variable (cap : Nat) (model : WHIRCallerSupport.ProductionLayout)
    (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q : Nat)
    (packet : RawWHIRKeys.Packet ctx Q) (saved : AnchoredHeaderCodec.Record)
    (proofs : Array PrunedMerklePaths)

abbrev completeProgram := WHIRSourceChronology.compile
  (AnchoredPhysicalDriver.verifySource cap .fresh model ctx stack Q packet saved proofs)

/-- All source, caller and verifier calls, charged at their actual full-path
source budget. The packet ancestry cap Q is not this compression budget. -/
theorem actualCounts : Counts (WHIRPhysicalVerifier.sourceBudget ctx Q packet)
    (completeProgram cap model ctx stack Q packet saved proofs) :=
  (WHIRSourceChronology.compile_counted _ _).mpr
    (AnchoredPhysicalDriver.verifySource_counted cap .fresh model ctx stack Q packet saved proofs)

def completeTrace (C : PrimitiveOracle) : PublicLog :=
  primitiveLog C ctx.iv (completeProgram cap model ctx stack Q packet saved proofs)
    (WHIRPhysicalVerifier.sourceBudget ctx Q packet)
    (actualCounts cap model ctx stack Q packet saved proofs)

theorem completeTrace_authentic (C : PrimitiveOracle) :
    AuthenticLog C (completeTrace cap model ctx stack Q packet saved proofs C) :=
  primitiveLog_authentic C _ _ _ _

variable (B : Nat) (limit : WHIRPhysicalVerifier.sourceBudget ctx Q packet ≤ B)
    (C : PrimitiveOracle)

/-- Chosen real table realization for the SAME actual complete source. -/
theorem mixedView_real :
    AnchoredMixedIdealSourceAcceptance.mixedView cap .fresh model ctx stack Q packet saved proofs
      ctx.iv B limit C (WHIRRealSimulator.rawTable B C) =
      (runReal C ctx.iv (completeProgram cap model ctx stack Q packet saved proofs)).view := by
  unfold AnchoredMixedIdealSourceAcceptance.mixedView
  rw [PublicCompressionCouplingMixed.compile_actual]
  exact WHIRRealSimulator.runIdeal_view C ctx.iv _ ⟨rfl,by simp⟩ _ _ limit _

/-- Every actual allocation ordinary record belongs to the COMPLETE primitive
trace, including hidden construction calls and verifier compression calls. -/
theorem wholeLog_subset :
    ∀ record ∈ PCSBCSNativeCapturedLogs.wholeLog cap model ctx stack Q packet saved proofs B limit C
      (WHIRRealSimulator.rawTable B C),
      record ∈ completeTrace cap model ctx stack Q packet saved proofs C := by
  intro record member
  unfold PCSBCSNativeCapturedLogs.wholeLog PCSBCSCapturedIdealNativeAcceptance.allocationProgram
    PCSBCSCapturedIdealNativeAcceptance.table at member
  exact mixed_atomic_ordinary_subset (p := packet.val.profile)
    (boundary := (RawWHIRKeys.entry ctx packet.val).frames.length) C ctx.iv
    (completeProgram cap model ctx stack Q packet saved proofs) _ limit
    (actualCounts cap model ctx stack Q packet saved proofs) record member

theorem wholeLog_collision
    (bad : OutputCollision (PCSBCSNativeCapturedLogs.wholeLog cap model ctx stack Q packet saved proofs
      B limit C (WHIRRealSimulator.rawTable B C))) :
    OutputCollision (completeTrace cap model ctx stack Q packet saved proofs C) :=
  PublicMerkleProbability.collision_mono
    (wholeLog_subset cap model ctx stack Q packet saved proofs B limit C) bad

/-- The global clean case uses the SAME causal alarm as frozen openings, with no
extra union term. This does not assert a collision causes a row mismatch. -/
theorem wholeLog_clean_of_alarm (roots : PublicMerkleProbability.RootPolicy)
    (quiet : PublicMerkleProbability.traceAlarm roots []
      (completeTrace cap model ctx stack Q packet saved proofs C) = false) :
    ¬ OutputCollision (PCSBCSNativeCapturedLogs.wholeLog cap model ctx stack Q packet saved proofs
      B limit C (WHIRRealSimulator.rawTable B C)) := by
  intro bad
  have collision := wholeLog_collision cap model ctx stack Q packet saved proofs B limit C bad
  have clean := PublicMerkleProbability.traceAlarm_clean C roots []
    (completeTrace cap model ctx stack Q packet saved proofs C)
    (by intro n d h; cases h)
    (completeTrace_authentic cap model ctx stack Q packet saved proofs C)
    (by rintro ⟨a,b,d,h,_⟩; cases h) quiet
  apply clean
  apply PublicMerkleProbability.collision_mono _ collision
  intro event member
  exact List.mem_append_left _ (List.mem_reverse.mpr member)

/-- Genuine retained opener subruns from the actual native success. -/
theorem real_success_observed (a : AnchoredPhysicalDriver.Accepted ctx Q cap packet saved)
    (success : (runReal C ctx.iv (completeProgram cap model ctx stack Q packet saved proofs)).view.result.value = some a) :
    ∀ opening ∈ a.wire.openings,
      WHIRPhysicalOpeningRuns.ObservedOpening saved.shape.lanes proofs
        (runReal C ctx.iv (completeProgram cap model ctx stack Q packet saved proofs)).view.observations opening := by
  have run := WHIRPhysicalCaller.real_source_runs C ctx.iv
    (AnchoredPhysicalDriver.verifySource cap .fresh model ctx stack Q packet saved proofs)
  rw [WHIRSourceChronology.real_source_trace] at run
  rw [success] at run
  obtain ⟨_,_,_,_,observed⟩ := AnchoredPhysicalExecution.verifySource_execution
    cap .fresh model ctx stack Q packet saved proofs _ a run
  exact observed

/-- Actual success supplies ALL accepted opening hash plans and their strict
ordinary-tag bounds. Neither observed-plan nor trace-identity premises occur. -/
theorem real_success_evaluated (a : AnchoredPhysicalDriver.Accepted ctx Q cap packet saved)
    (success : (runReal C ctx.iv (completeProgram cap model ctx stack Q packet saved proofs)).view.result.value = some a) :
    ∀ opening ∈ a.wire.openings, ∀ path ∈ opening.result.paths,
      ∀ bytes ∈ path.opening.inputs (hashing (hash C)),
        bytes.length < 2^56 ∧ ∀ event ∈ PublicMerkleLog.plan C bytes,
          event ∈ completeTrace cap model ctx stack Q packet saved proofs C := by
  have observed := real_success_observed cap model ctx stack Q packet saved proofs C a success
  intro opening member
  exact observed_complete_evaluated C ctx.iv
    (completeProgram cap model ctx stack Q packet saved proofs) _
    (actualCounts cap model ctx stack Q packet saved proofs) opening (observed opening member)

theorem real_success_geometry (a : AnchoredPhysicalDriver.Accepted ctx Q cap packet saved)
    (success : (runReal C ctx.iv (completeProgram cap model ctx stack Q packet saved proofs)).view.result.value = some a) :
    ∀ opening ∈ a.wire.openings, ∀ path ∈ opening.result.paths, ∃ row : List K,
      row.length = (if opening.level.val = 0 then saved.shape.lanes
        else WHIRPhysicalVerifier.leafWords packet.val.profile opening.level.val) ∧
      path.leafData = leafImage 0 (WHIRPhysicalVerifier.leafWords packet.val.profile opening.level.val) row ∧
      path.leafData.length = WHIRPhysicalVerifier.leafWords packet.val.profile opening.level.val ∧
      path.path.length = (ParameterBounds.length (ParameterBounds.config packet.val.profile) opening.level.val).log2 ∧
      path.root (hash C) = opening.root := by
  intro opening member
  exact observed_complete_geometry C ctx.iv
    (completeProgram cap model ctx stack Q packet saved proofs) opening
    (real_success_observed cap model ctx stack Q packet saved proofs C a success opening member)

end Driver

#print axioms mixed_seed_origin
#print axioms atomic_ordinary_origin
#print axioms mixed_atomic_ordinary_subset
#print axioms mixed_atomic_collision_alarm
#print axioms observed_complete_evaluated
#print axioms observed_complete_geometry
#print axioms sourceLog_physical_subset
#print axioms sourceLog_clean_of_alarm
#print axioms actualCounts
#print axioms mixedView_real
#print axioms wholeLog_subset
#print axioms wholeLog_collision
#print axioms wholeLog_clean_of_alarm
#print axioms real_success_observed
#print axioms real_success_geometry
#print axioms real_success_evaluated
end Whir.PCSBCSNativePhysicalMerkleBad
