import Whir.AnchoredPhysicalAfter
import Whir.PCSBCSNativePhysicalMerkleBad
import Whir.PCSBCSNativePublicCapture
import Whir.PCSBCSMerkleSeedProjection
import Whir.PCSBCSCapturedSourceTransport

/-! Whole historical native executions retain the attacker's queries and the
actual first-address capture. Physical freezes may include the nonordinary
calls of the addressed raw response, but never add its answer to the capture. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Whir.PCSBCSNativePhysicalFreeze
open Concrete FiatShamirGame DuplexFraming DuplexModeGame TypedOracleCompiler
open PublicMerkleLog PublicCompressionProgram
open MerkleTransport MerkleTransport.Commitments
open MerkleBinding
open PCSBCSNativePublicCapture PCSBCSConstructionReplayTrace

section Whole
variable (cap : Nat) (registry : WHIRPhysicalDriver.ProductionRegistry) (Q : Nat)
    (attacker : WHIRSourceChronology.Source cap (AnchoredPhysicalAfter.Input registry.context Q))

abbrev wholeProgram := WHIRSourceChronology.compile
  (AnchoredPhysicalAfter.verifyAfter cap registry Q attacker)

/-- The operational opening subrun comes from whole success, not a suffix
capture and not an assumed equality of the two simulator caches. -/
theorem whole_success_observed (C : PrimitiveOracle)
    (accepted : AnchoredPhysicalAfter.Accepted registry.context Q cap)
    (success : (runReal C registry.context.iv (wholeProgram cap registry Q attacker)).view.result.value =
      some accepted) :
    ∀ opening ∈ accepted.native.wire.openings,
      WHIRPhysicalOpeningRuns.ObservedOpening accepted.input.record.shape.lanes accepted.input.proofs
        (runReal C registry.context.iv (wholeProgram cap registry Q attacker)).view.observations opening := by
  have run := WHIRPhysicalCaller.real_source_runs C registry.context.iv
    (AnchoredPhysicalAfter.verifyAfter cap registry Q attacker)
  rw [WHIRSourceChronology.real_source_trace] at run
  rw [success] at run
  obtain ⟨input,before,after,native,split,_,nativeRun,equal⟩ :=
    AnchoredPhysicalAfter.native_segment cap registry Q attacker _ accepted run
  cases equal
  obtain ⟨_,_,_,_,observed⟩ := AnchoredPhysicalExecution.verifySource_execution
    cap .fresh (registry.packetModel Q input.packet) registry.context rfl Q
    input.packet input.record input.proofs after native nativeRun
  intro opening member
  exact (observed opening member).mono (by
    intro o present
    rw [split]
    exact List.mem_append_right _ present)

theorem whole_success_evaluated (C : PrimitiveOracle) (A : Nat)
    (counted : Counts A (wholeProgram cap registry Q attacker))
    (accepted : AnchoredPhysicalAfter.Accepted registry.context Q cap)
    (success : (runReal C registry.context.iv (wholeProgram cap registry Q attacker)).view.result.value =
      some accepted) :
    ∀ opening ∈ accepted.native.wire.openings, ∀ path ∈ opening.result.paths,
      ∀ bytes ∈ path.opening.inputs (hashing (hash C)), bytes.length < 2^56 ∧
        ∀ event ∈ PublicMerkleLog.plan C bytes,
          event ∈ primitiveLog C registry.context.iv (wholeProgram cap registry Q attacker) A counted := by
  intro opening member
  exact PCSBCSNativePhysicalMerkleBad.observed_complete_evaluated C registry.context.iv
    (wholeProgram cap registry Q attacker) A counted opening
    (whole_success_observed cap registry Q attacker C accepted success opening member)

theorem whole_success_geometry (C : PrimitiveOracle)
    (accepted : AnchoredPhysicalAfter.Accepted registry.context Q cap)
    (success : (runReal C registry.context.iv (wholeProgram cap registry Q attacker)).view.result.value =
      some accepted) :
    ∀ opening ∈ accepted.native.wire.openings, ∀ path ∈ opening.result.paths, ∃ row : List K,
      row.length = (if opening.level.val = 0 then accepted.input.record.shape.lanes
        else WHIRPhysicalVerifier.leafWords accepted.input.packet.val.profile opening.level.val) ∧
      path.leafData = leafImage 0
        (WHIRPhysicalVerifier.leafWords accepted.input.packet.val.profile opening.level.val) row ∧
      path.leafData.length = WHIRPhysicalVerifier.leafWords accepted.input.packet.val.profile opening.level.val ∧
      path.path.length = (ParameterBounds.length
        (ParameterBounds.config accepted.input.packet.val.profile) opening.level.val).log2 ∧
      path.root (hash C) = opening.root := by
  intro opening member
  exact PCSBCSNativePhysicalMerkleBad.observed_complete_geometry C registry.context.iv
    (wholeProgram cap registry Q attacker) opening
    (whole_success_observed cap registry Q attacker C accepted success opening member)
end Whole

/-- Duplicate-retaining physical calls, in execution order. -/
def physicalTrace (C : PrimitiveOracle) (iv : Digest32) (seen : List Observation) : PublicLog :=
  seen.flatMap (fun o => queryTrace C iv o.query)

theorem physicalTrace_actual {R : Type} (C : PrimitiveOracle) (iv : Digest32)
    (program : Program R) (A : Nat) (counted : Counts A program) :
    primitiveLog C iv program A counted = physicalTrace C iv (runReal C iv program).view.observations := by
  induction program generalizing A with
  | done => rfl
  | ask q next ih =>
    rw [primitiveLog_ask,ih]
    rfl

abbrev RawEvent (B : Nat) := Sigma (fun _ : PublicCompressionCouplingMixed.Key B => Digest32)

def drawLog {B : Nat} (events : List (RawEvent B)) : PublicLog := events.flatMap rawOrdinary

/-- Cache coverage is membership, deliberately not list equality: repeats
remain in physicalTrace while a cached mixed query makes no seed draw. -/
structure Covered (C : PrimitiveOracle) (cache seeds physical : PublicLog) : Prop where
  authentic : AuthenticLog C cache
  seeds_physical : ∀ e ∈ seeds, e ∈ physical
  physical_seeds : ∀ n d, (n,d) ∈ physical → tag n = 0 → (n,d) ∈ seeds
  cache_seeds : ∀ n d, (n,d) ∈ cache → tag n = 0 → (n,d) ∈ seeds

private theorem step_covered (B : Nat) (C : PrimitiveOracle) (iv : Digest32)
    (cache seeds physical : PublicLog) (covered : Covered C cache seeds physical)
    (o : Observation) (answer : o.answer = realAnswer C iv o.query) :
    Covered C (nextLog cache o) (drawLog (observationDraw B iv cache o) ++ seeds)
      (physical ++ queryTrace C iv o.query) := by
  rcases o with ⟨query,d⟩
  cases query with
  | construction coordinate valid =>
    have noOrdinary : ∀ n e, (n,e) ∈ queryTrace C iv (.construction coordinate valid) → tag n ≠ 0 := by
      intro n e member
      have positive := PublicCompressionProgram.construction_tags C iv coordinate valid n e member
      omega
    have empty : drawLog (observationDraw B iv cache ⟨.construction coordinate valid,d⟩) = [] := by
      simp only [observationDraw]
      split <;> rfl
    rw [empty,List.nil_append]
    refine ⟨covered.authentic,?_,?_,covered.cache_seeds⟩
    · intro e member
      exact List.mem_append_left _ (covered.seeds_physical e member)
    · intro n e member ordinary
      rcases List.mem_append.mp member with earlier | current
      · exact covered.physical_seeds n e earlier ordinary
      · exact False.elim (noOrdinary n e current ordinary)
  | primitive purpose input =>
    change d = C input at answer
    subst d
    have trace : queryTrace C iv (.primitive purpose input) = [(input,C input)] := rfl
    have auth : AuthenticLog C (nextLog cache ⟨.primitive purpose input,C input⟩) := by
      intro n d member
      rcases List.mem_cons.mp member with equal | old
      · cases equal; rfl
      · exact covered.authentic n d old
    cases hit : DuplexPublicSimulator.lookup cache input with
    | some d =>
      have same : d = C input := (covered.authentic input d (DuplexPublicSimulator.lookup_mem hit)).symm
      have empty : drawLog (observationDraw B iv cache ⟨.primitive purpose input,C input⟩) = [] := by
        simp [observationDraw,hit,drawLog]
      rw [empty,List.nil_append,trace]
      refine ⟨auth,?_,?_,?_⟩
      · intro e member
        exact List.mem_append_left _ (covered.seeds_physical e member)
      · intro n e member ordinary
        rcases List.mem_append.mp member with earlier | current
        · exact covered.physical_seeds n e earlier ordinary
        · have equal := List.mem_singleton.mp current
          cases equal
          exact covered.cache_seeds input (C input) (same ▸ DuplexPublicSimulator.lookup_mem hit) ordinary
      · intro n e member ordinary
        rcases List.mem_cons.mp member with equal | earlier
        · cases equal
          exact covered.cache_seeds input (C input) (same ▸ DuplexPublicSimulator.lookup_mem hit) ordinary
        · exact covered.cache_seeds n e earlier ordinary
    | none =>
      cases key : DuplexPublicSimulator.privateKey B cache input with
      | some raw =>
        have nonordinary : tag input ≠ 0 := by
          intro ordinary
          have empty := PCSBCSMerkleSeedProjection.privateKey_none B cache ordinary
          rw [key] at empty
          cases empty
        have empty : drawLog (observationDraw B iv cache ⟨.primitive purpose input,C input⟩) = [] := by
          simp [observationDraw,hit,key,drawLog,rawOrdinary]
        rw [empty,List.nil_append,trace]
        refine ⟨auth,?_,?_,?_⟩
        · intro e member
          exact List.mem_append_left _ (covered.seeds_physical e member)
        · intro n e member ordinary
          rcases List.mem_append.mp member with earlier | current
          · exact covered.physical_seeds n e earlier ordinary
          · cases List.mem_singleton.mp current
            exact False.elim (nonordinary ordinary)
        · intro n e member ordinary
          rcases List.mem_cons.mp member with equal | earlier
          · cases equal
            exact False.elim (nonordinary ordinary)
          · exact covered.cache_seeds n e earlier ordinary
      | none =>
        have draws : drawLog (observationDraw B iv cache ⟨.primitive purpose input,C input⟩) =
            [(input,C input)] := by simp [observationDraw,hit,key,drawLog,rawOrdinary]
        rw [draws,trace]
        refine ⟨auth,?_,?_,?_⟩
        · intro e member
          rcases List.mem_append.mp member with current | earlier
          · exact List.mem_append_right _ current
          · exact List.mem_append_left _ (covered.seeds_physical e earlier)
        · intro n d member ordinary
          rcases List.mem_append.mp member with earlier | current
          · exact List.mem_append_right _ (covered.physical_seeds n d earlier ordinary)
          · exact List.mem_append_left _ current
        · intro n d member ordinary
          rcases List.mem_cons.mp member with equal | earlier
          · exact List.mem_append_left _ (List.mem_singleton.mpr equal)
          · exact List.mem_append_right _ (covered.cache_seeds n d earlier ordinary)

def captureFrom {B : Nat} (events : List (RawEvent B)) (prior : PublicLog) : PublicLog :=
  events.foldl (fun log event => rawOrdinary event ++ log) prior

private theorem draws_cases (B : Nat) (iv : Digest32) (cache : PublicLog) (o : Observation) :
    observationDraw B iv cache o = [] ∨ ∃ event, observationDraw B iv cache o = [event] := by
  rcases o with ⟨query,d⟩
  cases query with
  | primitive purpose input =>
    cases hit : DuplexPublicSimulator.lookup cache input with
    | some d => exact Or.inl (by simp [observationDraw,hit])
    | none =>
      cases key : DuplexPublicSimulator.privateKey B cache input with
      | none => exact Or.inr ⟨⟨.inl input,d⟩,by simp [observationDraw,hit,key]⟩
      | some raw => exact Or.inr ⟨⟨.inr raw,d⟩,by simp [observationDraw,hit,key]⟩
  | construction coordinate valid =>
    by_cases bound : pathCost coordinate ≤ B
    · exact Or.inr ⟨⟨.inr (constructionKey B iv coordinate bound),d⟩,by simp [observationDraw,bound]⟩
    · exact Or.inl (by simp [observationDraw,bound])

private theorem cache_step_subset (C : PrimitiveOracle) (iv : Digest32)
    (cache physical : PublicLog) (subset : ∀ e ∈ cache, e ∈ physical)
    (o : Observation) (answer : o.answer = realAnswer C iv o.query) :
    ∀ e ∈ nextLog cache o, e ∈ physical ++ queryTrace C iv o.query := by
  rcases o with ⟨query,d⟩
  cases query with
  | construction coordinate valid =>
    exact fun e member => List.mem_append_left _ (subset e member)
  | primitive purpose input =>
    change d = C input at answer
    subst d
    intro e member
    rcases List.mem_cons.mp member with equal | earlier
    · exact List.mem_append_right _ (List.mem_singleton.mpr equal)
    · exact List.mem_append_left _ (subset e earlier)

/-- Low-level first-mention join. The current cache is the genuine recursively
updated whole cache; all its records have physical provenance before this ask.
An address decoder that never addresses seed keys freezes after the current
raw response's nonordinary physical calls. No trace split is an input. -/
theorem firstPrefix_freeze {Root : Type} [DecidableEq Root]
    (B : Nat) (C : PrimitiveOracle) (iv : Digest32)
    (address : PublicCompressionCouplingMixed.Key B → List Root) (ref : Root)
    (noSeed : ∀ input, ref ∉ address (.inl input))
    (seen : List Observation) (cache seeds physical : PublicLog)
    (covered : Covered C cache seeds physical)
    (cachePhysical : ∀ e ∈ cache, e ∈ physical)
    (answers : ∀ o ∈ seen, o.answer = realAnswer C iv o.query)
    (captured : List (RawEvent B))
    (found : firstPrefix address ref (mixedTrace B iv cache seen) = some captured) :
    ∃ earlier current later currentCache event,
      seen = earlier ++ current :: later ∧
      observationDraw B iv currentCache current = [event] ∧
      ref ∈ address event.1 ∧
      (∀ e ∈ currentCache, e ∈ physical ++ physicalTrace C iv earlier) ∧
      AuthenticLog C currentCache ∧
      (∀ e ∈ captureFrom captured seeds,
        e ∈ physical ++ (physicalTrace C iv earlier ++ queryTrace C iv current.query)) ∧
      (∀ n d, (n,d) ∈ physical ++ (physicalTrace C iv earlier ++ queryTrace C iv current.query) →
        tag n = 0 → (n,d) ∈ captureFrom captured seeds) := by
  induction seen generalizing cache seeds physical captured with
  | nil => simp [mixedTrace,firstPrefix] at found
  | cons o rest ih =>
    have correct := answers o List.mem_cons_self
    have updated := step_covered B C iv cache seeds physical covered o correct
    have cacheUpdated := cache_step_subset C iv cache physical cachePhysical o correct
    have restAnswers : ∀ x ∈ rest, x.answer = realAnswer C iv x.query :=
      fun x member => answers x (List.mem_cons_of_mem _ member)
    rcases draws_cases B iv cache o with empty | ⟨event,single⟩
    · have nextFound : firstPrefix address ref (mixedTrace B iv (nextLog cache o) rest) = some captured := by
        simpa only [mixedTrace,empty,List.nil_append] using found
      have seedEqual : drawLog (observationDraw B iv cache o) ++ seeds = seeds := by
        simp [empty,drawLog]
      rw [seedEqual] at updated
      obtain ⟨earlier,current,later,currentCache,event,split,draw,addressed,cacheSub,auth,sub,sat⟩ :=
        ih (nextLog cache o) seeds (physical ++ queryTrace C iv o.query)
          updated cacheUpdated restAnswers captured nextFound
      refine ⟨o :: earlier,current,later,currentCache,event,?_,draw,addressed,?_,auth,?_,?_⟩
      · simp only [split,List.cons_append]
      · simpa only [physicalTrace,List.flatMap_cons,List.append_assoc] using cacheSub
      · simpa only [physicalTrace,List.flatMap_cons,List.append_assoc] using sub
      · simpa only [physicalTrace,List.flatMap_cons,List.append_assoc] using sat
    · have first : firstPrefix address ref (event :: mixedTrace B iv (nextLog cache o) rest) =
          some captured := by simpa only [mixedTrace,single,List.singleton_append] using found
      by_cases addressed : ref ∈ address event.1
      · have prefixEmpty : captured = [] := by
          simpa only [firstPrefix,addressed,↓reduceIte,Option.some.injEq] using first.symm
        subst captured
        have ordinaryEmpty : rawOrdinary event = [] := by
          rcases event with ⟨key,d⟩
          cases key with
          | inl input => exact False.elim (noSeed input addressed)
          | inr raw => rfl
        have seedEqual : drawLog (observationDraw B iv cache o) ++ seeds = seeds := by
          simp [single,drawLog,ordinaryEmpty]
        rw [seedEqual] at updated
        refine ⟨[],o,rest,cache,event,rfl,single,addressed,?_,covered.authentic,?_,?_⟩
        · simpa only [physicalTrace,List.flatMap_nil,List.append_nil] using cachePhysical
        · simpa only [captureFrom,List.foldl_nil,physicalTrace,List.flatMap_nil,List.nil_append]
            using updated.seeds_physical
        · simpa only [captureFrom,List.foldl_nil,physicalTrace,List.flatMap_nil,List.nil_append]
            using updated.physical_seeds
      · obtain ⟨tail,nextFound,equal⟩ := Option.map_eq_some_iff.mp
          (by simpa only [firstPrefix,addressed,↓reduceIte] using first)
        subst captured
        have seedEqual : drawLog (observationDraw B iv cache o) ++ seeds =
            rawOrdinary event ++ seeds := by simp [single,drawLog]
        rw [seedEqual] at updated
        obtain ⟨earlier,current,later,currentCache,hit,split,draw,addressed,cacheSub,auth,sub,sat⟩ :=
          ih (nextLog cache o) (rawOrdinary event ++ seeds) (physical ++ queryTrace C iv o.query)
            updated cacheUpdated restAnswers tail nextFound
        refine ⟨o :: earlier,current,later,currentCache,hit,?_,draw,addressed,?_,auth,?_,?_⟩
        · simp only [split,List.cons_append]
        · simpa only [physicalTrace,List.flatMap_cons,List.append_assoc] using cacheSub
        · simpa only [captureFrom,List.foldl_cons,physicalTrace,List.flatMap_cons,List.append_assoc]
            using sub
        · simpa only [captureFrom,List.foldl_cons,physicalTrace,List.flatMap_cons,List.append_assoc]
            using sat

/-- Position-sensitive boundary recovery retains the actual occurrence, even
when the same query has appeared earlier. -/
theorem observations_boundary_at {R : Type} (C : PrimitiveOracle) (iv : Digest32)
    (program : Program R) (earlier : List Observation) (current : Observation)
    (later : List Observation)
    (split : (runReal C iv program).view.observations = earlier ++ current :: later) :
    ∃ next, AskBoundary C iv program (physicalTrace C iv earlier) current.query next := by
  induction program generalizing earlier with
  | done value =>
    have member : current ∈ (runReal C iv (.done value)).view.observations := by
      rw [split]
      exact List.mem_append_right _ List.mem_cons_self
    cases member
  | ask q next ih =>
    cases earlier with
    | nil =>
      have equal : (⟨q,realAnswer C iv q⟩ : Observation) = current :=
        (List.cons.inj split).1
      cases equal
      exact ⟨next,.here q next⟩
    | cons head rest =>
      have equal : (⟨q,realAnswer C iv q⟩ : Observation) = head :=
        (List.cons.inj split).1
      cases equal
      obtain ⟨tail,reached⟩ := ih _ rest (List.cons.inj split).2
      exact ⟨tail,.step q next reached⟩

section Capture
variable {p : ParameterBounds.Profile} {B boundary : Nat} {iv : Digest32}
local notation "part" => PCSBCSChallengeOracle.EnteredPacket.partition
  (p := p) (Q := B) (iv := iv) (boundary := boundary)
local notation "Keys" => PCSBCSSourceRootCapture.Key
  (p := p) (Q := B) (iv := iv) (boundary := boundary)
local notation "Answers" => PCSBCSSourceRootCapture.Answer
  (p := p) (Q := B) (iv := iv) (boundary := boundary)

theorem allocatedSeed_other (input : Node) :
    ∃ other, allocatedKey (p := p) (B := B) (iv := iv) (boundary := boundary) (.inl input) = .inr other := by
  have unrecognized : (part).recognize (.inl input) = none := by
    cases found : (part).recognize (.inl input) with
    | none => rfl
    | some block =>
      have impossible := (part).encode_recognize _ block found
      change Sum.inr _ = Sum.inl input at impossible
      cases impossible
  refine ⟨⟨.inl input,unrecognized⟩,?_⟩
  unfold allocatedKey
  split
  · rename_i block found
    have impossible := found.symm.trans unrecognized
    cases impossible
  · rfl

/-- Actual whole-program first capture has an exact physical freeze. The only
address precondition is the executable decoder's exclusion of nonpacket keys;
neither saturation nor inclusion nor a physical split is supplied. -/
theorem source_firstMention_freeze {R : Type} (C : PrimitiveOracle)
    (program : Program R) (A : Nat) (limit : A ≤ B) (counted : Counts A program)
    (address : Keys → List PCSBCSSourceRootReferences.Reference)
    (noOther : ∀ other, address (.inr other) = [])
    (ref : PCSBCSSourceRootReferences.Reference)
    (events : List (Sigma Answers))
    (mentioned : PCSBCSFirstRootDisclosure.firstMention address ref
      (PCSBCSChallengeOracle.Atomic.program part
        (PublicCompressionCouplingMixed.compile B iv [] program A limit counted))
      ((part).split (PublicCompressionCouplingMixed.oracle C (WHIRRealSimulator.rawTable B C))) =
        some events) :
    ∃ earlier current later cache event next,
      (runReal C iv program).view.observations = earlier ++ current :: later ∧
      AskBoundary C iv program (physicalTrace C iv earlier) current.query next ∧
      observationDraw B iv cache current = [event] ∧
      ref ∈ address (allocatedKey event.1) ∧
      (∀ e ∈ cache, e ∈ physicalTrace C iv earlier) ∧
      AuthenticLog C cache ∧
      primitiveLog C iv program A counted =
        (physicalTrace C iv earlier ++ queryTrace C iv current.query) ++ physicalTrace C iv later ∧
      (∀ e ∈ PCSBCSCapturedNativeReplyBridge.sourceLog address ref
        (PCSBCSChallengeOracle.Atomic.program part
          (PublicCompressionCouplingMixed.compile B iv [] program A limit counted))
        ((part).split (PublicCompressionCouplingMixed.oracle C (WHIRRealSimulator.rawTable B C))),
        e ∈ physicalTrace C iv earlier ++ queryTrace C iv current.query) ∧
      (∀ n d, (n,d) ∈ physicalTrace C iv earlier ++ queryTrace C iv current.query →
        tag n = 0 → (n,d) ∈ PCSBCSCapturedNativeReplyBridge.sourceLog address ref
          (PCSBCSChallengeOracle.Atomic.program part
            (PublicCompressionCouplingMixed.compile B iv [] program A limit counted))
          ((part).split (PublicCompressionCouplingMixed.oracle C (WHIRRealSimulator.rawTable B C)))) := by
  have realView :
      Sampling.eval (PublicCompressionCouplingMixed.oracle C (WHIRRealSimulator.rawTable B C))
        (PublicCompressionCouplingMixed.compile B iv [] program A limit counted) =
        (runReal C iv program).view := by
    rw [PublicCompressionCouplingMixed.compile_actual]
    exact WHIRRealSimulator.runIdeal_view C iv _ ⟨rfl,by simp⟩ _ _ limit _
  have atomicView := PCSBCSChallengeOracle.Atomic.eval_program part
    ((part).split (PublicCompressionCouplingMixed.oracle C (WHIRRealSimulator.rawTable B C)))
    (PublicCompressionCouplingMixed.compile B iv [] program A limit counted)
  rw [RawOracleCoupling.Partition.join_split,realView] at atomicView
  have prefixFound := publicPrefix_actual (p := p) (boundary := boundary)
    C (WHIRRealSimulator.rawTable B C) program A limit counted address ref
  dsimp only at prefixFound
  rw [mentioned,atomicView] at prefixFound
  obtain ⟨rawPrefix,rawFound,_⟩ := Option.map_eq_some_iff.mp prefixFound.symm
  have publicFound : firstPrefix (fun raw => address (allocatedKey raw)) ref
      (mixedTrace B iv [] (runReal C iv program).view.observations) = some rawPrefix := rawFound
  have noSeed : ∀ input, ref ∉ address
      (allocatedKey (p := p) (B := B) (iv := iv) (boundary := boundary) (.inl input)) := by
    intro input
    obtain ⟨other,equal⟩ := allocatedSeed_other (p := p) (B := B) (iv := iv) (boundary := boundary) input
    rw [equal,noOther]
    simp
  obtain ⟨earlier,current,later,cache,event,split,draw,addressed,cacheSub,auth,sub,sat⟩ :=
    firstPrefix_freeze B C iv (fun raw => address (allocatedKey raw)) ref noSeed
      (runReal C iv program).view.observations [] [] []
      ⟨by simp [AuthenticLog],by simp,by simp,by simp⟩ (by simp)
      (fun o member => observation_answer C iv program o member) rawPrefix publicFound
  obtain ⟨next,reached⟩ := observations_boundary_at C iv program earlier current later split
  have logEqual := publicLog_actual (p := p) (boundary := boundary)
    C (WHIRRealSimulator.rawTable B C) program A limit counted address ref
  dsimp only at logEqual
  rw [atomicView] at logEqual
  have captureEqual : publicLog address ref (runReal C iv program).view = captureFrom rawPrefix [] := by
    simp only [PCSBCSNativePublicCapture.publicLog,rawFound,Option.getD_some,captureFrom]
  rw [captureEqual] at logEqual
  refine ⟨earlier,current,later,cache,event,next,split,reached,draw,addressed,?_,auth,?_,?_,?_⟩
  · simpa only [List.nil_append] using cacheSub
  · rw [physicalTrace_actual,split]
    simp only [physicalTrace,List.flatMap_append,List.flatMap_cons,List.append_assoc]
  · rw [logEqual]
    simpa only [List.nil_append] using sub
  · rw [logEqual]
    simpa only [List.nil_append] using sat

end Capture

/-- Exactly the physical-prefix obligations of FrozenOpeningBad; root scanner
admission is a separate causal source theorem, not a field assumed here. -/
structure PhysicalFreeze (trace oldLog : PublicLog) where
  before : PublicLog
  after : PublicLog
  split : trace = before ++ after
  captured : ∀ e ∈ oldLog, e ∈ before
  saturated : ∀ n d, (n,d) ∈ before → tag n = 0 → (n,d) ∈ oldLog

section ActualAddress
variable {p : ParameterBounds.Profile} {B boundary : Nat} {iv : Digest32}

noncomputable abbrev allocationProgram {R : Type} (program : Program R) (A : Nat) (limit : A ≤ B)
    (counted : Counts A program) :=
  PCSBCSChallengeOracle.Atomic.program
    (PCSBCSChallengeOracle.EnteredPacket.partition (p := p) (Q := B) (iv := iv) (boundary := boundary))
    (PublicCompressionCouplingMixed.compile B iv [] program A limit counted)

noncomputable abbrev actualTable (C : PrimitiveOracle) :=
  (PCSBCSChallengeOracle.EnteredPacket.partition (p := p) (Q := B) (iv := iv) (boundary := boundary)).split
    (PublicCompressionCouplingMixed.oracle C (WHIRRealSimulator.rawTable B C))

noncomputable abbrev actualSourceLog {R : Type} (C : PrimitiveOracle) (program : Program R)
    (A : Nat) (limit : A ≤ B) (counted : Counts A program) (ref : PCSBCSSourceRootReferences.Reference) :=
  PCSBCSCapturedNativeReplyBridge.sourceLog
    (PCSBCSCapturedSourceTransport.address (p := p) (Q := B) (iv := iv) (boundary := boundary)) ref
    (allocationProgram (p := p) (boundary := boundary) program A limit counted)
    (actualTable (p := p) (B := B) (iv := iv) (boundary := boundary) C)

/-- Actual whole allocation execution has the same public view, including all
prequeries and repeats. This does not identify its private cache with a suffix. -/
theorem allocationView_real {R : Type} (C : PrimitiveOracle)
    (program : Program R) (A : Nat) (limit : A ≤ B) (counted : Counts A program) :
    Sampling.eval (actualTable (p := p) (B := B) (iv := iv) (boundary := boundary) C)
      (allocationProgram (p := p) (boundary := boundary) program A limit counted) =
        (runReal C iv program).view := by
  rw [PCSBCSChallengeOracle.Atomic.eval_program,RawOracleCoupling.Partition.join_split,
    PublicCompressionCouplingMixed.compile_actual]
  exact WHIRRealSimulator.runIdeal_view C iv _ ⟨rfl,by simp⟩ _ _ limit _

/-- Exact first-mentioned source capture from the complete actual public view.
The getter reads no verifier-only execution or assumed suffix cache. -/
theorem actualSourceLog_public {R : Type} (C : PrimitiveOracle)
    (program : Program R) (A : Nat) (limit : A ≤ B) (counted : Counts A program)
    (ref : PCSBCSSourceRootReferences.Reference) :
    actualSourceLog (p := p) (iv := iv) (boundary := boundary) C program A limit counted ref =
      PCSBCSNativePublicCapture.publicLog
        (PCSBCSCapturedSourceTransport.address (p := p) (Q := B) (iv := iv) (boundary := boundary))
        ref (runReal C iv program).view := by
  have equality := publicLog_actual (p := p) (iv := iv) (boundary := boundary)
    C (WHIRRealSimulator.rawTable B C) program A limit counted PCSBCSCapturedSourceTransport.address ref
  dsimp only at equality
  rw [allocationView_real (p := p) (boundary := boundary) C program A limit counted] at equality
  exact equality


/-- Executable public byte-only address; no address-exclusion premise remains. -/
theorem actual_firstMention_freeze {R : Type} (C : PrimitiveOracle)
    (program : Program R) (A : Nat) (limit : A ≤ B) (counted : Counts A program)
    (ref : PCSBCSSourceRootReferences.Reference)
    (events : List (Sigma (PCSBCSSourceRootCapture.Answer
      (p := p) (Q := B) (iv := iv) (boundary := boundary))))
    (mentioned : PCSBCSFirstRootDisclosure.firstMention
      (PCSBCSCapturedSourceTransport.address (p := p) (Q := B) (iv := iv) (boundary := boundary)) ref
      (allocationProgram (p := p) (boundary := boundary) program A limit counted)
      (actualTable (p := p) (B := B) (iv := iv) (boundary := boundary) C) = some events) :
    Nonempty (PhysicalFreeze (primitiveLog C iv program A counted)
      (actualSourceLog (p := p) (iv := iv) (boundary := boundary) C program A limit counted ref)) := by
  obtain ⟨earlier,current,later,_,_,_,_,_,_,_,_,_,split,sub,sat⟩ :=
    source_firstMention_freeze (p := p) (boundary := boundary) C program A limit counted
      PCSBCSCapturedSourceTransport.address (by intro other; rfl) ref events mentioned
  exact ⟨⟨physicalTrace C iv earlier ++ queryTrace C iv current.query,
    physicalTrace C iv later,split,sub,sat⟩⟩
end ActualAddress

section CountedWhole
variable (cap : Nat) (registry : WHIRPhysicalDriver.ProductionRegistry) (Q : Nat)
    (attacker : WHIRSourceChronology.Source cap (AnchoredPhysicalAfter.Input registry.context Q))
    (a b : Nat) (attackerCounted : WHIRSourceChronology.Counts a attacker)
    (budget : WHIRSourceBackfill.AllResults
      (fun input => WHIRPhysicalVerifier.sourceBudget registry.context Q input.packet ≤ b)
      (WHIRSourceChronology.erase attacker))

include attackerCounted budget in
theorem whole_counted : Counts (a+b) (wholeProgram cap registry Q attacker) :=
  (WHIRSourceChronology.compile_counted _ _).mpr
    (AnchoredPhysicalAfter.verifyAfter_counted cap registry Q attacker a b attackerCounted budget)

/-- Whole-prefix freeze, with the actual counted attacker.bind allocation
program and the actual table. Arbitrary attacker asks are retained. -/
theorem counted_whole_firstMention_freeze (p : ParameterBounds.Profile)
    (B boundary : Nat) (limit : a+b ≤ B)
    (C : PrimitiveOracle) (ref : PCSBCSSourceRootReferences.Reference)
    (events : List (Sigma (PCSBCSSourceRootCapture.Answer
      (p := p) (Q := B) (iv := registry.context.iv) (boundary := boundary))))
    (mentioned : PCSBCSFirstRootDisclosure.firstMention
      (PCSBCSCapturedSourceTransport.address (p := p) (Q := B)
        (iv := registry.context.iv) (boundary := boundary)) ref
      (allocationProgram (p := p) (boundary := boundary) (wholeProgram cap registry Q attacker)
        (a+b) limit (whole_counted cap registry Q attacker a b attackerCounted budget))
      (actualTable (p := p) (B := B) (iv := registry.context.iv) (boundary := boundary) C) =
        some events) :
    Nonempty (PhysicalFreeze
      (primitiveLog C registry.context.iv (wholeProgram cap registry Q attacker) (a+b)
        (whole_counted cap registry Q attacker a b attackerCounted budget))
      (actualSourceLog (p := p) (iv := registry.context.iv) (boundary := boundary) C (wholeProgram cap registry Q attacker)
        (a+b) limit (whole_counted cap registry Q attacker a b attackerCounted budget) ref)) :=
  actual_firstMention_freeze C _ _ _ _ ref events mentioned

/-- All full zero-prefix plans, derived from actual whole success and actual
attacker/verifier source budgets, not assumed plan or suffix-capture facts. -/
theorem counted_whole_success_evaluated (C : PrimitiveOracle)
    (accepted : AnchoredPhysicalAfter.Accepted registry.context Q cap)
    (success : (runReal C registry.context.iv (wholeProgram cap registry Q attacker)).view.result.value =
      some accepted) :
    ∀ opening ∈ accepted.native.wire.openings, ∀ path ∈ opening.result.paths,
      ∀ bytes ∈ path.opening.inputs (hashing (hash C)), bytes.length < 2^56 ∧
        ∀ event ∈ PublicMerkleLog.plan C bytes,
          event ∈ primitiveLog C registry.context.iv (wholeProgram cap registry Q attacker) (a+b)
            (whole_counted cap registry Q attacker a b attackerCounted budget) :=
  whole_success_evaluated cap registry Q attacker C (a+b)
    (whole_counted cap registry Q attacker a b attackerCounted budget) accepted success
end CountedWhole

#print axioms whole_success_observed
#print axioms whole_success_evaluated
#print axioms whole_success_geometry
#print axioms physicalTrace_actual
#print axioms firstPrefix_freeze
#print axioms source_firstMention_freeze
#print axioms actual_firstMention_freeze
#print axioms counted_whole_firstMention_freeze
#print axioms counted_whole_success_evaluated
#print axioms allocationView_real
#print axioms actualSourceLog_public

end Whir.PCSBCSNativePhysicalFreeze
