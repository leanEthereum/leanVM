import Whir.SpongefishCurrentGoodEvent
import Whir.SpongefishCurrentOpeningPackets

/-! The current #607 basic full-prefix knowledge endpoint for the full source program (`SpongefishCurrentOpeningProgram.fullProgram`), which runs the counted caller and opening replay and then re-walks the opening with whole-hash Merkle authentication.

A natively accepted run whose public opening predicate fails raises the complete Merkle trace alarm under the current root policy (`opening_cover`): the first-mention capture of the opening's root reference is an exact physical freeze, and the public seed agrees with the real oracle on every hashed path input. Otherwise, without an ordinary output collision, the run is the public good event on its real view (`native_goodFull`): real-world frame counting identifies the post-binding coordinate, the received record is the selected raw record of that key and the prepared original is the public candidate. The endpoint `full_knowledge_bound` therefore has the three summands of `finalBound` and the single obligation `refines`; `full_knowledge_all` and `full_knowledge_level` cover every received record through the four binding message shapes. -/
namespace Whir.SpongefishCurrentKnowledgeEndpoint
open Concrete FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame TypedOracleCompiler
open SpongefishPCSRoundFrames SpongefishCurrentOpeningPackets
set_option autoImplicit false

/-! ## Real-world frame counting -/

/-- The pending update of one accepted actual call. -/
theorem actualCall_pending (c : Compression) (cur next : Cursor) (call : Call)
    (ok : SpongefishCurrentPrimitiveEventCompiler.actualCall c cur call = .ok next) :
    (∃ (kind : WireKind) (value : kind.Value), call = .read kind ∧
      next.pending = SpongefishPCSRoundFrames.bind cur.pending (kind.codec.bytes value)) ∨
    (∃ g, call = .draw g ∧ next.pending = SpongefishPCSRoundFrames.draw cur.pending g.bytes) ∨
    (call = .hint ∧ next.pending = cur.pending) := by
  cases call with
  | read kind =>
    left
    cases parsed : kind.codec.parse cur.narg with
    | none => simp [SpongefishCurrentPrimitiveEventCompiler.actualCall,SpongefishPCSRoundFrames.read,parsed] at ok
    | some pair =>
      obtain ⟨value,rest⟩ := pair
      simp only [SpongefishCurrentPrimitiveEventCompiler.actualCall,SpongefishPCSRoundFrames.read,parsed] at ok
      simp only [Option.bind_eq_bind,Option.bind_some,Option.pure_def,Except.ok.injEq] at ok
      subst ok
      exact ⟨kind,value,rfl,rfl⟩
  | draw g =>
    right; left
    simp only [SpongefishCurrentPrimitiveEventCompiler.actualCall] at ok
    cases hs : squeezeGroup c cur g with
    | error e => simp [hs] at ok
    | ok pair =>
      rcases pair with ⟨mid,bytes⟩
      simp only [hs,Except.ok.injEq] at ok
      subst ok
      refine ⟨g,rfl,?_⟩
      cases hq : squeeze c cur.state g.bytes with
      | error e => simp [squeezeGroup,hq] at hs
      | ok out =>
        rcases out with ⟨s,drawn⟩
        simp only [squeezeGroup,hq] at hs
        cases hs
        rfl
  | hint =>
    right; right
    cases hints : cur.hints with
    | nil => simp [SpongefishCurrentPrimitiveEventCompiler.actualCall,takeHint,hints] at ok
    | cons bytes rest =>
      simp only [SpongefishCurrentPrimitiveEventCompiler.actualCall,takeHint,hints,Except.ok.injEq] at ok
      subst ok
      exact ⟨rfl,rfl⟩

theorem bind_shaped (m : Pending) (s : Nat × Bool) (kind : WireKind) (value : kind.Value)
    (shaped : Shaped m s) :
    Shaped (SpongefishPCSRoundFrames.bind m (kind.codec.bytes value))
      (s.1,s.2 || decide (kind.codec.size ≠ 0)) := by
  obtain ⟨frames,ready,zeroed⟩ := shaped
  by_cases zero : kind.codec.size = 0
  · have empty := (codec_bytes_eq_nil kind value).mpr zero
    rw [empty]
    simpa [Shaped,SpongefishPCSRoundFrames.bind,zero] using (⟨frames,ready,zeroed⟩ : Shaped m s)
  · have nonempty : kind.codec.bytes value ≠ [] := fun h => zero ((codec_bytes_eq_nil kind value).mp h)
    obtain ⟨run,consumed⟩ := bind_nonempty m _ nonempty
    refine ⟨by rw [bind_frames]; exact frames,?_,fun _ => consumed⟩
    simp [zero,run]

theorem draw_shaped (m : Pending) (s : Nat × Bool) (n : Nat) (positive : n ≠ 0)
    (shaped : Shaped m s) :
    Shaped (SpongefishPCSRoundFrames.draw m n) (if s.2 then s.1+1 else s.1,false) := by
  obtain ⟨frames,ready,_⟩ := shaped
  obtain ⟨drawFrames,drawRun,_⟩ := draw_facts m n positive
  refine ⟨?_,by simp [drawRun],fun h => (h drawRun).elim⟩
  rw [drawFrames]
  by_cases empty : m.run = []
  · have notReady : s.2 = false := by simpa [empty] using ready
    simp [SpongefishPCSRoundFrames.close,empty,notReady,frames]
  · have isReady : s.2 = true := ready.mpr empty
    simp [close_frames _ empty,isReady,frames]

/-- One accepted actual call follows the static frame shape, keeps the domain and extends the closed frames. -/
theorem actualCall_shape (c : Compression) (cur next : Cursor) (call : Call)
    (ok : SpongefishCurrentPrimitiveEventCompiler.actualCall c cur call = .ok next) :
    (∀ s, Shaped cur.pending s → Shaped next.pending (frameShape s [call])) ∧
      next.pending.domain = cur.pending.domain ∧ cur.pending.frames <+: next.pending.frames := by
  rcases actualCall_pending c cur next call ok with ⟨kind,value,rfl,pending⟩ | ⟨g,rfl,pending⟩ |
    ⟨rfl,pending⟩ <;> rw [pending]
  · exact ⟨fun s shaped => bind_shaped _ s kind value shaped,bind_domain _ _,
      by rw [bind_frames]⟩
  · obtain ⟨drawFrames,_,drawDomain⟩ := draw_facts cur.pending g.bytes (group_bytes_pos g)
    refine ⟨fun s shaped => draw_shaped _ s _ (group_bytes_pos g) shaped,drawDomain,?_⟩
    rw [drawFrames]
    exact close_prefix _
  · exact ⟨fun _ shaped => shaped,rfl,List.prefix_refl _⟩

theorem frameShape_cons (s : Nat × Bool) (call : Call) (calls : List Call) :
    frameShape s (call :: calls) = frameShape (frameShape s [call]) calls := by
  cases call <;> rfl

/-- An accepted actual replay follows the static frame shape, keeps the domain and extends the closed frames. -/
theorem actualReplay_shape (c : Compression) :
    ∀ (calls : List Call) (cur fin : Cursor),
      SpongefishCurrentPrimitiveEventCompiler.actualReplay c cur calls = .ok fin →
      (∀ s, Shaped cur.pending s → Shaped fin.pending (frameShape s calls)) ∧
        fin.pending.domain = cur.pending.domain ∧ cur.pending.frames <+: fin.pending.frames
  | [], cur, fin, ok => by
    simp only [SpongefishCurrentPrimitiveEventCompiler.actualReplay,Except.ok.injEq] at ok
    subst ok
    exact ⟨fun _ shaped => shaped,rfl,List.prefix_refl _⟩
  | call :: calls, cur, fin, ok => by
    simp only [SpongefishCurrentPrimitiveEventCompiler.actualReplay] at ok
    cases step : SpongefishCurrentPrimitiveEventCompiler.actualCall c cur call with
    | error e => rw [step] at ok; cases ok
    | ok mid =>
      rw [step] at ok
      obtain ⟨shape₁,domain₁,prefix₁⟩ := actualCall_shape c cur mid call step
      obtain ⟨shape₂,domain₂,prefix₂⟩ := actualReplay_shape c calls mid fin ok
      refine ⟨fun s shaped => ?_,domain₂.trans domain₁,prefix₁.trans prefix₂⟩
      rw [frameShape_cons]
      exact shape₂ _ (shape₁ s shaped)

theorem setup_shaped (c : Compression) (parameter : Digest32) (tag instanceBytes narg : List Byte)
    (hints : List (List Byte)) (initial : Cursor)
    (setup : SpongefishCurrentObservedSessionEntry.actualSetup c parameter tag instanceBytes narg hints =
      some initial) :
    Shaped initial.pending (0,decide (instanceBytes ≠ [])) := by
  unfold SpongefishCurrentObservedSessionEntry.actualSetup at setup
  obtain ⟨_,_,same⟩ := Option.map_eq_some_iff.mp setup
  subst same
  by_cases empty : instanceBytes = [] <;>
    simp [Shaped,SpongefishCurrentObservedSessionEntry.cursor,SpongefishPCSRoundFrames.bind,empty]

variable {p : ParameterBounds.Profile}
local notation "cfg" => ParameterBounds.config p

/-- Real-world frame counting: when the opening starts with `boundary` closed frames and a pending prover run, the post-binding coordinate of the full view's replay data is the native post-binding coordinate. -/
theorem postBinding_native (c : Compression) (instanceBytes : List Byte) (tape : List Call)
    (grinding : Fin (cfg).folds.size → Fin 64) (boundary : Nat) (initial next final : Cursor)
    (start : Shaped initial.pending (0,decide (instanceBytes ≠ [])))
    (ready : openingShape instanceBytes tape = (boundary,true))
    (tapeRun : SpongefishCurrentPrimitiveEventCompiler.actualReplay c initial tape = .ok next)
    (openRun : SpongefishCurrentPrimitiveEventCompiler.actualReplay c next
      (SpongefishCurrentOpeningAcceptance.openingCalls grinding) = .ok final) :
    SpongefishCurrentGoodEvent.postBinding boundary (SpongefishCurrentMixedModeCompiler.forget final) =
      SpongefishCurrentModeQueries.coordinate next.pending (next.pending.consumed / 32) := by
  obtain ⟨shapes,_,_⟩ := actualReplay_shape c tape initial next tapeRun
  have shaped := shapes _ start
  unfold openingShape at ready
  rw [ready] at shaped
  obtain ⟨frames,run,zeroed⟩ := shaped
  have nonempty : next.pending.run ≠ [] := run.mp rfl
  have consumed := zeroed nonempty
  obtain ⟨rest,head⟩ := SpongefishCurrentOpeningAcceptance.openingCalls_head (p := p) grinding
  rw [head] at openRun
  simp only [SpongefishCurrentPrimitiveEventCompiler.actualReplay] at openRun
  cases step : SpongefishCurrentPrimitiveEventCompiler.actualCall c next (.draw .stackFamilyAndLambda) with
  | error e => rw [step] at openRun; cases openRun
  | ok mid =>
    rw [step] at openRun
    obtain ⟨_,domainRest,prefixRest⟩ := actualReplay_shape c rest mid final openRun
    rcases actualCall_pending c next mid _ step with ⟨_,_,bad,_⟩ | ⟨g,same,pending⟩ | ⟨bad,_⟩
    · cases bad
    · cases same
      obtain ⟨drawFrames,_,drawDomain⟩ := draw_facts next.pending _ (group_bytes_pos .stackFamilyAndLambda)
      have closedPrefix : (SpongefishPCSRoundFrames.close next.pending).frames <+:
          (SpongefishPCSRoundFrames.close final.pending).frames := by
        rw [← drawFrames,← pending]
        exact prefixRest.trans (close_prefix _)
      have domainEq : final.pending.domain = next.pending.domain := by
        rw [domainRest,pending,drawDomain]
      have closedLength : (SpongefishPCSRoundFrames.close next.pending).frames.length = boundary + 1 := by
        rw [close_frames _ nonempty,List.length_append,frames]
        rfl
      obtain ⟨tail,tailEq⟩ := closedPrefix
      have takeEq : ((SpongefishPCSRoundFrames.close final.pending).frames.map
          ByteFrame.historicalCore).take (boundary+1) =
          (SpongefishPCSRoundFrames.close next.pending).frames.map ByteFrame.historicalCore := by
        rw [← tailEq,List.map_append]
        exact List.take_left' (by rw [List.length_map,closedLength])
      unfold SpongefishCurrentGoodEvent.postBinding SpongefishCurrentModeQueries.coordinate
      rw [consumed]
      simp only [SpongefishCurrentMixedModeCompiler.forget,Pending.core,close_domain,domainEq,takeEq,
        Nat.zero_div]
    · cases bad

/-! ## Opening cover -/

open SpongefishCurrentOpeningProgram in
/-- The real view of a counted program is the evaluation of its compiled mixed program on the real table. -/
theorem compiled_view {R : Type} (C : PrimitiveOracle) (iv : Digest32) (program : Program R) (Q : Nat)
    (counted : Counts Q program) :
    Sampling.eval (PublicCompressionCouplingMixed.oracle C (WHIRRealSimulator.rawTable Q C))
      (PublicCompressionCouplingMixed.compile Q iv [] program Q (le_refl Q) counted) =
      (runReal C iv program).view := by
  rw [PublicCompressionCouplingMixed.compile_actual]
  exact WHIRRealSimulator.runIdeal_view C iv _ ⟨rfl,by simp⟩ _ _ (le_refl Q) _

/-- The public seed of a real view agrees with the oracle on every ordinary primitive-log entry. -/
theorem publicSeed_ordinary {R : Type} (C : PrimitiveOracle) (iv : Digest32) (program : Program R) (Q : Nat)
    (counted : Counts Q program) (n : Node) (d : Digest32) (ordinary : tag n = 0)
    (logged : (n,d) ∈ PublicCompressionProgram.primitiveLog C iv program Q counted) :
    PCSBCSPublicPrimitiveOpening.publicSeed (runReal C iv program).view n = C n := by
  have public_ := PublicCompressionProgram.ordinary_public C iv program Q counted n d ordinary logged
  obtain ⟨o,member,found⟩ := List.mem_filterMap.mp public_
  rcases o with ⟨query,answer⟩
  cases query with
  | construction => simp at found
  | primitive purpose input =>
    simp only [Option.some.injEq,Prod.mk.injEq] at found
    obtain ⟨rfl,rfl⟩ := found
    have seeded := PCSBCSPublicPrimitiveOpening.publicSeed_observed C (WHIRRealSimulator.rawTable Q C)
      program Q (le_refl Q) counted purpose input answer (by rw [compiled_view]; exact member)
    rw [compiled_view] at seeded
    rw [seeded]
    exact (PublicCompressionProgram.primitiveLog_authentic C iv program Q counted input answer logged).symm

open SpongefishCurrentOpeningProgram in
/-- Item 1: a natively accepted full run whose public opening predicate fails raises the complete Merkle trace alarm under the current root policy. -/
theorem opening_cover (C : PrimitiveOracle) (iv : Digest32) (tag instanceBytes : List Byte)
    (layout : WHIRCallerClaims.CallerLayout) (before payloadCalls messages : List Call)
    (decode : Decoder) (grinding : Fin (cfg).folds.size → Fin 64)
    (prefixProgram : Program SpongefishCurrentInitializedMode.Input) (A : Nat)
    (attacker : Counts A prefixProgram) (headerFrames boundary : Nat)
    (Bad : PCSBCSCallerBinding.CallerInput p → View (FullResult p) → Prop)
    (native : NativeAcceptedBadFull C iv tag instanceBytes layout before payloadCalls messages decode
      grinding prefixProgram Bad)
    (loud : ¬ SpongefishCurrentGoodEvent.Quiet grinding (AnchoredSourceCaller.shape layout) headerFrames
      boundary (fullBudget tag instanceBytes layout before payloadCalls messages grinding A) iv
      (runReal C iv (fullProgram iv tag instanceBytes layout before payloadCalls messages decode grinding
        prefixProgram)).view) :
    PublicMerkleProbability.traceAlarm
      (SpongefishCurrentRootPolicy.targets p grinding (AnchoredSourceCaller.shape layout) headerFrames
        boundary (fullBudget tag instanceBytes layout before payloadCalls messages grinding A) iv) []
      (PublicCompressionProgram.primitiveLog C iv
        (fullProgram iv tag instanceBytes layout before payloadCalls messages decode grinding prefixProgram)
        (fullBudget tag instanceBytes layout before payloadCalls messages grinding A)
        (fullProgram_counted iv tag instanceBytes layout before payloadCalls messages decode grinding
          prefixProgram A attacker)) = true := by
  obtain ⟨r,input,initial,pre,received,payload,next,setup,preRun,receivedEq,payloadRun,bindingEq,
    messagesEq,⟨opened⟩,_,_⟩ := native
  obtain ⟨resultEq,authenticated⟩ := fullProgram_native C iv tag instanceBytes layout before payloadCalls
    messages decode grinding prefixProgram A attacker r input initial pre received payload next setup
    preRun receivedEq payloadRun bindingEq messagesEq opened
  cases quiet : PublicMerkleProbability.traceAlarm
      (SpongefishCurrentRootPolicy.targets p grinding (AnchoredSourceCaller.shape layout) headerFrames
        boundary (fullBudget tag instanceBytes layout before payloadCalls messages grinding A) iv) []
      (PublicCompressionProgram.primitiveLog C iv
        (fullProgram iv tag instanceBytes layout before payloadCalls messages decode grinding prefixProgram)
        (fullBudget tag instanceBytes layout before payloadCalls messages grinding A)
        (fullProgram_counted iv tag instanceBytes layout before payloadCalls messages decode grinding
          prefixProgram A attacker)) with
  | true => rfl
  | false =>
    exfalso
    apply loud
    intro col colEq o member frozen captured bad
    rw [resultEq] at colEq
    cases colEq
    obtain ⟨_,paths⟩ := authenticated o member
    rw [← compiled_view C iv _ _ (fullProgram_counted iv tag instanceBytes layout before payloadCalls messages
      decode grinding prefixProgram A attacker),SpongefishCurrentRootPolicy.publicCapture_source] at captured
    have refRoot : (SpongefishCurrentGoodEvent.openingReference (AnchoredSourceCaller.shape layout) o).root =
        o.root := by
      unfold SpongefishCurrentGoodEvent.openingReference
      split <;> rfl
    obtain ⟨_,clean⟩ := SpongefishCurrentRootPolicy.captured_opening_quiet p grinding
      (AnchoredSourceCaller.shape layout) headerFrames boundary _ iv C _ _ (le_refl _) _ _ frozen captured
      quiet o.opened.paths (fun path inPaths bytes input => (paths path inPaths bytes input).1)
      (fun path inPaths bytes input => (paths path inPaths bytes input).2)
    rw [refRoot] at clean
    apply clean
    refine (PCSBCSPublicPrimitiveOpening.openPrimitiveBad_locality C _ frozen.queryPrefix o.root
      o.opened.paths ?_).mp bad
    rintro path inPaths bytes input ⟨n,d⟩ planned
    obtain ⟨small,logged⟩ := paths path inPaths bytes input
    exact publicSeed_ordinary C iv _ _ _ n d (PublicMerkleLog.plan_tag_zero C bytes small n d planned)
      (logged _ planned)

/-! ## Reduction to the public good event -/

/-- Raw construction keys depend only on the expanded mode key. -/
theorem constructionKey_congr {Q : Nat} (iv : Digest32) (a b : Coordinate) (ha : pathCost a ≤ Q)
    (hb : pathCost b ≤ Q) (same : modeKey iv a = modeKey iv b) :
    constructionKey Q iv a ha = constructionKey Q iv b hb := by
  have restrict : ∀ (x y : Extracted) (equal : x = y) (hx : x.message.length ≤ Q)
      (tx : x.template.length ≤ Q) (hy : y.message.length ≤ Q) (ty : y.template.length ≤ Q),
      restrictKey Q x hx tx = restrictKey Q y hy ty := by
    intro x y equal _ _ _ _
    subst equal
    rfl
  exact restrict _ _ same _ _ _ _

/-- A raw record of a construction key stays a raw record of the same coordinate at every larger budget. -/
theorem rawRecords_lift {Q Q' : Nat} (shape : AnchoredHeaderCodec.Shape) (iv : Digest32) (q : Coordinate)
    (work : pathCost q ≤ Q) (work' : pathCost q ≤ Q') (le : Q ≤ Q') (r : SpongefishSessionAdapter.Record)
    (member : r ∈ SpongefishCurrentRecordModeCapture.rawRecords shape iv (constructionKey Q iv q work)) :
    r ∈ SpongefishCurrentRecordModeCapture.rawRecords shape iv (constructionKey Q' iv q work') := by
  obtain ⟨q',bound,valid,keyEq,inRecords⟩ :=
    SpongefishCurrentRecordModeCapture.rawRecords_sound shape iv _ r member
  have modeEq : modeKey iv q' = modeKey iv q := by
    simpa only [expand_constructionKey] using congrArg expandKey keyEq
  rw [constructionKey_congr iv q q' work' (le_trans bound le) modeEq.symm,
    SpongefishCurrentRecordModeCapture.rawRecords_construction shape iv q' valid]
  exact inRecords

/-- The binding messages end with a positive read, so the opening starts with a pending prover run. -/
theorem binding_ready (instanceBytes : List Byte) (pre : List Call) (shape : AnchoredHeaderCodec.Shape)
    (k : Nat) :
    openingShape instanceBytes (pre ++ SpongefishCurrentBCSKnowledge.bindingCalls shape k) =
      ((openingShape instanceBytes (pre ++ SpongefishCurrentBCSKnowledge.bindingCalls shape k)).1,true) :=
  openingShape_ready instanceBytes _ _ .scalar
    (by rw [SpongefishCurrentBCSKnowledge.bindingCalls]; exact (List.append_assoc _ _ _).symm) (by decide)

open SpongefishCurrentOpeningProgram in
/-- Native acceptance with public extraction failure, without an ordinary output collision and with a quiet opening, is the public good event on the real full view. -/
theorem native_goodFull (C : PrimitiveOracle) (iv : Digest32) (tag instanceBytes : List Byte)
    (nonempty : instanceBytes ≠ []) (layout : WHIRCallerClaims.CallerLayout)
    (before payloadCalls messages : List Call) (k : Nat)
    (beforeEq : SpongefishCurrentSourceCallerOriginal.shapeCalls
      (SpongefishCurrentSourceCallerOriginal.preludeShape layout) = some before)
    (payloadEq : SpongefishCurrentSourceCallerOriginal.shapeCalls
      (SpongefishCurrentSourceCallerOriginal.payloadShape layout) = some payloadCalls)
    (messagesEq : messages = SpongefishCurrentBCSKnowledge.bindingCalls (AnchoredSourceCaller.shape layout) k)
    (decode : Decoder) (grinding : Fin (cfg).folds.size → Fin 64)
    (prefixProgram : Program SpongefishCurrentInitializedMode.Input) (A : Nat)
    (attacker : Counts A prefixProgram) (headerFrames boundary : Nat)
    (boundaryEq : boundary = (openingShape instanceBytes (before ++
      SpongefishCurrentAcceptedJoin.headerCalls (AnchoredSourceCaller.shape layout).logN ++ payloadCalls ++
        messages)).1)
    (native : NativeAcceptedBadFull C iv tag instanceBytes layout before payloadCalls messages decode
      grinding prefixProgram (SpongefishCurrentGoodEvent.ExtractionFails grinding
        (AnchoredSourceCaller.shape layout) headerFrames boundary
        (fullBudget tag instanceBytes layout before payloadCalls messages grinding A) iv))
    (collision : ¬ PublicMerkleLog.OutputCollision (PCSBCSPublicPrimitiveOpening.publicOrdinaryLog
      (fullBudget tag instanceBytes layout before payloadCalls messages grinding A) iv
      (runReal C iv (fullProgram iv tag instanceBytes layout before payloadCalls messages decode grinding
        prefixProgram)).view))
    (quiet : SpongefishCurrentGoodEvent.Quiet grinding (AnchoredSourceCaller.shape layout) headerFrames
      boundary (fullBudget tag instanceBytes layout before payloadCalls messages grinding A) iv
      (runReal C iv (fullProgram iv tag instanceBytes layout before payloadCalls messages decode grinding
        prefixProgram)).view) :
    SpongefishCurrentGoodEvent.GoodFull (fullBudget tag instanceBytes layout before payloadCalls messages
      grinding A) iv instanceBytes layout grinding headerFrames boundary k
      (runReal C iv (fullProgram iv tag instanceBytes layout before payloadCalls messages decode grinding
        prefixProgram)).view := by
  obtain ⟨r,input,initial,pre,received,payload,next,setup,preRun,receivedEq,payloadRun,bindingEq,
    messagesCalls,⟨opened⟩,physical,bad⟩ := native
  have resultEq := (fullProgram_native C iv tag instanceBytes layout before payloadCalls messages decode
    grinding prefixProgram A attacker r input initial pre received payload next setup preRun receivedEq
    payloadRun bindingEq messagesCalls opened).1
  have shapeEq := (SpongefishCurrentCommitmentReceive.receive_retains _ pre received _ r receivedEq).1
  obtain ⟨_,_,_,work0,member0,publicEq,_⟩ :=
    SpongefishCurrentOpeningAcceptance.accepted_opening_original C iv layout r tag instanceBytes
      prefixProgram A attacker nonempty before payloadCalls beforeEq payloadEq initial pre received
      payload next setup preRun receivedEq payloadRun bindingEq decode grinding input opened
  -- the post-binding coordinate, by real-world frame counting
  have tapeRun := SpongefishCurrentAcceptedJoin.composition_replay (compressionOf C) layout r before
    payloadCalls initial pre received payload next preRun receivedEq payloadRun bindingEq
  rw [shapeEq,messagesCalls] at tapeRun
  have ready : openingShape instanceBytes (before ++ SpongefishCurrentAcceptedJoin.headerCalls
      (AnchoredSourceCaller.shape layout).logN ++ payloadCalls ++ messages) = (boundary,true) := by
    rw [boundaryEq,messagesEq]
    exact binding_ready instanceBytes _ _ k
  have postEq := postBinding_native (compressionOf C) instanceBytes _ grinding boundary initial next
    opened.final (setup_shaped _ _ _ _ _ _ initial setup) ready tapeRun
    (SpongefishCurrentOpeningAcceptance.run_replay C decode grinding r.shape.lanes _ _ _ opened.ran)
  -- the full view's caller lookups are the old program's, at a larger budget
  have sameCalls : SpongefishCurrentSourceJoinProbability.calls layout before payloadCalls messages grinding =
      before ++ SpongefishCurrentAcceptedJoin.headerCalls r.shape.logN ++ payloadCalls ++
        SpongefishCurrentAcceptedJoin.messageCalls r ++
        SpongefishCurrentOpeningAcceptance.openingCalls grinding := by
    rw [SpongefishCurrentSourceJoinProbability.calls,shapeEq,messagesCalls]
  have capped := SpongefishCurrentReplayProvenance.observation_cap
    (SpongefishCurrentReplayProvenance.real_runs C iv _) _
    (SpongefishCurrentInitializedMode.afterPrefix_counted iv tag instanceBytes prefixProgram
      (before ++ SpongefishCurrentAcceptedJoin.headerCalls r.shape.logN ++ payloadCalls ++
        SpongefishCurrentAcceptedJoin.messageCalls r ++ SpongefishCurrentOpeningAcceptance.openingCalls grinding)
      A attacker)
  have le : A + SpongefishCurrentInitializedMode.budget tag instanceBytes
      (before ++ SpongefishCurrentAcceptedJoin.headerCalls r.shape.logN ++ payloadCalls ++
        SpongefishCurrentAcceptedJoin.messageCalls r ++ SpongefishCurrentOpeningAcceptance.openingCalls grinding) ≤
        fullBudget tag instanceBytes layout before payloadCalls messages grinding A := by
    unfold fullBudget SpongefishCurrentSourceJoinProbability.budget
    rw [sameCalls]
    exact Nat.le_add_right _ _
  have fullObservations := PrunedMerkleProgram.HashProgram.bind_real_observations C iv
    (SpongefishCurrentSourceJoinProbability.program iv tag instanceBytes layout before payloadCalls
      messages grinding prefixProgram)
    (openingPhase decode grinding (AnchoredSourceCaller.shape layout).lanes (rootIndex before)
      (openingOffset layout before payloadCalls messages))
  have oldObservations : (runReal C iv (SpongefishCurrentSourceJoinProbability.program iv tag instanceBytes
      layout before payloadCalls messages grinding prefixProgram)).view.observations =
        (runReal C iv (SpongefishCurrentInitializedMode.afterPrefix iv tag instanceBytes prefixProgram
          (before ++ SpongefishCurrentAcceptedJoin.headerCalls r.shape.logN ++ payloadCalls ++
            SpongefishCurrentAcceptedJoin.messageCalls r ++
            SpongefishCurrentOpeningAcceptance.openingCalls grinding))).view.observations := by
    unfold SpongefishCurrentSourceJoinProbability.program
    rw [sameCalls]
  rw [oldObservations] at fullObservations
  have same : ∀ q, SpongefishCurrentCallerGetter.lookup q
      (runReal C iv (fullProgram iv tag instanceBytes layout before payloadCalls messages decode grinding
        prefixProgram)).view.observations =
      SpongefishCurrentCallerGetter.lookup q (runReal C iv (SpongefishCurrentInitializedMode.afterPrefix iv
        tag instanceBytes prefixProgram (before ++ SpongefishCurrentAcceptedJoin.headerCalls r.shape.logN ++
          payloadCalls ++ SpongefishCurrentAcceptedJoin.messageCalls r ++
          SpongefishCurrentOpeningAcceptance.openingCalls grinding))).view.observations := by
    intro q
    rw [fullProgram,fullObservations]
    exact lookup_append_primitive q _ (openingPhase_primitive C iv decode grinding _ _ _ _) _
  have candidateEq : SpongefishCurrentSourceCallerOriginal.candidate
      (Q := fullBudget tag instanceBytes layout before payloadCalls messages grinding A) p layout
      (SpongefishCurrentModeQueries.coordinate next.pending (next.pending.consumed / 32)) r instanceBytes
      (runReal C iv (fullProgram iv tag instanceBytes layout before payloadCalls messages decode grinding
        prefixProgram)).view.observations = some input := by
    rw [← physical,← publicEq]
    unfold SpongefishCurrentSourceCallerOriginal.candidate SpongefishCurrentSourceCallerOriginal.replay
    rw [answer_lift _ _ le capped same]
  have work := le_trans work0 le
  refine ⟨SpongefishCurrentMixedModeCompiler.forget opened.final,opened.collected,r,input,resultEq,?_,?_,
    ⟨opened.seed,opened.proof,opened.seeded,opened.parsed,opened.equations⟩,bad,collision,quiet⟩
  · rw [postEq]
    exact ⟨work,SpongefishCurrentCallerOriginalTable.recordOf_eq _ iv k _ r
      (rawRecords_lift _ iv _ work0 work le r member0) (messagesCalls.trans messagesEq)⟩
  · rw [postEq]
    exact candidateEq

open SpongefishCurrentOpeningProgram in
/-- Item 2: real native acceptance with public extraction failure reduces pointwise to the public good event or the complete Merkle trace alarm under the current root policy. -/
theorem reduction_full {Coins : Type} (iv : Digest32) (tag instanceBytes : List Byte)
    (nonempty : instanceBytes ≠ []) (layout : WHIRCallerClaims.CallerLayout)
    (before payloadCalls messages : List Call) (k : Nat)
    (beforeEq : SpongefishCurrentSourceCallerOriginal.shapeCalls
      (SpongefishCurrentSourceCallerOriginal.preludeShape layout) = some before)
    (payloadEq : SpongefishCurrentSourceCallerOriginal.shapeCalls
      (SpongefishCurrentSourceCallerOriginal.payloadShape layout) = some payloadCalls)
    (messagesEq : messages = SpongefishCurrentBCSKnowledge.bindingCalls (AnchoredSourceCaller.shape layout) k)
    (decode : Decoder) (grinding : Fin (cfg).folds.size → Fin 64)
    (prefixProgram : Coins → Program SpongefishCurrentInitializedMode.Input) (A : Nat)
    (attacker : ∀ coin, Counts A (prefixProgram coin)) (headerFrames boundary : Nat)
    (boundaryEq : boundary = (openingShape instanceBytes (before ++
      SpongefishCurrentAcceptedJoin.headerCalls (AnchoredSourceCaller.shape layout).logN ++ payloadCalls ++
        messages)).1) :
    SpongefishCurrentBCSKnowledge.Reduction
      (SpongefishCurrentRootPolicy.targets p grinding (AnchoredSourceCaller.shape layout) headerFrames
        boundary (fullBudget tag instanceBytes layout before payloadCalls messages grinding A) iv) iv
      (fun coin => fullProgram iv tag instanceBytes layout before payloadCalls messages decode grinding
        (prefixProgram coin))
      (fun coin => fullProgram_counted iv tag instanceBytes layout before payloadCalls messages decode
        grinding (prefixProgram coin) A (attacker coin))
      (fun C coin => NativeAcceptedBadFull C iv tag instanceBytes layout before payloadCalls messages decode
        grinding (prefixProgram coin) (SpongefishCurrentGoodEvent.ExtractionFails grinding
          (AnchoredSourceCaller.shape layout) headerFrames boundary
          (fullBudget tag instanceBytes layout before payloadCalls messages grinding A) iv))
      (SpongefishCurrentGoodEvent.goodFull (fullBudget tag instanceBytes layout before payloadCalls messages
        grinding A) iv instanceBytes layout grinding headerFrames boundary k) := by
  intro C coin native
  by_cases collision : PublicMerkleLog.OutputCollision (PCSBCSPublicPrimitiveOpening.publicOrdinaryLog
      (fullBudget tag instanceBytes layout before payloadCalls messages grinding A) iv
      (runReal C iv (fullProgram iv tag instanceBytes layout before payloadCalls messages decode grinding
        (prefixProgram coin))).view)
  · exact Or.inr (SpongefishCurrentBCSKnowledge.collision_alarm C iv _ _ _ _ collision)
  · by_cases quiet : SpongefishCurrentGoodEvent.Quiet grinding (AnchoredSourceCaller.shape layout)
        headerFrames boundary (fullBudget tag instanceBytes layout before payloadCalls messages grinding A) iv
        (runReal C iv (fullProgram iv tag instanceBytes layout before payloadCalls messages decode grinding
          (prefixProgram coin))).view
    · left
      simp only [SpongefishCurrentGoodEvent.goodFull,decide_eq_true_eq]
      exact native_goodFull C iv tag instanceBytes nonempty layout before payloadCalls messages k beforeEq
        payloadEq messagesEq decode grinding (prefixProgram coin) A (attacker coin) headerFrames boundary
        boundaryEq native collision quiet
    · exact Or.inr (opening_cover C iv tag instanceBytes layout before payloadCalls messages decode grinding
        (prefixProgram coin) A (attacker coin) headerFrames boundary _ native quiet)

/-! ## Endpoint -/

noncomputable local instance (Q : Nat) (iv : Digest32) (grinding : Fin (cfg).folds.size → Fin 64)
    (boundary : Nat) (key : SpongefishCurrentRoundPackets.Key p Q iv grinding boundary) :
    Fintype (SpongefishCurrentRoundPackets.Answer p Q iv grinding boundary key) :=
  match key with
  | .inl _ => inferInstance
  | .inr _ => inferInstance

open Classical SpongefishCurrentOpeningProgram in
/-- Item 3: the current #607 basic full-prefix knowledge bound for one binding message shape. The real event is: the caller tape replays and the record binding verifies on the real primitive, the PCS opening is natively accepted, and the prepared original fails public straight-line extraction on the frozen Root0 image. The bound has the three explicit summands of `finalBound`; the only remaining obligation is `refines`, a state path of the current round node model on every ideal table where the public good event fires. -/
theorem full_knowledge_bound {Coins : Type} [Fintype Coins] [Nonempty Coins]
    (iv : Digest32) (tag instanceBytes : List Byte) (nonempty : instanceBytes ≠ [])
    (layout : WHIRCallerClaims.CallerLayout) (before payloadCalls messages : List Call) (k : Nat)
    (beforeEq : SpongefishCurrentSourceCallerOriginal.shapeCalls
      (SpongefishCurrentSourceCallerOriginal.preludeShape layout) = some before)
    (payloadEq : SpongefishCurrentSourceCallerOriginal.shapeCalls
      (SpongefishCurrentSourceCallerOriginal.payloadShape layout) = some payloadCalls)
    (messagesEq : messages = SpongefishCurrentBCSKnowledge.bindingCalls (AnchoredSourceCaller.shape layout) k)
    (decode : Decoder) (grinding : Fin (cfg).folds.size → Fin 64)
    (prefixProgram : Coins → Program SpongefishCurrentInitializedMode.Input) (A : Nat)
    (attacker : ∀ coin, Counts A (prefixProgram coin)) (headerFrames boundary : Nat)
    (boundaryEq : boundary = (openingShape instanceBytes (before ++
      SpongefishCurrentAcceptedJoin.headerCalls (AnchoredSourceCaller.shape layout).logN ++ payloadCalls ++
        messages)).1)
    (build : Coins → SpongefishCurrentRoundPackets.Builder p
      (fullBudget tag instanceBytes layout before payloadCalls messages grinding A) iv grinding boundary)
    (refines : ∀ coin, SpongefishCurrentBCSKnowledge.Refines
      (SpongefishCurrentRoundPackets.partition p
        (fullBudget tag instanceBytes layout before payloadCalls messages grinding A) iv grinding boundary)
      (SpongefishCurrentRoundPackets.model p
        (fullBudget tag instanceBytes layout before payloadCalls messages grinding A) iv grinding boundary
        (build coin)) iv
      (fullProgram iv tag instanceBytes layout before payloadCalls messages decode grinding (prefixProgram coin))
      (fullProgram_counted iv tag instanceBytes layout before payloadCalls messages decode grinding
        (prefixProgram coin) A (attacker coin))
      (SpongefishCurrentGoodEvent.goodFull (fullBudget tag instanceBytes layout before payloadCalls messages
        grinding A) iv instanceBytes layout grinding headerFrames boundary k)) :
    average (fun coins : PrimitiveOracle × Coins =>
      if NativeAcceptedBadFull coins.1 iv tag instanceBytes layout before payloadCalls messages decode grinding
        (prefixProgram coins.2) (SpongefishCurrentGoodEvent.ExtractionFails grinding
          (AnchoredSourceCaller.shape layout) headerFrames boundary
          (fullBudget tag instanceBytes layout before payloadCalls messages grinding A) iv)
      then (1 : ℚ) else 0) ≤
      SpongefishCurrentBCSKnowledge.finalBound
        (fullBudget tag instanceBytes layout before payloadCalls messages grinding A : ℚ) := by
  have union := SpongefishCurrentBCSKnowledge.reduction_union _ iv _ _ _ _
    (reduction_full iv tag instanceBytes nonempty layout before payloadCalls messages k beforeEq payloadEq
      messagesEq decode grinding prefixProgram A attacker headerFrames boundary boundaryEq)
  have merkle := SpongefishCurrentBCSKnowledge.merkle_bound
    (SpongefishCurrentRootPolicy.targets p grinding (AnchoredSourceCaller.shape layout) headerFrames boundary
      (fullBudget tag instanceBytes layout before payloadCalls messages grinding A) iv)
    (SpongefishCurrentRootPolicy.targets_cap p grinding (AnchoredSourceCaller.shape layout) headerFrames
      boundary (fullBudget tag instanceBytes layout before payloadCalls messages grinding A) iv) iv
    (fun coin => fullProgram iv tag instanceBytes layout before payloadCalls messages decode grinding
      (prefixProgram coin))
    (fun coin => fullProgram_counted iv tag instanceBytes layout before payloadCalls messages decode grinding
      (prefixProgram coin) A (attacker coin))
  have nonnegative : (0 : ℚ) ≤ PCSRoundByRoundKnowledge.rbrError := by
    unfold PCSRoundByRoundKnowledge.rbrError SupportedCandidateExtraction.radiusEnvelope
    positivity
  have real := SpongefishCurrentBCSKnowledge.real_bound _
    (fun coin => SpongefishCurrentRoundPackets.model p _ iv grinding boundary (build coin))
    PCSRoundByRoundKnowledge.rbrError nonnegative
    (fun coin => SpongefishCurrentRoundPackets.conditional_hazard p _ iv grinding boundary (build coin))
    iv _ _ _ refines
  have rbr : PCSRoundByRoundKnowledge.rbrError = (17/32 : ℚ)^56 + 1/2^78 := by
    simp only [PCSRoundByRoundKnowledge.rbrError,SupportedCandidateExtraction.radiusEnvelope]
  rw [rbr,duplexModeLoss_eq] at real
  unfold SpongefishCurrentBCSKnowledge.finalBound
  exact union.trans (add_le_add real merkle)

/-! ### Every record-binding message shape -/

/-- Closed frames at the opening start for binding message shape `k`. -/
def fullBoundary (instanceBytes : List Byte) (layout : WHIRCallerClaims.CallerLayout)
    (before payloadCalls : List Call) (k : Nat) : Nat :=
  (openingShape instanceBytes (before ++
    SpongefishCurrentAcceptedJoin.headerCalls (AnchoredSourceCaller.shape layout).logN ++ payloadCalls ++
      SpongefishCurrentBCSKnowledge.bindingCalls (AnchoredSourceCaller.shape layout) k)).1

open SpongefishCurrentOpeningProgram in
/-- Native full acceptance for SOME binding message shape, with a property chosen per shape. -/
def NativeAcceptedAnyFull (C : PrimitiveOracle) (iv : Digest32) (tag instanceBytes : List Byte)
    (layout : WHIRCallerClaims.CallerLayout) (before payloadCalls : List Call) (decode : Decoder)
    (grinding : Fin (cfg).folds.size → Fin 64)
    (prefixProgram : Program SpongefishCurrentInitializedMode.Input)
    (Bad : Fin 4 → PCSBCSCallerBinding.CallerInput p → View (FullResult p) → Prop) : Prop :=
  ∃ k : Fin 4, NativeAcceptedBadFull C iv tag instanceBytes layout before payloadCalls
    (SpongefishCurrentBCSKnowledge.bindingCalls (AnchoredSourceCaller.shape layout) k.val) decode grinding
    prefixProgram (Bad k)

open SpongefishCurrentOpeningProgram in
/-- Every natively accepted full run, whatever its received record, has one of the four binding message shapes. -/
theorem messages_binding_full (C : PrimitiveOracle) (iv : Digest32) (tag instanceBytes : List Byte)
    (layout : WHIRCallerClaims.CallerLayout) (before payloadCalls messages : List Call) (decode : Decoder)
    (grinding : Fin (cfg).folds.size → Fin 64)
    (prefixProgram : Program SpongefishCurrentInitializedMode.Input)
    (Bad : PCSBCSCallerBinding.CallerInput p → View (FullResult p) → Prop)
    (native : NativeAcceptedBadFull C iv tag instanceBytes layout before payloadCalls messages decode
      grinding prefixProgram Bad) :
    ∃ k : Fin 4, messages = SpongefishCurrentBCSKnowledge.bindingCalls (AnchoredSourceCaller.shape layout) k.val := by
  obtain ⟨r,_,initial,pre,received,_,_,setup,preRun,receivedEq,_,_,messagesEq,_⟩ := native
  obtain ⟨packs,pointLength⟩ := SpongefishCurrentBCSKnowledge.accepted_packs _ iv tag instanceBytes _ _
    layout before r initial pre received setup preRun receivedEq
  have shapeEq := (SpongefishCurrentCommitmentReceive.receive_retains _ pre received _ r receivedEq).1
  have exact := SpongefishCurrentBCSKnowledge.messageCalls_binding r pointLength
  rw [shapeEq] at exact
  exact ⟨⟨_,packs⟩,messagesEq.symm.trans exact⟩

open Classical SpongefishCurrentOpeningProgram in
/-- Union over the four binding message shapes. -/
theorem nativeAnyFull_union {Coins : Type} [Fintype Coins]
    (iv : Digest32) (tag instanceBytes : List Byte)
    (layout : WHIRCallerClaims.CallerLayout) (before payloadCalls : List Call) (decode : Decoder)
    (grinding : Fin (cfg).folds.size → Fin 64)
    (prefixProgram : Coins → Program SpongefishCurrentInitializedMode.Input)
    (Bad : Fin 4 → PCSBCSCallerBinding.CallerInput p → View (FullResult p) → Prop) :
    average (fun coins : PrimitiveOracle × Coins =>
      if NativeAcceptedAnyFull coins.1 iv tag instanceBytes layout before payloadCalls decode grinding
        (prefixProgram coins.2) Bad then (1 : ℚ) else 0) ≤
      ∑ k : Fin 4, average (fun coins : PrimitiveOracle × Coins =>
        if NativeAcceptedBadFull coins.1 iv tag instanceBytes layout before payloadCalls
          (SpongefishCurrentBCSKnowledge.bindingCalls (AnchoredSourceCaller.shape layout) k.val) decode
          grinding (prefixProgram coins.2) (Bad k) then (1 : ℚ) else 0) := by
  unfold average
  rw [← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro coins _
  by_cases any : NativeAcceptedAnyFull coins.1 iv tag instanceBytes layout before payloadCalls decode
      grinding (prefixProgram coins.2) Bad
  · obtain ⟨k,hk⟩ := any
    simp only [show NativeAcceptedAnyFull coins.1 iv tag instanceBytes layout before payloadCalls decode
      grinding (prefixProgram coins.2) Bad from ⟨k,hk⟩,↓reduceIte]
    calc (1 : ℚ) = if NativeAcceptedBadFull coins.1 iv tag instanceBytes layout before payloadCalls
          (SpongefishCurrentBCSKnowledge.bindingCalls (AnchoredSourceCaller.shape layout) k.val) decode
          grinding (prefixProgram coins.2) (Bad k) then 1 else 0 := by simp only [hk,↓reduceIte]
      _ ≤ _ := Finset.single_le_sum (f := fun k : Fin 4 =>
          if NativeAcceptedBadFull coins.1 iv tag instanceBytes layout before payloadCalls
            (SpongefishCurrentBCSKnowledge.bindingCalls (AnchoredSourceCaller.shape layout) k.val) decode
            grinding (prefixProgram coins.2) (Bad k) then (1 : ℚ) else 0)
          (fun _ _ => by split <;> norm_num) (Finset.mem_univ k)
  · simp only [any,↓reduceIte]
    exact Finset.sum_nonneg (fun _ _ => by split <;> norm_num)

open Classical SpongefishCurrentOpeningProgram in
/-- The current endpoint for EVERY received record: each of the four binding message shapes carries its own builder and `refines` obligation, and the bound is the sum of the four three-summand bounds. -/
theorem full_knowledge_all {Coins : Type} [Fintype Coins] [Nonempty Coins]
    (iv : Digest32) (tag instanceBytes : List Byte) (nonempty : instanceBytes ≠ [])
    (layout : WHIRCallerClaims.CallerLayout) (before payloadCalls : List Call)
    (beforeEq : SpongefishCurrentSourceCallerOriginal.shapeCalls
      (SpongefishCurrentSourceCallerOriginal.preludeShape layout) = some before)
    (payloadEq : SpongefishCurrentSourceCallerOriginal.shapeCalls
      (SpongefishCurrentSourceCallerOriginal.payloadShape layout) = some payloadCalls)
    (decode : Decoder) (grinding : Fin (cfg).folds.size → Fin 64)
    (prefixProgram : Coins → Program SpongefishCurrentInitializedMode.Input) (A : Nat)
    (attacker : ∀ coin, Counts A (prefixProgram coin)) (headerFrames : Nat)
    (build : ∀ k : Fin 4, Coins → SpongefishCurrentRoundPackets.Builder p
      (fullBudget tag instanceBytes layout before payloadCalls
        (SpongefishCurrentBCSKnowledge.bindingCalls (AnchoredSourceCaller.shape layout) k.val) grinding A) iv
      grinding (fullBoundary instanceBytes layout before payloadCalls k.val))
    (refines : ∀ (k : Fin 4) coin, SpongefishCurrentBCSKnowledge.Refines
      (SpongefishCurrentRoundPackets.partition p
        (fullBudget tag instanceBytes layout before payloadCalls
          (SpongefishCurrentBCSKnowledge.bindingCalls (AnchoredSourceCaller.shape layout) k.val) grinding A) iv
        grinding (fullBoundary instanceBytes layout before payloadCalls k.val))
      (SpongefishCurrentRoundPackets.model p _ iv grinding
        (fullBoundary instanceBytes layout before payloadCalls k.val) (build k coin)) iv
      (fullProgram iv tag instanceBytes layout before payloadCalls
        (SpongefishCurrentBCSKnowledge.bindingCalls (AnchoredSourceCaller.shape layout) k.val) decode grinding
        (prefixProgram coin))
      (fullProgram_counted iv tag instanceBytes layout before payloadCalls
        (SpongefishCurrentBCSKnowledge.bindingCalls (AnchoredSourceCaller.shape layout) k.val) decode grinding
        (prefixProgram coin) A (attacker coin))
      (SpongefishCurrentGoodEvent.goodFull (fullBudget tag instanceBytes layout before payloadCalls
        (SpongefishCurrentBCSKnowledge.bindingCalls (AnchoredSourceCaller.shape layout) k.val) grinding A) iv
        instanceBytes layout grinding headerFrames (fullBoundary instanceBytes layout before payloadCalls k.val)
        k.val)) :
    average (fun coins : PrimitiveOracle × Coins =>
      if NativeAcceptedAnyFull coins.1 iv tag instanceBytes layout before payloadCalls decode grinding
        (prefixProgram coins.2) (fun k => SpongefishCurrentGoodEvent.ExtractionFails grinding
          (AnchoredSourceCaller.shape layout) headerFrames
          (fullBoundary instanceBytes layout before payloadCalls k.val)
          (fullBudget tag instanceBytes layout before payloadCalls
            (SpongefishCurrentBCSKnowledge.bindingCalls (AnchoredSourceCaller.shape layout) k.val) grinding A) iv)
      then (1 : ℚ) else 0) ≤
      ∑ k : Fin 4, SpongefishCurrentBCSKnowledge.finalBound (fullBudget tag instanceBytes layout before
        payloadCalls (SpongefishCurrentBCSKnowledge.bindingCalls (AnchoredSourceCaller.shape layout) k.val)
        grinding A : ℚ) :=
  (nativeAnyFull_union iv tag instanceBytes layout before payloadCalls decode grinding prefixProgram _).trans
    (Finset.sum_le_sum fun k _ => full_knowledge_bound iv tag instanceBytes nonempty layout before
      payloadCalls _ k.val beforeEq payloadEq rfl decode grinding prefixProgram A attacker headerFrames _ rfl
      (build k) (refines k))

open Classical SpongefishCurrentOpeningProgram in
/-- The current endpoint at the deployed grinding, evaluated numerically: if every binding message shape has an aggregate budget of at most `2^64` units, the real probability of native acceptance with public extraction failure is at most the sum over the four shapes of `Q / 2^51`, under the same `refines` obligations. -/
theorem full_knowledge_level {Coins : Type} [Fintype Coins] [Nonempty Coins]
    (iv : Digest32) (tag instanceBytes : List Byte) (nonempty : instanceBytes ≠ [])
    (layout : WHIRCallerClaims.CallerLayout) (before payloadCalls : List Call)
    (beforeEq : SpongefishCurrentSourceCallerOriginal.shapeCalls
      (SpongefishCurrentSourceCallerOriginal.preludeShape layout) = some before)
    (payloadEq : SpongefishCurrentSourceCallerOriginal.shapeCalls
      (SpongefishCurrentSourceCallerOriginal.payloadShape layout) = some payloadCalls)
    (decode : Decoder) (prefixProgram : Coins → Program SpongefishCurrentInitializedMode.Input) (A : Nat)
    (attacker : ∀ coin, Counts A (prefixProgram coin)) (headerFrames : Nat)
    (build : ∀ k : Fin 4, Coins → SpongefishCurrentRoundPackets.Builder p
      (fullBudget tag instanceBytes layout before payloadCalls
        (SpongefishCurrentBCSKnowledge.bindingCalls (AnchoredSourceCaller.shape layout) k.val)
        (SpongefishCurrentBCSKnowledge.deployedGrinding p) A) iv
      (SpongefishCurrentBCSKnowledge.deployedGrinding p) (fullBoundary instanceBytes layout before payloadCalls k.val))
    (refines : ∀ (k : Fin 4) coin, SpongefishCurrentBCSKnowledge.Refines
      (SpongefishCurrentRoundPackets.partition p
        (fullBudget tag instanceBytes layout before payloadCalls
          (SpongefishCurrentBCSKnowledge.bindingCalls (AnchoredSourceCaller.shape layout) k.val)
          (SpongefishCurrentBCSKnowledge.deployedGrinding p) A) iv
        (SpongefishCurrentBCSKnowledge.deployedGrinding p)
        (fullBoundary instanceBytes layout before payloadCalls k.val))
      (SpongefishCurrentRoundPackets.model p _ iv (SpongefishCurrentBCSKnowledge.deployedGrinding p)
        (fullBoundary instanceBytes layout before payloadCalls k.val) (build k coin)) iv
      (fullProgram iv tag instanceBytes layout before payloadCalls
        (SpongefishCurrentBCSKnowledge.bindingCalls (AnchoredSourceCaller.shape layout) k.val) decode
        (SpongefishCurrentBCSKnowledge.deployedGrinding p) (prefixProgram coin))
      (fullProgram_counted iv tag instanceBytes layout before payloadCalls
        (SpongefishCurrentBCSKnowledge.bindingCalls (AnchoredSourceCaller.shape layout) k.val) decode
        (SpongefishCurrentBCSKnowledge.deployedGrinding p) (prefixProgram coin) A (attacker coin))
      (SpongefishCurrentGoodEvent.goodFull (fullBudget tag instanceBytes layout before payloadCalls
        (SpongefishCurrentBCSKnowledge.bindingCalls (AnchoredSourceCaller.shape layout) k.val)
        (SpongefishCurrentBCSKnowledge.deployedGrinding p) A) iv instanceBytes layout
        (SpongefishCurrentBCSKnowledge.deployedGrinding p) headerFrames
        (fullBoundary instanceBytes layout before payloadCalls k.val) k.val))
    (cap : ∀ k : Fin 4, fullBudget tag instanceBytes layout before payloadCalls
      (SpongefishCurrentBCSKnowledge.bindingCalls (AnchoredSourceCaller.shape layout) k.val)
      (SpongefishCurrentBCSKnowledge.deployedGrinding p) A ≤ 2^64) :
    average (fun coins : PrimitiveOracle × Coins =>
      if NativeAcceptedAnyFull coins.1 iv tag instanceBytes layout before payloadCalls decode
        (SpongefishCurrentBCSKnowledge.deployedGrinding p) (prefixProgram coins.2)
        (fun k => SpongefishCurrentGoodEvent.ExtractionFails (SpongefishCurrentBCSKnowledge.deployedGrinding p)
          (AnchoredSourceCaller.shape layout) headerFrames
          (fullBoundary instanceBytes layout before payloadCalls k.val)
          (fullBudget tag instanceBytes layout before payloadCalls
            (SpongefishCurrentBCSKnowledge.bindingCalls (AnchoredSourceCaller.shape layout) k.val)
            (SpongefishCurrentBCSKnowledge.deployedGrinding p) A) iv)
      then (1 : ℚ) else 0) ≤
      ∑ k : Fin 4, (fullBudget tag instanceBytes layout before payloadCalls
        (SpongefishCurrentBCSKnowledge.bindingCalls (AnchoredSourceCaller.shape layout) k.val)
        (SpongefishCurrentBCSKnowledge.deployedGrinding p) A : ℚ) / 2^51 :=
  (full_knowledge_all iv tag instanceBytes nonempty layout before payloadCalls beforeEq payloadEq decode
    (SpongefishCurrentBCSKnowledge.deployedGrinding p) prefixProgram A attacker headerFrames build
    refines).trans (Finset.sum_le_sum fun k _ =>
      SpongefishCurrentBCSKnowledge.finalBound_le _ (by positivity) (by exact_mod_cast cap k))

#print axioms actualReplay_shape
#print axioms postBinding_native
#print axioms publicSeed_ordinary
#print axioms opening_cover
#print axioms rawRecords_lift
#print axioms native_goodFull
#print axioms reduction_full
#print axioms full_knowledge_bound
#print axioms messages_binding_full
#print axioms nativeAnyFull_union
#print axioms full_knowledge_all
#print axioms full_knowledge_level

end Whir.SpongefishCurrentKnowledgeEndpoint
