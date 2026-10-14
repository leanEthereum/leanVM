import Whir.SpongefishCurrentHistoryReplies

/-! Glue between the current #607 full source program, its opening phase and the commitment header.

`openingEvents_full`: on every table, a successful full-program view has the same opening events under the walk offset `openingOffset` and under the opening packets' suffix `SpongefishCurrentOpeningPackets.openingEvents`.

`headerFrames` is the static number of closed frames right after the anchor draw closes the commitment header frame. `headerFrames_le` bounds it by the post-binding frame count. `header_full`: on every table, if the full-program view succeeds and the caller original at the post-binding coordinate succeeds, then the header frames of the post-binding history decode the root read by the header root event. The caller original is needed: the replay reads the three header scalars without checking them, and only the original's `header` step checks that they are the canonical constants, in a replay whose closed history is the post-binding history. -/
namespace Whir.SpongefishCurrentHeaderGlue
open Concrete FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame
open SpongefishPCSRoundFrames SpongefishCurrentModeQueries SpongefishCurrentMixedModeCompiler
open SpongefishCurrentOpeningPackets SpongefishCurrentHistoryReplies RawOracleCoupling TypedOracleCompiler
open SpongefishCurrentOpeningAcceptance
set_option autoImplicit false

/-- The four reads of the commitment header: three scalars and the raw32 root. -/
def headerReads : List Call := [.read .scalar,.read .scalar,.read .scalar,.read .root]

/-- The semantic replay of a call list containing the header reads followed by a draw closes a frame ending with the four header read events. -/
theorem header_frame (ans : Coordinate → Digest32) (cur : SemanticCursor) (s : Nat × Bool)
    (shaped : Shaped cur.data.pending s) (good : CacheOK ans cur.cache)
    (B rest : List Call) (g : Group) (fin : SemanticCursor)
    (ok : (runWith ans (replayProgram cur (B ++ (headerReads ++ .draw g :: rest)))).result = .ok fin) :
    ∃ (evs evsR : List SourceEvent) (a b c rt dr X : List Byte) (root : Digest32),
      fin.data.events = cur.data.events ++ evs ++
        (.prover .scalar a :: .prover .scalar b :: .prover .scalar c :: .prover .root rt ::
          .verifier dr :: evsR) ∧
      evs.length = B.length ∧ rt = WireKind.root.codec.bytes root ∧
      ((close fin.data.pending).frames.map byteRun)[(frameShape s (B ++ headerReads)).1]? =
        some (X ++ (a ++ b ++ c ++ rt)) := by
  rw [← List.append_assoc] at ok
  obtain ⟨mid4,ok4,okR,_⟩ := replay_append ans cur (B ++ headerReads) (.draw g :: rest) fin ok
  obtain ⟨midB,okB,okH,_⟩ := replay_append ans cur B headerReads mid4 ok4
  obtain ⟨evsB,eventsB,shapesB,_⟩ := replay_apply ans cur B good midB okB
  obtain ⟨_,goodB,_⟩ := replay_shape ans cur B s shaped good midB okB
  obtain ⟨evs4,events4,shapes4,pending4⟩ := replay_apply ans midB headerReads goodB mid4 okH
  obtain ⟨shaped4,good4,_⟩ := replay_shape ans cur (B ++ headerReads) s shaped good mid4 ok4
  obtain ⟨evsD,eventsD,shapesD,pendingD⟩ := replay_apply ans mid4 (.draw g :: rest) good4 fin okR
  unfold headerReads at shapes4
  rcases shapes4 with _ | ⟨⟨va,rfl⟩,_ | ⟨⟨vb,rfl⟩,_ | ⟨⟨vc,rfl⟩,_ | ⟨⟨vr,rfl⟩,_ | _⟩⟩⟩⟩
  rcases shapesD with _ | @⟨_,_,_,evsR,⟨dr,drLength,rfl⟩,_⟩
  have run4 : mid4.data.pending.run = midB.data.pending.run ++
      (WireKind.scalar.codec.bytes va ++ WireKind.scalar.codec.bytes vb ++ WireKind.scalar.codec.bytes vc ++
        WireKind.root.codec.bytes vr) := by
    rw [pending4]
    simp [applyEvents,SpongefishCurrentHistoryReplies.bind_run,List.append_assoc]
  have nonempty : mid4.data.pending.run ≠ [] := by
    rw [run4]
    simp [Codec.bytes,WireKind.codec,rootCodec]
  have positive : dr.length ≠ 0 := by
    rw [drLength]
    exact group_bytes_pos g
  obtain ⟨drawFrames,drawRun,_⟩ := draw_facts mid4.data.pending dr.length positive
  have framesFin : fin.data.pending.frames.map byteRun =
      (mid4.data.pending.frames.map byteRun ++ [mid4.data.pending.run]) ++ chunks [] evsR := by
    rw [pendingD]
    simp only [applyEvents]
    rw [apply_frames,drawFrames,drawRun,close_frames _ nonempty]
    simp [byteRun]
  obtain ⟨t,closeEq⟩ := close_prefix fin.data.pending
  refine ⟨evsB,evsR,WireKind.scalar.codec.bytes va,WireKind.scalar.codec.bytes vb,
    WireKind.scalar.codec.bytes vc,WireKind.root.codec.bytes vr,dr,midB.data.pending.run,vr,?_,
    shapesB.length_eq.symm,rfl,?_⟩
  · rw [eventsD,events4,eventsB]
    simp
  · rw [← closeEq,List.map_append,framesFin,← shaped4.1,run4]
    simp

/-- Number of closed frames right after the anchor draw that closes the commitment header frame, for the replay of `before` followed by the commitment header from the literal initial cursor. -/
def headerFrames (instanceBytes : List Byte) (layout : WHIRCallerClaims.CallerLayout) (before : List Call) : Nat :=
  (openingShape instanceBytes
    (before ++ (SpongefishCurrentAcceptedJoin.headerCalls (AnchoredSourceCaller.shape layout).logN).take 5)).1

theorem headerFrames_eq (instanceBytes : List Byte) (layout : WHIRCallerClaims.CallerLayout)
    (before : List Call) :
    headerFrames instanceBytes layout before =
      (frameShape (0,decide (instanceBytes ≠ [])) (before ++ headerReads)).1 + 1 := by
  unfold headerFrames openingShape
  rw [show (SpongefishCurrentAcceptedJoin.headerCalls (AnchoredSourceCaller.shape layout).logN).take 5 =
    headerReads ++ [.draw (.anchor ((AnchoredSourceCaller.shape layout).logN-1))] from rfl,
    ← List.append_assoc,frameShape_append]
  have ready : (frameShape (0,decide (instanceBytes ≠ [])) (before ++ headerReads)).2 = true := by
    rw [frameShape_append]
    simp [headerReads,frameShape,WireKind.codec,rootCodec]
  simp only [frameShape,ready,↓reduceIte]

/-- A successful getter run of a construction-only program is its run under the fixed coordinate answer that agrees with the getter. -/
theorem run_runWith {A : Type} (get : Query → Option Digest32) (ans : Coordinate → Digest32)
    (agree : ∀ c valid d, get (.construction c valid) = some d → d = ans c) :
    ∀ (prog : Program A), ConstructionOnly prog → ∀ a,
      SpongefishCurrentCallerGetter.run get prog = some a → (runWith ans prog).result = a
  | .done x, _, a, ran => Option.some.inj ran
  | .ask (.construction c valid) next, only, a, ran => by
    obtain ⟨d,got,rest⟩ := Option.bind_eq_some_iff.mp ran
    have same := agree c valid d got
    subst same
    exact run_runWith get ans agree (next (ans c)) (only _) a rest
  | .ask (.primitive _ _) _, only, _, _ => only.elim

/-- The prelude token parser consumes exactly one event per prelude call. -/
theorem tokens_split : ∀ (shape : List WHIRCallerShape.EventShape) (cs : List Call)
    (E R : List SourceEvent) (ts : List WHIRCallerClaims.CallerToken),
    SpongefishCurrentSourceCallerOriginal.shapeCalls shape = some cs →
    SpongefishCurrentSourceCallerOriginal.tokens shape E = some (ts,R) →
      ∃ P, E = P ++ R ∧ P.length = cs.length := by
  intro shape
  induction shape with
  | nil =>
    intro cs E R ts hc ht
    simp only [SpongefishCurrentSourceCallerOriginal.shapeCalls,Option.some.injEq] at hc
    simp only [SpongefishCurrentSourceCallerOriginal.tokens,Option.some.injEq,Prod.mk.injEq] at ht
    subst hc
    exact ⟨[],by simp [ht.2],rfl⟩
  | cons sh shape ih =>
    intro cs E R ts hc ht
    cases sh with
    | absorb n =>
      simp only [SpongefishCurrentSourceCallerOriginal.shapeCalls] at hc
      split at hc
      · obtain ⟨cs',hcs',rfl⟩ := Option.map_eq_some_iff.mp hc
        rcases E with _ | ⟨e,events⟩
        · simp [SpongefishCurrentSourceCallerOriginal.tokens] at ht
        · cases e with
          | prover kind bytes =>
            cases kind with
            | scalar =>
              simp only [SpongefishCurrentSourceCallerOriginal.tokens] at ht
              split at ht
              · contradiction
              · obtain ⟨_,_,ht⟩ := Option.bind_eq_some_iff.mp ht
                obtain ⟨⟨tail,rest⟩,tailEq,ht⟩ := Option.bind_eq_some_iff.mp ht
                cases ht
                obtain ⟨P,split,length⟩ := ih cs' events rest tail hcs' tailEq
                exact ⟨_ :: P,by rw [split]; rfl,by simp [length]⟩
            | _ => simp [SpongefishCurrentSourceCallerOriginal.tokens] at ht
          | _ => simp [SpongefishCurrentSourceCallerOriginal.tokens] at ht
      · contradiction
    | squeeze n =>
      simp only [SpongefishCurrentSourceCallerOriginal.shapeCalls] at hc
      split at hc
      · obtain ⟨cs',hcs',rfl⟩ := Option.map_eq_some_iff.mp hc
        rcases E with _ | ⟨e,events⟩
        · simp [SpongefishCurrentSourceCallerOriginal.tokens] at ht
        · cases e with
          | verifier bytes =>
            simp only [SpongefishCurrentSourceCallerOriginal.tokens] at ht
            split at ht
            · contradiction
            · obtain ⟨_,_,ht⟩ := Option.bind_eq_some_iff.mp ht
              obtain ⟨⟨tail,rest⟩,tailEq,ht⟩ := Option.bind_eq_some_iff.mp ht
              cases ht
              obtain ⟨P,split,length⟩ := ih cs' events rest tail hcs' tailEq
              exact ⟨_ :: P,by rw [split]; rfl,by simp [length]⟩
          | _ => simp [SpongefishCurrentSourceCallerOriginal.tokens] at ht
      · contradiction
    | nonce bits =>
      simp only [SpongefishCurrentSourceCallerOriginal.shapeCalls] at hc
      split at hc
      · obtain ⟨cs',hcs',rfl⟩ := Option.map_eq_some_iff.mp hc
        rcases E with _ | ⟨e,_ | ⟨e',events⟩⟩
        · simp [SpongefishCurrentSourceCallerOriginal.tokens] at ht
        · cases e <;> simp [SpongefishCurrentSourceCallerOriginal.tokens] at ht
        · cases e with
          | verifier challenge =>
            cases e' with
            | prover kind bytes =>
              cases kind with
              | nonce =>
                simp only [SpongefishCurrentSourceCallerOriginal.tokens] at ht
                split at ht
                · contradiction
                · obtain ⟨_,_,ht⟩ := Option.bind_eq_some_iff.mp ht
                  split at ht
                  · contradiction
                  · obtain ⟨⟨tail,rest⟩,tailEq,ht⟩ := Option.bind_eq_some_iff.mp ht
                    cases ht
                    obtain ⟨P,split,length⟩ := ih cs' events rest tail hcs' tailEq
                    exact ⟨_ :: _ :: P,by rw [split]; rfl,by simp [length]⟩
              | _ => simp [SpongefishCurrentSourceCallerOriginal.tokens] at ht
            | _ => simp [SpongefishCurrentSourceCallerOriginal.tokens] at ht
          | _ => simp [SpongefishCurrentSourceCallerOriginal.tokens] at ht
      · contradiction

/-! ## The caller original reads a canonical header from the post-binding history -/

/-- A successful caller original at `q` replays its tape to a closed history equal to `q.history`. In that replay the frame closed by the anchor draw ends with the canonical header bytes of the selected record's root. -/
theorem candidate_header {Q : Nat} (p : ParameterBounds.Profile) (layout : WHIRCallerClaims.CallerLayout)
    (q : Coordinate) (r : SpongefishSessionAdapter.Record) (instanceBytes : List Byte)
    (obs : List Observation) (input : PCSBCSCallerBinding.CallerInput p) (before : List Call)
    (beforeEq : SpongefishCurrentSourceCallerOriginal.shapeCalls
      (SpongefishCurrentSourceCallerOriginal.preludeShape layout) = some before)
    (accepted : SpongefishCurrentSourceCallerOriginal.candidate (Q := Q) p layout q r instanceBytes obs =
      some input) :
    r.shape = AnchoredSourceCaller.shape layout ∧ r.shape.Valid ∧
      ∃ (m : Pending) (X : List Byte), (close m).core.history = q.history ∧
        ((close m).frames.map byteRun)[(frameShape (0,decide (instanceBytes ≠ [])) (before ++ headerReads)).1]? =
          some (X ++ SpongefishCurrentAnchorHeader.bytes r.shape r.root) := by
  unfold SpongefishCurrentSourceCallerOriginal.candidate at accepted
  obtain ⟨result,replayed,finished⟩ := Option.bind_eq_some_iff.mp accepted
  unfold SpongefishCurrentSourceCallerOriginal.replay at replayed
  split at replayed
  · contradiction
  obtain ⟨tape,tapeEq,ran⟩ := Option.bind_eq_some_iff.mp replayed
  unfold SpongefishCurrentSourceCallerOriginal.calls at tapeEq
  obtain ⟨before',before'Eq,tapeEq⟩ := Option.bind_eq_some_iff.mp tapeEq
  rw [beforeEq] at before'Eq
  cases before'Eq
  obtain ⟨payload,_,tapeEq⟩ := Option.bind_eq_some_iff.mp tapeEq
  cases tapeEq
  let ans : Coordinate → Digest32 := fun c => (SpongefishCurrentCallerGetter.bounded (Q := Q) obs c).getD zeroDigest
  have agree : ∀ c valid d, SpongefishCurrentCallerGetter.answer (Q := Q) obs (.construction c valid) = some d →
      d = ans c := by
    intro c valid d got
    simp only [SpongefishCurrentCallerGetter.answer] at got
    simp [ans,got]
  have ok := run_runWith _ ans agree _ (replay_only _ _) result ran
  cases result with
  | error failure =>
    simp [SpongefishCurrentSourceCallerOriginal.finish,eraseResult] at finished
  | ok fin =>
    unfold SpongefishCurrentSourceCallerOriginal.finish at finished
    obtain ⟨d,dEq,finished⟩ := Option.bind_eq_some_iff.mp finished
    simp only [Option.some.injEq] at dEq
    subst dEq
    dsimp only at finished
    split at finished
    · contradiction
    rename_i guards
    have closeEq : (close fin.data.pending).core.history = q.history := by
      by_contra differ
      exact guards (Or.inl differ)
    obtain ⟨events,eventsEq,finished⟩ := Option.bind_eq_some_iff.mp finished
    obtain ⟨claims,parsed,_⟩ := Option.bind_eq_some_iff.mp finished
    unfold SpongefishCurrentSourceCallerOriginal.parseEvents at parsed
    split at parsed
    · contradiction
    rename_i shapeEq
    have shapeEq : r.shape = AnchoredSourceCaller.shape layout := by simpa using shapeEq
    obtain ⟨e1,preludeEq,parsed⟩ := Option.bind_eq_some_iff.mp parsed
    obtain ⟨e2,headerEq,_⟩ := Option.bind_eq_some_iff.mp parsed
    unfold SpongefishCurrentSourceCallerOriginal.prelude at preludeEq
    obtain ⟨⟨ts,e1'⟩,tokensEq,preludeEq⟩ := Option.bind_eq_some_iff.mp preludeEq
    obtain ⟨⟨_,restP⟩,_,preludeEq⟩ := Option.bind_eq_some_iff.mp preludeEq
    have e1Eq : e1' = e1 := by
      by_cases empty : restP = []
      · simpa [empty] using preludeEq
      · simp [empty] at preludeEq
    subst e1Eq
    have form : before ++ [.read .scalar,.read .scalar,.read .scalar,.read .root,
        .draw (.anchor (r.shape.logN-1)),.read .scalar] ++ payload ++
        (SpongefishRecordBindingParser.messages r).map (fun message => Call.read message.1) =
        before ++ (headerReads ++ .draw (.anchor (r.shape.logN-1)) :: (.read .scalar :: (payload ++
          (SpongefishRecordBindingParser.messages r).map (fun message => Call.read message.1)))) := by
      simp [headerReads]
    rw [form] at ok
    obtain ⟨evs,evsR,a,b,c,rt,dr,X,_,events',evsLength,_,frame⟩ := header_frame ans _ _
      (initial_shaped _ _ _ _) (fun _ _ h => by cases h) before _ _ fin ok
    simp only [SpongefishCurrentInitializedMode.initial_data (state := {cv := zeroDigest}),
      SpongefishCurrentMixedModeCompiler.forget,SpongefishCurrentObservedSessionEntry.cursor] at events'
    rw [events'] at eventsEq
    simp only [List.cons_append,
      SpongefishCurrentSourceCallerOriginal.callerEvents,Option.some.injEq] at eventsEq
    subst eventsEq
    obtain ⟨P,split,PLength⟩ := tokens_split _ _ _ _ _ beforeEq tokensEq
    have tailEq := List.append_inj_right split (by simp [PLength,evsLength])
    subst tailEq
    obtain ⟨a',b',c',root',_,_,_,shaped,decoded,_⟩ :=
      SpongefishCurrentSourceCallerOriginal.header_source r _ e2 headerEq
    simp only [List.cons.injEq,SourceEvent.prover.injEq] at shaped
    obtain ⟨⟨_,rfl⟩,⟨_,rfl⟩,⟨_,rfl⟩,⟨_,rfl⟩,_⟩ := shaped
    obtain ⟨valid,source⟩ := SpongefishCurrentAnchorHeader.decode_source _ _ _ _ decoded
    rw [List.append_nil] at source
    refine ⟨shapeEq,valid,fin.data.pending,X,closeEq,?_⟩
    rw [frame,← source]

/-! ## The old source run inside the full program -/

/-- Every leaf of a program satisfies `P`. -/
def Always {S : Type} (P : S → Prop) : Program S → Prop
  | .done s => P s
  | .ask _ next => ∀ d, Always P (next d)

theorem ideal_always {Q : Nat} {Seed State S : Type} (sim : Simulator Q Seed State)
    (ro : RawKey Q → Digest32) (iv : Digest32) (P : S → Prop) (prog : Program S) (always : Always P prog) :
    ∀ (state : State) (remaining : Nat) (cap : remaining ≤ Q) (counted : Counts remaining prog),
      P (runIdeal sim ro iv state prog remaining cap counted).view.result := by
  induction prog with
  | done s => intro _ _ _ _; exact always
  | ask q next ih =>
    cases q with
    | primitive purpose input =>
      intro state remaining cap counted
      simp only [runIdeal,prepend]
      exact ih _ (always _) _ _ _ _
    | construction c valid =>
      intro state remaining cap counted
      simp only [runIdeal,prepend]
      exact ih _ (always _) _ _ _ _

theorem always_bind {R S : Type} (P : S → Prop) (prog : Program R) (k : R → Program S)
    (later : ∀ r, Always P (k r)) : Always P (WHIRModeFinal.bind prog k) := by
  induction prog with
  | done r => exact later r
  | ask q next ih => exact fun d => ih d

variable {p : ParameterBounds.Profile}

theorem openingPhase_always (decode : SpongefishCurrentOpeningProgram.Decoder)
    (grinding : Fin (ParameterBounds.config p).folds.size → Fin 64) (lanes index offset : Nat)
    (res : SpongefishCurrentSourceJoinProbability.SourceResult) :
    Always (fun s : SpongefishCurrentOpeningProgram.FullResult p => s.1 = res)
      (SpongefishCurrentOpeningProgram.openingPhase decode grinding lanes index offset res) := by
  unfold SpongefishCurrentOpeningProgram.openingPhase
  split
  · split
    · rfl
    · exact always_bind _ _ _ (fun _ => rfl)
  · rfl

/-- A successful full-program view on any table contains a successful semantic replay of the whole old call list from a literal initial cursor, under a fixed coordinate answer. -/
theorem full_success {Q : Nat} {Packet : Type} {Block : Packet → Type}
    (part : Partition (PublicCompressionCouplingMixed.Key Q) Packet Block) (iv : Digest32)
    (tag instanceBytes : List Byte) (layout : WHIRCallerClaims.CallerLayout)
    (before payloadCalls messages : List Call) (decode : SpongefishCurrentOpeningProgram.Decoder)
    (grinding : Fin (ParameterBounds.config p).folds.size → Fin 64)
    (prefixProgram : Program SpongefishCurrentInitializedMode.Input)
    (counted : Counts Q (SpongefishCurrentOpeningProgram.fullProgram iv tag instanceBytes layout before
      payloadCalls messages decode grinding prefixProgram))
    (table : (key : part.Key) → part.Answer (D := Digest32) key) (data : Data) (col : Collected p)
    (result : (Sampling.eval table (SpongefishCurrentBCSKnowledge.source part iv
      (SpongefishCurrentOpeningProgram.fullProgram iv tag instanceBytes layout before payloadCalls messages
        decode grinding prefixProgram) counted)).result = (some (.ok data),some col)) :
    ∃ (ans : Coordinate → Digest32) (session : Digest32) (narg : List Byte) (hints : List (List Byte))
      (fin : SemanticCursor),
      (runWith ans (replayProgram (SpongefishCurrentInitializedMode.initial session instanceBytes narg hints)
        (SpongefishCurrentSourceJoinProbability.calls layout before payloadCalls messages grinding))).result =
          .ok fin ∧ fin.data = data := by
  let program := SpongefishCurrentSourceJoinProbability.program iv tag instanceBytes layout before
    payloadCalls messages grinding prefixProgram
  let k := SpongefishCurrentOpeningProgram.openingPhase decode grinding
    (AnchoredSourceCaller.shape layout).lanes (SpongefishCurrentOpeningProgram.rootIndex before)
    (SpongefishCurrentOpeningProgram.openingOffset layout before payloadCalls messages)
  obtain ⟨state,rest,cap,counted',same⟩ := source_bind part iv program k counted table
  have kept := ideal_always (DuplexPublicSimulator.simulator Q) (roOf part table) iv _ _ (openingPhase_always (p := p) decode grinding _ _ _
    (Sampling.eval table (SpongefishCurrentBCSKnowledge.source part iv program
      (WHIRModeFinal.bind_prefix_counted program k Q counted))).result) state rest cap counted'
  have resultEq := congrArg View.result same
  change (Sampling.eval table (SpongefishCurrentBCSKnowledge.source part iv
      (SpongefishCurrentOpeningProgram.fullProgram iv tag instanceBytes layout before payloadCalls messages
        decode grinding prefixProgram) counted)).result = _ at resultEq
  rw [result] at resultEq
  rw [← resultEq] at kept
  have success := kept.symm
  rw [eval_source] at success
  obtain ⟨session,narg,hints,fin,replayOk,finData,_⟩ := afterPrefix_replay
    (DuplexPublicSimulator.simulator Q) (roOf part table) iv tag instanceBytes prefixProgram
    (SpongefishCurrentSourceJoinProbability.calls layout before payloadCalls messages grinding) _ Q
    (Nat.le_refl Q) _ data success
  exact ⟨_,session,narg,hints,fin,replayOk,finData⟩

/-! ## Opening events and the commitment header in the full program -/

/-- The two opening event segments agree on any event list with one call event per call of the old source program after the public instance event. -/
theorem openingEvents_eq (layout : WHIRCallerClaims.CallerLayout) (before payloadCalls messages : List Call)
    (grinding : Fin (ParameterBounds.config p).folds.size → Fin 64) (instanceBytes : List Byte) (data : Data)
    (evs : List SourceEvent) (events : data.events = .publicBytes instanceBytes :: evs)
    (shapes : List.Forall₂ SpongefishCurrentOpeningProgram.CallEvent
      (SpongefishCurrentSourceJoinProbability.calls layout before payloadCalls messages grinding) evs) :
    SpongefishCurrentOpeningProgram.openingEvents
        (SpongefishCurrentOpeningProgram.openingOffset layout before payloadCalls messages) data =
      SpongefishCurrentOpeningPackets.openingEvents grinding data.events := by
  have length := shapes.length_eq
  unfold SpongefishCurrentOpeningProgram.openingEvents SpongefishCurrentOpeningPackets.openingEvents
    SpongefishCurrentOpeningProgram.openingOffset
  congr 1
  rw [events,List.length_cons,← length]
  simp only [SpongefishCurrentSourceJoinProbability.calls,List.length_append]
  omega

/-- On every table, a successful full-program view has the same opening events under the offset of the opening walk and under the opening packets. -/
theorem openingEvents_full {Q : Nat} {Packet : Type} {Block : Packet → Type}
    (part : Partition (PublicCompressionCouplingMixed.Key Q) Packet Block) (iv : Digest32)
    (tag instanceBytes : List Byte) (layout : WHIRCallerClaims.CallerLayout)
    (before payloadCalls messages : List Call) (decode : SpongefishCurrentOpeningProgram.Decoder)
    (grinding : Fin (ParameterBounds.config p).folds.size → Fin 64)
    (prefixProgram : Program SpongefishCurrentInitializedMode.Input)
    (counted : Counts Q (SpongefishCurrentOpeningProgram.fullProgram iv tag instanceBytes layout before
      payloadCalls messages decode grinding prefixProgram))
    (table : (key : part.Key) → part.Answer (D := Digest32) key) (data : Data) (col : Collected p)
    (result : (Sampling.eval table (SpongefishCurrentBCSKnowledge.source part iv
      (SpongefishCurrentOpeningProgram.fullProgram iv tag instanceBytes layout before payloadCalls messages
        decode grinding prefixProgram) counted)).result = (some (.ok data),some col)) :
    SpongefishCurrentOpeningProgram.openingEvents
        (SpongefishCurrentOpeningProgram.openingOffset layout before payloadCalls messages) data =
      SpongefishCurrentOpeningPackets.openingEvents grinding data.events := by
  obtain ⟨ans,session,narg,hints,fin,ok,finData⟩ := full_success part iv tag instanceBytes layout before
    payloadCalls messages decode grinding prefixProgram counted table data col result
  subst finData
  obtain ⟨evs,events,shapes,_⟩ := replay_apply ans _ _ (fun _ _ h => by cases h) fin ok
  exact openingEvents_eq layout before payloadCalls messages grinding instanceBytes fin.data evs
    (by rw [events]; rfl) shapes

theorem frameShape_mono : ∀ (s : Nat × Bool) (xs : List Call), s.1 ≤ (frameShape s xs).1
  | _, [] => le_rfl
  | s, .read kind :: rest => frameShape_mono (s.1,s.2 || decide (kind.codec.size ≠ 0)) rest
  | s, .hint :: rest => frameShape_mono s rest
  | s, .draw _ :: rest => by
    have later := frameShape_mono (if s.2 then s.1+1 else s.1,false) rest
    simp only [frameShape]
    exact le_trans (b := if s.2 = true then s.1+1 else s.1) (by split <;> omega) later

/-- The header frame count is at most the post-binding frame count. -/
theorem headerFrames_le (instanceBytes : List Byte) (layout : WHIRCallerClaims.CallerLayout)
    (before payloadCalls messages : List Call) (boundary : Nat)
    (opening : openingShape instanceBytes (before ++
      SpongefishCurrentAcceptedJoin.headerCalls (AnchoredSourceCaller.shape layout).logN ++ payloadCalls ++
        messages) = (boundary,true)) :
    headerFrames instanceBytes layout before ≤ boundary + 1 := by
  have split : before ++ SpongefishCurrentAcceptedJoin.headerCalls (AnchoredSourceCaller.shape layout).logN ++
      payloadCalls ++ messages =
      (before ++ (SpongefishCurrentAcceptedJoin.headerCalls (AnchoredSourceCaller.shape layout).logN).take 5) ++
        (.read .scalar :: (payloadCalls ++ messages)) := by
    simp [SpongefishCurrentAcceptedJoin.headerCalls]
  unfold openingShape at opening
  rw [split,frameShape_append] at opening
  have grow := frameShape_mono (frameShape (0,decide (instanceBytes ≠ []))
    (before ++ (SpongefishCurrentAcceptedJoin.headerCalls (AnchoredSourceCaller.shape layout).logN).take 5))
    (.read .scalar :: (payloadCalls ++ messages))
  rw [opening] at grow
  unfold headerFrames openingShape
  omega

/-- On every table, a successful full-program view whose post-binding caller original succeeds decodes the commitment root of the header root event from the header frames of the post-binding history. -/
theorem header_full {Q : Nat} {Packet : Type} {Block : Packet → Type}
    (part : Partition (PublicCompressionCouplingMixed.Key Q) Packet Block) (iv : Digest32)
    (tag instanceBytes : List Byte) (layout : WHIRCallerClaims.CallerLayout)
    (before payloadCalls messages : List Call) (decode : SpongefishCurrentOpeningProgram.Decoder)
    (grinding : Fin (ParameterBounds.config p).folds.size → Fin 64)
    (prefixProgram : Program SpongefishCurrentInitializedMode.Input)
    (beforeEq : SpongefishCurrentSourceCallerOriginal.shapeCalls
      (SpongefishCurrentSourceCallerOriginal.preludeShape layout) = some before)
    (counted : Counts Q (SpongefishCurrentOpeningProgram.fullProgram iv tag instanceBytes layout before
      payloadCalls messages decode grinding prefixProgram))
    (table : (key : part.Key) → part.Answer (D := Digest32) key) (data : Data) (col : Collected p)
    (result : (Sampling.eval table (SpongefishCurrentBCSKnowledge.source part iv
      (SpongefishCurrentOpeningProgram.fullProgram iv tag instanceBytes layout before payloadCalls messages
        decode grinding prefixProgram) counted)).result = (some (.ok data),some col))
    (boundary B : Nat) (r : SpongefishSessionAdapter.Record) (input : PCSBCSCallerBinding.CallerInput p)
    (obs : List Observation)
    (accepted : SpongefishCurrentSourceCallerOriginal.candidate (Q := B) p layout
      (SpongefishCurrentGoodEvent.postBinding boundary data) r instanceBytes obs = some input)
    (root0 : Digest32)
    (rootEq : SpongefishCurrentOpeningProgram.headerRoot (SpongefishCurrentOpeningProgram.rootIndex before)
      data.events = some root0) :
    SpongefishCurrentAnchorHeader.fromHistory (AnchoredSourceCaller.shape layout)
      {(SpongefishCurrentGoodEvent.postBinding boundary data).history with
        frames := (SpongefishCurrentGoodEvent.postBinding boundary data).history.frames.take
          (headerFrames instanceBytes layout before)} = some root0 := by
  obtain ⟨ans,session,narg,hints,fin,ok,finData⟩ := full_success part iv tag instanceBytes layout before
    payloadCalls messages decode grinding prefixProgram counted table data col result
  subst finData
  have form : SpongefishCurrentSourceJoinProbability.calls layout before payloadCalls messages grinding =
      before ++ (headerReads ++ .draw (.anchor ((AnchoredSourceCaller.shape layout).logN-1)) ::
        (.read .scalar :: (payloadCalls ++ messages ++ openingCalls grinding))) := by
    simp [SpongefishCurrentSourceJoinProbability.calls,SpongefishCurrentAcceptedJoin.headerCalls,headerReads]
  rw [form] at ok
  obtain ⟨evs,evsR,a,b,c,rt,dr,X,root,events,evsLength,rtEq,frame⟩ := header_frame ans _ _
    (initial_shaped _ _ _ _) (fun _ _ h => by cases h) before _ _ fin ok
  obtain ⟨shapeEq,valid,m,X',closeEq,frame'⟩ := candidate_header p layout _ r instanceBytes obs input before
    beforeEq accepted
  rw [headerFrames_eq]
  generalize (frameShape (0,decide (instanceBytes ≠ [])) (before ++ headerReads)).1 = N at frame frame'
  have hFrames : (SpongefishCurrentGoodEvent.postBinding boundary fin.data).history.frames =
      (close m).frames.map ByteFrame.historicalCore := by
    rw [← closeEq]
    rfl
  have postFrames : (SpongefishCurrentGoodEvent.postBinding boundary fin.data).history.frames =
      ((close fin.data.pending).frames.map ByteFrame.historicalCore).take (boundary+1) := rfl
  have sameBytes : (close m).frames.map byteRun = ((close fin.data.pending).frames.map byteRun).take (boundary+1) := by
    have := congrArg (List.map frameBytes) (hFrames.symm.trans postFrames)
    simpa only [List.map_map,← List.map_take,
      show frameBytes ∘ ByteFrame.historicalCore = byteRun from funext frameBytes_core] using this
  have origAt := frame'
  rw [sameBytes,List.getElem?_take] at origAt
  split_ifs at origAt
  rw [frame,Option.some.injEq] at origAt
  have rootBytes : rt = SpongefishSessionAdapter.rawRoot r.root := by
    apply List.append_inj_right' (s₁ := X ++ (a ++ b ++ c)) (s₂ := X' ++
      SpongefishSessionAdapter.scalarsBytes
        (SpongefishSessionAdapter.constants AnchoredHeaderCodec.anchorMarker r.shape))
    · simpa [SpongefishCurrentAnchorHeader.bytes,SpongefishSessionAdapter.commitPrefix,List.append_assoc] using origAt
    · rw [rtEq]
      simp [SpongefishSessionAdapter.rawRoot,Codec.bytes,WireKind.codec,rootCodec]
  have rootIs : SpongefishCurrentOpeningProgram.headerRoot (SpongefishCurrentOpeningProgram.rootIndex before)
      fin.data.events = some r.root := by
    rw [events]
    unfold SpongefishCurrentOpeningProgram.headerRoot SpongefishCurrentOpeningProgram.rootIndex
    simp only [SpongefishCurrentInitializedMode.initial_data (state := {cv := zeroDigest}),
      SpongefishCurrentMixedModeCompiler.forget,SpongefishCurrentObservedSessionEntry.cursor]
    rw [show 1 + before.length + 3 = ([SourceEvent.publicBytes instanceBytes] ++ evs).length + 3 by
      simp [evsLength]; omega]
    rw [List.getElem?_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left,List.getElem?_cons_succ,List.getElem?_cons_zero,rootBytes]
    have parsed := Codec.parse_append rootCodec r.root []
    rw [List.append_nil] at parsed
    simp only [WireKind.codec]
    rw [show SpongefishSessionAdapter.rawRoot r.root = rootCodec.bytes r.root from rfl,parsed]
    rfl
  rw [rootIs,Option.some.injEq] at rootEq
  subst rootEq
  obtain ⟨f,fAt,fBytes⟩ : ∃ f, (close m).frames[N]? = some f ∧
      byteRun f = X' ++ SpongefishCurrentAnchorHeader.bytes r.shape r.root := by
    rw [List.getElem?_map] at frame'
    obtain ⟨f,fAt,fEq⟩ := Option.map_eq_some_iff.mp frame'
    exact ⟨f,fAt,fEq⟩
  cases f with
  | absorb previous source =>
    simp only [byteRun] at fBytes
    unfold SpongefishCurrentAnchorHeader.fromHistory
    rw [hFrames,List.take_add_one,List.getElem?_map,fAt]
    simp only [Option.map_some,Option.toList_some,ByteFrame.historicalCore,List.getLast?_append,
      List.getLast?_singleton,Option.some_or]
    rw [fBytes,← shapeEq]
    exact SpongefishCurrentAnchorHeader.suffix_recovery r.shape valid r.root X'

#print axioms header_frame
#print axioms headerFrames_eq
#print axioms tokens_split
#print axioms candidate_header
#print axioms full_success
#print axioms openingEvents_eq
#print axioms openingEvents_full
#print axioms headerFrames_le
#print axioms header_full

end Whir.SpongefishCurrentHeaderGlue
