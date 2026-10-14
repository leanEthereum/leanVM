import Whir.SpongefishCurrentBCSKnowledge
import Whir.PCSBCSNativePublicCapture

/-! Table-getter form of the current #607 public caller reconstruction.

`tableCandidate` is the computation of `SpongefishCurrentSourceCallerOriginal.candidate`
with construction queries of the caller replay answered by an arbitrary coordinate getter.
The getter carries any budget restriction itself. Results:

* `candidate_tableCandidate`: an accepted observation-list candidate is accepted with
  every getter that agrees with the in-budget construction observations.
* `tableCandidate_local`: the candidate reads the getter only at coordinates whose
  history has strictly fewer frames than the post-binding history `q.history`. With
  `boundary + 1 = q.history.frames.length`, every opening packet (more than `boundary`
  frames) is outside the queried set (`tableCandidate_boundary`).
* `recordOf`: unique selection of the received record among the raw-key record
  candidates by its binding message calls.
* `physicalCandidate_tableCandidate`, `candidate_table`, `candidate_packets`: the real
  construction oracle, any raw table, and any joined packet table are admissible getters.
* `native_selected`: all of the above at the post-binding coordinate of `NativeAcceptedBad`. -/
namespace Whir.SpongefishCurrentCallerOriginalTable
open Concrete FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame
open SpongefishPCSRoundFrames SpongefishCurrentModeQueries SpongefishCurrentMixedModeCompiler
open SpongefishCurrentSourceCallerOriginal
set_option autoImplicit false

abbrev run {A : Type} := @SpongefishCurrentCallerGetter.run A

/-! ## Generic getter lemmas for `SpongefishCurrentCallerGetter.run` -/

theorem run_seq {A B : Type} (get : Query → Option Digest32) (p : Program A)
    (f : A → Program B) :
    run get (WHIRModeFinal.bind p f) = (run get p).bind (fun a => run get (f a)) := by
  induction p with
  | done a => simp [WHIRModeFinal.bind,run,SpongefishCurrentCallerGetter.run]
  | ask q next ih =>
    simp only [WHIRModeFinal.bind,run,SpongefishCurrentCallerGetter.run] at ih ⊢
    cases get q with
    | none => rfl
    | some d => simpa only [Option.bind_some] using ih d

/-- A getter extending another getter on every answered query preserves every
successful run. Only queries actually issued matter. -/
theorem run_extend {A : Type} (a b : Query → Option Digest32)
    (extends_ : ∀ query d, a query = some d → b query = some d) (p : Program A) (x : A)
    (accepted : run a p = some x) : run b p = some x := by
  induction p with
  | done => exact accepted
  | ask q next ih =>
    simp only [run,SpongefishCurrentCallerGetter.run] at accepted ⊢
    obtain ⟨d,found,rest⟩ := Option.bind_eq_some_iff.mp accepted
    rw [extends_ q d found,Option.bind_some]
    exact ih d rest

/-! ## Cursor rank -/

/-- Twice the closed frame count, minus one while a prover run is still open. -/
def rank (m : Pending) : Nat := 2 * m.frames.length + if m.run = [] then 0 else 1

theorem rank_bind (m : Pending) (bytes : List Byte) :
    rank m ≤ rank (SpongefishPCSRoundFrames.bind m bytes) := by
  by_cases empty : bytes = []
  · simp [SpongefishPCSRoundFrames.bind,empty]
  · simp only [rank,SpongefishPCSRoundFrames.bind,empty,↓reduceIte,List.append_eq_nil_iff,
      and_false]
    split <;> omega

theorem rank_draw (m : Pending) (n : Nat) : rank m ≤ rank (draw m n) := by
  by_cases zero : n = 0
  · simp [draw,zero]
  · by_cases open_ : m.run = []
    · simp [rank,draw,close,zero,open_]
    · simp [rank,draw,close,zero,open_]

theorem rank_draw_positive (m : Pending) (n : Nat) (positive : n ≠ 0) :
    rank (draw m n) = 2 * (close m).frames.length := by
  by_cases open_ : m.run = []
  · simp [rank,draw,close,positive,open_]
  · simp [rank,draw,close,positive,open_]

theorem rank_open (m : Pending) (open_ : m.run ≠ []) :
    rank m + 1 = 2 * (close m).frames.length := by
  simp [rank,close,open_]
  omega

theorem coordinate_frames (m : Pending) (block : Nat) :
    (coordinate m block).history.frames.length = (close m).frames.length := by
  simp [coordinate,Pending.core]

/-! ## Replay structure -/

theorem request_congr (a b : Query → Option Digest32) (cache : Cache) (q : Coordinate)
    (valid : DuplexEncoding.Admissible q)
    (agree : a (.construction q valid) = b (.construction q valid)) :
    run a (request cache q valid) = run b (request cache q valid) := by
  unfold request
  cases cache q with
  | some d => rfl
  | none => simp only [run,SpongefishCurrentCallerGetter.run,agree]

theorem collect_congr (a b : Query → Option Digest32) (m : Pending)
    (agree : ∀ block valid, a (.construction (coordinate m block) valid) =
      b (.construction (coordinate m block) valid)) :
    ∀ (ps : List Nat) (valid : ∀ p ∈ ps, DuplexEncoding.Admissible (coordinate m (p/32)))
      (cache : Cache), run a (collect m ps valid cache) = run b (collect m ps valid cache)
  | [], _, _ => rfl
  | p :: ps, valid, cache => by
    simp only [collect,seq,run_seq,request_congr a b cache _ _ (agree _ _)]
    congr 1
    funext x
    obtain ⟨next,d⟩ := x
    rw [collect_congr a b m agree ps]
    rfl

theorem replay_mono (get : Query → Option Digest32) :
    ∀ (calls : List Call) (cur last : SemanticCursor),
      run get (replayProgram cur calls) = some (.ok last) →
        rank cur.data.pending ≤ rank last.data.pending
  | [], cur, last, accepted => by
    simp only [replayProgram,run,SpongefishCurrentCallerGetter.run,Option.some.injEq,
      Except.ok.injEq] at accepted
    rw [accepted]
  | .read kind :: calls, cur, last, accepted => by
    simp only [replayProgram] at accepted
    split at accepted
    · simp [run,SpongefishCurrentCallerGetter.run] at accepted
    · rename_i value rest _
      exact (rank_bind _ _).trans (replay_mono get calls _ last accepted)
  | .hint :: calls, cur, last, accepted => by
    simp only [replayProgram] at accepted
    split at accepted
    · simp [run,SpongefishCurrentCallerGetter.run] at accepted
    · have grown := replay_mono get calls _ last accepted
      exact grown
  | .draw g :: calls, cur, last, accepted => by
    simp only [replayProgram] at accepted
    split at accepted
    · have grown := replay_mono get calls _ last accepted
      exact grown
    · split at accepted
      · rw [run_seq] at accepted
        obtain ⟨⟨cache,bytes⟩,_,rest⟩ := Option.bind_eq_some_iff.mp accepted
        exact (rank_draw _ _).trans (replay_mono get calls _ last rest)
      · simp [run,SpongefishCurrentCallerGetter.run] at accepted

/-- Transfer of an accepted replay between getters that agree on every
construction coordinate of rank-bounded history. -/
theorem replay_transfer (a b : Query → Option Digest32) (N : Nat)
    (agree : ∀ q valid, 2 * q.history.frames.length < N →
      a (.construction q valid) = b (.construction q valid)) :
    ∀ (calls : List Call) (cur last : SemanticCursor),
      run a (replayProgram cur calls) = some (.ok last) → rank last.data.pending < N →
        run b (replayProgram cur calls) = some (.ok last)
  | [], cur, last, accepted, _ => accepted
  | .read kind :: calls, cur, last, accepted, small => by
    simp only [replayProgram] at accepted ⊢
    split at accepted
    · simp [run,SpongefishCurrentCallerGetter.run] at accepted
    · rename_i value rest _
      exact replay_transfer a b N agree calls _ last accepted small
  | .hint :: calls, cur, last, accepted, small => by
    simp only [replayProgram] at accepted ⊢
    split at accepted
    · simp [run,SpongefishCurrentCallerGetter.run] at accepted
    · rename_i bytes rest _
      exact replay_transfer a b N agree calls _ last accepted small
  | .draw g :: calls, cur, last, accepted, small => by
    simp only [replayProgram] at accepted ⊢
    split at accepted
    · rename_i zero
      simp only [zero,↓reduceDIte]
      exact replay_transfer a b N agree calls _ last accepted small
    · rename_i zero
      simp only [zero,↓reduceDIte]
      split at accepted
      · rename_i guard
        simp only [guard,↓reduceDIte]
        rw [run_seq] at accepted ⊢
        obtain ⟨⟨cache,bytes⟩,collected,rest⟩ := Option.bind_eq_some_iff.mp accepted
        have grown := replay_mono a calls _ last rest
        have level : 2 * (close cur.data.pending).frames.length < N := by
          have drawn := rank_draw_positive cur.data.pending g.bytes zero
          simp only [SpongefishCurrentMixedModeCompiler.drawn] at grown
          omega
        rw [← collect_congr a b cur.data.pending (fun block valid => agree _ valid
          (by rw [coordinate_frames]; exact level)), collected,Option.bind_some]
        exact replay_transfer a b N agree calls _ last rest small
      · simp [run,SpongefishCurrentCallerGetter.run] at accepted

/-- A replay whose tape ends with a read of positive width ends with an open run. -/
theorem replay_last_read (get : Query → Option Digest32) (kind : WireKind)
    (positive : kind.codec.size ≠ 0) :
    ∀ (pre : List Call) (cur last : SemanticCursor),
      run get (replayProgram cur (pre ++ [.read kind])) = some (.ok last) →
        last.data.pending.run ≠ []
  | [], cur, last, accepted => by
    simp only [List.nil_append,replayProgram] at accepted
    split at accepted
    · simp [run,SpongefishCurrentCallerGetter.run] at accepted
    · rename_i value rest _
      simp only [run,SpongefishCurrentCallerGetter.run,Option.some.injEq,Except.ok.injEq] at accepted
      subst last
      simp only [readNext,boundData,SpongefishCurrentRecordModeCapture.bind_run]
      intro empty
      have len := congrArg List.length empty
      simp [Codec.bytes] at len
      omega
  | .read k :: pre, cur, last, accepted => by
    simp only [List.cons_append,replayProgram] at accepted
    split at accepted
    · simp [run,SpongefishCurrentCallerGetter.run] at accepted
    · exact replay_last_read get kind positive pre _ last accepted
  | .hint :: pre, cur, last, accepted => by
    simp only [List.cons_append,replayProgram] at accepted
    split at accepted
    · simp [run,SpongefishCurrentCallerGetter.run] at accepted
    · exact replay_last_read get kind positive pre _ last accepted
  | .draw g :: pre, cur, last, accepted => by
    simp only [List.cons_append,replayProgram] at accepted
    split at accepted
    · exact replay_last_read get kind positive pre _ last accepted
    · split at accepted
      · rw [run_seq] at accepted
        obtain ⟨⟨cache,bytes⟩,_,rest⟩ := Option.bind_eq_some_iff.mp accepted
        exact replay_last_read get kind positive pre _ last rest
      · simp [run,SpongefishCurrentCallerGetter.run] at accepted

/-! ## Getter-parametric caller candidate -/

/-- The literal caller replay start of `SpongefishCurrentSourceCallerOriginal.replay`. -/
def start (q : Coordinate) (instanceBytes : List Byte) : SemanticCursor :=
  SpongefishCurrentInitializedMode.initial q.history.domain instanceBytes
    ((historyBytes q).drop instanceBytes.length) []

/-- `SpongefishCurrentSourceCallerOriginal.replay` with an arbitrary query getter. -/
def replayWith (get : Query → Option Digest32) (layout : WHIRCallerClaims.CallerLayout)
    (q : Coordinate) (r : SpongefishSessionAdapter.Record) (instanceBytes : List Byte) :
    Option Result := do
  if supported q instanceBytes = false then none else do
    let tape ← calls layout r
    SpongefishCurrentCallerGetter.run get (replayProgram (start q instanceBytes) tape)

/-- `SpongefishCurrentSourceCallerOriginal.candidate` with an arbitrary query getter. -/
def candidateWith (get : Query → Option Digest32) (p : ParameterBounds.Profile)
    (layout : WHIRCallerClaims.CallerLayout) (q : Coordinate) (r : SpongefishSessionAdapter.Record)
    (instanceBytes : List Byte) : Option (PCSBCSCallerBinding.CallerInput p) := do
  let result ← replayWith get layout q r instanceBytes
  finish p layout q r (eraseResult result)

theorem candidate_with {Q : Nat} (p : ParameterBounds.Profile)
    (layout : WHIRCallerClaims.CallerLayout) (q : Coordinate) (r : SpongefishSessionAdapter.Record)
    (instanceBytes : List Byte) (observations : List Observation) :
    candidate (Q := Q) p layout q r instanceBytes observations =
      candidateWith (SpongefishCurrentCallerGetter.answer (Q := Q) observations) p layout q r
        instanceBytes := rfl

/-- Construction queries are answered by a coordinate getter; primitive queries
(never issued by the caller replay) are rejected. -/
def tableAnswer (getter : Coordinate → Option Digest32) : Query → Option Digest32
  | .construction q _ => getter q
  | .primitive _ _ => none

/-- Table-getter caller reconstruction. Budget restrictions belong to the getter. -/
def tableCandidate (p : ParameterBounds.Profile) (layout : WHIRCallerClaims.CallerLayout)
    (q : Coordinate) (r : SpongefishSessionAdapter.Record) (instanceBytes : List Byte)
    (getter : Coordinate → Option Digest32) : Option (PCSBCSCallerBinding.CallerInput p) :=
  candidateWith (tableAnswer getter) p layout q r instanceBytes

theorem candidateWith_eq_some (get : Query → Option Digest32) (p : ParameterBounds.Profile)
    (layout : WHIRCallerClaims.CallerLayout) (q : Coordinate) (r : SpongefishSessionAdapter.Record)
    (instanceBytes : List Byte) (input : PCSBCSCallerBinding.CallerInput p) :
    candidateWith get p layout q r instanceBytes = some input ↔
      ∃ tape last, supported q instanceBytes = true ∧ calls layout r = some tape ∧
        run get (replayProgram (start q instanceBytes) tape) = some (.ok last) ∧
        finish p layout q r (.ok last.data) = some input := by
  constructor
  · intro accepted
    obtain ⟨result,replayed,finished⟩ := Option.bind_eq_some_iff.mp accepted
    unfold replayWith at replayed
    by_cases unsupported : supported q instanceBytes = false
    · simp [unsupported] at replayed
    · have sup : supported q instanceBytes = true := by simpa using unsupported
      simp only [sup,Bool.true_eq_false,↓reduceIte] at replayed
      obtain ⟨tape,tapeEq,ran⟩ := Option.bind_eq_some_iff.mp replayed
      obtain ⟨data,_,ok,_⟩ := finish_exact p layout q r _ input finished
      cases result with
      | error e => cases ok
      | ok last => exact ⟨tape,last,sup,tapeEq,ran,finished⟩
  · rintro ⟨tape,last,sup,tapeEq,ran,finished⟩
    have replayed : replayWith get layout q r instanceBytes = some (.ok last) := by
      unfold replayWith
      simp only [sup,Bool.true_eq_false,↓reduceIte]
      rw [tapeEq]
      exact ran
    unfold candidateWith
    rw [replayed]
    exact finished

theorem candidateWith_extend (a b : Query → Option Digest32)
    (extends_ : ∀ query d, a query = some d → b query = some d) (p : ParameterBounds.Profile)
    (layout : WHIRCallerClaims.CallerLayout) (q : Coordinate) (r : SpongefishSessionAdapter.Record)
    (instanceBytes : List Byte) (input : PCSBCSCallerBinding.CallerInput p)
    (accepted : candidateWith a p layout q r instanceBytes = some input) :
    candidateWith b p layout q r instanceBytes = some input := by
  obtain ⟨tape,last,sup,tapeEq,ran,finished⟩ :=
    (candidateWith_eq_some a p layout q r instanceBytes input).mp accepted
  exact (candidateWith_eq_some b p layout q r instanceBytes input).mpr
    ⟨tape,last,sup,tapeEq,run_extend a b extends_ _ _ ran,finished⟩

/-- Getters agreeing on every construction query accept the same candidates. -/
theorem candidateWith_constructions (a b : Query → Option Digest32)
    (agree : ∀ c valid, a (.construction c valid) = b (.construction c valid))
    (p : ParameterBounds.Profile) (layout : WHIRCallerClaims.CallerLayout) (q : Coordinate)
    (r : SpongefishSessionAdapter.Record) (instanceBytes : List Byte)
    (input : PCSBCSCallerBinding.CallerInput p)
    (accepted : candidateWith a p layout q r instanceBytes = some input) :
    candidateWith b p layout q r instanceBytes = some input := by
  obtain ⟨tape,last,sup,tapeEq,ran,finished⟩ :=
    (candidateWith_eq_some a p layout q r instanceBytes input).mp accepted
  exact (candidateWith_eq_some b p layout q r instanceBytes input).mpr
    ⟨tape,last,sup,tapeEq,replay_transfer a b (rank last.data.pending + 1)
      (fun c valid _ => agree c valid) _ _ last ran (by omega),finished⟩

theorem lookup_sound (c : Coordinate) : ∀ (observations : List Observation) (d : Digest32),
    SpongefishCurrentCallerGetter.lookup c observations = some d →
      ∃ o ∈ observations, ∃ valid, o.query = .construction c valid ∧ o.answer = d
  | [], d, found => by simp [SpongefishCurrentCallerGetter.lookup] at found
  | o :: os, d, found => by
    simp only [SpongefishCurrentCallerGetter.lookup] at found
    split at found
    · rename_i other valid query
      split at found
      · rename_i same
        subst same
        exact ⟨o,List.mem_cons_self,valid,query,Option.some.inj found⟩
      · obtain ⟨x,member,rest⟩ := lookup_sound c os d found
        exact ⟨x,List.mem_cons_of_mem _ member,rest⟩
    · obtain ⟨x,member,rest⟩ := lookup_sound c os d found
      exact ⟨x,List.mem_cons_of_mem _ member,rest⟩

/-- Item 1: an accepted observation-list candidate is accepted by every coordinate
getter that returns the recorded answer at each in-budget construction observation. -/
theorem candidate_tableCandidate {Q : Nat} (p : ParameterBounds.Profile)
    (layout : WHIRCallerClaims.CallerLayout) (q : Coordinate) (r : SpongefishSessionAdapter.Record)
    (instanceBytes : List Byte) (observations : List Observation)
    (getter : Coordinate → Option Digest32) (input : PCSBCSCallerBinding.CallerInput p)
    (accepted : candidate (Q := Q) p layout q r instanceBytes observations = some input)
    (agree : ∀ o ∈ observations, ∀ c valid, o.query = .construction c valid → pathCost c ≤ Q →
      getter c = some o.answer) :
    tableCandidate p layout q r instanceBytes getter = some input := by
  apply candidateWith_extend _ _ _ p layout q r instanceBytes input accepted
  intro query d found
  cases query with
  | primitive => cases found
  | construction c valid =>
    simp only [SpongefishCurrentCallerGetter.answer,SpongefishCurrentCallerGetter.bounded] at found
    split at found
    · rename_i work
      obtain ⟨o,member,v,query,answer⟩ := lookup_sound c observations d found
      rw [← answer]
      exact agree o member c v query work
    · cases found

/-! ## Locality: only histories strictly shorter than the post-binding history -/

/-- The caller tape ends with the record value read. -/
theorem calls_last (layout : WHIRCallerClaims.CallerLayout) (r : SpongefishSessionAdapter.Record)
    (tape : List Call) (tapeEq : calls layout r = some tape) :
    ∃ pre, tape = pre ++ [.read .scalar] := by
  unfold calls at tapeEq
  obtain ⟨before,_,tapeEq⟩ := Option.bind_eq_some_iff.mp tapeEq
  obtain ⟨payload,_,tapeEq⟩ := Option.bind_eq_some_iff.mp tapeEq
  obtain ⟨M,messagesEq⟩ : ∃ M, SpongefishRecordBindingParser.messages r =
      M ++ [⟨.scalar,r.value⟩] := ⟨_,rfl⟩
  refine ⟨before ++ [.read .scalar,.read .scalar,.read .scalar,.read .root,
    .draw (.anchor (r.shape.logN-1)),.read .scalar] ++ payload ++
    M.map (fun message => .read message.1),?_⟩
  rw [← Option.some.inj tapeEq,messagesEq,List.map_append]
  simp

theorem tableCandidate_local_some (p : ParameterBounds.Profile)
    (layout : WHIRCallerClaims.CallerLayout) (q : Coordinate) (r : SpongefishSessionAdapter.Record)
    (instanceBytes : List Byte) (g h : Coordinate → Option Digest32)
    (agree : ∀ c, c.history.frames.length < q.history.frames.length → g c = h c)
    (input : PCSBCSCallerBinding.CallerInput p)
    (accepted : tableCandidate p layout q r instanceBytes g = some input) :
    tableCandidate p layout q r instanceBytes h = some input := by
  obtain ⟨tape,last,sup,tapeEq,ran,finished⟩ :=
    (candidateWith_eq_some _ p layout q r instanceBytes input).mp accepted
  obtain ⟨data,_,ok,history,_⟩ := finish_exact p layout q r _ input finished
  cases ok
  obtain ⟨pre,rfl⟩ := calls_last layout r tape tapeEq
  have open_ := replay_last_read _ .scalar (by decide) pre _ last ran
  have closed := rank_open _ open_
  have frames : (close last.data.pending).frames.length = q.history.frames.length := by
    rw [← history]
    simp [Pending.core]
  refine (candidateWith_eq_some _ p layout q r instanceBytes input).mpr
    ⟨_,last,sup,tapeEq,?_,finished⟩
  exact replay_transfer _ _ (2 * q.history.frames.length)
    (fun c valid small => agree c (by omega)) _ _ last ran (by omega)

/-- Item 2: `tableCandidate` reads its getter only at coordinates whose history has
strictly fewer frames than the post-binding history `q.history`. -/
theorem tableCandidate_local (p : ParameterBounds.Profile)
    (layout : WHIRCallerClaims.CallerLayout) (q : Coordinate) (r : SpongefishSessionAdapter.Record)
    (instanceBytes : List Byte) (g h : Coordinate → Option Digest32)
    (agree : ∀ c, c.history.frames.length < q.history.frames.length → g c = h c) :
    tableCandidate p layout q r instanceBytes g = tableCandidate p layout q r instanceBytes h := by
  cases hg : tableCandidate p layout q r instanceBytes g with
  | some input =>
    exact (tableCandidate_local_some p layout q r instanceBytes g h agree input hg).symm
  | none =>
    cases hh : tableCandidate p layout q r instanceBytes h with
    | none => rfl
    | some input =>
      have back := tableCandidate_local_some p layout q r instanceBytes h g
        (fun c small => (agree c small).symm) input hh
      rw [hg] at back
      cases back

/-- With `q.history.frames.length ≤ boundary + 1` (the post-binding history is the
history of the first opening packet, index `0` of `classify`, so equality holds there),
the candidate reads only histories with at most `boundary` frames. -/
theorem tableCandidate_boundary (p : ParameterBounds.Profile)
    (layout : WHIRCallerClaims.CallerLayout) (q : Coordinate) (r : SpongefishSessionAdapter.Record)
    (instanceBytes : List Byte) (g h : Coordinate → Option Digest32) (boundary : Nat)
    (atBoundary : q.history.frames.length ≤ boundary + 1)
    (agree : ∀ c, c.history.frames.length ≤ boundary → g c = h c) :
    tableCandidate p layout q r instanceBytes g = tableCandidate p layout q r instanceBytes h :=
  tableCandidate_local p layout q r instanceBytes g h (fun c small => agree c (by omega))

/-- Every current round packet history has more than `boundary` frames. -/
theorem packet_frames {p : ParameterBounds.Profile} {Q : Nat}
    {grinding : Fin (ParameterBounds.config p).folds.size → Fin 64} {boundary : Nat}
    (packet : SpongefishCurrentRoundPackets.Packet p Q grinding boundary) :
    boundary < packet.history.frames.length := by
  have classified := packet.classified
  unfold SpongefishCurrentRoundPackets.classify at classified
  split at classified
  · assumption
  · cases classified

/-! ## Record selection -/

/-- Byte width of a read call; draws and hints carry no prover bytes. -/
def callBytes : Call → Nat
  | .read kind => kind.codec.size
  | _ => 0

theorem messages_width (ms : List SpongefishRecordBindingParser.Message) :
    (ms.flatMap SpongefishRecordBindingParser.Message.bytes).length =
      ((ms.map (fun message => Call.read message.1)).map callBytes).sum := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    simp [List.flatMap_cons,ih,callBytes,SpongefishRecordBindingParser.Message.bytes,Codec.bytes]

theorem opening_width (r : SpongefishSessionAdapter.Record) :
    (SpongefishSessionAdapter.openingBytes r).length =
      ((SpongefishCurrentAcceptedJoin.messageCalls r).map callBytes).sum := by
  rw [← SpongefishRecordBindingParser.messages_bytes,messages_width]
  rfl

theorem suffix_decode (shape : AnchoredHeaderCodec.Shape) (source : List Byte)
    (r : SpongefishSessionAdapter.Record)
    (member : r ∈ SpongefishCurrentRecordDecoder.suffixCandidates shape source) :
    SpongefishCurrentRecordDecoder.decode shape (SpongefishSessionAdapter.openingBytes r) =
      some (r,[]) := by
  obtain ⟨packs,_,accepted⟩ := List.mem_filterMap.mp member
  unfold SpongefishCurrentRecordDecoder.suffixAt at accepted
  cases read : SpongefishCurrentRecordDecoder.decode shape
      (source.drop (source.length-(208+24*(packs+shape.logN)))) with
  | none => simp [read] at accepted
  | some pair =>
    obtain ⟨s,rest⟩ := pair
    simp only [read] at accepted
    change (if rest = [] then some s else none) = some r at accepted
    split at accepted
    · rename_i empty
      cases accepted
      subst empty
      have canonical := SpongefishCurrentRecordDecoder.decode_source shape _ [] r read
      rw [List.append_nil] at canonical
      rw [← canonical]
      exact read
    · contradiction

theorem suffix_unique (shape : AnchoredHeaderCodec.Shape) (source : List Byte)
    (r s : SpongefishSessionAdapter.Record)
    (hr : r ∈ SpongefishCurrentRecordDecoder.suffixCandidates shape source)
    (hs : s ∈ SpongefishCurrentRecordDecoder.suffixCandidates shape source)
    (same : SpongefishCurrentAcceptedJoin.messageCalls r =
      SpongefishCurrentAcceptedJoin.messageCalls s) : r = s := by
  have dr := suffix_decode shape source r hr
  have ds := suffix_decode shape source s hs
  have sr := SpongefishCurrentRecordDecoder.suffixCandidates_source shape source r hr
  have ss := SpongefishCurrentRecordDecoder.suffixCandidates_source shape source s hs
  have len : (SpongefishSessionAdapter.openingBytes r).length =
      (SpongefishSessionAdapter.openingBytes s).length := by
    rw [opening_width,opening_width,same]
  have image : SpongefishSessionAdapter.openingBytes r = SpongefishSessionAdapter.openingBytes s := by
    rw [List.suffix_iff_eq_drop] at sr ss
    rw [sr,ss,len]
  rw [image,ds] at dr
  exact (congrArg Prod.fst (Option.some.inj dr)).symm

theorem records_unique (shape : AnchoredHeaderCodec.Shape) (history : FramedHistory)
    (r s : SpongefishSessionAdapter.Record)
    (hr : r ∈ SpongefishCurrentRecordModeCapture.records shape history)
    (hs : s ∈ SpongefishCurrentRecordModeCapture.records shape history)
    (same : SpongefishCurrentAcceptedJoin.messageCalls r =
      SpongefishCurrentAcceptedJoin.messageCalls s) : r = s := by
  unfold SpongefishCurrentRecordModeCapture.records at hr hs
  split at hr
  · rename_i previous bytes last
    rw [last] at hs
    exact suffix_unique shape bytes r s hr hs same
  · simp at hr

theorem rawRecords_unique {Q : Nat} (shape : AnchoredHeaderCodec.Shape) (iv : Digest32)
    (key : RawKey Q) (r s : SpongefishSessionAdapter.Record)
    (hr : r ∈ SpongefishCurrentRecordModeCapture.rawRecords shape iv key)
    (hs : s ∈ SpongefishCurrentRecordModeCapture.rawRecords shape iv key)
    (same : SpongefishCurrentAcceptedJoin.messageCalls r =
      SpongefishCurrentAcceptedJoin.messageCalls s) : r = s := by
  unfold SpongefishCurrentRecordModeCapture.rawRecords at hr hs
  split at hr
  · simp at hr
  · rename_i q decoded
    rw [decoded] at hs
    exact records_unique shape q.history r s hr hs same

/-- Item 3: the raw-key record candidate whose binding message calls are those of
`k` normalized pending packs. -/
def recordOf {Q : Nat} (shape : AnchoredHeaderCodec.Shape) (iv : Digest32) (k : Nat)
    (key : RawKey Q) : Option SpongefishSessionAdapter.Record :=
  (SpongefishCurrentRecordModeCapture.rawRecords shape iv key).find?
    (fun r => decide (SpongefishCurrentAcceptedJoin.messageCalls r =
      SpongefishCurrentBCSKnowledge.bindingCalls shape k))

theorem recordOf_sound {Q : Nat} (shape : AnchoredHeaderCodec.Shape) (iv : Digest32) (k : Nat)
    (key : RawKey Q) (r : SpongefishSessionAdapter.Record) (selected : recordOf shape iv k key = some r) :
    r ∈ SpongefishCurrentRecordModeCapture.rawRecords shape iv key ∧
      SpongefishCurrentAcceptedJoin.messageCalls r = SpongefishCurrentBCSKnowledge.bindingCalls shape k := by
  refine ⟨List.mem_of_find?_eq_some selected,?_⟩
  simpa using List.find?_some selected

theorem recordOf_eq {Q : Nat} (shape : AnchoredHeaderCodec.Shape) (iv : Digest32) (k : Nat)
    (key : RawKey Q) (r : SpongefishSessionAdapter.Record)
    (member : r ∈ SpongefishCurrentRecordModeCapture.rawRecords shape iv key)
    (messagesEq : SpongefishCurrentAcceptedJoin.messageCalls r =
      SpongefishCurrentBCSKnowledge.bindingCalls shape k) :
    recordOf shape iv k key = some r := by
  cases found : recordOf shape iv k key with
  | none =>
    have missing := List.find?_eq_none.mp found r member
    simp [messagesEq] at missing
  | some s =>
    obtain ⟨hs,sCalls⟩ := recordOf_sound shape iv k key s found
    exact congrArg some (rawRecords_unique shape iv key s r hs member (sCalls.trans messagesEq.symm))

/-! ## Real and ideal getters -/

/-- Answers of the real construction oracle. -/
def realGetter (C : PrimitiveOracle) (iv : Digest32) (q : Coordinate) : Option Digest32 :=
  some (evalCoordinate (compressionOf C) iv q)

theorem physicalCandidate_real (C : PrimitiveOracle) (iv : Digest32) (p : ParameterBounds.Profile)
    (layout : WHIRCallerClaims.CallerLayout) (q : Coordinate) (r : SpongefishSessionAdapter.Record)
    (instanceBytes : List Byte) (input : PCSBCSCallerBinding.CallerInput p)
    (accepted : physicalCandidate C iv p layout q r instanceBytes = some input) :
    candidateWith (fun query => some (realAnswer C iv query)) p layout q r instanceBytes =
      some input := by
  obtain ⟨result,replayed,finished⟩ := Option.bind_eq_some_iff.mp accepted
  unfold physicalReplay at replayed
  by_cases unsupported : supported q instanceBytes = false
  · simp [unsupported] at replayed
  · have sup : supported q instanceBytes = true := by simpa using unsupported
    simp only [sup,Bool.true_eq_false,↓reduceIte] at replayed
    obtain ⟨tape,tapeEq,ran⟩ := Option.bind_eq_some_iff.mp replayed
    have transport := SpongefishCurrentMixedModeCompiler.replay_real C iv (start q instanceBytes)
      (SpongefishCurrentObservedSessionEntry.cursor q.history.domain instanceBytes
        ((historyBytes q).drop instanceBytes.length) []
        (absorb (compressionOf C) (SpongefishSessionAdapter.init (compressionOf C) iv q.history.domain)
          instanceBytes))
      rfl (session_bridge (compressionOf C) iv q.history.domain instanceBytes)
      (by intro other d found; cases found) tape
    have realRun := SpongefishCurrentCallerGetter.run_real C iv
      (replayProgram (start q instanceBytes) tape) (fun query => some (realAnswer C iv query))
      (fun o member => by rw [SpongefishCurrentCallerGetter.real_consistent C iv _ o member])
    have resultEq : result = eraseResult (runReal C iv (replayProgram (start q instanceBytes)
        tape)).view.result := by
      rw [transport]
      exact (Option.some.inj ran).symm
    obtain ⟨data,_,ok,_⟩ := finish_exact p layout q r _ input finished
    rw [resultEq] at ok finished
    cases final : (runReal C iv (replayProgram (start q instanceBytes) tape)).view.result with
    | error e => rw [final] at ok; cases ok
    | ok last =>
      rw [final] at realRun finished
      exact (candidateWith_eq_some _ p layout q r instanceBytes input).mpr
        ⟨tape,last,sup,tapeEq,realRun,finished⟩

/-- Item 4 (real): the physical caller candidate is the table candidate of the real
construction oracle. -/
theorem physicalCandidate_tableCandidate (C : PrimitiveOracle) (iv : Digest32)
    (p : ParameterBounds.Profile) (layout : WHIRCallerClaims.CallerLayout) (q : Coordinate)
    (r : SpongefishSessionAdapter.Record) (instanceBytes : List Byte)
    (input : PCSBCSCallerBinding.CallerInput p)
    (accepted : physicalCandidate C iv p layout q r instanceBytes = some input) :
    tableCandidate p layout q r instanceBytes (realGetter C iv) = some input :=
  candidateWith_constructions (fun query => some (realAnswer C iv query)) (tableAnswer (realGetter C iv))
    (fun _ _ => rfl) p layout q r instanceBytes input
    (physicalCandidate_real C iv p layout q r instanceBytes input accepted)

/-- In-budget construction answers of a raw table. -/
def tableGetter (Q : Nat) (iv : Digest32) (table : PublicCompressionCouplingMixed.Key Q → Digest32)
    (q : Coordinate) : Option Digest32 :=
  if work : pathCost q ≤ Q then some (table (.inr (constructionKey Q iv q work))) else none

theorem execute_trace {K D R : Type} {n : Nat} (oracle : K → D) :
    ∀ (t : TypedOracleCompiler.Sampling K (fun _ => D) R n),
      ∀ e ∈ (TypedOracleCompiler.Sampling.execute oracle t).2, e.2 = oracle e.1
  | .ret _ => by simp [TypedOracleCompiler.Sampling.execute]
  | .draw k next => by
    intro e member
    simp only [TypedOracleCompiler.Sampling.execute,List.mem_cons] at member
    rcases member with rfl | member
    · rfl
    · exact execute_trace oracle (next (oracle k)) e member

theorem mixedTrace_construction (B : Nat) (iv : Digest32) :
    ∀ (log : DuplexPublicSimulator.PublicLog) (os : List Observation) (o : Observation),
      o ∈ os → ∀ c valid, o.query = .construction c valid → ∀ work : pathCost c ≤ B,
        (⟨.inr (constructionKey B iv c work),o.answer⟩ :
          Sigma (fun _ : PublicCompressionCouplingMixed.Key B => Digest32)) ∈
          PCSBCSNativePublicCapture.mixedTrace B iv log os
  | _, [], _, member, _, _, _, _ => by cases member
  | log, x :: xs, o, member, c, valid, query, work => by
    simp only [PCSBCSNativePublicCapture.mixedTrace,List.mem_append]
    rcases List.mem_cons.mp member with rfl | member
    · left
      simp [PCSBCSNativePublicCapture.observationDraw,query,work]
    · right
      exact mixedTrace_construction B iv _ xs o member c valid query work

/-- Every in-budget construction observation of a compiled program carries the raw
table answer at its construction key, for an arbitrary raw table. -/
theorem table_observed {R : Type} (Q : Nat) (table : PublicCompressionCouplingMixed.Key Q → Digest32)
    (iv : Digest32) (log : DuplexPublicSimulator.PublicLog) (program : Program R) (remaining : Nat)
    (limit : remaining ≤ Q) (counted : Counts remaining program) :
    ∀ o ∈ (TypedOracleCompiler.Sampling.eval table
        (PublicCompressionCouplingMixed.compile Q iv log program remaining limit counted)).observations,
      ∀ c valid, o.query = .construction c valid → pathCost c ≤ Q →
        tableGetter Q iv table c = some o.answer := by
  intro o member c valid query work
  have split : table = PublicCompressionCouplingMixed.oracle (fun input => table (.inl input))
      (fun key => table (.inr key)) := by
    funext key
    cases key <;> rfl
  rw [split] at member ⊢
  have traced := mixedTrace_construction Q iv log _ o member c valid query work
  rw [← PCSBCSNativePublicCapture.mixedTrace_actual] at traced
  have answered := execute_trace _ _ _ traced
  simp only [tableGetter,work,↓reduceDIte]
  exact congrArg some answered.symm

/-- Item 4 (ideal): a candidate accepted on the observations of a compiled program
run on any raw table is the table candidate of that table. -/
theorem candidate_table {R : Type} (Q : Nat) (table : PublicCompressionCouplingMixed.Key Q → Digest32)
    (iv : Digest32) (log : DuplexPublicSimulator.PublicLog) (program : Program R) (remaining : Nat)
    (limit : remaining ≤ Q) (counted : Counts remaining program) (p : ParameterBounds.Profile)
    (layout : WHIRCallerClaims.CallerLayout) (q : Coordinate) (r : SpongefishSessionAdapter.Record)
    (instanceBytes : List Byte) (input : PCSBCSCallerBinding.CallerInput p)
    (accepted : candidate (Q := Q) p layout q r instanceBytes (TypedOracleCompiler.Sampling.eval table
      (PublicCompressionCouplingMixed.compile Q iv log program remaining limit counted)).observations =
      some input) :
    tableCandidate p layout q r instanceBytes (tableGetter Q iv table) = some input :=
  candidate_tableCandidate p layout q r instanceBytes _ _ input accepted
    (table_observed Q table iv log program remaining limit counted)

/-- Item 4 (ideal, packet source): on a packet table, the source view of
`SpongefishCurrentBCSKnowledge.source` is the compiled view on the joined raw table. -/
theorem candidate_packets {Packet : Type} {Block : Packet → Type} {R : Type} (Q : Nat)
    (part : RawOracleCoupling.Partition (PublicCompressionCouplingMixed.Key Q) Packet Block)
    (table : (key : part.Key) → part.Answer (D := Digest32) key)
    (iv : Digest32) (program : Program R) (counted : Counts Q program) (p : ParameterBounds.Profile)
    (layout : WHIRCallerClaims.CallerLayout) (q : Coordinate) (r : SpongefishSessionAdapter.Record)
    (instanceBytes : List Byte) (input : PCSBCSCallerBinding.CallerInput p)
    (accepted : candidate (Q := Q) p layout q r instanceBytes (TypedOracleCompiler.Sampling.eval table
      (SpongefishCurrentBCSKnowledge.source part iv program counted)).observations = some input) :
    tableCandidate p layout q r instanceBytes (tableGetter Q iv (part.join table)) = some input := by
  unfold SpongefishCurrentBCSKnowledge.source at accepted
  rw [PCSBCSChallengeOracle.Atomic.eval_program] at accepted
  exact candidate_table Q _ iv [] program Q (le_refl Q) counted p layout q r instanceBytes input accepted

/-! ## Native accepted witnesses -/

open SpongefishCurrentSourceJoinProbability in
/-- Items 3 and 4 under `NativeAcceptedBad` with binding message calls of `k` packs:
the received record is the selected record of the post-binding construction key, and
the prepared original is both the real-oracle table candidate and the public candidate
of the source view at that coordinate. -/
theorem native_selected {p : ParameterBounds.Profile} (C : PrimitiveOracle) (iv : Digest32)
    (tag instanceBytes : List Byte) (nonempty : instanceBytes ≠ [])
    (layout : WHIRCallerClaims.CallerLayout) (before payloadCalls : List Call) (k : Nat)
    (beforeEq : shapeCalls (preludeShape layout) = some before)
    (payloadEq : shapeCalls (payloadShape layout) = some payloadCalls)
    (decode : List Nat → Nat → List Byte → Option MerkleTransport.PrunedMerklePaths)
    (grinding : Fin (ParameterBounds.config p).folds.size → Fin 64)
    (prefixProgram : Program SpongefishCurrentInitializedMode.Input) (A : Nat)
    (attacker : Counts A prefixProgram)
    (Bad : PCSBCSCallerBinding.CallerInput p → View SourceResult → Prop)
    (native : NativeAcceptedBad C iv tag instanceBytes layout before payloadCalls
      (SpongefishCurrentBCSKnowledge.bindingCalls (AnchoredSourceCaller.shape layout) k) decode
      grinding prefixProgram Bad) :
    let messages := SpongefishCurrentBCSKnowledge.bindingCalls (AnchoredSourceCaller.shape layout) k
    let Q := budget tag instanceBytes layout before payloadCalls messages grinding A
    let view := (runReal C iv (program iv tag instanceBytes layout before payloadCalls messages
      grinding prefixProgram)).view
    ∃ (r : SpongefishSessionAdapter.Record) (input : PCSBCSCallerBinding.CallerInput p)
      (next : Cursor) (work : pathCost (coordinate next.pending (next.pending.consumed / 32)) ≤ Q),
      recordOf (AnchoredSourceCaller.shape layout) iv k
        (constructionKey Q iv (coordinate next.pending (next.pending.consumed / 32)) work) = some r ∧
      tableCandidate p layout (coordinate next.pending (next.pending.consumed / 32)) r instanceBytes
        (realGetter C iv) = some input ∧
      candidate (Q := Q) p layout (coordinate next.pending (next.pending.consumed / 32)) r
        instanceBytes view.observations = some input ∧
      Bad input view := by
  intro messages Q view
  obtain ⟨r,input,initial,pre,received,payload,next,setup,preRun,receivedEq,payloadRun,bindingEq,
    messagesEq,⟨opened⟩,physical,bad⟩ := native
  have shapeEq := (SpongefishCurrentCommitmentReceive.receive_retains _ pre received _ r receivedEq).1
  obtain ⟨_,_,_,work,member,publicEq,_⟩ :=
    SpongefishCurrentOpeningAcceptance.accepted_opening_original C iv layout r tag instanceBytes
      prefixProgram A attacker nonempty before payloadCalls beforeEq payloadEq initial pre received
      payload next setup preRun receivedEq payloadRun bindingEq decode grinding input opened
  have sameCalls : SpongefishCurrentSourceJoinProbability.calls layout before payloadCalls
      (SpongefishCurrentBCSKnowledge.bindingCalls (AnchoredSourceCaller.shape layout) k) grinding =
      before ++ SpongefishCurrentAcceptedJoin.headerCalls r.shape.logN ++ payloadCalls ++
        SpongefishCurrentAcceptedJoin.messageCalls r ++
        SpongefishCurrentOpeningAcceptance.openingCalls grinding := by
    rw [SpongefishCurrentSourceJoinProbability.calls,shapeEq,messagesEq]
  simp only [messages,Q,view,budget,program] at bad ⊢
  rw [sameCalls] at bad ⊢
  exact ⟨r,input,next,work,recordOf_eq _ iv k _ r member messagesEq,
    physicalCandidate_tableCandidate C iv p layout _ r instanceBytes input physical,
    publicEq.trans physical,bad⟩

#print axioms run_seq
#print axioms run_extend
#print axioms replay_mono
#print axioms replay_transfer
#print axioms replay_last_read
#print axioms candidateWith_eq_some
#print axioms candidateWith_extend
#print axioms candidateWith_constructions
#print axioms candidate_tableCandidate
#print axioms calls_last
#print axioms tableCandidate_local
#print axioms tableCandidate_boundary
#print axioms packet_frames
#print axioms records_unique
#print axioms rawRecords_unique
#print axioms recordOf_sound
#print axioms recordOf_eq
#print axioms physicalCandidate_real
#print axioms physicalCandidate_tableCandidate
#print axioms table_observed
#print axioms candidate_table
#print axioms candidate_packets
#print axioms native_selected

end Whir.SpongefishCurrentCallerOriginalTable
