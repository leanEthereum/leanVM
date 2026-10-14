import Whir.SpongefishCurrentByteTransport
import Whir.SpongefishCurrentCallerGetterCoverage
import Whir.SpongefishCurrentObservedRecordBinding

/-! Accepted current caller path to the public original list. The parser's
reconstructed proof bytes, derived domain and empty hint list are consequences
of the actual accepted replay, not join equations: the parser replays the caller
tape on exactly the consumed prefix of the attacker's proof bytes, and the
caller grammar contains no hint. The source continues with an arbitrary verifier
suffix `rest`, which is where the post-binding coordinate is queried.

Receive and expected-record binding are joined to the literal caller tape: the
accepted native composition (setup, prelude, receive, payload, binding) is one
accepted actual replay of `calls layout r`. Native PCS equation, proof-of-work
and original-claim acceptance remain outside this byte-level join. -/
namespace Whir.SpongefishCurrentAcceptedJoin
open Concrete FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame
open SpongefishPCSRoundFrames SpongefishCurrentModeQueries
open SpongefishCurrentMixedModeCompiler SpongefishCurrentReplayProvenance
open SpongefishCurrentCallerGetterCoverage
set_option autoImplicit false
set_option maxRecDepth 10000

/-! ## Hint-free caller grammar -/

def HintFree (calls : List Call) : Prop := ∀ c ∈ calls, c ≠ .hint

theorem shapeCalls_hintFree : ∀ (shape : List WHIRCallerShape.EventShape) (calls : List Call),
    SpongefishCurrentSourceCallerOriginal.shapeCalls shape = some calls → HintFree calls
  | [], calls, h => by
    simp only [SpongefishCurrentSourceCallerOriginal.shapeCalls, Option.some.injEq] at h
    subst h
    intro c member
    cases member
  | .absorb n :: rest, calls, h => by
    simp only [SpongefishCurrentSourceCallerOriginal.shapeCalls] at h
    split at h
    · obtain ⟨tail, tailEq, rfl⟩ := Option.map_eq_some_iff.mp h
      intro c member
      rcases List.mem_cons.mp member with rfl | later
      · simp
      · exact shapeCalls_hintFree rest tail tailEq c later
    · cases h
  | .squeeze n :: rest, calls, h => by
    simp only [SpongefishCurrentSourceCallerOriginal.shapeCalls] at h
    split at h
    · obtain ⟨tail, tailEq, rfl⟩ := Option.map_eq_some_iff.mp h
      intro c member
      rcases List.mem_cons.mp member with rfl | later
      · simp
      · exact shapeCalls_hintFree rest tail tailEq c later
    · cases h
  | .nonce bits :: rest, calls, h => by
    simp only [SpongefishCurrentSourceCallerOriginal.shapeCalls] at h
    split at h
    · obtain ⟨tail, tailEq, rfl⟩ := Option.map_eq_some_iff.mp h
      intro c member
      rcases List.mem_append.mp member with first | later
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at first
        rcases first with rfl | rfl <;> simp
      · exact shapeCalls_hintFree rest tail tailEq c later
    · cases h

/-- The four caller tape parts. -/
def headerCalls (logN : Nat) : List Call :=
  [.read .scalar,.read .scalar,.read .scalar,.read .root,.draw (.anchor (logN-1)),.read .scalar]

def messageCalls (r : SpongefishSessionAdapter.Record) : List Call :=
  (SpongefishRecordBindingParser.messages r).map (fun message => .read message.1)

theorem calls_parts (layout : WHIRCallerClaims.CallerLayout) (r : SpongefishSessionAdapter.Record)
    (tape : List Call) (callOrder : SpongefishCurrentSourceCallerOriginal.calls layout r = some tape) :
    ∃ before payload,
      SpongefishCurrentSourceCallerOriginal.shapeCalls
        (SpongefishCurrentSourceCallerOriginal.preludeShape layout) = some before ∧
      SpongefishCurrentSourceCallerOriginal.shapeCalls
        (SpongefishCurrentSourceCallerOriginal.payloadShape layout) = some payload ∧
      tape = before ++ headerCalls r.shape.logN ++ payload ++ messageCalls r := by
  unfold SpongefishCurrentSourceCallerOriginal.calls at callOrder
  obtain ⟨before, beforeEq, callOrder⟩ := Option.bind_eq_some_iff.mp callOrder
  obtain ⟨payload, payloadEq, callOrder⟩ := Option.bind_eq_some_iff.mp callOrder
  exact ⟨before, payload, beforeEq, payloadEq, (Option.some.inj callOrder).symm⟩

theorem calls_hintFree (layout : WHIRCallerClaims.CallerLayout) (r : SpongefishSessionAdapter.Record)
    (tape : List Call) (callOrder : SpongefishCurrentSourceCallerOriginal.calls layout r = some tape) :
    HintFree tape := by
  obtain ⟨before, payload, beforeEq, payloadEq, rfl⟩ := calls_parts layout r tape callOrder
  have first := shapeCalls_hintFree _ _ beforeEq
  have second := shapeCalls_hintFree _ _ payloadEq
  intro c member
  rcases List.mem_append.mp member with member | member
  · rcases List.mem_append.mp member with member | member
    · rcases List.mem_append.mp member with member | member
      · exact first c member
      · simp only [headerCalls, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · exact second c member
  · obtain ⟨message, _, rfl⟩ := List.mem_map.mp member
    simp

/-! ## Replay invariants -/

theorem replay_suffix (C : PrimitiveOracle) (iv : Digest32) :
    ∀ (calls : List Call) (cur fin : SemanticCursor),
      (runReal C iv (replayProgram cur calls)).view.result = .ok fin →
      fin.data.narg <:+ cur.data.narg
  | [], cur, fin, h => by
    simp only [replayProgram, runReal, Except.ok.injEq] at h
    subst h
    exact List.suffix_refl _
  | .read kind :: calls, cur, fin, h => by
    cases parsed : kind.codec.parse cur.data.narg with
    | none => simp [replayProgram, parsed, runReal] at h
    | some pair =>
      obtain ⟨value, rest⟩ := pair
      simp only [replayProgram, parsed] at h
      have tail := replay_suffix C iv calls _ fin h
      have bytes := Codec.canonical_read kind.codec cur.data.narg rest value parsed
      rw [bytes]
      exact tail.trans (List.suffix_append _ _)
  | .hint :: calls, cur, fin, h => by
    cases hintEq : cur.data.hints with
    | nil => simp [replayProgram, hintEq, runReal] at h
    | cons bytes rest =>
      simp only [replayProgram, hintEq] at h
      exact (replay_suffix C iv calls _ fin h :)
  | .draw group :: calls, cur, fin, h => by
    by_cases zero : group.bytes = 0
    · simp only [replayProgram, zero, ↓reduceDIte] at h
      exact (replay_suffix C iv calls _ fin h :)
    · by_cases guard : cur.data.pending.consumed + group.bytes ≤ maxCursor
      · simp only [replayProgram, zero, ↓reduceDIte, guard, seq,
          WHIRModeFinal.bind_real_result] at h
        exact (replay_suffix C iv calls _ fin h :)
      · simp [replayProgram, zero, guard, runReal] at h

theorem bind_domain (m : Pending) (bytes : List Byte) :
    (SpongefishPCSRoundFrames.bind m bytes).domain = m.domain := by
  unfold SpongefishPCSRoundFrames.bind
  split <;> rfl

theorem close_domain (m : Pending) : (close m).domain = m.domain := by
  unfold close
  split <;> rfl

theorem draw_domain (m : Pending) (n : Nat) : (draw m n).domain = m.domain := by
  unfold draw
  split
  · rfl
  · exact close_domain m

theorem coordinate_domain (m : Pending) (block : Nat) :
    (coordinate m block).history.domain = m.domain := by
  simp only [coordinate, Pending.core]
  exact close_domain m

theorem replay_domain (C : PrimitiveOracle) (iv : Digest32) :
    ∀ (calls : List Call) (cur fin : SemanticCursor),
      (runReal C iv (replayProgram cur calls)).view.result = .ok fin →
      fin.data.pending.domain = cur.data.pending.domain
  | [], cur, fin, h => by
    simp only [replayProgram, runReal, Except.ok.injEq] at h
    subst h
    rfl
  | .read kind :: calls, cur, fin, h => by
    cases parsed : kind.codec.parse cur.data.narg with
    | none => simp [replayProgram, parsed, runReal] at h
    | some pair =>
      obtain ⟨value, rest⟩ := pair
      simp only [replayProgram, parsed] at h
      exact (replay_domain C iv calls _ fin h).trans (bind_domain _ _)
  | .hint :: calls, cur, fin, h => by
    cases hintEq : cur.data.hints with
    | nil => simp [replayProgram, hintEq, runReal] at h
    | cons bytes rest =>
      simp only [replayProgram, hintEq] at h
      exact (replay_domain C iv calls _ fin h :)
  | .draw group :: calls, cur, fin, h => by
    by_cases zero : group.bytes = 0
    · simp only [replayProgram, zero, ↓reduceDIte] at h
      exact (replay_domain C iv calls _ fin h :)
    · by_cases guard : cur.data.pending.consumed + group.bytes ≤ maxCursor
      · simp only [replayProgram, zero, ↓reduceDIte, guard, seq,
          WHIRModeFinal.bind_real_result] at h
        exact (replay_domain C iv calls _ fin h).trans (draw_domain _ _)
      · simp [replayProgram, zero, guard, runReal] at h

/-- Accepted prefix of a call list: the replay of `xs ++ ys` is the replay of
`xs` followed by the replay of `ys` from its accepted cursor. -/
theorem replay_append (C : PrimitiveOracle) (iv : Digest32) (ys : List Call) :
    ∀ (xs : List Call) (cur fin : SemanticCursor),
      (runReal C iv (replayProgram cur xs)).view.result = .ok fin →
      (runReal C iv (replayProgram cur (xs ++ ys))).view.observations =
        (runReal C iv (replayProgram cur xs)).view.observations ++
          (runReal C iv (replayProgram fin ys)).view.observations ∧
      (runReal C iv (replayProgram cur (xs ++ ys))).view.result =
        (runReal C iv (replayProgram fin ys)).view.result
  | [], cur, fin, h => by
    simp only [replayProgram, runReal, Except.ok.injEq] at h
    subst h
    simp [replayProgram, runReal]
  | .read kind :: xs, cur, fin, h => by
    cases parsed : kind.codec.parse cur.data.narg with
    | none => simp [replayProgram, parsed, runReal] at h
    | some pair =>
      obtain ⟨value, rest⟩ := pair
      simp only [replayProgram, parsed] at h
      simp only [List.cons_append, replayProgram, parsed]
      exact replay_append C iv ys xs _ fin h
  | .hint :: xs, cur, fin, h => by
    cases hintEq : cur.data.hints with
    | nil => simp [replayProgram, hintEq, runReal] at h
    | cons bytes rest =>
      simp only [replayProgram, hintEq] at h
      simp only [List.cons_append, replayProgram, hintEq]
      exact replay_append C iv ys xs _ fin h
  | .draw group :: xs, cur, fin, h => by
    by_cases zero : group.bytes = 0
    · simp only [replayProgram, zero, ↓reduceDIte] at h
      simp only [List.cons_append, replayProgram, zero, ↓reduceDIte]
      exact replay_append C iv ys xs _ fin h
    · by_cases guard : cur.data.pending.consumed + group.bytes ≤ maxCursor
      · simp only [replayProgram, zero, ↓reduceDIte, guard, seq,
          WHIRModeFinal.bind_real_result] at h
        simp only [List.cons_append, replayProgram, zero, ↓reduceDIte, guard, seq,
          WHIRModeFinal.bind_real_result, bind_real_observations]
        have tail := replay_append C iv ys xs _ fin h
        exact ⟨by rw [tail.1, List.append_assoc], tail.2⟩
      · simp [replayProgram, zero, guard, runReal] at h

/-! ## Replay on the consumed prefix -/

/-- The same semantic cursor with extra unread proof bytes and arbitrary hints. -/
def shift (cur : SemanticCursor) (extra : List Byte) (hints : List (List Byte)) : SemanticCursor :=
  {cur with data := {cur.data with narg := cur.data.narg ++ extra, hints := hints}}

/-- A hint-free replay accepted with `extra` still unread performs exactly the
same queries, with the same answers, when `extra` is removed from its input. -/
theorem shift_replay (C : PrimitiveOracle) (iv : Digest32) (extra : List Byte)
    (hints : List (List Byte)) :
    ∀ (calls : List Call), HintFree calls → ∀ (cur fin : SemanticCursor),
      (runReal C iv (replayProgram (shift cur extra hints) calls)).view.result = .ok fin →
      extra <:+ fin.data.narg →
      ∃ parsed : SemanticCursor,
        (runReal C iv (replayProgram cur calls)).view.result = .ok parsed ∧
        fin = shift parsed extra hints ∧
        (runReal C iv (replayProgram cur calls)).view.observations =
          (runReal C iv (replayProgram (shift cur extra hints) calls)).view.observations
  | [], _, cur, fin, h, _ => by
    simp only [replayProgram, runReal, Except.ok.injEq] at h
    subst h
    exact ⟨cur, rfl, rfl, rfl⟩
  | .read kind :: calls, free, cur, fin, h, unread => by
    have rest_free : HintFree calls := fun c member => free c (List.mem_cons_of_mem _ member)
    cases parsed : kind.codec.parse (shift cur extra hints).data.narg with
    | none => simp [replayProgram, parsed, runReal] at h
    | some pair =>
      obtain ⟨value, after⟩ := pair
      simp only [replayProgram, parsed] at h
      have tail := replay_suffix C iv calls _ fin h
      obtain ⟨before, rfl⟩ := unread.trans tail
      have bytes := Codec.canonical_read kind.codec _ _ value parsed
      have prefixEq : cur.data.narg = kind.codec.bytes value ++ before := by
        have joined : cur.data.narg ++ extra = (kind.codec.bytes value ++ before) ++ extra := by
          rw [List.append_assoc]
          exact bytes
        exact List.append_cancel_right joined
      have parsedA : kind.codec.parse cur.data.narg = some (value, before) := by
        rw [prefixEq]
        exact Codec.parse_append _ _ _
      have same : readNext (shift cur extra hints) kind value (before ++ extra) =
          shift (readNext cur kind value before) extra hints := rfl
      rw [same] at h
      obtain ⟨parsedCur, ok, finEq, observed⟩ :=
        shift_replay C iv extra hints calls rest_free _ fin h unread
      refine ⟨parsedCur, ?_, finEq, ?_⟩
      · simp only [replayProgram, parsedA]
        exact ok
      · simp only [replayProgram, parsedA, parsed]
        rw [same]
        exact observed
  | .hint :: _, free, _, _, _, _ => absurd rfl (free .hint List.mem_cons_self)
  | .draw group :: calls, free, cur, fin, h, unread => by
    have rest_free : HintFree calls := fun c member => free c (List.mem_cons_of_mem _ member)
    by_cases zero : group.bytes = 0
    · simp only [replayProgram, zero, ↓reduceDIte] at h
      have same : ({shift cur extra hints with data := {(shift cur extra hints).data with
          events := (shift cur extra hints).data.events ++ [.verifier []]}} : SemanticCursor) =
          shift {cur with data := {cur.data with events := cur.data.events ++ [.verifier []]}}
            extra hints := rfl
      rw [same] at h
      obtain ⟨parsedCur, ok, finEq, observed⟩ :=
        shift_replay C iv extra hints calls rest_free _ fin h unread
      refine ⟨parsedCur, ?_, finEq, ?_⟩
      · simp only [replayProgram, zero, ↓reduceDIte]
        exact ok
      · simp only [replayProgram, zero, ↓reduceDIte]
        rw [same]
        exact observed
    · by_cases guard : cur.data.pending.consumed + group.bytes ≤ maxCursor
      · have guardB : (shift cur extra hints).data.pending.consumed + group.bytes ≤ maxCursor := guard
        let P := collect cur.data.pending (positions cur.data.pending group.bytes)
          (positions_valid _ cur.framed _ guard) cur.cache
        have progB : replayProgram (shift cur extra hints) (.draw group :: calls) =
            seq P (fun (cache, bytes) =>
              replayProgram (shift (drawn cur group.bytes guard cache bytes) extra hints) calls) := by
          simp only [replayProgram, zero, ↓reduceDIte, guardB]
          rfl
        have progA : replayProgram cur (.draw group :: calls) =
            seq P (fun (cache, bytes) => replayProgram (drawn cur group.bytes guard cache bytes) calls) := by
          simp only [replayProgram, zero, ↓reduceDIte, guard]
          rfl
        obtain ⟨⟨cache, bytes⟩, hr⟩ : ∃ x, (runReal C iv P).view.result = x := ⟨_, rfl⟩
        rw [progB, seq, WHIRModeFinal.bind_real_result, hr] at h
        obtain ⟨parsedCur, ok, finEq, observed⟩ :=
          shift_replay C iv extra hints calls rest_free _ fin h unread
        refine ⟨parsedCur, ?_, finEq, ?_⟩
        · rw [progA, seq, WHIRModeFinal.bind_real_result, hr]
          exact ok
        · rw [progA, progB, seq, bind_real_observations, bind_real_observations, hr]
          exact congrArg _ observed
      · have guardB : ¬ (shift cur extra hints).data.pending.consumed + group.bytes ≤ maxCursor := guard
        simp [replayProgram, zero, guardB, runReal] at h

/-! ## Parser coverage from the accepted replay -/

theorem initial_domain (session : Digest32) (instanceBytes narg : List Byte)
    (hints : List (List Byte)) :
    (SpongefishCurrentInitializedMode.initial session instanceBytes narg hints).data.pending.domain =
      session :=
  SpongefishCurrentInitializedMode.constructor_domain session instanceBytes narg hints {cv := zeroDigest}

/-- The parser's reconstructed proof bytes, derived domain and empty hints are
derived from the accepted actual replay of the caller tape. The source runs the
tape followed by an arbitrary verifier suffix; the coordinate is the first
post-tape construction coordinate at any output block. -/
theorem candidate_accepted (C : PrimitiveOracle) (iv : Digest32)
    (p : ParameterBounds.Profile) (layout : WHIRCallerClaims.CallerLayout)
    (r : SpongefishSessionAdapter.Record) (tag instanceBytes : List Byte)
    (prefixProgram : Program SpongefishCurrentInitializedMode.Input)
    (tape rest : List Call) (A : Nat) (attacker : Counts A prefixProgram)
    (nonempty : instanceBytes ≠ [])
    (callOrder : SpongefishCurrentSourceCallerOriginal.calls layout r = some tape)
    (fin : SemanticCursor) (block : Nat)
    (accepted : (runReal C iv (replayProgram (SpongefishCurrentInitializedMode.initial
      (SpongefishSessionAdapter.derive (compressionOf C) iv tag) instanceBytes
      (runReal C iv prefixProgram).view.result.narg
      (runReal C iv prefixProgram).view.result.hints) tape)).view.result = .ok fin) :
    SpongefishCurrentSourceCallerOriginal.candidate
      (Q := A + SpongefishCurrentInitializedMode.budget tag instanceBytes (tape ++ rest))
      p layout (coordinate fin.data.pending block) r instanceBytes
      (runReal C iv (SpongefishCurrentInitializedMode.afterPrefix iv tag instanceBytes
        prefixProgram (tape ++ rest))).view.observations =
    SpongefishCurrentSourceCallerOriginal.physicalCandidate C iv p layout
      (coordinate fin.data.pending block) r instanceBytes := by
  apply SpongefishCurrentSourceCallerOriginal.candidate_physical
  intro tape' tapeEq o member
  have tapeSame := Option.some.inj (callOrder.symm.trans tapeEq)
  subst tapeSame
  set input := (runReal C iv prefixProgram).view.result with inputDef
  set session := SpongefishSessionAdapter.derive (compressionOf C) iv tag with sessionDef
  have saved := SpongefishCurrentByteTransport.replay_conserves C iv (instanceBytes ++ input.narg)
    (SpongefishCurrentInitializedMode.initial session instanceBytes input.narg input.hints) tape
    (SpongefishCurrentByteTransport.initial_conserves session instanceBytes input.narg input.hints)
  rw [accepted] at saved
  change retainedBytes fin.data.pending ++ fin.data.narg = instanceBytes ++ input.narg at saved
  obtain ⟨consumed, consumedEq⟩ := replay_suffix C iv tape _ fin accepted
  change consumed ++ fin.data.narg = input.narg at consumedEq
  have retained : retainedBytes fin.data.pending = instanceBytes ++ consumed := by
    rw [← consumedEq, ← List.append_assoc] at saved
    exact List.append_cancel_right saved
  have bytesEq : (SpongefishCurrentSourceCallerOriginal.historyBytes
      (coordinate fin.data.pending block)).drop instanceBytes.length = consumed := by
    rw [SpongefishCurrentByteTransport.coordinate_bytes, retained, List.drop_left]
  have domainEq : (coordinate fin.data.pending block).history.domain = session := by
    rw [coordinate_domain, replay_domain C iv tape _ fin accepted, initial_domain]
  rw [bytesEq, domainEq] at member
  have shifted : SpongefishCurrentInitializedMode.initial session instanceBytes input.narg input.hints =
      shift (SpongefishCurrentInitializedMode.initial session instanceBytes consumed [])
        fin.data.narg input.hints := by
    rw [← consumedEq]
    rfl
  have acceptedShift := accepted
  rw [shifted] at acceptedShift
  obtain ⟨_, _, _, observed⟩ := shift_replay C iv fin.data.narg input.hints tape
    (calls_hintFree layout r tape callOrder) _ fin acceptedShift (List.suffix_refl _)
  rw [observed, ← shifted] at member
  apply actual_getter C iv
    (SpongefishCurrentInitializedMode.afterPrefix iv tag instanceBytes prefixProgram (tape ++ rest))
    (replayProgram (SpongefishCurrentInitializedMode.initial session instanceBytes input.narg
      input.hints) tape) _
    (SpongefishCurrentInitializedMode.afterPrefix_counted iv tag instanceBytes prefixProgram
      (tape ++ rest) A attacker)
    ?_ (initialized_recorded C iv session instanceBytes input.narg input.hints tape).2 o member
  intro o' member'
  apply afterPrefix_replay_included C iv tag instanceBytes prefixProgram (tape ++ rest) nonempty
  rw [(replay_append C iv rest tape _ fin accepted).1]
  exact List.mem_append_left _ member'

/-! ## The physical pending buffer never exceeds one block -/

theorem absorbByte_bounded (c : Compression) (s : State) (b : Byte) (h : s.pending.size ≤ 64) :
    (absorbByte c s b).pending.size ≤ 64 := by
  unfold absorbByte
  by_cases consumed : s.consumed = 0 <;> by_cases full : s.pending.size = 64 <;>
    simp [consumed, full, Array.size_push] <;> omega

theorem absorb_bounded (c : Compression) :
    ∀ (bytes : List Byte) (s : State), s.pending.size ≤ 64 → (absorb c s bytes).pending.size ≤ 64
  | [], _, h => h
  | b :: bytes, s, h => absorb_bounded c bytes _ (absorbByte_bounded c s b h)

theorem squeezeLoop_pending (c : Compression) :
    ∀ (n : Nat) (s : State), (squeezeLoop c n s).1.pending = s.pending
  | 0, _ => rfl
  | n + 1, s => by
    simp only [squeezeLoop]
    exact (squeezeLoop_pending c n _).trans rfl

theorem squeeze_bounded (c : Compression) (s t : State) (n : Nat) (bytes : List Byte)
    (h : s.pending.size ≤ 64) (ok : squeeze c s n = .ok (t, bytes)) : t.pending.size ≤ 64 := by
  unfold squeeze at ok
  split at ok
  · cases ok
    exact h
  · split at ok
    · have stateEq : t = (squeezeLoop c n (finish c s)).1 :=
        (congrArg Prod.fst (Except.ok.inj ok)).symm
      rw [stateEq, squeezeLoop_pending]
      unfold finish
      split
      · exact h
      · simp
    · cases ok

open SpongefishCurrentPrimitiveEventCompiler in
theorem actualReplay_bounded (c : Compression) :
    ∀ (calls : List Call) (cur next : Cursor), cur.state.pending.size ≤ 64 →
      actualReplay c cur calls = .ok next → next.state.pending.size ≤ 64
  | [], cur, next, h, ok => by
    simp only [actualReplay, Except.ok.injEq] at ok
    subst ok
    exact h
  | call :: calls, cur, next, h, ok => by
    simp only [actualReplay] at ok
    cases step : actualCall c cur call with
    | error e => simp [step] at ok
    | ok mid =>
      simp only [step] at ok
      apply actualReplay_bounded c calls mid next _ ok
      cases call with
      | read kind =>
        simp only [actualCall] at step
        cases readEq : SpongefishPCSRoundFrames.read c cur kind with
        | none => simp [readEq] at step
        | some pair =>
          simp only [readEq, Except.ok.injEq] at step
          subst step
          cases parsed : kind.codec.parse cur.narg with
          | none => simp [SpongefishPCSRoundFrames.read, parsed] at readEq
          | some value =>
            obtain ⟨v0, rest⟩ := value
            rw [SpongefishPCSRoundFrames.read_append c cur kind v0 rest
              (Codec.canonical_read kind.codec cur.narg rest v0 parsed)] at readEq
            rw [← Option.some.inj readEq]
            exact absorb_bounded c _ _ h
      | draw g =>
        simp only [actualCall] at step
        cases drawn : squeezeGroup c cur g with
        | error e => simp [drawn] at step
        | ok pair =>
          simp only [drawn, Except.ok.injEq] at step
          subst step
          unfold squeezeGroup at drawn
          cases squeezed : squeeze c cur.state g.bytes with
          | error e => simp [squeezed] at drawn
          | ok result =>
            simp only [squeezed] at drawn
            cases drawn
            exact squeeze_bounded c cur.state result.1 g.bytes result.2 h squeezed
      | hint =>
        simp only [actualCall] at step
        cases taken : takeHint cur with
        | none => simp [taken] at step
        | some after =>
          simp only [taken, Except.ok.injEq] at step
          subst step
          unfold takeHint at taken
          split at taken
          · cases taken
          · cases taken
            exact h

theorem setup_bounded (c : Compression) (iv : Digest32) (tag instanceBytes narg : List Byte)
    (hints : List (List Byte)) (initial : Cursor)
    (setup : SpongefishCurrentObservedSessionEntry.actualSetup c iv tag instanceBytes narg hints =
      some initial) : initial.state.pending.size ≤ 64 := by
  unfold SpongefishCurrentObservedSessionEntry.actualSetup SpongefishSessionAdapter.newSession at setup
  split at setup
  · cases setup
  · cases setup
    exact absorb_bounded c _ _ (by simp [SpongefishSessionAdapter.init, seed])

/-! ## Receive and binding are one accepted replay of the caller tape -/

open SpongefishCurrentPrimitiveEventCompiler in
theorem actualReplay_append (c : Compression) (ys : List Call) :
    ∀ (xs : List Call) (cur mid : Cursor), actualReplay c cur xs = .ok mid →
      actualReplay c cur (xs ++ ys) = actualReplay c mid ys
  | [], cur, mid, h => by
    simp only [actualReplay, Except.ok.injEq] at h
    subst h
    rfl
  | x :: xs, cur, mid, h => by
    simp only [List.cons_append, actualReplay] at h ⊢
    cases step : actualCall c cur x with
    | error e => simp [step] at h
    | ok next =>
      simp only [step] at h ⊢
      exact actualReplay_append c ys xs next mid h

open SpongefishCurrentPrimitiveEventCompiler SpongefishRecordBindingParser in
theorem verifyFields_replay (c : Compression) :
    ∀ (messages : List SpongefishRecordBindingParser.Message) (cur next : Cursor),
      verifyFields c cur messages = some next →
      actualReplay c cur (messages.map (fun message => .read message.1)) = .ok next
  | [], cur, next, h => by
    simp only [verifyFields, Option.some.injEq] at h
    subst h
    rfl
  | message :: messages, cur, next, h => by
    simp only [verifyFields] at h
    obtain ⟨mid, midEq, h⟩ := Option.bind_eq_some_iff.mp h
    have readOk : ∃ value, SpongefishPCSRoundFrames.read c cur message.1 = some (mid, value) := by
      unfold checkedRead at midEq
      cases hr : SpongefishPCSRoundFrames.read c cur message.1 with
      | none => simp [hr] at midEq
      | some pair =>
        simp only [hr] at midEq
        split at midEq
        · cases Option.some.inj midEq
          exact ⟨pair.2, rfl⟩
        · cases midEq
    obtain ⟨value, readEq⟩ := readOk
    simp only [List.map_cons, actualReplay, actualCall, readEq]
    exact verifyFields_replay c messages mid next h

open SpongefishCurrentPrimitiveEventCompiler in
theorem receive_replay (c : Compression) (cur next : Cursor) (shape : AnchoredHeaderCodec.Shape)
    (r : SpongefishSessionAdapter.Record)
    (accepted : SpongefishCurrentCommitmentReceive.receive c cur shape = some (next, r)) :
    actualReplay c cur (headerCalls shape.logN) = .ok next := by
  obtain ⟨header, root, sampled, bytes, point, value, readHeader, drawn, _, readValue, _⟩ :=
    SpongefishCurrentCommitmentReceive.receive_runs c cur next shape r accepted
  have fields := ((SpongefishCurrentAnchorHeader.readHeader_exact c cur header shape root).mp
    readHeader).2
  have first := verifyFields_replay c (SpongefishCurrentAnchorHeader.fields shape root) cur header fields
  have split : headerCalls shape.logN =
      (SpongefishCurrentAnchorHeader.fields shape root).map (fun message => .read message.1) ++
        [.draw (.anchor (shape.logN-1)),.read .scalar] := by
    simp [headerCalls, SpongefishCurrentAnchorHeader.fields,
      SpongefishRecordBindingParser.scalarMessages, SpongefishSessionAdapter.constants]
  rw [split, actualReplay_append c _ _ cur header first]
  simp [actualReplay, actualCall, drawn, readValue]

open SpongefishCurrentPrimitiveEventCompiler in
/-- The accepted native composition is one accepted replay of the caller tape. -/
theorem composition_replay (c : Compression) (layout : WHIRCallerClaims.CallerLayout)
    (r : SpongefishSessionAdapter.Record) (before payloadCalls : List Call)
    (initial pre received payload next : Cursor)
    (preRun : actualReplay c initial before = .ok pre)
    (receivedEq : SpongefishCurrentCommitmentReceive.receive c pre
      (AnchoredSourceCaller.shape layout) = some (received, r))
    (payloadRun : actualReplay c received payloadCalls = .ok payload)
    (bindingEq : SpongefishRecordBindingParser.verify c payload r = some next) :
    actualReplay c initial (before ++ headerCalls r.shape.logN ++ payloadCalls ++ messageCalls r) =
      .ok next := by
  have shapeEq := (SpongefishCurrentCommitmentReceive.receive_retains c pre received _ r receivedEq).1
  have header := receive_replay c pre received _ r receivedEq
  rw [← shapeEq] at header
  have binding := verifyFields_replay c (SpongefishRecordBindingParser.messages r) payload next
    bindingEq
  rw [actualReplay_append c _ _ _ _ (by rw [actualReplay_append c _ _ _ _ (by
    rw [actualReplay_append c _ _ _ _ preRun]; exact header)]; exact payloadRun)]
  exact binding

/-- The accepted native composition is the accepted semantic source replay of
the caller tape, with the same erased cursor data. -/
theorem accepted_semantic (C : PrimitiveOracle) (iv : Digest32)
    (layout : WHIRCallerClaims.CallerLayout) (r : SpongefishSessionAdapter.Record)
    (tag instanceBytes narg : List Byte) (hints : List (List Byte)) (nonempty : instanceBytes ≠ [])
    (before payloadCalls : List Call) (initial pre received payload next : Cursor)
    (setup : SpongefishCurrentObservedSessionEntry.actualSetup (compressionOf C) iv tag instanceBytes
      narg hints = some initial)
    (preRun : SpongefishCurrentPrimitiveEventCompiler.actualReplay (compressionOf C) initial before =
      .ok pre)
    (receivedEq : SpongefishCurrentCommitmentReceive.receive (compressionOf C) pre
      (AnchoredSourceCaller.shape layout) = some (received, r))
    (payloadRun : SpongefishCurrentPrimitiveEventCompiler.actualReplay (compressionOf C) received
      payloadCalls = .ok payload)
    (bindingEq : SpongefishRecordBindingParser.verify (compressionOf C) payload r = some next) :
    ∃ fin : SemanticCursor,
      (runReal C iv (replayProgram (SpongefishCurrentInitializedMode.initial
        (SpongefishSessionAdapter.derive (compressionOf C) iv tag) instanceBytes narg hints)
        (before ++ headerCalls r.shape.logN ++ payloadCalls ++ messageCalls r))).view.result =
          .ok fin ∧
      fin.data = SpongefishCurrentMixedModeCompiler.forget next := by
  set session := SpongefishSessionAdapter.derive (compressionOf C) iv tag with sessionDef
  have initialEq : SpongefishCurrentObservedSessionEntry.cursor session instanceBytes narg hints
      (absorb (compressionOf C) (SpongefishSessionAdapter.init (compressionOf C) iv session)
        instanceBytes) = initial := by
    simpa [SpongefishCurrentObservedSessionEntry.actualSetup, SpongefishSessionAdapter.newSession,
      nonempty] using setup
  have tapeRun := composition_replay (compressionOf C) layout r before payloadCalls initial pre
    received payload next preRun receivedEq payloadRun bindingEq
  have erased := SpongefishCurrentMixedModeCompiler.replay_real C iv
    (SpongefishCurrentInitializedMode.initial session instanceBytes narg hints)
    (SpongefishCurrentObservedSessionEntry.cursor session instanceBytes narg hints
      (absorb (compressionOf C) (SpongefishSessionAdapter.init (compressionOf C) iv session)
        instanceBytes))
    rfl (session_bridge (compressionOf C) iv session instanceBytes)
    (by intro other d found; cases found) (before ++ headerCalls r.shape.logN ++ payloadCalls ++
      messageCalls r)
  rw [initialEq, tapeRun] at erased
  revert erased
  cases (runReal C iv (replayProgram (SpongefishCurrentInitializedMode.initial session
    instanceBytes narg hints) (before ++ headerCalls r.shape.logN ++ payloadCalls ++
      messageCalls r))).view.result with
  | error e => intro erased; cases erased
  | ok fin =>
    intro erased
    exact ⟨fin, rfl, Except.ok.inj erased⟩

/-- Accepted native setup, prelude, receive, payload and expected-record binding,
followed by a source query of the post-binding coordinate, place the physically
prepared original in the public extractor's original list. No equation between
the parser's reconstruction and the native path is assumed. -/
theorem accepted_original (C : PrimitiveOracle) (iv : Digest32)
    (p : ParameterBounds.Profile) (layout : WHIRCallerClaims.CallerLayout)
    (r : SpongefishSessionAdapter.Record) (tag instanceBytes : List Byte)
    (prefixProgram : Program SpongefishCurrentInitializedMode.Input)
    (rest : List Call) (A : Nat) (attacker : Counts A prefixProgram)
    (nonempty : instanceBytes ≠ [])
    (before payloadCalls : List Call)
    (beforeEq : SpongefishCurrentSourceCallerOriginal.shapeCalls
      (SpongefishCurrentSourceCallerOriginal.preludeShape layout) = some before)
    (payloadEq : SpongefishCurrentSourceCallerOriginal.shapeCalls
      (SpongefishCurrentSourceCallerOriginal.payloadShape layout) = some payloadCalls)
    (initial pre received payload next : Cursor)
    (setup : SpongefishCurrentObservedSessionEntry.actualSetup (compressionOf C) iv tag instanceBytes
      (runReal C iv prefixProgram).view.result.narg
      (runReal C iv prefixProgram).view.result.hints = some initial)
    (preRun : SpongefishCurrentPrimitiveEventCompiler.actualReplay (compressionOf C) initial before =
      .ok pre)
    (receivedEq : SpongefishCurrentCommitmentReceive.receive (compressionOf C) pre
      (AnchoredSourceCaller.shape layout) = some (received, r))
    (payloadRun : SpongefishCurrentPrimitiveEventCompiler.actualReplay (compressionOf C) received
      payloadCalls = .ok payload)
    (bindingEq : SpongefishRecordBindingParser.verify (compressionOf C) payload r = some next)
    (block : Nat) (blockBound : block < 2^44) :
    let tape := before ++ headerCalls r.shape.logN ++ payloadCalls ++ messageCalls r
    let Q := A + SpongefishCurrentInitializedMode.budget tag instanceBytes (tape ++ rest)
    let q := coordinate next.pending block
    let observations := (runReal C iv (SpongefishCurrentInitializedMode.afterPrefix iv tag
      instanceBytes prefixProgram (tape ++ rest))).view.observations
    (∃ proof d, (⟨.construction q proof, d⟩ : Observation) ∈ observations) →
    ∃ work : pathCost q ≤ Q,
      r ∈ SpongefishCurrentRecordModeCapture.rawRecords (AnchoredSourceCaller.shape layout) iv
        (constructionKey Q iv q work) ∧
      SpongefishCurrentSourceCallerOriginal.candidate (Q := Q) p layout q r instanceBytes observations =
        SpongefishCurrentSourceCallerOriginal.physicalCandidate C iv p layout q r instanceBytes ∧
      ∀ input, SpongefishCurrentSourceCallerOriginal.physicalCandidate C iv p layout q r
          instanceBytes = some input →
        input ∈ SpongefishCurrentSourceCallerOriginal.original p layout iv
          (constructionKey Q iv q work) instanceBytes observations := by
  intro tape Q q observations queried
  set input := (runReal C iv prefixProgram).view.result with inputDef
  set session := SpongefishSessionAdapter.derive (compressionOf C) iv tag with sessionDef
  obtain ⟨shapeEq, contextEq, _, header, _, _, _, readHeader, _⟩ :=
    SpongefishCurrentCommitmentReceive.receive_retains _ pre received _ r receivedEq
  have valid : r.shape.Valid := by
    rw [shapeEq]
    exact ((SpongefishCurrentAnchorHeader.readHeader_exact _ pre header _ r.root).mp readHeader).1
  have pendingBound : r.context.pending.length ≤ 64 := by
    rw [contextEq]
    simpa [SpongefishSessionAdapter.capture] using
      actualReplay_bounded _ before initial pre (setup_bounded _ _ _ _ _ _ _ setup) preRun
  have callOrder : SpongefishCurrentSourceCallerOriginal.calls layout r = some tape := by
    simp only [SpongefishCurrentSourceCallerOriginal.calls, beforeEq, payloadEq]
    rfl
  obtain ⟨fin, accepted, finData⟩ := accepted_semantic C iv layout r tag instanceBytes input.narg
    input.hints nonempty before payloadCalls initial pre received payload next setup preRun
    receivedEq payloadRun bindingEq
  have pendingEq : fin.data.pending = next.pending := congrArg Data.pending finData
  have framed : FrameDomain next.pending := pendingEq ▸ fin.framed
  obtain ⟨proof, d, member⟩ := queried
  have work := observation_cap (real_runs C iv _) _
    (SpongefishCurrentInitializedMode.afterPrefix_counted iv tag instanceBytes prefixProgram
      (tape ++ rest) A attacker) _ member
  have selected := (SpongefishCurrentSourceCallerOriginal.receive_binding_candidate
    (compressionOf C) iv pre received payload next (AnchoredSourceCaller.shape layout) r
    receivedEq bindingEq valid pendingBound framed block blockBound work).1
  have complete := candidate_accepted C iv p layout r tag instanceBytes prefixProgram tape rest A
    attacker nonempty callOrder fin block accepted
  rw [pendingEq] at complete
  refine ⟨work, selected, complete, ?_⟩
  intro prepared preparedEq
  unfold SpongefishCurrentSourceCallerOriginal.original
  rw [WHIRHeaderRoots.decodeRaw_construction iv _ (coordinate_admissible _ framed block blockBound) work]
  apply List.mem_filterMap.mpr
  exact ⟨r, selected, complete.trans preparedEq⟩

theorem collect_head (C : PrimitiveOracle) (iv : Digest32) (m : Pending) (P : List Nat)
    (valid : ∀ p ∈ P, DuplexEncoding.Admissible (coordinate m (p/32))) (cache : Cache)
    (p : Nat) (ps : List Nat) (head : P = p :: ps) (miss : cache (coordinate m (p/32)) = none) :
    ∃ proof d, (⟨.construction (coordinate m (p/32)) proof, d⟩ : Observation) ∈
      (runReal C iv (collect m P valid cache)).view.observations := by
  subst head
  simp only [collect, seq, bind_real_observations]
  refine ⟨valid p List.mem_cons_self, evalCoordinate (compressionOf C) iv (coordinate m (p/32)),
    List.mem_append_left _ ?_⟩
  simp [request, miss, runReal, prepend, realAnswer]

/-- A positive verifier draw after an accepted tape queries the first output
block of the post-tape coordinate, or found it already recorded in the tape. -/
theorem next_draw_queried (C : PrimitiveOracle) (iv : Digest32) (cur fin : SemanticCursor)
    (tape rest : List Call) (g : Group)
    (accepted : (runReal C iv (replayProgram cur tape)).view.result = .ok fin)
    (recorded : Recorded fin.cache (runReal C iv (replayProgram cur tape)).view.observations)
    (positive : g.bytes ≠ 0) (guard : fin.data.pending.consumed + g.bytes ≤ maxCursor) :
    ∃ proof d, (⟨.construction (coordinate fin.data.pending (fin.data.pending.consumed / 32)) proof,
      d⟩ : Observation) ∈ (runReal C iv (replayProgram cur (tape ++ .draw g :: rest))).view.observations := by
  rw [(replay_append C iv _ tape cur fin accepted).1]
  cases hit : fin.cache (coordinate fin.data.pending (fin.data.pending.consumed / 32)) with
  | some d =>
    obtain ⟨proof, member⟩ := recorded _ d hit
    exact ⟨proof, d, List.mem_append_left _ member⟩
  | none =>
    have prog : replayProgram fin (.draw g :: rest) =
        seq (collect fin.data.pending (positions fin.data.pending g.bytes)
          (positions_valid _ fin.framed _ guard) fin.cache)
          (fun (cache, bytes) => replayProgram (drawn fin g.bytes guard cache bytes) rest) := by
      simp only [replayProgram, positive, ↓reduceDIte, guard]
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero positive
    have head : positions fin.data.pending g.bytes =
        (fin.data.pending.consumed + 0) :: (List.range k).map (fun j => fin.data.pending.consumed + (j+1)) := by
      simp [positions, hk, List.range_succ_eq_map]
    obtain ⟨proof, d, member⟩ := collect_head C iv fin.data.pending _
      (positions_valid _ fin.framed _ guard) fin.cache _ _ head (by simpa using hit)
    simp only [Nat.add_zero] at member
    refine ⟨proof, d, List.mem_append_right _ ?_⟩
    rw [prog, seq, bind_real_observations]
    exact List.mem_append_left _ member

/-- When the verifier suffix begins with a positive challenge draw, as the PCS
opening does after binding, the post-binding query is derived rather than assumed. -/
theorem accepted_original_next (C : PrimitiveOracle) (iv : Digest32)
    (p : ParameterBounds.Profile) (layout : WHIRCallerClaims.CallerLayout)
    (r : SpongefishSessionAdapter.Record) (tag instanceBytes : List Byte)
    (prefixProgram : Program SpongefishCurrentInitializedMode.Input)
    (g : Group) (rest : List Call) (A : Nat) (attacker : Counts A prefixProgram)
    (nonempty : instanceBytes ≠ [])
    (before payloadCalls : List Call)
    (beforeEq : SpongefishCurrentSourceCallerOriginal.shapeCalls
      (SpongefishCurrentSourceCallerOriginal.preludeShape layout) = some before)
    (payloadEq : SpongefishCurrentSourceCallerOriginal.shapeCalls
      (SpongefishCurrentSourceCallerOriginal.payloadShape layout) = some payloadCalls)
    (initial pre received payload next : Cursor)
    (setup : SpongefishCurrentObservedSessionEntry.actualSetup (compressionOf C) iv tag instanceBytes
      (runReal C iv prefixProgram).view.result.narg
      (runReal C iv prefixProgram).view.result.hints = some initial)
    (preRun : SpongefishCurrentPrimitiveEventCompiler.actualReplay (compressionOf C) initial before =
      .ok pre)
    (receivedEq : SpongefishCurrentCommitmentReceive.receive (compressionOf C) pre
      (AnchoredSourceCaller.shape layout) = some (received, r))
    (payloadRun : SpongefishCurrentPrimitiveEventCompiler.actualReplay (compressionOf C) received
      payloadCalls = .ok payload)
    (bindingEq : SpongefishRecordBindingParser.verify (compressionOf C) payload r = some next)
    (positive : g.bytes ≠ 0) (guard : next.pending.consumed + g.bytes ≤ maxCursor) :
    let tape := before ++ headerCalls r.shape.logN ++ payloadCalls ++ messageCalls r
    let Q := A + SpongefishCurrentInitializedMode.budget tag instanceBytes (tape ++ .draw g :: rest)
    let q := coordinate next.pending (next.pending.consumed / 32)
    let observations := (runReal C iv (SpongefishCurrentInitializedMode.afterPrefix iv tag
      instanceBytes prefixProgram (tape ++ .draw g :: rest))).view.observations
    ∃ work : pathCost q ≤ Q,
      r ∈ SpongefishCurrentRecordModeCapture.rawRecords (AnchoredSourceCaller.shape layout) iv
        (constructionKey Q iv q work) ∧
      SpongefishCurrentSourceCallerOriginal.candidate (Q := Q) p layout q r instanceBytes observations =
        SpongefishCurrentSourceCallerOriginal.physicalCandidate C iv p layout q r instanceBytes ∧
      ∀ input, SpongefishCurrentSourceCallerOriginal.physicalCandidate C iv p layout q r
          instanceBytes = some input →
        input ∈ SpongefishCurrentSourceCallerOriginal.original p layout iv
          (constructionKey Q iv q work) instanceBytes observations := by
  intro tape Q q observations
  obtain ⟨fin, accepted, finData⟩ := accepted_semantic C iv layout r tag instanceBytes
    (runReal C iv prefixProgram).view.result.narg (runReal C iv prefixProgram).view.result.hints
    nonempty before payloadCalls initial pre received payload next setup preRun receivedEq
    payloadRun bindingEq
  have pendingEq : fin.data.pending = next.pending := congrArg Data.pending finData
  have recorded := (initialized_recorded C iv (SpongefishSessionAdapter.derive (compressionOf C) iv tag)
    instanceBytes (runReal C iv prefixProgram).view.result.narg
    (runReal C iv prefixProgram).view.result.hints tape).1
  rw [accepted] at recorded
  have queried : ∃ proof d, (⟨.construction (coordinate next.pending (next.pending.consumed / 32))
      proof, d⟩ : Observation) ∈ (runReal C iv (replayProgram (SpongefishCurrentInitializedMode.initial
        (SpongefishSessionAdapter.derive (compressionOf C) iv tag) instanceBytes
        (runReal C iv prefixProgram).view.result.narg (runReal C iv prefixProgram).view.result.hints)
        (tape ++ .draw g :: rest))).view.observations := by
    rw [← pendingEq]
    exact next_draw_queried C iv _ fin tape rest g accepted recorded positive
      (by rw [pendingEq]; exact guard)
  obtain ⟨proof, d, member⟩ := queried
  have blockBound : next.pending.consumed / 32 < 2^44 := by
    simp only [maxCursor] at guard
    omega
  exact accepted_original C iv p layout r tag instanceBytes prefixProgram (.draw g :: rest) A
    attacker nonempty before payloadCalls beforeEq payloadEq initial pre received payload next setup
    preRun receivedEq payloadRun bindingEq _ blockBound
    ⟨proof, d, afterPrefix_replay_included C iv tag instanceBytes prefixProgram
      (tape ++ .draw g :: rest) nonempty _ member⟩

#print axioms calls_hintFree
#print axioms replay_suffix
#print axioms replay_domain
#print axioms replay_append
#print axioms shift_replay
#print axioms candidate_accepted
#print axioms composition_replay
#print axioms accepted_original
#print axioms accepted_original_next

/-- The same conclusion from the observed physical compiler, which retains the
actual record-capture context: its accepted snapshot's pending history selects
the post-binding coordinate. -/
theorem observed_original (C : PrimitiveOracle) (iv : Digest32)
    (p : ParameterBounds.Profile) (layout : WHIRCallerClaims.CallerLayout)
    (r : SpongefishSessionAdapter.Record) (tag instanceBytes : List Byte)
    (prefixProgram : Program SpongefishCurrentInitializedMode.Input)
    (rest : List Call) (A : Nat) (attacker : Counts A prefixProgram)
    (nonempty : instanceBytes ≠ [])
    (before payloadCalls : List Call)
    (beforeEq : SpongefishCurrentSourceCallerOriginal.shapeCalls
      (SpongefishCurrentSourceCallerOriginal.preludeShape layout) = some before)
    (payloadEq : SpongefishCurrentSourceCallerOriginal.shapeCalls
      (SpongefishCurrentSourceCallerOriginal.payloadShape layout) = some payloadCalls)
    (snapshot : SpongefishCurrentPhysicalModeCompiler.Captured)
    (accepted : (runReal C iv (SpongefishCurrentObservedRecordBinding.program iv tag instanceBytes
      (runReal C iv prefixProgram).view.result.narg (runReal C iv prefixProgram).view.result.hints
      (AnchoredSourceCaller.shape layout) before payloadCalls)).view.result =
        some (.ok (snapshot, r)))
    (block : Nat) (blockBound : block < 2^44) :
    let tape := before ++ headerCalls r.shape.logN ++ payloadCalls ++ messageCalls r
    let Q := A + SpongefishCurrentInitializedMode.budget tag instanceBytes (tape ++ rest)
    let q := coordinate snapshot.1.pending block
    let observations := (runReal C iv (SpongefishCurrentInitializedMode.afterPrefix iv tag
      instanceBytes prefixProgram (tape ++ rest))).view.observations
    (∃ proof d, (⟨.construction q proof, d⟩ : Observation) ∈ observations) →
    ∃ work : pathCost q ≤ Q,
      r ∈ SpongefishCurrentRecordModeCapture.rawRecords (AnchoredSourceCaller.shape layout) iv
        (constructionKey Q iv q work) ∧
      SpongefishCurrentSourceCallerOriginal.candidate (Q := Q) p layout q r instanceBytes observations =
        SpongefishCurrentSourceCallerOriginal.physicalCandidate C iv p layout q r instanceBytes ∧
      ∀ input, SpongefishCurrentSourceCallerOriginal.physicalCandidate C iv p layout q r
          instanceBytes = some input →
        input ∈ SpongefishCurrentSourceCallerOriginal.original p layout iv
          (constructionKey Q iv q work) instanceBytes observations := by
  obtain ⟨initial, pre, received, payload, next, setup, preRun, receivedEq, payloadRun, bindingEq,
    snapshotEq, _⟩ := SpongefishCurrentObservedRecordBinding.program_accepted C iv tag instanceBytes
      _ _ _ before payloadCalls snapshot r accepted
  subst snapshotEq
  exact accepted_original C iv p layout r tag instanceBytes prefixProgram rest A attacker nonempty
    before payloadCalls beforeEq payloadEq initial pre received payload next setup preRun receivedEq
    payloadRun bindingEq block blockBound

#print axioms observed_original

end Whir.SpongefishCurrentAcceptedJoin
