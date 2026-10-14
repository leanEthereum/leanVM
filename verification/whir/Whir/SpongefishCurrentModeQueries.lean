import Whir.SpongefishOrdinarySession

/-! Current successful source draws are byte projections of absorb-only output
coordinates. This is the deterministic bridge into the already-proved whole
mode game; it does not assume uniformity or current native acceptance. -/
namespace Whir.SpongefishCurrentModeQueries
open Concrete FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame
open SpongefishPCSRoundFrames
set_option autoImplicit false

/-- Source-byte framing bounds, not accepted algebraic claims. -/
def FrameDomain (m : Pending) : Prop :=
  (∀ f ∈ m.frames, match f with | .absorb previous bytes => previous < 2^49 ∧ bytes ≠ []) ∧
    m.previous ≤ maxCursor

/-- Closing a pending prover run is part of the semantic query, not a supplied CV. -/
def coordinate (m : Pending) (block : Nat) : Coordinate :=
  ⟨(close m).core.history,.output block⟩

theorem coordinate_admissible (m : Pending) (valid : FrameDomain m)
    (block : Nat) (bounded : block < 2^44) : DuplexEncoding.Admissible (coordinate m block) := by
  have sourceFrames : ∀ f ∈ (close m).frames,
      match f with | .absorb previous bytes => previous < 2^49 ∧ bytes ≠ [] := by
    intro f member
    by_cases empty : m.run = []
    · simp only [close,empty,↓reduceIte] at member
      exact valid.1 f member
    · simp only [close,empty,↓reduceIte,List.mem_append,List.mem_singleton] at member
      rcases member with inOld | rfl
      · exact valid.1 f inOld
      · exact ⟨by have := valid.2; simp only [maxCursor] at this; omega,empty⟩
  change (∀ f ∈ (close m).frames.map ByteFrame.historicalCore, DuplexEncoding.FrameValid f) ∧ _
  constructor
  · intro f member
    obtain ⟨frame,inFrame,rfl⟩ := List.mem_map.mp member
    cases frame with
    | absorb previous bytes => exact sourceFrames _ inFrame
  · exact bounded

/-- The source state contains exactly the public closed history and cursor. -/
theorem finished_state (c : Compression) (parameter : Digest32) (m : Pending) (s : State)
    (h : RepresentsCurrent c parameter m s) :
    finish c s = {cv := evalHistory c parameter (close m).core.history,consumed := m.consumed,output := (finish c s).output} := by
  have hf := finish_represents c parameter m.core s h
  have closed := materialize_closed c parameter (closeRun m.core) (finish c s).output
    hf.1 (closeRun_empty m.core)
  have state := hf.2.1.trans closed
  have history : (closeRun m.core).history = (close m).core.history :=
    congrArg Model.history (close_core m).symm
  have cursor : (closeRun m.core).consumed = m.consumed := closeRun_consumed m.core
  rw [history,cursor] at state
  exact state

/-- Every actual returned byte refers to the same prior prover history. The
byte position, not a projected query index, determines the output coordinate. -/
theorem squeezed_byte (c : Compression) (parameter : Digest32) (m : Pending) (s t : State)
    (h : RepresentsCurrent c parameter m s) (n : Nat) (positive : n ≠ 0)
    (bytes : List Byte) (ok : squeeze c s n = .ok (t,bytes)) (j : Nat) (within : j < n) :
    bytes[j]'(by obtain ⟨_,len⟩ := squeeze_exact_cursor c s t n bytes ok; omega) =
      evalCoordinate c parameter (coordinate m ((m.consumed+j)/32))
        ⟨(m.consumed+j)%32,Nat.mod_lt _ (by decide)⟩ := by
  have hf := finish_represents c parameter m.core s h
  have state := finished_state c parameter m s h
  have cv : (finish c s).cv = evalHistory c parameter (close m).core.history :=
    congrArg State.cv state
  have cursor : (finish c s).consumed = m.consumed := congrArg State.consumed state
  have value := AnchoredByteStreamSampler.squeezeLoop_getElem c (finish c s) n j hf.2.2 within
  unfold squeeze at ok
  simp only [positive,↓reduceIte] at ok
  split at ok
  · have exactBytes : (squeezeLoop c n (finish c s)).2 = bytes :=
      congrArg Prod.snd (Except.ok.inj ok)
    simpa only [exactBytes,cv,cursor,coordinate,evalCoordinate,evalTerminal] using value
  · contradiction

/-- The source guard also certifies the finite output-block address. -/
theorem squeezed_coordinate_admissible (c : Compression) (parameter : Digest32)
    (m : Pending) (s t : State) (h : RepresentsCurrent c parameter m s)
    (valid : FrameDomain m) (n : Nat) (positive : n ≠ 0) (bytes : List Byte)
    (ok : squeeze c s n = .ok (t,bytes)) (j : Nat) (within : j < n) :
    DuplexEncoding.Admissible (coordinate m ((m.consumed+j)/32)) := by
  have cursor : s.consumed = m.consumed :=
    h.2.1 ▸ materialize_consumed c parameter m.core s.output h.1
  have limit : s.consumed+n ≤ maxCursor := by
    unfold squeeze at ok
    simp only [positive,↓reduceIte] at ok
    split at ok
    · assumption
    · contradiction
  apply coordinate_admissible m valid
  rw [cursor] at limit
  simp only [maxCursor] at limit
  omega

theorem initial_frame_domain (session : Digest32) : FrameDomain {domain := session} := by
  simp [FrameDomain,maxCursor]

theorem close_frame_domain (m : Pending) (valid : FrameDomain m) : FrameDomain (close m) := by
  unfold close
  by_cases empty : m.run = []
  · simpa only [empty,↓reduceIte] using valid
  · simp only [empty,↓reduceIte,FrameDomain,List.mem_append,List.mem_singleton]
    constructor
    · intro f member
      rcases member with old | rfl
      · exact valid.1 f old
      · change m.previous < 2^49 ∧ m.run ≠ []
        exact ⟨by have := valid.2; simp only [maxCursor] at this; omega,empty⟩
    · simp [maxCursor]

theorem bind_frame_domain (m : Pending) (bytes : List Byte) (valid : FrameDomain m)
    (cursor : m.consumed ≤ maxCursor) : FrameDomain (bind m bytes) := by
  unfold SpongefishPCSRoundFrames.bind
  by_cases empty : bytes = []
  · simpa only [empty,↓reduceIte] using valid
  · simp only [empty,↓reduceIte,FrameDomain]
    exact ⟨valid.1,by split; exact valid.2; exact cursor⟩

theorem draw_frame_domain (m : Pending) (n : Nat) (valid : FrameDomain m) :
    FrameDomain (draw m n) := by
  unfold draw
  by_cases empty : n = 0
  · simpa only [empty,↓reduceIte] using valid
  · simpa only [empty,↓reduceIte,FrameDomain] using close_frame_domain m valid

theorem replayCall_frame_domain (c : Compression) (parameter : Digest32) (cur next : Cursor)
    (call : Call) (h : RepresentsCurrent c parameter cur.pending cur.state)
    (valid : FrameDomain cur.pending) (ok : replayCall c cur call = some next) :
    FrameDomain next.pending := by
  cases call with
  | read kind =>
    simp only [replayCall] at ok
    cases parsed : read c cur kind with
    | none => simp [parsed] at ok
    | some pair =>
      rcases pair with ⟨after,value⟩
      simp only [parsed,Option.map_some,Option.some.injEq] at ok
      subst next
      unfold SpongefishPCSRoundFrames.read at parsed
      cases decoded : kind.codec.parse cur.narg with
      | none => simp [decoded] at parsed
      | some pair =>
        rcases pair with ⟨actual,rest⟩
        simp only [decoded] at parsed
        rcases parsed with ⟨rfl,rfl⟩
        exact bind_frame_domain cur.pending _ valid h.1.2.2.1
  | draw group =>
    simp only [replayCall,squeezeGroup] at ok
    cases result : squeeze c cur.state group.bytes with
    | error e => simp [result] at ok
    | ok pair =>
      rcases pair with ⟨state,bytes⟩
      simp only [result] at ok
      cases ok
      exact draw_frame_domain cur.pending group.bytes valid
  | hint =>
    simp only [replayCall,takeHint] at ok
    cases hints : cur.hints with
    | nil => simp [hints] at ok
    | cons bytes rest =>
      simp only [hints,Option.some.injEq] at ok
      cases ok
      exact valid

/-- Successful normalized current replay derives frame admission from the
initial state, not from a supplied accepted-transcript certificate. -/
theorem all_round_frame_domain (c : Compression) (parameter : Digest32) (cur next : Cursor)
    (calls : List Call) (h : RepresentsCurrent c parameter cur.pending cur.state)
    (valid : FrameDomain cur.pending) (ok : replayCalls c cur calls = some next) :
    RepresentsCurrent c parameter next.pending next.state ∧ FrameDomain next.pending := by
  induction calls generalizing cur with
  | nil =>
    simp only [replayCalls,Option.some.injEq] at ok
    subst next
    exact ⟨h,valid⟩
  | cons call calls ih =>
    simp only [replayCalls] at ok
    obtain ⟨after,step,tail⟩ := Option.bind_eq_some_iff.mp ok
    exact ih after (replayCall_bridge c parameter cur after call h step)
      (replayCall_frame_domain c parameter cur after call h valid step) tail

#print axioms all_round_frame_domain

#print axioms coordinate_admissible
#print axioms finished_state
#print axioms squeezed_byte
#print axioms squeezed_coordinate_admissible
end Whir.SpongefishCurrentModeQueries
