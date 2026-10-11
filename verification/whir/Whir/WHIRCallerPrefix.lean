import Whir.WHIRHistoryKey
import Whir.DuplexFraming

/-! Continuation from the live caller transcript at conditional #552. The caller
ends by absorbing scalars (`flock/src/lincheck.rs:515-517`, or a root in direct
PCS tests), so its output cursor is zero but its buffered run need not be empty.
The first PCS squeeze finishes that run. We retain its exact seed and all prior
frames; no live chaining value is replaced by `seed(domain, statement)`. -/
/-! These lemmas apply to each actual entered context. Entry domain and statement are the original caller seed fields, not a new PCS claim digest. The raw recognizer retains the actual prefix bytes in each packet; it does not select one fixed prefix for all clones of a seed. `WHIRCallerShape` computes the boundary count from public control shape while permitting arbitrary data values. Binding that public caller shape and the PCS profile remains separate. -/
namespace Whir.WHIRCallerPrefix
open Concrete Protocol FiatShamirGame DuplexRefinement WHIRHistory WHIRHistoryKey

/-- Prefixing a ghost history changes no buffer or cursor and computes no hash. -/
def prepend (frames : List Frame) (m : Model) : Model :=
  {m with history := {m.history with frames := frames ++ m.history.frames}}

@[simp] theorem prepend_nil (m : Model) : prepend [] m = m := by
  cases m; rfl

@[simp] theorem prepend_history (frames : List Frame) (m : Model) :
    (prepend frames m).history =
      ⟨m.history.domain,m.history.statement,frames ++ m.history.frames⟩ := rfl

 theorem prepend_closeRun (frames : List Frame) (m : Model) :
    closeRun (prepend frames m) = prepend frames (closeRun m) := by
  by_cases h : m.run = [] <;>
    simp [prepend, closeRun, h, List.append_assoc]

 theorem prepend_modelAbsorb (frames : List Frame) (m : Model) (bytes : List Byte) :
    modelAbsorb (prepend frames m) bytes = prepend frames (modelAbsorb m bytes) := by
  by_cases h : bytes = []
  · simp [modelAbsorb, h]
  · simp [modelAbsorb, prepend, h]
    rfl

 theorem prepend_modelNonce (frames : List Frame) (m : Model) (nonce : Scalar24) (bits : Nat) :
    modelNonce (prepend frames m) nonce bits = prepend frames (modelNonce m nonce bits) := by
  simp only [modelNonce, prepend_closeRun]
  simp [prepend, List.append_assoc]

 theorem prepend_modelSqueeze (frames : List Frame) (m : Model) (n : Nat) :
    modelSqueeze (prepend frames m) n = prepend frames (modelSqueeze m n) := by
  by_cases h : n = 0
  · simp [modelSqueeze, h]
  · simp only [modelSqueeze, h, ↓reduceIte, prepend_closeRun]
    rfl

 theorem prepend_pendingModel (frames : List Frame) (m : Model) (p : Pending) :
    pendingModel (prepend frames m) p = prepend frames (pendingModel m p) := by
  simp only [pendingModel, prepend_modelAbsorb]
  cases p.nonce <;> simp [prepend_modelNonce]

 theorem prepend_modelEvent (frames : List Frame) (m : Model) (e : WHIRHistory.Event) :
    modelEvent (prepend frames m) e = prepend frames (modelEvent m e) := by
  cases e <;> simp only [modelEvent, prepend_modelAbsorb, prepend_modelNonce, prepend_modelSqueeze]

 theorem prepend_modelEvents (frames : List Frame) (m : Model) (events : List WHIRHistory.Event) :
    modelEvents (prepend frames m) events = prepend frames (modelEvents m events) := by
  induction events generalizing m with
  | nil => rfl
  | cons e es ih =>
    change modelEvents (modelEvent (prepend frames m) e) es =
      prepend frames (modelEvents (modelEvent m e) es)
    rw [prepend_modelEvent, ih]

/-- Reuse the existing protocol recurrence, with the actual normalized entry
history as its fixed prefix. Only the ghost initial history is extended. -/
def completedModelFrom (width : Nat → Nat) (entry : FramedHistory) (ps : List Pending) : Model :=
  prepend entry.frames (completedModel width entry.domain entry.statement ps)

def beforeModelFrom (width : Nat → Nat) (entry : FramedHistory) (ps : List Pending) : Model :=
  prepend entry.frames (beforeModel width entry.domain entry.statement ps)

def outputKeyFrom (width : Nat → Nat) (entry : FramedHistory)
    (ps : List Pending) (block : Nat) : FiatShamirGame.Coordinate :=
  ⟨(closeRun (beforeModelFrom width entry ps)).history,.output block⟩

@[simp] theorem completedModelFrom_empty (width : Nat → Nat) (domain statement : Digest32)
    (ps : List Pending) : completedModelFrom width ⟨domain,statement,[]⟩ ps =
      completedModel width domain statement ps := by simp [completedModelFrom]

@[simp] theorem beforeModelFrom_empty (width : Nat → Nat) (domain statement : Digest32)
    (ps : List Pending) : beforeModelFrom width ⟨domain,statement,[]⟩ ps =
      beforeModel width domain statement ps := by simp [beforeModelFrom]

 theorem completedModelFrom_cons (width : Nat → Nat) (entry : FramedHistory)
    (m : Pending) (ps : List Pending) :
    completedModelFrom width entry (m :: ps) =
      modelSqueeze (pendingModel (completedModelFrom width entry ps) m) (width ps.length) := by
  simp only [completedModelFrom, completedModel, prepend_pendingModel, prepend_modelSqueeze]

 theorem beforeModelFrom_cons (width : Nat → Nat) (entry : FramedHistory)
    (m : Pending) (ps : List Pending) :
    beforeModelFrom width entry (m :: ps) = pendingModel (completedModelFrom width entry ps) m := by
  simp only [beforeModelFrom, beforeModel, completedModelFrom, prepend_pendingModel]

 theorem outputKeyFrom_empty (width : Nat → Nat) (domain statement : Digest32)
    (ps : List Pending) (block : Nat) :
    outputKeyFrom width ⟨domain,statement,[]⟩ ps block = outputKey width domain statement ps block := by
  simp [outputKeyFrom, beforeModelFrom, outputKey]

 theorem before_historyFrom (width : Nat → Nat) (positive : ∀ n, 0 < width n)
    (entry : FramedHistory) {ps : List Pending} (normal : Normal ps) :
    (closeRun (beforeModelFrom width entry ps)).history =
      ⟨entry.domain,entry.statement,entry.frames ++ canonicalFrames width ps⟩ := by
  simp only [beforeModelFrom, prepend_closeRun, prepend_history,
    before_history width positive entry.domain entry.statement normal]

 theorem outputKeyFrom_history (width : Nat → Nat) (positive : ∀ n, 0 < width n)
    (entry : FramedHistory) {ps : List Pending} (normal : Normal ps) (block : Nat) :
    (outputKeyFrom width entry ps block).history =
      ⟨entry.domain,entry.statement,entry.frames ++ canonicalFrames width ps⟩ :=
  before_historyFrom width positive entry normal

 theorem parse_outputKeyFrom (width : Nat → Nat) (positive : ∀ n, 0 < width n)
    (entry : FramedHistory) {ps : List Pending} (normal : Normal ps) (block : Nat) :
    parseSteps ((outputKeyFrom width entry ps block).history.frames.drop entry.frames.length) =
      some ps.dropLast.reverse := by
  rw [outputKeyFrom_history width positive entry normal]
  simp only [List.drop_left, canonicalFrames, steps_roundtrip, List.map_reverse, annotated_erases]

 theorem outputKeyFrom_injective (width width' : Nat → Nat)
    (positive : ∀ n, 0 < width n) (positive' : ∀ n, 0 < width' n)
    (entry : FramedHistory) {ps qs : List Pending} (hp : Normal ps) (hq : Normal qs)
    (block block' : Nat) (same : outputKeyFrom width entry ps block = outputKeyFrom width' entry qs block') :
    ps = qs ∧ block = block' := by
  have hh := congrArg (fun k : FiatShamirGame.Coordinate => k.history.frames) same
  have ht := congrArg FiatShamirGame.Coordinate.terminal same
  rw [outputKeyFrom_history width positive entry hp,
    outputKeyFrom_history width' positive' entry hq] at hh
  exact ⟨canonicalFrames_injective width width' hp hq (List.append_cancel_left hh), Terminal.output.inj ht⟩

 theorem outputKeyFrom_admissible (c : Config) (width : Nat → Nat)
    (positive : ∀ n, 0 < width n) (bounded : ∀ n, width n < 2^49)
    (entry : FramedHistory) (entryValid : ∀ f ∈ entry.frames, DuplexEncoding.FrameValid f)
    (ps : List Pending) (block : Nat) (nonempty : ps ≠ [])
    (admitted : scheduledAdmissible c ps = true)
    (blockBound : block < (width (ps.length-1)+31)/32) :
    DuplexEncoding.Admissible (outputKeyFrom width entry ps block) := by
  have hn := scheduled_normal c ps nonempty admitted
  have hs := outputKey_admissible c width positive bounded entry.domain entry.statement ps block nonempty admitted blockBound
  constructor
  · rw [outputKeyFrom_history width positive entry hn]
    intro f hf
    rcases List.mem_append.mp hf with hf | hf
    · exact entryValid f hf
    · exact canonicalFrames_valid width bounded hn (scheduled_nonce_bits c ps admitted) f hf
  · exact hs.2

 theorem production_stackOutputKeyFrom_admissible (p : ParameterBounds.Profile)
    (entry : FramedHistory) (entryValid : ∀ f ∈ entry.frames, DuplexEncoding.FrameValid f)
    (ps : List Pending) (block : Nat) (nonempty : ps ≠ [])
    (admitted : scheduledAdmissible (ParameterBounds.config p) ps = true)
    (blockBound : block < (stackWidth (ParameterBounds.config p) (ps.length-1)+31)/32) :
    DuplexEncoding.Admissible (outputKeyFrom (stackWidth (ParameterBounds.config p)) entry ps block) :=
  outputKeyFrom_admissible _ _ (stackWidth_positive p) (stackWidth_bounded p)
    entry entryValid ps block nonempty admitted blockBound

 theorem production_outputKeyFrom_admissible (p : ParameterBounds.Profile)
    (entry : FramedHistory) (entryValid : ∀ f ∈ entry.frames, DuplexEncoding.FrameValid f)
    (ps : List Pending) (block : Nat) (nonempty : ps ≠ [])
    (admitted : scheduledAdmissible (ParameterBounds.config p) ps = true)
    (blockBound : block < (standaloneWidth (ParameterBounds.config p) (ps.length-1)+31)/32) :
    DuplexEncoding.Admissible (outputKeyFrom (standaloneWidth (ParameterBounds.config p)) entry ps block) :=
  outputKeyFrom_admissible _ _ (standaloneWidth_positive p) (standaloneWidth_bounded p)
    entry entryValid ps block nonempty admitted blockBound

 theorem closeRun_idempotent (m : Model) : closeRun (closeRun m) = closeRun m := by
  by_cases h : m.run = [] <;> simp [closeRun, h]

 theorem modelSqueeze_closeRun (m : Model) (n : Nat) (positive : 0 < n) :
    modelSqueeze (closeRun m) n = modelSqueeze m n := by
  simp only [modelSqueeze, Nat.ne_of_gt positive, ↓reduceIte, closeRun_idempotent, closeRun_consumed]

/-- The actual pending caller run is normalized once, exactly as a positive
squeeze does. In particular a held 64-byte block remains final, not nonfinal. -/
 theorem normalized_entry (width : Nat → Nat) (m : Model) (valid : m.Valid)
    (cursor : m.consumed = 0) :
    closeRun m = completedModelFrom width (closeRun m).history [] := by
  have hr := closeRun_empty m
  have hp := (closeRun_valid m valid).2.1 hr
  have hc : (closeRun m).consumed = 0 := (closeRun_consumed m).trans cursor
  cases he : closeRun m
  simp_all [completedModelFrom, completedModel, prepend]

/-- No reseeding: the input executable state is the live caller state. The
continuation theorem follows from actual event execution and its first positive
squeeze, which is exactly the WHIR/stack wire compiler's first event. -/
 theorem execute_from_entry (compress : Compression) (powOK : Digest32 → Scalar24 → Nat → Bool)
    (iv : Digest32) (entry : Model) (s t : State) (width : Nat → Nat)
    (h : Represents compress iv entry s) (cursor : entry.consumed = 0)
    (n : Nat) (positive : 0 < n) (events : List WHIRHistory.Event)
    (ok : executeEvents compress powOK s (.squeeze n :: events) = some t) :
    Represents compress iv
      (modelEvents (completedModelFrom width (closeRun entry).history []) (.squeeze n :: events)) t := by
  have actual := executeEvents_represents compress powOK iv (.squeeze n :: events) entry s t h ok
  have hn := normalized_entry width entry h.1 cursor
  have eq : modelEvents (completedModelFrom width (closeRun entry).history []) (.squeeze n :: events) =
      modelEvents entry (.squeeze n :: events) := by
    rw [← hn]
    simp only [modelEvents, List.foldl_cons, modelEvent, modelSqueeze_closeRun entry n positive]
  rw [eq]
  exact actual

 theorem beforeModelFrom_consumed (width : Nat → Nat) (positive : ∀ n, 0 < width n)
    (entry : FramedHistory) {ps : List Pending} (normal : Normal ps) :
    (beforeModelFrom width entry ps).consumed = 0 := by
  change (beforeModel width entry.domain entry.statement ps).consumed = 0
  cases normal with
  | initial => simp [beforeModel, completedModel, initialPending, pendingModel, modelAbsorb, scalarBytes]
  | @cons ps prior m nonempty =>
    rw [beforeModel, completed_normal width positive _ _ prior]
    have hn : scalarBytes m.scalars ≠ [] := fun h => nonempty ((scalarBytes_empty _).mp h)
    simp only [pendingModel, modelAbsorb, hn, ↓reduceIte]
    cases m.nonce <;> simp [modelNonce]

/-- Exact byte stream of the real next squeeze at a continued caller history.
`Represents` is the checked machine relation, propagated by execute_from_entry. -/
 theorem squeeze_frame_bytes_from (compress : Compression) (iv : Digest32)
    (width : Nat → Nat) (positive : ∀ n, 0 < width n) (entry : FramedHistory)
    {ps : List Pending} (normal : Normal ps) (s t : State)
    (h : Represents compress iv (beforeModelFrom width entry ps) s)
    (n : Nat) (bytes : List Byte) (ok : squeeze compress s n = .ok (t,bytes)) :
    bytes = stream compress (evalHistory compress iv (outputKeyFrom width entry ps 0).history) 0 n := by
  have he := squeeze_frame_bytes compress iv (beforeModelFrom width entry ps) s t h n bytes ok
  simpa only [outputKeyFrom, beforeModelFrom_consumed width positive entry normal] using he

 theorem initial_squeeze_frame_bytes (compress : Compression) (iv : Digest32)
    (entry : Model) (s t : State) (h : Represents compress iv entry s)
    (cursor : entry.consumed = 0) (n : Nat) (bytes : List Byte)
    (ok : squeeze compress s n = .ok (t,bytes)) :
    bytes = stream compress (evalHistory compress iv (closeRun entry).history) 0 n := by
  simpa only [cursor] using squeeze_frame_bytes compress iv entry s t h n bytes ok

theorem closeRun_frameValid (m : Model) (valid : m.Valid)
    (frames : ∀ f ∈ m.history.frames, DuplexEncoding.FrameValid f) :
    ∀ f ∈ (closeRun m).history.frames, DuplexEncoding.FrameValid f := by
  by_cases h : m.run = []
  · simpa [closeRun, h] using frames
  · simp only [closeRun, h, ↓reduceIte]
    intro f hf
    rcases List.mem_append.mp hf with hf | hf
    · exact frames f hf
    · have he : f = .absorb m.previous m.run := List.mem_singleton.mp hf
      subst f
      exact ⟨by have hp := valid.2.2.2; unfold maxCursor at hp; omega, h⟩

/-- Prefix validity is derived from the actual source transition system.
It is not a semantic claim-binding or compression-collision certificate. -/
theorem reachable_frameValid (compress : Compression) (iv domain statement : Digest32)
    {m : Model} {s : State} (h : Reachable compress iv domain statement m s) :
    ∀ f ∈ m.history.frames, DuplexEncoding.FrameValid f := by
  induction h with
  | seed => simp
  | absorb h bytes ih =>
    simp only [modelAbsorb]
    split <;> exact ih
  | squeeze h n ok ih =>
    simp only [modelSqueeze]
    split
    · exact ih
    · exact closeRun_frameValid _ (reachable_represents _ _ _ _ h).1 ih
  | nonce h nonce bits limit ih =>
    have valid := (reachable_represents _ _ _ _ h).1
    have closed := closeRun_frameValid _ valid ih
    simp only [modelNonce]
    intro f hf
    rcases List.mem_append.mp hf with hf | hf
    · exact closed f hf
    · have he : f = .nonce _ bits nonce := List.mem_singleton.mp hf
      subst f
      refine ⟨?_,limit⟩
      rw [closeRun_consumed]
      have hc := valid.2.2.1
      unfold maxCursor at hc
      omega

theorem reachable_entry_frameValid (compress : Compression) (iv domain statement : Digest32)
    {m : Model} {s : State} (h : Reachable compress iv domain statement m s) :
    ∀ f ∈ (closeRun m).history.frames, DuplexEncoding.FrameValid f :=
  closeRun_frameValid m (reachable_represents _ _ _ _ h).1 (reachable_frameValid _ _ _ _ h)

/-- Caller work stays charged: it is an actual additional root-to-terminal
prefix, not a cached or free seed replacement. -/
theorem pathCostFrom (width : Nat → Nat) (positive : ∀ n, 0 < width n)
    (entry : FramedHistory) {ps : List Pending} (normal : Normal ps) (block : Nat) :
    DuplexFraming.pathCost (outputKeyFrom width entry ps block) =
      2 + (entry.frames.flatMap DuplexEncoding.framePlan).length +
        ((canonicalFrames width ps).flatMap DuplexEncoding.framePlan).length := by
  unfold DuplexFraming.pathCost DuplexEncoding.plan
  rw [outputKeyFrom_history width positive entry normal]
  simp [List.flatMap_append, Nat.add_comm, Nat.add_left_comm]
  omega

theorem canonical_cost_drop (width : Nat → Nat) {ps : List Pending}
    (normal : Normal ps) (n : Nat) :
    ((canonicalFrames width (ps.drop n)).flatMap DuplexEncoding.framePlan).length ≤
      ((canonicalFrames width ps).flatMap DuplexEncoding.framePlan).length := by
  induction normal generalizing n with
  | initial =>
    cases n <;> simp [canonicalFrames, annotated, encodeSteps]
  | @cons ps hp m hm ih =>
    cases n with
    | zero => simp
    | succ n =>
      simp only [List.drop_succ_cons]
      apply (ih n).trans
      rw [canonicalFrames_cons width m ps hp.nonempty]
      simp

theorem pathCostFrom_drop (c : Config) (width : Nat → Nat) (positive : ∀ n, 0 < width n)
    (entry : FramedHistory) (ps : List Pending) (n block block' : Nat)
    (nonempty : ps ≠ []) (suffixNonempty : ps.drop n ≠ [])
    (admitted : scheduledAdmissible c ps = true) :
    DuplexFraming.pathCost (outputKeyFrom width entry (ps.drop n) block) ≤
      DuplexFraming.pathCost (outputKeyFrom width entry ps block') := by
  have hn := scheduled_normal c ps nonempty admitted
  have hs := scheduled_normal c (ps.drop n) suffixNonempty
    (scheduledAdmissible_drop c ps n admitted)
  rw [pathCostFrom width positive entry hs, pathCostFrom width positive entry hn]
  exact Nat.add_le_add_left (canonical_cost_drop width hn n) _

theorem stackWireEvents_head (config : Config) (digests : Nat → Digest32)
    (bits : Nat → Nat) (nonces : Nat → E) (replies : List CausalGame.Reply)
    (events : List WHIRHistory.Event)
    (compiled : stackWireEvents config digests bits nonces replies = some events) :
    ∃ rest, events = .squeeze 192 :: rest := by
  simp only [stackWireEvents] at compiled
  cases hw : wireEvents config digests bits nonces replies with
  | none => simp [hw] at compiled
  | some es =>
    simp only [hw] at compiled
    cases es with
    | nil => cases compiled
    | cons e rest =>
      cases e <;> cases compiled
      exact ⟨rest,rfl⟩

/-- The actual stack wire compiler, not an assumed continuation shape, provides
the first positive squeeze used to preserve the live caller transcript. -/
theorem execute_stackWire_from_entry (compress : Compression)
    (powOK : Digest32 → Scalar24 → Nat → Bool) (iv : Digest32)
    (entry : Model) (s t : State) (h : Represents compress iv entry s)
    (cursor : entry.consumed = 0) (config : Config) (digests : Nat → Digest32)
    (bits : Nat → Nat) (nonces : Nat → E) (replies : List CausalGame.Reply)
    (events : List WHIRHistory.Event)
    (compiled : stackWireEvents config digests bits nonces replies = some events)
    (executed : executeEvents compress powOK s events = some t) :
    Represents compress iv
      (modelEvents (completedModelFrom (stackWidth config) (closeRun entry).history []) events) t := by
  obtain ⟨rest,rfl⟩ := stackWireEvents_head config digests bits nonces replies events compiled
  exact execute_from_entry compress powOK iv entry s t (stackWidth config) h cursor 192
    (by decide) rest executed

end Whir.WHIRCallerPrefix
