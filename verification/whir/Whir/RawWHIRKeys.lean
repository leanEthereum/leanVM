import Whir.DuplexModeGame
import Whir.WHIRCallerOutputs

/-! Executable partition of the actual bounded message/template oracle. A packet
is identified by its seed statement, actual caller-entry frames, and pending
history. The public frame boundary count and prior-output cap are fixed in the
context; caller clones with different bytes keep distinct cache identities.
Ancestor answers are completed by the shared cache, never injected into syntax. -/
namespace Whir.RawWHIRKeys
open FiatShamirGame DuplexFraming DuplexModeGame WHIRHistory WHIRHistoryKey

inductive Mode where
  | standalone | stack
  deriving DecidableEq

structure Context where
  mode : Mode
  iv : Digest32
  domain : Digest32
  catalog : Digest32 → Option ParameterBounds.Profile
  entryLength : Digest32 → Nat
  callerOutputCap : Nat


def width (mode : Mode) (p : ParameterBounds.Profile) : Nat → Nat :=
  match mode with
  | .standalone => standaloneWidth (ParameterBounds.config p)
  | .stack => stackWidth (ParameterBounds.config p)

theorem width_positive (mode : Mode) (p : ParameterBounds.Profile) (n : Nat) :
    0 < width mode p n := by
  cases mode
  · exact standaloneWidth_positive p n
  · exact stackWidth_positive p n

theorem width_bounded (mode : Mode) (p : ParameterBounds.Profile) (n : Nat) :
    width mode p n < 2^49 := by
  cases mode
  · exact standaloneWidth_bounded p n
  · exact stackWidth_bounded p n

structure PacketData where
  statement : Digest32
  profile : ParameterBounds.Profile
  messages : List Pending
  entryFrames : List Frame
  deriving DecidableEq

def entry (ctx : Context) (p : PacketData) : FramedHistory :=
  ⟨ctx.domain, p.statement, p.entryFrames⟩

def blocks (ctx : Context) (p : PacketData) : Nat :=
  (width ctx.mode p.profile (p.messages.length-1) + 31) / 32

def coordinate (ctx : Context) (p : PacketData) (block : Nat) : FiatShamirGame.Coordinate :=
  ⟨⟨ctx.domain,p.statement,
    p.entryFrames ++ canonicalFrames (width ctx.mode p.profile) p.messages⟩,.output block⟩

theorem pathCost_block (ctx : Context) (p : PacketData) (block : Nat) :
    pathCost (coordinate ctx p block) = pathCost (coordinate ctx p 0) := by
  simp [coordinate, pathCost, DuplexEncoding.plan]

/-- The full uncached path includes the caller frames, not only the WHIR
suffix. Initial packets therefore do not silently reset primitive accounting. -/
theorem pathCost_prefix (ctx : Context) (p : PacketData) (block : Nat) :
    pathCost (coordinate ctx p block) =
      (p.entryFrames.flatMap DuplexEncoding.framePlan).length +
      ((canonicalFrames (width ctx.mode p.profile) p.messages).flatMap DuplexEncoding.framePlan).length + 2 := by
  simp [coordinate, pathCost, DuplexEncoding.plan, List.flatMap_append, Nat.add_assoc]

/-- Empty entry framing is only a mathematical submode. Actual live callers
must supply their normalized prior frames instead of claiming this premise. -/
theorem coordinate_empty (ctx : Context) (p : PacketData) (block : Nat)
    (normal : Normal p.messages) (empty : p.entryFrames = []) :
    coordinate ctx p block =
      outputKey (width ctx.mode p.profile) ctx.domain p.statement p.messages block := by
  simp only [coordinate, empty, List.nil_append, outputKey,
    before_history _ (width_positive ctx.mode _) _ _ normal]

/-- Exact equality to the physical continuation's normalized framed key. -/
theorem coordinate_eq_outputKeyFrom (ctx : Context) (p : PacketData) (block : Nat)
    (normal : Normal p.messages) :
    coordinate ctx p block =
      WHIRCallerPrefix.outputKeyFrom (width ctx.mode p.profile) (entry ctx p) p.messages block := by
  simp only [WHIRCallerPrefix.outputKeyFrom,
    WHIRCallerPrefix.before_historyFrom _ (width_positive ctx.mode _) _ normal]
  rfl

/-- The entry framing check is discharged from the source transition relation,
including the live caller's active run. No decoder-validity premise is needed. -/
theorem entryValid_of_reachable (ctx : Context) (p : PacketData)
    (compress : DuplexRefinement.Compression) (m : DuplexRefinement.Model) (s : DuplexRefinement.State)
    (reachable : DuplexRefinement.Reachable compress ctx.iv ctx.domain p.statement m s)
    (aligned : entry ctx p = (DuplexRefinement.closeRun m).history) :
    ∀ f ∈ p.entryFrames, DuplexEncoding.FrameValid f := by
  have frames := congrArg FramedHistory.frames aligned
  change p.entryFrames = (DuplexRefinement.closeRun m).history.frames at frames
  rw [frames]
  exact WHIRCallerPrefix.reachable_entry_frameValid _ _ _ _ reachable

def ValidPacket (ctx : Context) (Q : Nat) (p : PacketData) : Prop :=
  ctx.catalog p.statement = some p.profile ∧ p.messages ≠ [] ∧
  scheduledAdmissible (ParameterBounds.config p.profile) p.messages = true ∧
  pathCost (coordinate ctx p 0) ≤ Q ∧
  (∀ f ∈ p.entryFrames, DuplexEncoding.FrameValid f) ∧
  p.entryFrames.length = ctx.entryLength p.statement ∧
  WHIRCallerOutputs.callerOutputCount p.entryFrames ≤ ctx.callerOutputCap

instance (ctx : Context) (Q : Nat) (p : PacketData) : Decidable (ValidPacket ctx Q p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

abbrev Packet (ctx : Context) (Q : Nat) := {p : PacketData // ValidPacket ctx Q p}
abbrev Position (ctx : Context) (Q : Nat) := (p : Packet ctx Q) × Fin (blocks ctx p.val)

theorem packet_pathBound (ctx : Context) (Q : Nat) (p : Packet ctx Q) :
    pathCost (coordinate ctx p.val 0) ≤ Q := p.property.2.2.2.1

theorem packet_entryValid (ctx : Context) (Q : Nat) (p : Packet ctx Q) :
    ∀ f ∈ p.val.entryFrames, DuplexEncoding.FrameValid f := p.property.2.2.2.2.1

theorem packet_entryLength (ctx : Context) (Q : Nat) (p : Packet ctx Q) :
    p.val.entryFrames.length = ctx.entryLength p.val.statement := p.property.2.2.2.2.2.1

theorem packet_callerOutputBound (ctx : Context) (Q : Nat) (p : Packet ctx Q) :
    WHIRCallerOutputs.callerOutputCount p.val.entryFrames ≤ ctx.callerOutputCap :=
  p.property.2.2.2.2.2.2

def encode (ctx : Context) (Q : Nat) (pos : Position ctx Q) : RawKey Q :=
  constructionKey Q ctx.iv (coordinate ctx pos.1.val pos.2.val)
    (by rw [pathCost_block]; exact packet_pathBound ctx Q pos.1)

theorem coordinate_admissible (ctx : Context) (Q : Nat) (pos : Position ctx Q) :
    DuplexEncoding.Admissible (coordinate ctx pos.1.val pos.2.val) := by
  have normal := scheduled_normal _ _ pos.1.property.2.1 pos.1.property.2.2.1
  rw [coordinate_eq_outputKeyFrom ctx pos.1.val pos.2.val normal]
  exact WHIRCallerPrefix.outputKeyFrom_admissible (ParameterBounds.config pos.1.val.profile)
    _ (width_positive ctx.mode _) (width_bounded ctx.mode _) (entry ctx pos.1.val)
    (packet_entryValid ctx Q pos.1) _ _ pos.1.property.2.1 pos.1.property.2.2.1 pos.2.isLt

def parseCoordinate (ctx : Context) (q : FiatShamirGame.Coordinate) : Option (PacketData × Nat) := do
  let profile ← ctx.catalog q.history.statement
  let steps ← parseSteps (q.history.frames.drop (ctx.entryLength q.history.statement))
  match q.terminal with
  | .output block => pure (⟨q.history.statement, profile, steps.reverse ++ [initialPending],
      q.history.frames.take (ctx.entryLength q.history.statement)⟩, block)
  | _ => none

def candidate (ctx : Context) {Q : Nat} (raw : RawKey Q) : Option (PacketData × Nat) := do
  let q ← DuplexEncoding.decode (extractedPlan (expandKey raw))
  parseCoordinate ctx q

/-- The final exact reconstruction check also checks the fixed IV, the domain,
caller-entry frames, final flags, CV holes, lengths, and every other raw bit. -/
def recognize (ctx : Context) (Q : Nat) (raw : RawKey Q) : Option (Position ctx Q) :=
  match candidate ctx raw with
  | none => none
  | some (p,block) =>
    if hp : ValidPacket ctx Q p then
      if hb : block < blocks ctx p then
        let pos : Position ctx Q := ⟨⟨p,hp⟩,⟨block,hb⟩⟩
        if encode ctx Q pos = raw then some pos else none
      else none
    else none

theorem extractedPlan_modeKey (iv : Digest32) (q : FiatShamirGame.Coordinate) :
    extractedPlan (modeKey iv q) = DuplexEncoding.plan q := by
  unfold modeKey keyFromPlan extractedPlan
  have step : ∀ p : List DuplexEncoding.Instruction,
      ((p.map (fun i => (if DuplexEncoding.readRole i.2 = 1 then some iv else none,i.1))).zip
        (p.map (fun i => (i.2,true)))).map (fun p => (p.1.2,p.2.1)) = p := by
    intro p
    induction p with
    | nil => rfl
    | cons i p ih => simp [ih]
  rw [step, List.reverse_reverse]

theorem parseCoordinate_coordinate (ctx : Context) (Q : Nat) (pos : Position ctx Q) :
    parseCoordinate ctx (coordinate ctx pos.1.val pos.2.val) = some (pos.1.val,pos.2.val) := by
  have hn := scheduled_normal (ParameterBounds.config pos.1.val.profile) pos.1.val.messages
    pos.1.property.2.1 pos.1.property.2.2.1
  simp only [coordinate, parseCoordinate, pos.1.property.1, ← packet_entryLength ctx Q pos.1,
    List.drop_left, List.take_left, canonicalFrames, steps_roundtrip, List.map_reverse, annotated_erases]
  change some ((⟨pos.1.val.statement, pos.1.val.profile,
    pos.1.val.messages.dropLast.reverse.reverse ++ [initialPending],pos.1.val.entryFrames⟩ : PacketData), pos.2.val) = _
  rw [List.reverse_reverse, hn.restore]

theorem candidate_encode (ctx : Context) (Q : Nat) (pos : Position ctx Q) :
    candidate ctx (encode ctx Q pos) = some (pos.1.val,pos.2.val) := by
  simp only [candidate, encode, expand_constructionKey, extractedPlan_modeKey,
    DuplexEncoding.decode_plan _ (coordinate_admissible ctx Q pos)]
  exact parseCoordinate_coordinate ctx Q pos

@[simp] theorem recognize_encode (ctx : Context) (Q : Nat) (pos : Position ctx Q) :
    recognize ctx Q (encode ctx Q pos) = some pos := by
  rw [recognize, candidate_encode]
  simp only [pos.1.property, pos.2.isLt, dite_true]
  rfl

theorem encode_recognize (ctx : Context) (Q : Nat) (raw : RawKey Q) (pos : Position ctx Q)
    (h : recognize ctx Q raw = some pos) : encode ctx Q pos = raw := by
  unfold recognize at h
  split at h
  · contradiction
  · split at h
    · split at h
      · dsimp only at h
        split at h
        · cases Option.some.inj h
          assumption
        · contradiction
      · contradiction
    · contradiction

theorem recognize_iff (ctx : Context) (Q : Nat) (raw : RawKey Q) (pos : Position ctx Q) :
    recognize ctx Q raw = some pos ↔ encode ctx Q pos = raw := by
  constructor
  · exact encode_recognize ctx Q raw pos
  · rintro rfl
    exact recognize_encode ctx Q pos

theorem encode_injective (ctx : Context) (Q : Nat) : Function.Injective (encode ctx Q) := by
  intro a b h
  have he := congrArg (recognize ctx Q) h
  simpa only [recognize_encode, Option.some.injEq] using he

def Garbage (ctx : Context) (Q : Nat) (raw : RawKey Q) : Prop := recognize ctx Q raw = none

instance (ctx : Context) (Q : Nat) (raw : RawKey Q) : Decidable (Garbage ctx Q raw) :=
  inferInstanceAs (Decidable (_ = _))

theorem garbage_iff (ctx : Context) (Q : Nat) (raw : RawKey Q) :
    Garbage ctx Q raw ↔ ∀ pos, encode ctx Q pos ≠ raw := by
  constructor
  · intro h pos he
    have hr := (recognize_iff ctx Q raw pos).mpr he
    rw [h] at hr
    contradiction
  · intro h
    unfold Garbage
    cases hr : recognize ctx Q raw with
    | none => rfl
    | some pos => exact False.elim (h pos (encode_recognize ctx Q raw pos hr))

/-- All caller output coordinates before the public WHIR entry boundary lie
outside the packet partition, regardless of their observed digest values. -/
theorem short_history_garbage (ctx : Context) (Q : Nat) (q : FiatShamirGame.Coordinate)
    (valid : DuplexEncoding.Admissible q) (bounded : pathCost q ≤ Q)
    (short : q.history.frames.length < ctx.entryLength q.history.statement) :
    Garbage ctx Q (constructionKey Q ctx.iv q bounded) := by
  apply (garbage_iff ctx Q _).mpr
  intro pos same
  have rawSame := congrArg expandKey same
  simp only [encode, expand_constructionKey] at rawSame
  have equal := modeKey_injective ctx.iv (coordinate_admissible ctx Q pos) valid rawSame
  have hs := congrArg (fun c : FiatShamirGame.Coordinate => c.history.statement) equal
  have hl := congrArg (fun c : FiatShamirGame.Coordinate => c.history.frames.length) equal
  change pos.1.val.statement = q.history.statement at hs
  change (pos.1.val.entryFrames ++
    canonicalFrames (width ctx.mode pos.1.val.profile) pos.1.val.messages).length = q.history.frames.length at hl
  rw [List.length_append, packet_entryLength ctx Q pos.1, hs] at hl
  omega

theorem callerOutput_admissible (ctx : Context) (Q : Nat) (p : Packet ctx Q)
    (q : FiatShamirGame.Coordinate) (hq : q ∈ WHIRCallerOutputs.callerOutputs (entry ctx p.val)) :
    DuplexEncoding.Admissible q :=
  WHIRCallerOutputs.callerOutputs_admissible _ (packet_entryValid ctx Q p) q hq

theorem callerOutput_pathBound (ctx : Context) (Q : Nat) (p : Packet ctx Q)
    (q : FiatShamirGame.Coordinate) (hq : q ∈ WHIRCallerOutputs.callerOutputs (entry ctx p.val)) :
    pathCost q ≤ Q :=
  (WHIRCallerOutputs.callerOutputs_extended_pathCost_le (entry ctx p.val) q hq
    (canonicalFrames (width ctx.mode p.val.profile) p.val.messages) (.output 0)).trans
    (packet_pathBound ctx Q p)

/-- A source-enumerated earlier caller output is a literal shared raw-oracle
coordinate, not an independently resampled reply or an arbitrary table lookup. -/
def callerOutputKey (ctx : Context) (Q : Nat) (p : Packet ctx Q)
    (q : FiatShamirGame.Coordinate) (hq : q ∈ WHIRCallerOutputs.callerOutputs (entry ctx p.val)) :
    {raw : RawKey Q // Garbage ctx Q raw} :=
  ⟨constructionKey Q ctx.iv q (callerOutput_pathBound ctx Q p q hq),
    short_history_garbage ctx Q q (callerOutput_admissible ctx Q p q hq)
      (callerOutput_pathBound ctx Q p q hq) (by
        have h := WHIRCallerOutputs.callerOutputs_strict_prefix (entry ctx p.val) q hq
        have hs : q.history.statement = p.val.statement := h.2.1
        have hl : q.history.frames.length < p.val.entryFrames.length := h.2.2.1
        rw [packet_entryLength ctx Q p] at hl
        simpa only [hs] using hl)⟩

/-- Chronological strict caller prefixes, with all consumed output blocks and
their complete 32-byte answers. Warm these through the same garbage cache. -/
def callerGroups (ctx : Context) (Q : Nat) (p : Packet ctx Q) :
    List {raw : RawKey Q // Garbage ctx Q raw} :=
  (WHIRCallerOutputs.callerOutputs (entry ctx p.val)).attach.map
    (fun q => callerOutputKey ctx Q p q.val q.property)

theorem callerGroups_length (ctx : Context) (Q : Nat) (p : Packet ctx Q) :
    (callerGroups ctx Q p).length = WHIRCallerOutputs.callerOutputCount p.val.entryFrames := by
  simp [callerGroups, WHIRCallerOutputs.callerOutputs_length, entry]

theorem callerGroups_bound (ctx : Context) (Q : Nat) (p : Packet ctx Q) :
    (callerGroups ctx Q p).length ≤ ctx.callerOutputCap := by
  rw [callerGroups_length]
  exact packet_callerOutputBound ctx Q p

/-- Packet blocks are jointly injective, hence distinct packets have disjoint
raw coordinates and all remaining keys belong to the garbage complement. -/
theorem packet_blocks_disjoint (ctx : Context) (Q : Nat) (a b : Packet ctx Q)
    (i : Fin (blocks ctx a.val)) (j : Fin (blocks ctx b.val))
    (h : encode ctx Q ⟨a,i⟩ = encode ctx Q ⟨b,j⟩) : a = b :=
  congrArg Sigma.fst (encode_injective ctx Q h)

/-- Different actual caller clones never share any packet block, even if their
seed statement, public boundary count, and entire WHIR suffix are identical. -/
theorem clone_blocks_disjoint (ctx : Context) (Q : Nat) (a b : Packet ctx Q)
    (different : a.val.entryFrames ≠ b.val.entryFrames)
    (i : Fin (blocks ctx a.val)) (j : Fin (blocks ctx b.val)) :
    encode ctx Q ⟨a,i⟩ ≠ encode ctx Q ⟨b,j⟩ := by
  intro same
  exact different (congrArg (fun p : Packet ctx Q => p.val.entryFrames)
    (packet_blocks_disjoint ctx Q a b i j same))

theorem packet_depth (ctx : Context) (Q : Nat) (p : Packet ctx Q) :
    p.val.messages.length ≤ depth (ParameterBounds.config p.val.profile) :=
  scheduledAdmissible_depth _ _ p.property.2.2.1

theorem blocks_positive (ctx : Context) (p : PacketData) : 0 < blocks ctx p := by
  have h := width_positive ctx.mode p.profile (p.messages.length-1)
  unfold blocks
  omega

instance (ctx : Context) (Q : Nat) (p : Packet ctx Q) : Nonempty (Fin (blocks ctx p.val)) :=
  ⟨⟨0,blocks_positive ctx p.val⟩⟩

private instance : Finite UInt64 :=
  Finite.of_injective ByteCodec.encodeK ByteCodec.encodeK_injective

instance (ctx : Context) (Q : Nat) : Finite (Position ctx Q) :=
  Finite.of_injective (encode ctx Q) (encode_injective ctx Q)

instance (ctx : Context) (Q : Nat) : Finite (Packet ctx Q) :=
  Finite.of_injective
    (fun p : Packet ctx Q => (⟨p,⟨0,blocks_positive ctx p.val⟩⟩ : Position ctx Q))
    (fun _ _ h => congrArg Sigma.fst h)

noncomputable instance (ctx : Context) (Q : Nat) : Fintype (Packet ctx Q) := Fintype.ofFinite _

/-- Profiles are recovered from the one immutable statement catalog, not
independent tags that could split a single physical oracle coordinate. -/
theorem packet_ext (ctx : Context) (Q : Nat) (a b : Packet ctx Q)
    (hs : a.val.statement = b.val.statement) (hm : a.val.messages = b.val.messages)
    (he : a.val.entryFrames = b.val.entryFrames) : a = b := by
  have hp : a.val.profile = b.val.profile := by
    have ha := a.property.1
    rw [hs, b.property.1] at ha
    exact (Option.some.inj ha).symm
  apply Subtype.ext
  rcases a with ⟨⟨sa,pa,ma,ea⟩,ha⟩
  rcases b with ⟨⟨sb,pb,mb,eb⟩,hb⟩
  simp only at hs hm hp he
  cases hs
  cases hm
  cases hp
  cases he
  rfl

/-- Every actual scheduled block satisfying the raw mode path bound enters
the partition with precisely its statement, prefix, and block number. -/
theorem recognize_scheduled (ctx : Context) (Q : Nat) (p : PacketData)
    (catalogued : ctx.catalog p.statement = some p.profile)
    (nonempty : p.messages ≠ [])
    (scheduled : scheduledAdmissible (ParameterBounds.config p.profile) p.messages = true)
    (entryValid : ∀ f ∈ p.entryFrames, DuplexEncoding.FrameValid f)
    (entryLength : p.entryFrames.length = ctx.entryLength p.statement)
    (callerBound : WHIRCallerOutputs.callerOutputCount p.entryFrames ≤ ctx.callerOutputCap)
    (block : Nat) (inRange : block < blocks ctx p)
    (bounded : pathCost (coordinate ctx p block) ≤ Q) :
    recognize ctx Q (constructionKey Q ctx.iv (coordinate ctx p block) bounded) =
      some ⟨⟨p,⟨catalogued,nonempty,scheduled,
        (by simpa only [pathCost_block] using bounded),entryValid,entryLength,callerBound⟩⟩,⟨block,inRange⟩⟩ := by
  let pos : Position ctx Q := ⟨⟨p,⟨catalogued,nonempty,scheduled,
    (by simpa only [pathCost_block] using bounded),entryValid,entryLength,callerBound⟩⟩,⟨block,inRange⟩⟩
  change recognize ctx Q (encode ctx Q pos) = some pos
  exact recognize_encode ctx Q pos

theorem recognized_syntax (ctx : Context) (Q : Nat) (raw : RawKey Q) (pos : Position ctx Q)
    (recognized : recognize ctx Q raw = some pos) :
    expandKey raw = modeKey ctx.iv (coordinate ctx pos.1.val pos.2.val) := by
  rw [← encode_recognize ctx Q raw pos recognized]
  exact expand_constructionKey _ _ _ _

/-- Removing newest messages removes final framed runs, never increases the
uncached public-compression path cost. -/
theorem canonicalCost_drop_le (w : Nat → Nat) (messages : List Pending) (n : Nat) :
    ((canonicalFrames w (messages.drop n)).flatMap DuplexEncoding.framePlan).length ≤
      ((canonicalFrames w messages).flatMap DuplexEncoding.framePlan).length := by
  induction n generalizing messages with
  | zero => simp
  | succ n ih =>
    cases messages with
    | nil => simp
    | cons m messages =>
      rw [List.drop_succ_cons]
      apply (ih messages).trans
      cases messages with
      | nil => simp [canonicalFrames, annotated, encodeSteps]
      | cons m' rest =>
        rw [canonicalFrames_cons w m (m' :: rest) (by simp),
          List.flatMap_append, List.length_append]
        omega

theorem packet_drop_valid (ctx : Context) (Q : Nat) (p : Packet ctx Q)
    (n : Nat) (nonempty : p.val.messages.drop n ≠ []) :
    ValidPacket ctx Q {p.val with messages := p.val.messages.drop n} := by
  have hs := scheduledAdmissible_drop _ _ n p.property.2.2.1
  refine ⟨p.property.1,nonempty,hs,?_,packet_entryValid ctx Q p,packet_entryLength ctx Q p,
    packet_callerOutputBound ctx Q p⟩
  apply le_trans (b := pathCost (coordinate ctx p.val 0)) _ (packet_pathBound ctx Q p)
  have hc := canonicalCost_drop_le (width ctx.mode p.val.profile) p.val.messages n
  simp only [coordinate, pathCost, DuplexEncoding.plan,
    List.flatMap_append, List.length_cons, List.length_append]
  omega

def dropPacket (ctx : Context) (Q : Nat) (p : Packet ctx Q)
    (n : Nat) (nonempty : p.val.messages.drop n ≠ []) : Packet ctx Q :=
  ⟨{p.val with messages := p.val.messages.drop n},packet_drop_valid ctx Q p n nonempty⟩

theorem callerGroups_dropPacket (ctx : Context) (Q : Nat) (p : Packet ctx Q)
    (n : Nat) (nonempty : p.val.messages.drop n ≠ []) :
    callerGroups ctx Q (dropPacket ctx Q p n nonempty) = callerGroups ctx Q p := rfl

/-- Oldest first, exactly the strict suffixes needed by canonical completion.
No ancestor reply is selected or encoded by this list of syntax addresses. -/
def ancestors (ctx : Context) (Q : Nat) (p : Packet ctx Q) : List (Packet ctx Q) :=
  List.ofFn fun i : Fin (p.val.messages.length-1) =>
    dropPacket ctx Q p (p.val.messages.length-1-i.val)
      (by
        intro he
        have hl := congrArg List.length he
        simp only [List.length_drop, List.length_nil] at hl
        have hi := i.isLt
        omega)

theorem callerGroups_ancestor (ctx : Context) (Q : Nat) (p a : Packet ctx Q)
    (ha : a ∈ ancestors ctx Q p) : callerGroups ctx Q a = callerGroups ctx Q p := by
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
  exact callerGroups_dropPacket ctx Q p _ _

theorem ancestors_length (ctx : Context) (Q : Nat) (p : Packet ctx Q) :
    (ancestors ctx Q p).length = p.val.messages.length-1 := by
  simp [ancestors]

theorem ancestors_get (ctx : Context) (Q : Nat) (p : Packet ctx Q)
    (i : Fin (p.val.messages.length-1)) :
    ((ancestors ctx Q p)[i.val]'(by rw [ancestors_length]; exact i.isLt)).val.statement = p.val.statement ∧
    ((ancestors ctx Q p)[i.val]'(by rw [ancestors_length]; exact i.isLt)).val.messages =
      p.val.messages.drop (p.val.messages.length-1-i.val) := by
  simp [ancestors, dropPacket]

theorem ancestors_get_entryFrames (ctx : Context) (Q : Nat) (p : Packet ctx Q)
    (i : Fin (p.val.messages.length-1)) :
    ((ancestors ctx Q p)[i.val]'(by rw [ancestors_length]; exact i.isLt)).val.entryFrames =
      p.val.entryFrames := by
  simp [ancestors, dropPacket]

theorem ancestors_depth (ctx : Context) (Q : Nat) (p : Packet ctx Q) :
    (ancestors ctx Q p).length + 1 ≤ depth (ParameterBounds.config p.val.profile) := by
  have h := packet_depth ctx Q p
  have hn := List.length_pos_iff.mpr p.property.2.1
  rw [ancestors_length]
  omega

/-- Every ancestor's own completion chain is exactly the already visited
prefix of the oldest-first chain. This is the cache provenance ordering law. -/
theorem ancestors_ancestors (ctx : Context) (Q : Nat) (p : Packet ctx Q)
    (i : Nat) (hi : i < (ancestors ctx Q p).length) :
    ancestors ctx Q ((ancestors ctx Q p)[i]'hi) = (ancestors ctx Q p).take i := by
  have hi' : i < p.val.messages.length-1 := by simpa only [ancestors_length] using hi
  have ha := ancestors_get ctx Q p ⟨i,hi'⟩
  dsimp only at ha
  apply List.ext_getElem
  · rw [ancestors_length, ha.2, List.length_drop, List.length_take, ancestors_length]
    omega
  · intro j hj hk
    have hj' : j < i := lt_of_lt_of_le hk (List.length_take_le _ _)
    have hjs : j < ((ancestors ctx Q p)[i]'hi).val.messages.length-1 := by
      simpa only [ancestors_length] using hj
    have inner := ancestors_get ctx Q ((ancestors ctx Q p)[i]'hi) ⟨j,hjs⟩
    have outer := ancestors_get ctx Q p ⟨j,lt_trans hj' hi'⟩
    dsimp only at inner outer
    apply packet_ext ctx Q
    · rw [List.getElem_take]
      exact inner.1.trans (ha.1.trans outer.1.symm)
    · rw [List.getElem_take, inner.2, outer.2, ha.2, List.drop_drop, List.length_drop]
      congr 1
      omega
    · simp [ancestors, dropPacket]

/-- One closed allocation-depth bound for every profile in the immutable
catalog, covering rejecting as well as accepting scheduled branches. -/
def maxDepth : Nat :=
  Finset.univ.sup (fun p : ParameterBounds.Profile => depth (ParameterBounds.config p))

theorem profile_depth_le (p : ParameterBounds.Profile) :
    depth (ParameterBounds.config p) ≤ maxDepth :=
  Finset.le_sup (f := fun p : ParameterBounds.Profile => depth (ParameterBounds.config p))
    (Finset.mem_univ p)

theorem maxDepth_positive : 0 < maxDepth :=
  lt_of_lt_of_le (by decide : 0 < depth (ParameterBounds.config (0,0))) (profile_depth_le (0,0))

theorem ancestors_maxDepth (ctx : Context) (Q : Nat) (p : Packet ctx Q) :
    (ancestors ctx Q p).length + 1 ≤ maxDepth :=
  (ancestors_depth ctx Q p).trans (profile_depth_le p.val.profile)

theorem completion_ancestors (ctx : Context) (Q : Nat) (p : Packet ctx Q)
    (i : Nat) (hi : i < (ancestors ctx Q p ++ [p]).length) :
    ancestors ctx Q ((ancestors ctx Q p ++ [p])[i]'hi) =
      (ancestors ctx Q p ++ [p]).take i := by
  by_cases hlt : i < (ancestors ctx Q p).length
  · rw [List.getElem_append_left hlt,
      List.take_append_of_le_length (Nat.le_of_lt hlt)]
    exact ancestors_ancestors ctx Q p i hlt
  · have he : i = (ancestors ctx Q p).length := by
      simp only [List.length_append, List.length_singleton] at hi
      omega
    subst i
    simp

theorem ancestors_drop_one (ctx : Context) (Q : Nat) (p : Packet ctx Q)
    (nonempty : p.val.messages.drop 1 ≠ []) :
    ancestors ctx Q p =
      ancestors ctx Q (dropPacket ctx Q p 1 nonempty) ++ [dropPacket ctx Q p 1 nonempty] := by
  have hl : 1 < p.val.messages.length := by
    have h := List.length_pos_iff.mpr nonempty
    simp only [List.length_drop] at h
    omega
  have hi : p.val.messages.length-2 < (ancestors ctx Q p).length := by
    rw [ancestors_length]
    omega
  have hg := ancestors_get ctx Q p ⟨p.val.messages.length-2, by omega⟩
  dsimp only at hg
  have last : (ancestors ctx Q p)[p.val.messages.length-2]'hi = dropPacket ctx Q p 1 nonempty := by
    apply packet_ext ctx Q
    · exact hg.1
    · rw [hg.2]
      change p.val.messages.drop (p.val.messages.length-1-(p.val.messages.length-2)) =
        p.val.messages.drop 1
      congr 1
      omega
    · simp [ancestors, dropPacket]
  have hp := ancestors_ancestors ctx Q p (p.val.messages.length-2) hi
  rw [last] at hp
  rw [hp, ← last, List.take_concat_get']
  have he : p.val.messages.length-2+1 = (ancestors ctx Q p).length := by
    rw [ancestors_length]
    omega
  rw [he, List.take_length]

theorem ancestors_singleton (ctx : Context) (Q : Nat) (p : Packet ctx Q)
    (single : p.val.messages.length = 1) : ancestors ctx Q p = [] := by
  apply List.length_eq_zero_iff.mp
  rw [ancestors_length, single]

end Whir.RawWHIRKeys
