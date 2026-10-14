import Whir.SpongefishCurrentRoundPackets
import Whir.SpongefishCurrentAnchorAttackerPrefix
import Whir.PCSBCSSourceRootAdmission

/-! Current #607 root references, public root policy, first-mention capture and physical freeze for the opening phase.

A decoded current output key mentions Root0 when its history extends the commitment header frame (`headerFrames` closed frames, the last of which carries the literal current header), and it mentions the level root announced after the level-ending fold of every earlier opening draw. The opening draw with index `j` closes a history of `boundary + j + 1` frames (the convention of `SpongefishCurrentRoundPackets.classify`); its reply is absorbed into the next run, which is closed by the following draw as frame `boundary + j + 1`. A run is only closed by a positive draw (`SpongefishPCSRoundFrames.draw`), so after a level-ending fold the frame starts with the 48-byte fold message followed by the raw32 root (`SpongefishCurrentOpeningAcceptance.replyCalls`), possibly followed by later reads of a zero-width OOD round. The level root is therefore bytes 48..80 of that frame, with the Merkle geometry of `SpongefishCurrentOpeningAcceptance.openQuery` at the next level.

The root policy recovers coordinates from the newest-first primitive log, each entry reading only strictly older entries, and announces the roots of their references. Its target count is at most `Q*(Q+1)` and it only grows. Any real counted execution whose compiled mixed trace first mentions a reference has an exact physical freeze of the primitive log in which the reference root is already a target; under the same quiet trace alarm no primitive opening event is retained against the frozen ordinary log. -/
namespace Whir.SpongefishCurrentRootPolicy
open Concrete FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame TypedOracleCompiler
open PublicMerkleLog PCSBCSSourceRootReferences PCSBCSMerkleRootCache
set_option autoImplicit false

/-! ## Level geometry -/

section Geometry
variable (p : ParameterBounds.Profile)
local notation "cfg" => ParameterBounds.config p

/-- Merkle geometry of `openQuery` at level `i`: `length cfg i` leaves, full leaf width and row width `leafWords p i`. -/
def levelShape (i : Nat) : PCSBCSMerkleRootCache.Shape :=
  ⟨(ParameterBounds.length cfg i).log2,WHIRPhysicalVerifier.leafWords p i,
    WHIRPhysicalVerifier.leafWords p i⟩

theorem levelShape_geometry (i : Nat) :
    2^(levelShape p i).height = ParameterBounds.length cfg i ∧
    (levelShape p i).leafWords = WHIRPhysicalVerifier.leafWords p i ∧
    (levelShape p i).occupied = WHIRPhysicalVerifier.leafWords p i := by
  refine ⟨?_,rfl,rfl⟩
  simp only [levelShape,ParameterBounds.length,Nat.log2_two_pow]

/-- At every later level the geometry is the historical phase shape. -/
theorem levelShape_phase (i : Nat) : levelShape p (i+1) = phaseShape cfg (i+1) := by
  simp only [levelShape,phaseShape,ParameterBounds.length,Nat.log2_two_pow,
    WHIRPhysicalVerifier.leafWords,Nat.add_one_ne_zero,↓reduceIte]

private theorem take_one_sum (a : Array Nat) : (a.toList.take 1).sum = a[0]! := by
  rcases a with ⟨l⟩
  cases l <;> simp

/-- Root0's physical shape is the level-0 geometry of `openQuery` with row width `shape.lanes`. -/
theorem root0_geometry (shape : SpongefishSessionAdapter.Shape)
    (supported : SpongefishCurrentAnchorAttackerPrefix.Supported p shape) :
    2^(SpongefishCurrentPhysicalRootCapture.physicalShape shape).height = ParameterBounds.length cfg 0 ∧
    (SpongefishCurrentPhysicalRootCapture.physicalShape shape).leafWords =
      WHIRPhysicalVerifier.leafWords p 0 ∧
    (SpongefishCurrentPhysicalRootCapture.physicalShape shape).occupied = shape.lanes := by
  obtain ⟨heights,widths,lanes⟩ := SpongefishCurrentPhysicalRootCapture.physical_shape shape
  refine ⟨?_,?_,lanes⟩
  · rw [heights,supported.dimension,supported.batch,supported.rate]
    simp only [ParameterBounds.length,CausalGame.remaining,Nat.zero_add,take_one_sum]
  · rw [widths,supported.batch]
    simp [WHIRPhysicalVerifier.leafWords]
end Geometry

/-- The raw32 root read after the 48-byte fold message of a level-ending fold. -/
def levelRoot (bytes : List Byte) : Option Digest32 :=
  (SpongefishPCSRoundFrames.rootCodec.parse (bytes.drop 48)).map Prod.fst

theorem levelRoot_reply (message rest : List Byte) (width : message.length = 48) (root : Digest32) :
    levelRoot (message ++ SpongefishPCSRoundFrames.rootCodec.bytes root ++ rest) = some root := by
  simp only [levelRoot,List.append_assoc,List.drop_left' width,
    SpongefishPCSRoundFrames.Codec.parse_append,Option.map_some]

/-- The literal native reply of a level-ending fold: `[.read (.vector 2), .read .root]`. -/
theorem levelRoot_fold_reply (xs : Fin 2 → E) (root : Digest32) (rest : List Byte) :
    levelRoot ((SpongefishPCSRoundFrames.vectorCodec 2).bytes xs ++
      SpongefishPCSRoundFrames.rootCodec.bytes root ++ rest) = some root := by
  apply levelRoot_reply
  simp [SpongefishPCSRoundFrames.Codec.bytes,SpongefishPCSRoundFrames.vectorCodec]

/-! ## Frame count of a coordinate -/

private theorem chunks_ne_nil (first : Bool) (previous : Nat) (pending bytes : List Byte)
    (nonempty : pending ≠ []) : DuplexEncoding.chunks first previous pending bytes ≠ [] := by
  induction bytes generalizing first previous pending with
  | nil => simp [DuplexEncoding.chunks,nonempty]
  | cons b bs ih =>
    simp only [DuplexEncoding.chunks]
    split
    · simp
    · exact ih first previous (pending ++ [b]) (by simp)

private theorem framePlan_ne_nil (f : Frame) (valid : DuplexEncoding.FrameValid f) :
    DuplexEncoding.framePlan f ≠ [] := by
  cases f with
  | absorb previous bytes =>
    cases bytes with
    | nil => exact absurd rfl valid.2
    | cons b bs =>
      simp only [DuplexEncoding.framePlan,DuplexEncoding.chunks]
      split
      · simp
      · exact chunks_ne_nil true previous ([] ++ [b]) bs (by simp)
  | nonce previous bits nonce => simp [DuplexEncoding.framePlan]

/-- Every valid frame costs at least one compression, besides the seed and terminal calls. -/
theorem frames_pathCost (q : Coordinate) (valid : DuplexEncoding.Admissible q) :
    q.history.frames.length + 2 ≤ pathCost q := by
  have frames : ∀ fs : List Frame, (∀ f ∈ fs, DuplexEncoding.FrameValid f) →
      fs.length ≤ (fs.flatMap DuplexEncoding.framePlan).length := by
    intro fs
    induction fs with
    | nil => intro _; simp
    | cons f fs ih =>
      intro allValid
      have head := framePlan_ne_nil f (allValid f List.mem_cons_self)
      have tail := ih (fun g member => allValid g (List.mem_cons_of_mem _ member))
      have positive := List.length_pos_iff.mpr head
      simp only [List.flatMap_cons,List.length_append,List.length_cons]
      omega
  have bound := frames q.history.frames valid.1
  simp only [pathCost,DuplexEncoding.plan,List.length_cons,List.length_append]
  omega

/-! ## References -/

section References
variable (p : ParameterBounds.Profile) (grinding : Fin (ParameterBounds.config p).folds.size → Fin 64)
  (shape : SpongefishSessionAdapter.Shape) (headerFrames boundary : Nat)

/-- Root0, read from the commitment header frame of a history that extends it. -/
def anchorReference (h : FramedHistory) : Option Reference :=
  if headerFrames ≤ h.frames.length then
    (SpongefishCurrentAnchorHeader.fromHistory shape {h with frames := h.frames.take headerFrames}).map
      (SpongefishCurrentPhysicalRootCapture.reference shape)
  else none

/-- The level root announced in the reply frame of opening draw `j`, when that draw is the last fold of a non-final level. -/
def levelAt (h : FramedHistory) (j : Nat) : Option Reference :=
  match (SpongefishCurrentRoundPackets.openingDraws grinding)[j]? with
  | some (some (.fold i k)) =>
    if SpongefishCurrentOpeningAcceptance.isLastFold i k = true ∧
        i.val + 1 < (ParameterBounds.config p).folds.size then
      match h.frames[boundary + j + 1]? with
      | some (.absorb _ bytes) => (levelRoot bytes).map (fun root => ⟨root,levelShape p (i.val+1)⟩)
      | _ => none
    else none
  | _ => none

/-- All root references disclosed by a history: Root0 and the level roots of completed opening replies. -/
def references (h : FramedHistory) : List Reference :=
  (anchorReference shape headerFrames h).toList ++
    (List.range h.frames.length).filterMap (levelAt p grinding boundary h)

theorem references_length (h : FramedHistory) :
    (references p grinding shape headerFrames boundary h).length ≤ h.frames.length + 1 := by
  have anchor : (anchorReference shape headerFrames h).toList.length ≤ 1 := by
    cases anchorReference shape headerFrames h <;> simp
  have levels := List.length_filterMap_le (levelAt p grinding boundary h) (List.range h.frames.length)
  simp only [references,List.length_append,List.length_range] at levels ⊢
  omega

theorem anchor_mem (h : FramedHistory) (root : Digest32) (enough : headerFrames ≤ h.frames.length)
    (header : SpongefishCurrentAnchorHeader.fromHistory shape
      {h with frames := h.frames.take headerFrames} = some root) :
    SpongefishCurrentPhysicalRootCapture.reference shape root ∈
      references p grinding shape headerFrames boundary h := by
  apply List.mem_append_left
  simp [anchorReference,enough,header]

theorem level_mem (h : FramedHistory) (j : Nat) (i : Fin (ParameterBounds.config p).folds.size)
    (k : Fin (ParameterBounds.config p).folds[i.val]!)
    (draw : (SpongefishCurrentRoundPackets.openingDraws grinding)[j]? = some (some (.fold i k)))
    (last : SpongefishCurrentOpeningAcceptance.isLastFold i k = true)
    (later : i.val + 1 < (ParameterBounds.config p).folds.size)
    (previous : Nat) (bytes : List Byte)
    (frame : h.frames[boundary + j + 1]? = some (.absorb previous bytes))
    (root : Digest32) (parsed : levelRoot bytes = some root) :
    (⟨root,levelShape p (i.val+1)⟩ : Reference) ∈ references p grinding shape headerFrames boundary h := by
  apply List.mem_append_right
  obtain ⟨inside,_⟩ := List.getElem?_eq_some_iff.mp frame
  refine List.mem_filterMap.mpr ⟨j,List.mem_range.mpr (by omega),?_⟩
  simp only [levelAt,draw,last,later,and_self,↓reduceIte,frame,parsed,Option.map_some]

/-- References of a decoded coordinate; only output keys disclose roots. -/
def coordinateReferences (q : Coordinate) : List Reference :=
  match q.terminal with
  | .output _ => references p grinding shape headerFrames boundary q.history
  | _ => []

theorem coordinateReferences_length (q : Coordinate) (valid : DuplexEncoding.Admissible q) :
    (coordinateReferences p grinding shape headerFrames boundary q).length + 1 ≤ pathCost q := by
  have frames := frames_pathCost q valid
  have refs := references_length p grinding shape headerFrames boundary q.history
  unfold coordinateReferences
  split
  · omega
  · simp only [List.length_nil]
    omega

/-! ## Root policy -/

variable (Q : Nat) (iv : Digest32)

/-- Roots announced by one primitive entry, reading only the strictly older log. -/
def rootsAt (older : PublicLog) (input : Node) : List Digest32 :=
  ((PCSBCSSourceCoordinateDecoder.recover Q iv older input).map
    (fun q => (coordinateReferences p grinding shape headerFrames boundary q).map Reference.root)).getD []

/-- Newest-first log; announcements of older entries come first. -/
def scan : PublicLog → List Digest32
  | [] => []
  | (input,_) :: older => scan older ++ rootsAt p grinding shape headerFrames boundary Q iv older input

def targets : PublicMerkleProbability.RootPolicy := fun log =>
  (scan p grinding shape headerFrames boundary Q iv log).toFinset

theorem rootsAt_length (older : PublicLog) (input : Node) :
    (rootsAt p grinding shape headerFrames boundary Q iv older input).length ≤ Q + 1 := by
  unfold rootsAt
  cases recovered : PCSBCSSourceCoordinateDecoder.recover Q iv older input with
  | none => simp
  | some q =>
    obtain ⟨_,_,_,_,_,_,valid,cost⟩ := PCSBCSSourceCoordinateDecoder.recover_sound recovered
    have bound := coordinateReferences_length p grinding shape headerFrames boundary q valid
    simp only [Option.map_some,Option.getD_some,List.length_map]
    omega

theorem scan_length (log : PublicLog) :
    (scan p grinding shape headerFrames boundary Q iv log).length ≤ log.length * (Q+1) := by
  induction log with
  | nil => simp [scan]
  | cons record older ih =>
    rcases record with ⟨input,digest⟩
    have bound := rootsAt_length p grinding shape headerFrames boundary Q iv older input
    simp only [scan,List.length_append,List.length_cons]
    rw [Nat.succ_mul]
    omega

theorem targets_grow : PublicMerkleProbability.RootsGrow
    (targets p grinding shape headerFrames boundary Q iv) := by
  intro history record root member
  rcases record with ⟨input,digest⟩
  simp only [targets,scan,List.mem_toFinset,List.mem_append] at member ⊢
  exact Or.inl member

theorem targets_cap (log : PublicLog) (budget : log.length ≤ Q) :
    (targets p grinding shape headerFrames boundary Q iv log).card ≤ Q*(Q+1) := by
  have finite := List.toFinset_card_le (scan p grinding shape headerFrames boundary Q iv log)
  have count := scan_length p grinding shape headerFrames boundary Q iv log
  have cost := Nat.mul_le_mul_right (Q+1) budget
  exact finite.trans (count.trans cost)

theorem targets_append (newer older : PublicLog) :
    targets p grinding shape headerFrames boundary Q iv older ⊆
      targets p grinding shape headerFrames boundary Q iv (newer ++ older) := by
  induction newer with
  | nil => exact fun _ h => h
  | cons record newer ih =>
    exact fun _ h => targets_grow p grinding shape headerFrames boundary Q iv _ _ (ih h)

/-! ## First-mention capture -/

/-- Root addresses of a mixed key: decoded current output keys only; ordinary nodes have none. -/
def addresses {B : Nat} : PublicCompressionCouplingMixed.Key B → List Reference
  | .inl _ => []
  | .inr key =>
    match WHIRHeaderRoots.decodeRaw iv key with
    | none => []
    | some q => coordinateReferences p grinding shape headerFrames boundary q

def firstPrefix {B : Nat} (ref : Reference)
    (events : List (SpongefishCurrentPhysicalRootCapture.Event B)) :
    Option (List (SpongefishCurrentPhysicalRootCapture.Event B)) :=
  PCSBCSNativePublicCapture.firstPrefix (addresses p grinding shape headerFrames boundary iv) ref events

/-- Freeze the ordinary log strictly before the first mention, never including the mentioning answer. -/
def capture {B : Nat} (ref : Reference)
    (events : List (SpongefishCurrentPhysicalRootCapture.Event B)) : Option Frozen :=
  (firstPrefix p grinding shape headerFrames boundary iv ref events).map
    (fun before => freeze (SpongefishCurrentPhysicalRootCapture.ordinaryLog before) ref.root ref.shape)

def publicCapture {B : Nat} {R : Type} (ref : Reference) (view : DuplexModeGame.View R) : Option Frozen :=
  capture p grinding shape headerFrames boundary iv ref
    (PCSBCSNativePublicCapture.mixedTrace B iv [] view.observations)

theorem firstPrefix_source {B n : Nat} {R : Type} (ref : Reference)
    (program : Sampling (PublicCompressionCouplingMixed.Key B) (fun _ => Digest32) R n)
    (table : PublicCompressionCouplingMixed.Key B → Digest32) :
    PCSBCSFirstRootDisclosure.firstMention (addresses p grinding shape headerFrames boundary iv) ref
        program table =
      firstPrefix p grinding shape headerFrames boundary iv ref (Sampling.execute table program).2 :=
  PCSBCSNativePublicCapture.firstPrefix_execute _ _ _ _

theorem publicCapture_source {B : Nat} {R : Type} (ref : Reference)
    (seed : DuplexPublicSimulator.Seed) (ro : RawKey B → Digest32)
    (program : DuplexModeGame.Program R) (remaining : Nat) (limit : remaining ≤ B)
    (counted : DuplexModeGame.Counts remaining program) :
    let compiled := PublicCompressionCouplingMixed.compile B iv [] program remaining limit counted
    publicCapture (B := B) p grinding shape headerFrames boundary iv ref
        (Sampling.eval (PublicCompressionCouplingMixed.oracle seed ro) compiled) =
      capture p grinding shape headerFrames boundary iv ref
        (Sampling.execute (PublicCompressionCouplingMixed.oracle seed ro) compiled).2 := by
  dsimp only [publicCapture]
  rw [PCSBCSNativePublicCapture.mixedTrace_actual B seed ro iv [] program remaining limit counted]

end References

/-! ## Recovery at the first physical occurrence (generic IV) -/

section Recovery

private theorem body_mono {small large : DuplexPublicSimulator.PublicLog}
    (sub : ∀ e ∈ small, e ∈ large) {cv : Digest32} {ns : List Node}
    (body : DuplexPublicSimulator.PublicBody small cv ns) :
    DuplexPublicSimulator.PublicBody large cv ns := by
  induction body with
  | seed member seed => exact .seed (sub _ member) seed
  | step member internal child ih => exact .step (sub _ member) internal ih

private theorem functional_of_auth (C : PrimitiveOracle) (log : PublicLog)
    (auth : AuthenticLog C log) : DuplexPublicSimulator.Functional log := by
  intro n a b ha hb
  exact (auth n a ha).symm.trans (auth n b hb)

private theorem simulator_lookup_eq (log : PublicLog) (n : Node) :
    DuplexPublicSimulator.lookup log n = PublicMerkleLog.lookup log n := by
  induction log with
  | nil => rfl
  | cons record log ih =>
    rcases record with ⟨m,d⟩
    by_cases same : n = m
    · simp [DuplexPublicSimulator.lookup,PublicMerkleLog.lookup,List.find?,same]
    · have other : m ≠ n := Ne.symm same
      simp [DuplexPublicSimulator.lookup,PublicMerkleLog.lookup,List.find?,same,other] at ih ⊢
      exact ih

/-- `PCSBCSSourceRootAdmission.first_recovery` for an arbitrary IV: the quiet alarm recovers the coordinate at the first physical occurrence of its terminal, from the strictly older log. -/
theorem first_recovery (C : PrimitiveOracle) (roots : PublicMerkleProbability.RootPolicy)
    (B : Nat) (iv : Digest32) (log : PublicLog) (auth : AuthenticLog C log)
    (quiet : PublicMerkleProbability.traceAlarm roots [] log.reverse = false)
    (budget : log.length ≤ B) (input : Node) (rest : List Node)
    (terminal : isTerminal input)
    (body : DuplexPublicSimulator.PublicBody log input.cv rest)
    (present : (input,C input) ∈ log) (q : Coordinate)
    (valid : DuplexEncoding.Admissible q)
    (extracted : extract (input::rest) = some (modeKey iv q)) :
    ∃ newer older, log = newer ++ (input,C input)::older ∧
      PCSBCSSourceCoordinateDecoder.recover B iv older input = some q := by
  induction log with
  | nil => cases present
  | cons record log ih =>
    rcases record with ⟨n,d⟩
    have answer := auth n d List.mem_cons_self
    subst d
    have oldAuth : AuthenticLog C log := fun n d h => auth n d (List.mem_cons_of_mem _ h)
    have oldBudget : log.length ≤ B := by simp only [List.length_cons] at budget; omega
    have parts := quiet
    rw [List.reverse_cons,PublicMerkleProbability.traceAlarm_append] at parts
    simp only [Bool.or_eq_false_iff,List.reverse_reverse,List.append_nil,
      PublicMerkleProbability.traceAlarm,Bool.or_false,decide_eq_false_iff_not] at parts
    have oldQuiet := parts.1
    have safe := parts.2
    cases hit : PublicMerkleLog.lookup log n with
    | some d =>
      have old := PublicMerkleLog.lookup_mem hit
      have same := oldAuth n d old
      rw [← same] at old
      have oldBody := PublicCompressionCouplingRecognition.PublicBody.erase_repeat old body
      have oldPresent : (input,C input) ∈ log := by
        rcases List.mem_cons.mp present with equal | member
        · cases equal; exact old
        · exact member
      obtain ⟨newer,older,equal,recovered⟩ := ih oldAuth oldQuiet oldBudget oldBody oldPresent
      exact ⟨(n,C n)::newer,older,by simp only [List.cons_append,equal],recovered⟩
    | none =>
      by_cases same : n = input
      · subst n
        have oldBody := PublicCompressionCouplingRecognition.PublicBody.erase_terminal terminal body
        have clean : ¬ DuplexPublicSimulator.OutputCollision log := by
          have h := PublicMerkleProbability.traceAlarm_clean C roots [] log.reverse
            (by intro n d h; cases h)
            (fun n d h => oldAuth n d (List.mem_reverse.mp h))
            (by rintro ⟨a,b,d,h,_⟩; cases h) oldQuiet
          simp only [List.reverse_reverse,List.append_nil] at h
          exact fun ⟨a,b,d,ha,hb,ne⟩ => h ⟨a,b,d,ha,hb,ne⟩
        have recognized := DuplexPublicSimulator.recognized_complete
          (functional_of_auth C log oldAuth) clean terminal oldBody
        obtain ⟨key,found,keyExtracted⟩ := DuplexPublicSimulator.privateKey_of_recognized
          (by simpa only [simulator_lookup_eq] using hit) recognized budget
        have keySame : expandKey key = modeKey iv q :=
          Option.some.inj (keyExtracted.symm.trans extracted)
        exact ⟨[],log,rfl,PCSBCSSourceCoordinateDecoder.recover_of_modeKey found valid keySame⟩
      · have oldPresent : (input,C input) ∈ log := by
          rcases List.mem_cons.mp present with equal | member
          · exact False.elim (same (congrArg Prod.fst equal).symm)
          · exact member
        have avoid : ∀ m d, (m,d) ∈ log → C n ≠ m.cv := by
          intro m d member equal
          apply safe
          refine ⟨hit,?_⟩
          apply Finset.mem_union_right
          apply Finset.mem_union_right
          rw [equal]
          exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨(m,d),member,rfl⟩)
        have oldBody := PublicCompressionCouplingRecognition.PublicBody.erase_record body avoid
          (avoid input (C input) oldPresent)
        obtain ⟨newer,older,equal,recovered⟩ := ih oldAuth oldQuiet oldBudget oldBody oldPresent
        exact ⟨(n,C n)::newer,older,by simp only [List.cons_append,equal],recovered⟩

end Recovery

/-! ## Physical freeze and admission -/

section Admission
variable (p : ParameterBounds.Profile) (grinding : Fin (ParameterBounds.config p).folds.size → Fin 64)
  (shape : SpongefishSessionAdapter.Shape) (headerFrames boundary : Nat)

/-- A physically recorded terminal with its complete public body announces every reference of its coordinate. -/
theorem tree_target (Q : Nat) (iv : Digest32) (C : PrimitiveOracle) (log : PublicLog)
    (auth : AuthenticLog C log)
    (quiet : PublicMerkleProbability.traceAlarm
      (targets p grinding shape headerFrames boundary Q iv) [] log.reverse = false)
    (budget : log.length ≤ Q) (input : Node) (rest : List Node)
    (terminal : isTerminal input) (body : DuplexPublicSimulator.PublicBody log input.cv rest)
    (present : (input,C input) ∈ log) (q : Coordinate) (valid : DuplexEncoding.Admissible q)
    (extracted : extract (input::rest) = some (modeKey iv q))
    (ref : Reference) (member : ref ∈ coordinateReferences p grinding shape headerFrames boundary q) :
    ref.root ∈ targets p grinding shape headerFrames boundary Q iv log := by
  obtain ⟨newer,older,equal,recovered⟩ := first_recovery C _ Q iv log auth quiet budget
    input rest terminal body present q valid extracted
  have announced : ref.root ∈ targets p grinding shape headerFrames boundary Q iv ((input,C input)::older) := by
    simp only [targets,scan,List.mem_toFinset,List.mem_append]
    right
    simp only [rootsAt,recovered,Option.map_some,Option.getD_some,List.mem_map]
    exact ⟨ref,member,rfl⟩
  rw [equal]
  exact targets_append p grinding shape headerFrames boundary Q iv newer _ announced

/-- An actual mixed draw mentioning a reference was preceded by the physical calls announcing its root. -/
theorem draw_admission (B : Nat) (iv : Digest32) (C : PrimitiveOracle)
    (earlier cache : PublicLog) (current : Observation)
    (event : SpongefishCurrentPhysicalRootCapture.Event B)
    (cacheSub : ∀ e ∈ cache, e ∈ earlier)
    (auth : AuthenticLog C (earlier ++ PCSBCSConstructionReplayTrace.queryTrace C iv current.query))
    (quiet : PublicMerkleProbability.traceAlarm
      (targets p grinding shape headerFrames boundary B iv) []
      (earlier ++ PCSBCSConstructionReplayTrace.queryTrace C iv current.query) = false)
    (budget : (earlier ++ PCSBCSConstructionReplayTrace.queryTrace C iv current.query).length ≤ B)
    (draw : PCSBCSNativePublicCapture.observationDraw B iv cache current = [event])
    (ref : Reference)
    (mentioned : ref ∈ addresses p grinding shape headerFrames boundary iv event.1) :
    ref.root ∈ targets p grinding shape headerFrames boundary B iv
      (earlier ++ PCSBCSConstructionReplayTrace.queryTrace C iv current.query).reverse := by
  rcases event with ⟨raw,answer⟩
  cases raw with
  | inl node => simp [addresses] at mentioned
  | inr key =>
    cases decoded : WHIRHeaderRoots.decodeRaw iv key with
    | none => simp [addresses,decoded] at mentioned
    | some q =>
      have member : ref ∈ coordinateReferences p grinding shape headerFrames boundary q := by
        simpa only [addresses,decoded] using mentioned
      obtain ⟨bound,valid,keyEq⟩ := WHIRHeaderRoots.decodeRaw_sound iv key q decoded
      have prefixAuth : AuthenticLog C
          (earlier ++ PCSBCSConstructionReplayTrace.queryTrace C iv current.query).reverse :=
        fun n d h => auth n d (List.mem_reverse.mp h)
      have prefixQuiet : PublicMerkleProbability.traceAlarm
          (targets p grinding shape headerFrames boundary B iv) []
          ((earlier ++ PCSBCSConstructionReplayTrace.queryTrace C iv current.query).reverse).reverse =
            false := by
        simpa only [List.reverse_reverse] using quiet
      have prefixBudget :
          (earlier ++ PCSBCSConstructionReplayTrace.queryTrace C iv current.query).reverse.length ≤ B := by
        simpa only [List.length_reverse] using budget
      rcases current with ⟨query,d⟩
      cases query with
      | primitive purpose input =>
        unfold PCSBCSNativePublicCapture.observationDraw at draw
        cases hit : DuplexPublicSimulator.lookup cache input with
        | some old => simp [hit] at draw
        | none =>
          cases found : DuplexPublicSimulator.privateKey B cache input with
          | none =>
            simp only [hit,found,List.singleton_inj] at draw
            have impossible := congrArg Sigma.fst draw
            cases impossible
          | some actual =>
            simp only [hit,found,List.singleton_inj] at draw
            have keys : actual = key := Sum.inr.inj (congrArg Sigma.fst draw)
            subst keys
            obtain ⟨nodes,recognized,complete,extracted⟩ := DuplexPublicSimulator.privateKey_sound found
            obtain ⟨rest,rfl,body⟩ := DuplexPublicSimulator.recognized_publicBody recognized
            have terminal : isTerminal input := by
              obtain ⟨n,ns,equal,terminal,_⟩ := complete
              cases equal
              exact terminal
            have publicBody : DuplexPublicSimulator.PublicBody
                (earlier ++ PCSBCSConstructionReplayTrace.queryTrace C iv
                  (.primitive purpose input)).reverse input.cv rest :=
              body_mono (fun e he => List.mem_reverse.mpr (List.mem_append_left _ (cacheSub e he))) body
            have recorded : (input,C input) ∈
                (earlier ++ PCSBCSConstructionReplayTrace.queryTrace C iv
                  (.primitive purpose input)).reverse :=
              List.mem_reverse.mpr (List.mem_append_right _ List.mem_cons_self)
            have sourceExtract : extract (input::rest) = some (modeKey iv q) := by
              rw [← keyEq] at extracted
              exact extracted.trans (congrArg some (expand_constructionKey B iv q bound))
            exact tree_target p grinding shape headerFrames boundary B iv C _ prefixAuth prefixQuiet
              prefixBudget input rest terminal publicBody recorded q valid sourceExtract ref member
      | construction coordinate coordinateValid =>
        by_cases coordinateBound : pathCost coordinate ≤ B
        · simp only [PCSBCSNativePublicCapture.observationDraw,coordinateBound,↓reduceDIte,
            List.singleton_inj] at draw
          have keys : constructionKey B iv coordinate coordinateBound = key :=
            Sum.inr.inj (congrArg Sigma.fst draw)
          have same : q = coordinate := by
            rw [← keys,WHIRHeaderRoots.decodeRaw_construction iv coordinate coordinateValid
              coordinateBound] at decoded
            exact (Option.some.inj decoded).symm
          subst same
          obtain ⟨body,recorded⟩ := PCSBCSSourceRootAdmission.construction_body C iv q coordinateValid
            (earlier ++ PCSBCSConstructionReplayTrace.queryTrace C iv (.construction q coordinateValid)).reverse
            (fun e he => List.mem_reverse.mpr (List.mem_append_right _ he))
          have cv : (terminalNode
              (traceHistory (compressionOf C) iv q.history).state.cv q.terminal).cv =
              (traceHistory (compressionOf C) iv q.history).state.cv := by
            cases q.terminal <;> rfl
          rw [← cv] at body
          have terminal := terminal_node (traceHistory (compressionOf C) iv q.history).state.cv q.terminal
          have extracted := coordinateTree_key (compressionOf C) iv q coordinateValid
          exact tree_target p grinding shape headerFrames boundary B iv C _ prefixAuth prefixQuiet
            prefixBudget _ _ terminal body recorded q valid extracted ref member
        · simp [PCSBCSNativePublicCapture.observationDraw,coordinateBound] at draw

private theorem ordinaryLog_captureFrom {B : Nat}
    (events : List (SpongefishCurrentPhysicalRootCapture.Event B)) (prior : PublicLog) :
    events.foldl SpongefishCurrentPhysicalRootCapture.ordinaryStep prior =
      events.foldl (fun log event => PCSBCSNativePublicCapture.rawOrdinary event ++ log) prior := by
  induction events generalizing prior with
  | nil => rfl
  | cons event rest ih =>
    simp only [List.foldl_cons]
    rw [ih]
    congr 1
    rcases event with ⟨raw,answer⟩
    cases raw <;> rfl

/-- Actual first mention in the compiled real execution: exact physical freeze of the primitive log, with the reference root admitted by the policy before the freeze point. -/
theorem actual_firstMention_admitted {R : Type} (B : Nat) (iv : Digest32) (C : PrimitiveOracle)
    (program : Program R) (A : Nat) (limit : A ≤ B) (counted : Counts A program)
    (ref : Reference) (events : List (SpongefishCurrentPhysicalRootCapture.Event B))
    (mentioned : firstPrefix p grinding shape headerFrames boundary iv ref
      (Sampling.execute (PublicCompressionCouplingMixed.oracle C (WHIRRealSimulator.rawTable B C))
        (PublicCompressionCouplingMixed.compile B iv [] program A limit counted)).2 = some events)
    (quiet : PublicMerkleProbability.traceAlarm
      (targets p grinding shape headerFrames boundary B iv) []
      (PublicCompressionProgram.primitiveLog C iv program A counted) = false) :
    ∃ frozen : PCSBCSNativePhysicalFreeze.PhysicalFreeze
        (PublicCompressionProgram.primitiveLog C iv program A counted)
        (SpongefishCurrentPhysicalRootCapture.ordinaryLog events),
      ref.root ∈ targets p grinding shape headerFrames boundary B iv frozen.before.reverse := by
  have realView :
      Sampling.eval (PublicCompressionCouplingMixed.oracle C (WHIRRealSimulator.rawTable B C))
        (PublicCompressionCouplingMixed.compile B iv [] program A limit counted) =
        (runReal C iv program).view := by
    rw [PublicCompressionCouplingMixed.compile_actual]
    exact WHIRRealSimulator.runIdeal_view C iv _ ⟨rfl,by simp⟩ _ _ limit _
  have trace := PCSBCSNativePublicCapture.mixedTrace_actual B C (WHIRRealSimulator.rawTable B C)
    iv [] program A limit counted
  rw [realView] at trace
  rw [firstPrefix,trace] at mentioned
  obtain ⟨earlier,current,later,cache,event,split,draw,addressed,cacheSub,auth,sub,sat⟩ :=
    PCSBCSNativePhysicalFreeze.firstPrefix_freeze B C iv
      (addresses p grinding shape headerFrames boundary iv) ref (fun _ => by simp [addresses])
      (runReal C iv program).view.observations [] [] []
      ⟨by simp [AuthenticLog],by simp,by simp,by simp⟩ (by simp)
      (fun o member => PCSBCSConstructionReplayTrace.observation_answer C iv program o member)
      events mentioned
  have logSplit : PublicCompressionProgram.primitiveLog C iv program A counted =
      (PCSBCSNativePhysicalFreeze.physicalTrace C iv earlier ++
        PCSBCSConstructionReplayTrace.queryTrace C iv current.query) ++
        PCSBCSNativePhysicalFreeze.physicalTrace C iv later := by
    rw [PCSBCSNativePhysicalFreeze.physicalTrace_actual,split]
    simp only [PCSBCSNativePhysicalFreeze.physicalTrace,List.flatMap_append,List.flatMap_cons,
      List.append_assoc]
  have ordinary : SpongefishCurrentPhysicalRootCapture.ordinaryLog events =
      PCSBCSNativePhysicalFreeze.captureFrom events [] :=
    ordinaryLog_captureFrom events []
  have prefixAuth : AuthenticLog C (PCSBCSNativePhysicalFreeze.physicalTrace C iv earlier ++
      PCSBCSConstructionReplayTrace.queryTrace C iv current.query) := by
    intro n d member
    apply PublicCompressionProgram.primitiveLog_authentic C iv program A counted n d
    rw [logSplit]
    exact List.mem_append_left _ member
  have prefixQuiet : PublicMerkleProbability.traceAlarm
      (targets p grinding shape headerFrames boundary B iv) []
      (PCSBCSNativePhysicalFreeze.physicalTrace C iv earlier ++
        PCSBCSConstructionReplayTrace.queryTrace C iv current.query) = false := by
    rw [logSplit,PublicMerkleProbability.traceAlarm_append] at quiet
    exact (Bool.or_eq_false_iff.mp quiet).1
  have prefixBudget : (PCSBCSNativePhysicalFreeze.physicalTrace C iv earlier ++
      PCSBCSConstructionReplayTrace.queryTrace C iv current.query).length ≤ B := by
    have bound := PublicCompressionProgram.primitiveLog_length C iv program A counted
    rw [logSplit,List.length_append] at bound
    omega
  have target := draw_admission p grinding shape headerFrames boundary B iv C _ cache current event
    (by simpa only [List.nil_append] using cacheSub) prefixAuth prefixQuiet prefixBudget draw ref addressed
  refine ⟨⟨_,_,logSplit,?_,?_⟩,target⟩
  · rw [ordinary]
    simpa only [List.nil_append] using sub
  · rw [ordinary]
    simpa only [List.nil_append] using sat

/-- The quiet trace alarm excludes every retained primitive opening event against the first-mention frozen ordinary log, for every counted program. -/
theorem opening_quiet {R : Type} (B : Nat) (iv : Digest32) (C : PrimitiveOracle)
    (program : Program R) (A : Nat) (limit : A ≤ B) (counted : Counts A program)
    (ref : Reference) (events : List (SpongefishCurrentPhysicalRootCapture.Event B))
    (mentioned : firstPrefix p grinding shape headerFrames boundary iv ref
      (Sampling.execute (PublicCompressionCouplingMixed.oracle C (WHIRRealSimulator.rawTable B C))
        (PublicCompressionCouplingMixed.compile B iv [] program A limit counted)).2 = some events)
    (quiet : PublicMerkleProbability.traceAlarm
      (targets p grinding shape headerFrames boundary B iv) []
      (PublicCompressionProgram.primitiveLog C iv program A counted) = false)
    (output : List MerkleTransport.RawPath)
    (bounds : ∀ path ∈ output, ∀ bytes ∈ path.opening.inputs (MerkleTransport.hashing (hash C)),
      bytes.length < 2^56)
    (plans : ∀ path ∈ output, ∀ bytes ∈ path.opening.inputs (MerkleTransport.hashing (hash C)),
      ∀ e ∈ plan C bytes, e ∈ PublicCompressionProgram.primitiveLog C iv program A counted) :
    ¬ PublicMerkleBinding.OpenPrimitiveBad C
      (SpongefishCurrentPhysicalRootCapture.ordinaryLog events) ref.root output := by
  intro bad
  obtain ⟨frozen,registered⟩ := actual_firstMention_admitted p grinding shape headerFrames boundary
    B iv C program A limit counted ref events mentioned quiet
  have alarm := PublicMerkleProbability.opening_alarm C
    (targets p grinding shape headerFrames boundary B iv)
    (targets_grow p grinding shape headerFrames boundary B iv)
    (PublicCompressionProgram.primitiveLog C iv program A counted)
    (PublicCompressionProgram.primitiveLog_authentic C iv program A counted)
    ⟨frozen.before,frozen.after,_,ref.root,output,frozen.split,frozen.captured,
      frozen.saturated,registered,bounds,plans,bad⟩
  rw [quiet] at alarm
  cases alarm

/-- The same exclusion stated on the frozen capture itself. -/
theorem captured_opening_quiet {R : Type} (B : Nat) (iv : Digest32) (C : PrimitiveOracle)
    (program : Program R) (A : Nat) (limit : A ≤ B) (counted : Counts A program)
    (ref : Reference) (frozen : Frozen)
    (found : capture p grinding shape headerFrames boundary iv ref
      (Sampling.execute (PublicCompressionCouplingMixed.oracle C (WHIRRealSimulator.rawTable B C))
        (PublicCompressionCouplingMixed.compile B iv [] program A limit counted)).2 = some frozen)
    (quiet : PublicMerkleProbability.traceAlarm
      (targets p grinding shape headerFrames boundary B iv) []
      (PublicCompressionProgram.primitiveLog C iv program A counted) = false)
    (output : List MerkleTransport.RawPath)
    (bounds : ∀ path ∈ output, ∀ bytes ∈ path.opening.inputs (MerkleTransport.hashing (hash C)),
      bytes.length < 2^56)
    (plans : ∀ path ∈ output, ∀ bytes ∈ path.opening.inputs (MerkleTransport.hashing (hash C)),
      ∀ e ∈ plan C bytes, e ∈ PublicCompressionProgram.primitiveLog C iv program A counted) :
    frozen = freeze frozen.queryPrefix ref.root ref.shape ∧
    ¬ PublicMerkleBinding.OpenPrimitiveBad C frozen.queryPrefix ref.root output := by
  obtain ⟨events,mentioned,equal⟩ := Option.map_eq_some_iff.mp found
  subst frozen
  exact ⟨rfl,opening_quiet p grinding shape headerFrames boundary B iv C program A limit counted
    ref events mentioned quiet output bounds plans⟩

end Admission

#print axioms levelShape_geometry
#print axioms levelShape_phase
#print axioms root0_geometry
#print axioms levelRoot_reply
#print axioms levelRoot_fold_reply
#print axioms frames_pathCost
#print axioms references_length
#print axioms anchor_mem
#print axioms level_mem
#print axioms coordinateReferences_length
#print axioms rootsAt_length
#print axioms scan_length
#print axioms targets_grow
#print axioms targets_cap
#print axioms targets_append
#print axioms firstPrefix_source
#print axioms publicCapture_source
#print axioms first_recovery
#print axioms tree_target
#print axioms draw_admission
#print axioms actual_firstMention_admitted
#print axioms opening_quiet
#print axioms captured_opening_quiet

end Whir.SpongefishCurrentRootPolicy
