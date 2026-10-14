import Whir.PCSBCSCapturedSourceTransport
import Whir.PCSBCSChallengeOracleRestoration
import Whir.PCSBCSRestorationLiteralPath
import Whir.PCSBCSLiteralStatePath
import Whir.PCSRoundByRoundPublicEndpoint

/-! Exact strict-trace identities for the literal captured builder. These
identities are deterministic; no probability composition or Rust refinement is
hidden in this module's endpoints. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
namespace Whir.PCSBCSCapturedSourceStatePath
open Concrete Protocol CausalGame CausalProbability FiatShamirGame WHIRHistory
open PCSBCSChallengeOracle PCSBCSSourceRootReferences PCSBCSMerkleRootCache
open PCSBCSSourceCallerSnapshot PCSBCSSourceReplyInversion
open PCSBCSCallerBinding PCSBCSRestorationHazard PCSRoundByRoundTranscriptState
open TypedOracleCompiler TypedFiatShamirGame PCSStateRestoration.Latent
open CausalPositions

variable {p : ParameterBounds.Profile} {Q : Nat} {iv : Digest32} {boundary : Nat}
local notation "Keys" => PCSBCSSourceRootCapture.Key
  (p := p) (Q := Q) (iv := iv) (boundary := boundary)
local notation "Answers" => PCSBCSSourceRootCapture.Answer
  (p := p) (Q := Q) (iv := iv) (boundary := boundary)

/-- The production builder receives only other full packets; its unused
Earlier argument is not a supplied recovery oracle. -/
noncomputable def builder {R : Type} {n : Nat}
    (addresses : Keys → List Reference) (ref : Reference)
    (program : Sampling Keys Answers R n) (original : CallerInput p)
    (saved : AnchoredHeaderCodec.Record) : Restoration.Builder p Q iv boundary :=
  fun current other _ => fromCapture addresses ref program original saved current other

/-- The path is the actual terminal Pending history, truncated at every
scheduled coordinate. No caller-supplied list of restoration links is used. -/
def packetAt (final : EnteredPacket p Q iv boundary)
    (q : Coordinate (ParameterBounds.config p)) : EnteredPacket p Q iv boundary :=
  if earlier : position q < position final.2.coord then final.predecessor ⟨q,earlier⟩ else final

abbrev packets (final : EnteredPacket p Q iv boundary) : List (EnteredPacket p Q iv boundary) :=
  (schedule (ParameterBounds.config p)).map (packetAt final)

theorem packetAt_coord (final : EnteredPacket p Q iv boundary)
    (terminal : final.2.coord = lastCoordinate (ParameterBounds.config p))
    (q : Coordinate (ParameterBounds.config p)) : (packetAt final q).2.coord = q := by
  by_cases earlier : position q < position final.2.coord
  · have equal : packetAt final q = final.predecessor ⟨q,earlier⟩ := dite_eq_left earlier
    rw [equal]
    rfl
  · have equal : packetAt final q = final := dite_eq_right earlier
    rw [equal]
    apply CausalPrefix.position_injective
    have largest := lastCoordinate_max (ParameterBounds.config p) q
    rw [← terminal] at largest
    omega

theorem packetAt_entry (final : EnteredPacket p Q iv boundary)
    (q : Coordinate (ParameterBounds.config p)) : (packetAt final q).1 = final.1 := by
  by_cases earlier : position q < position final.2.coord
  · have equal : packetAt final q = final.predecessor ⟨q,earlier⟩ := dite_eq_left earlier
    rw [equal]
    rfl
  · have equal : packetAt final q = final := dite_eq_right earlier
    rw [equal]

theorem final_mem_packets (final : EnteredPacket p Q iv boundary) : final ∈ packets final := by
  apply List.mem_map.mpr
  refine ⟨final.2.coord,coordinate_mem_schedule _,?_⟩
  simp [packetAt]

theorem packets_entry (final current : EnteredPacket p Q iv boundary)
    (member : current ∈ packets final) : current.1 = final.1 := by
  obtain ⟨q,_,equal⟩ := List.mem_map.mp member
  rw [← equal]
  exact packetAt_entry final q

/-- Every strict source-history ancestor is literally another packet in the
constructed path. Its answer is already assigned in the same global table. -/
theorem predecessor_mem_packets (final current : EnteredPacket p Q iv boundary)
    (member : current ∈ packets final) (earlier : current.Earlier) :
    current.predecessor earlier ∈ packets final := by
  have source : current = final ∨ ∃ r : final.Earlier, current = final.predecessor r := by
    obtain ⟨q,_,equal⟩ := List.mem_map.mp member
    by_cases before : position q < position final.2.coord
    · exact Or.inr ⟨⟨q,before⟩,equal.symm.trans (dite_eq_left before)⟩
    · exact Or.inl (equal.symm.trans (dite_eq_right before))
  rcases source with rfl | ⟨r,rfl⟩
  · apply List.mem_map.mpr
    refine ⟨earlier.val,coordinate_mem_schedule _,?_⟩
    exact dite_eq_left earlier.property
  · have nested : position earlier.val < position final.2.coord := earlier.property.trans r.property
    rw [PCSBCSSourcePacketTape.predecessor_comp final r earlier]
    apply List.mem_map.mpr
    refine ⟨earlier.val,coordinate_mem_schedule _,?_⟩
    exact dite_eq_left nested

theorem packets_nonempty (final : EnteredPacket p Q iv boundary) : packets final ≠ [] := by
  intro empty
  have scheduleEmpty := List.map_eq_nil_iff.mp empty
  have member := coordinate_mem_schedule (.initial : Coordinate (ParameterBounds.config p))
  rw [scheduleEmpty] at member
  cases member

theorem packets_consecutive (final : EnteredPacket p Q iv boundary)
    (terminal : final.2.coord = lastCoordinate (ParameterBounds.config p))
    (i : Nat) (hi : i+1 < (packets final).length) :
    position ((packets final)[i+1]'hi).2.coord =
      position ((packets final)[i]'(by omega)).2.coord + 1 := by
  have bound : i+1 < depth (ParameterBounds.config p) := by simpa only [packets,List.length_map,depth] using hi
  have getAt (j : Nat) (hj : j < (packets final).length) :
      ((packets final)[j]'hj).2.coord =
        (schedule (ParameterBounds.config p))[j]'(by simpa only [packets,List.length_map] using hj) := by
    have equal : (packets final)[j]'hj = packetAt final
        ((schedule (ParameterBounds.config p))[j]'(by simpa only [packets,List.length_map] using hj)) :=
      List.getElem_map (packetAt final)
    rw [equal,packetAt_coord final terminal]
  rw [getAt (i+1) hi,getAt i (by omega)]
  exact (position_schedule_get (ParameterBounds.config p) ⟨i+1,bound⟩).trans
    (congrArg (fun n : Nat => n+1)
      (position_schedule_get (ParameterBounds.config p) ⟨i,by omega⟩)).symm

theorem packets_initial (final : EnteredPacket p Q iv boundary)
    (terminal : final.2.coord = lastCoordinate (ParameterBounds.config p))
    (current : EnteredPacket p Q iv boundary)
    (first : (packets final).head? = some current) : current.2.coord = .initial := by
  have initial := schedule_get_position (.initial : Coordinate (ParameterBounds.config p))
  simp only [position_initial] at initial
  have head : (schedule (ParameterBounds.config p)).head? = some .initial := by
    simpa only [List.head?_eq_getElem?] using initial
  simp only [packets,List.head?_map,head,Option.map_some,Option.some.injEq] at first
  rw [← first]
  exact packetAt_coord final terminal .initial

theorem lastCoordinate_position (c : Config) :
    position (lastCoordinate c) = depth c - 1 := by
  have positive : 0 < depth c := by
    simpa only [position_initial] using position_lt_depth (.initial : Coordinate c)
  let q := (schedule c)[depth c-1]'(by unfold depth at *; omega)
  have positionQ : position q = depth c-1 := position_schedule_get c ⟨depth c-1,by omega⟩
  have largest := lastCoordinate_max c q
  have inside := position_lt_depth (lastCoordinate c)
  omega

theorem packets_terminal (final : EnteredPacket p Q iv boundary)
    (terminal : final.2.coord = lastCoordinate (ParameterBounds.config p))
    (current : EnteredPacket p Q iv boundary)
    (last : (packets final).getLast? = some current) :
    current.2.coord = lastCoordinate (ParameterBounds.config p) := by
  simp only [packets,List.getLast?_map] at last
  obtain ⟨q,atLast,equal⟩ := Option.map_eq_some_iff.mp last
  rw [← equal,packetAt_coord final terminal]
  apply CausalPrefix.position_injective
  rw [lastCoordinate_position]
  rw [List.getLast?_eq_getElem?] at atLast
  obtain ⟨inside,stored⟩ := List.getElem?_eq_some_iff.mp atLast
  rw [← stored]
  exact position_schedule_get (ParameterBounds.config p)
    ⟨depth (ParameterBounds.config p)-1,inside⟩

/-- A decoded strict prefix agrees with the native trace exactly, including
array length. Future source responses cannot enter via a default get. -/
theorem replies_exact (current : Coordinate (ParameterBounds.config p))
    (saved : AnchoredHeaderCodec.Record) (registry : PCSBCSSourceFrozenAccessor.Captures)
    (messages : List Pending) (past : WHIRFiatShamir.Prefix current)
    (native : Array Reply) (parsed : Array Reply)
    (assembled : PCSBCSSourceFrozenReplies.replies current saved registry messages past = some parsed)
    (inverses : ∀ j, j < position current →
      (PCSBCSSourceFrozenAccessor.inverseAt current saved registry messages past j).map Inverted.reply = some native[j]!) :
    parsed = priorAnswers native (position current) := by
  apply Array.ext
  · rw [PCSBCSSourceFrozenReplies.replies_size current saved registry messages past parsed assembled]
    simp [priorAnswers]
  · intro j left right
    have earlier : j < position current := by
      rw [PCSBCSSourceFrozenReplies.replies_size current saved registry messages past parsed assembled] at left
      exact left
    have actual := PCSBCSSourceFrozenReplies.replies_index current saved registry messages past parsed assembled j earlier
    rw [inverses j earlier] at actual
    have equal : parsed[j]! = native[j]! := by
      rw [getElem!_def,← actual]
    have projected := priorAnswers_get native (position current) j earlier
    simpa only [getElem!_pos parsed j left,
      getElem!_pos (priorAnswers native (position current)) j right] using equal.trans projected.symm

/-- Strict incoming traces use only earlier literal packet answers. The current
whole packet is never read in these identities. -/
theorem incoming_exact (current : EnteredPacket p Q iv boundary) (table : Table Keys Answers)
    (ring : RingPCSGame.Prefix) (t : Tape (ParameterBounds.config p)) (native parsed : Array Reply)
    (answers : parsed = priorAnswers native (position current.2.coord))
    (raws : ∀ r : current.Earlier,
      PCSBCSSourcePacketTape.rawPrefix current (fun key => table key.val) r.val r.property = literalRaw ring t r.val) :
    incomingTrace (PCSBCSSourcePacketTape.ringPrefix current (fun key => table key.val))
      (PCSBCSSourcePacketTape.tape current (fun key => table key.val)) parsed current.2.coord =
        incomingTrace ring t native current.2.coord := by
  unfold incomingTrace
  congr 1
  · by_cases initial : current.2.coord = .initial
    · simp [initial]
    · have earlier : position (.initial : Coordinate (ParameterBounds.config p)) < position current.2.coord :=
        noninitial_positive current.2.coord initial
      have equal := congrArg Prod.fst (raws ⟨.initial,earlier⟩)
      simp only [PCSBCSSourcePacketTape.ringPrefix,PCSBCSSourcePacketTape.ringOfPrefix,
        dite_eq_left earlier,literalRaw] at equal ⊢
      simpa only [incomingTrace,ite_eq_right initial] using congrArg some equal
  · funext r
    by_cases earlier : position r < position current.2.coord
    · have sample := PCSBCSSourcePacketTape.get_table current table ⟨r,earlier⟩
      have raw := raws ⟨r,earlier⟩
      have projected : PCSBCSSourcePacketTape.project r (literalRaw ring t r) = get r t := by
        cases r <;> rfl
      rw [← PCSBCSSourcePacketTape.rawPrefix_table current table ⟨r,earlier⟩,raw,projected] at sample
      simp only [earlier,↓reduceIte,sample]
    · simp only [earlier,↓reduceIte]
  · rw [answers]
    apply Array.ext
    · simp [priorAnswers]
    · intro j left right
      have earlier : j < position current.2.coord := by simpa [priorAnswers] using left
      have outer := priorAnswers_get (priorAnswers native (position current.2.coord))
        (position current.2.coord) j earlier
      simpa only [getElem!_pos (priorAnswers (priorAnswers native (position current.2.coord))
        (position current.2.coord)) j left,
        getElem!_pos (priorAnswers native (position current.2.coord)) j right] using outer

/-- Successful actual capture assembly is the literal native incoming state,
not merely an equality of selected scalar fields. -/
theorem fromCapture_exact {R : Type} {n : Nat}
    (addresses : Keys → List Reference) (ref : Reference)
    (program : Sampling Keys Answers R n) (original : CallerInput p)
    (saved : AnchoredHeaderCodec.Record) (current : EnteredPacket p Q iv boundary)
    (table : Table Keys Answers) (frozen : Frozen)
    (root : capturedRegistry addresses program current (fun key => table key.val) ref = some frozen)
    (ring : RingPCSGame.Prefix) (t : Tape (ParameterBounds.config p)) (native : Array Reply)
    (raws : ∀ r : current.Earlier,
      PCSBCSSourcePacketTape.rawPrefix current (fun key => table key.val) r.val r.property = literalRaw ring t r.val)
    (inverses : ∀ j, j < position current.2.coord →
      (PCSBCSSourceFrozenAccessor.inverseAt current.2.coord saved
        (capturedRegistry addresses program current (fun key => table key.val)) current.2.messages
        (PCSBCSSourcePacketTape.strictPrefix current (fun key => table key.val)) j).map Inverted.reply = some native[j]!) :
    fromCapture addresses ref program original saved current (fun key => table key.val) =
      some (literalCallerData p original frozen.raw ring t native current.2.coord) := by
  obtain ⟨parsed,assembled⟩ := PCSBCSCapturedSourceTransport.replies_complete current.2.coord saved
    (capturedRegistry addresses program current (fun key => table key.val)) current.2.messages
    (PCSBCSSourcePacketTape.strictPrefix current (fun key => table key.val)) (by
      intro j earlier
      obtain ⟨reply,found,_⟩ := Option.map_eq_some_iff.mp (inverses j earlier)
      exact ⟨reply,found⟩)
  have exactAnswers := replies_exact current.2.coord saved
    (capturedRegistry addresses program current (fun key => table key.val)) current.2.messages
    (PCSBCSSourcePacketTape.strictPrefix current (fun key => table key.val)) native parsed assembled inverses
  have trace := incoming_exact current table ring t native parsed exactAnswers raws
  simp only [fromCapture,root,assembled]
  dsimp only [Bind.bind,Option.bind,Pure.pure]
  unfold literalCallerData incomingData
  rw [trace]

theorem node_after {R : Type} {n : Nat}
    (addresses : Keys → List Reference) (ref : Reference)
    (program : Sampling Keys Answers R n) (original : CallerInput p)
    (saved : AnchoredHeaderCodec.Record) (current : EnteredPacket p Q iv boundary)
    (table : Table Keys Answers) (root : BaseOracle)
    (ring : RingPCSGame.Prefix) (t : Tape (ParameterBounds.config p)) (native : Array Reply)
    (assembled : fromCapture addresses ref program original saved current (fun key => table key.val) =
      some (literalCallerData p original root ring t native current.2.coord))
    (raw : grouped current.2.coord (table (.inl current)) = literalRaw ring t current.2.coord) :
    after (Restoration.model p Q iv boundary (builder addresses ref program original saved))
      (.inl current) table = literalState p original root ring t native current.2.coord := by
  change (match fromCapture addresses ref program original saved current (fun key => table key.val) with
    | some caller => (callerCertificate p).after caller current.2.coord
        (grouped current.2.coord (table (.inl current)))
    | none => false) = _
  rw [assembled,raw]
  exact literal_after p original root ring t native current.2.coord

theorem node_before {R : Type} {n : Nat}
    (addresses : Keys → List Reference) (ref : Reference)
    (program : Sampling Keys Answers R n) (original : CallerInput p)
    (saved : AnchoredHeaderCodec.Record) (current : EnteredPacket p Q iv boundary)
    (table : Table Keys Answers) (root : BaseOracle)
    (ring : RingPCSGame.Prefix) (t : Tape (ParameterBounds.config p)) (native : Array Reply)
    (assembled : fromCapture addresses ref program original saved current (fun key => table key.val) =
      some (literalCallerData p original root ring t native current.2.coord))
    (different : current.2.coord ≠ .initial) :
    before (Restoration.model p Q iv boundary (builder addresses ref program original saved))
      (.inl current) table =
        literalState p original root ring t native
          (predecessor current.2.coord (noninitial_positive current.2.coord different)) := by
  have recovered : publicNode (Restoration.model p Q iv boundary
      (builder addresses ref program original saved)) (.inl current) table =
      some (literalCallerData p original root ring t native current.2.coord) := assembled
  unfold PCSStateRestoration.Latent.before
  rw [recovered]
  change (callerCertificate p).before
    (literalCallerData p original root ring t native current.2.coord) current.2.coord = _
  exact literal_before p original root ring t native current.2.coord different

theorem node_initial {R : Type} {n : Nat}
    (addresses : Keys → List Reference) (ref : Reference)
    (program : Sampling Keys Answers R n) (original : CallerInput p)
    (saved : AnchoredHeaderCodec.Record) (current : EnteredPacket p Q iv boundary)
    (table : Table Keys Answers) (root : BaseOracle)
    (ring : RingPCSGame.Prefix) (t : Tape (ParameterBounds.config p)) (native : Array Reply)
    (assembled : fromCapture addresses ref program original saved current (fun key => table key.val) =
      some (literalCallerData p original root ring t native current.2.coord))
    (initial : current.2.coord = .initial) :
    before (Restoration.model p Q iv boundary (builder addresses ref program original saved))
      (.inl current) table = false := by
  have recovered : publicNode (Restoration.model p Q iv boundary
      (builder addresses ref program original saved)) (.inl current) table =
      some (literalCallerData p original root ring t native current.2.coord) := assembled
  unfold PCSStateRestoration.Latent.before
  rw [recovered]
  change (callerCertificate p).before
    (literalCallerData p original root ring t native current.2.coord) current.2.coord = false
  rw [initial]
  rfl

/-- Neighbouring identities are proved from actual decoded snapshots and
literal consecutive coordinates. No before/after links are free premises. -/
theorem path_of_snapshots {R : Type} {n : Nat}
    (addresses : Keys → List Reference) (ref : Reference)
    (program : Sampling Keys Answers R n) (original : CallerInput p)
    (saved : AnchoredHeaderCodec.Record) (table : Table Keys Answers)
    (packets : List (EnteredPacket p Q iv boundary)) (exposed : List (Sigma Answers))
    (root : BaseOracle) (ring : RingPCSGame.Prefix) (t : Tape (ParameterBounds.config p))
    (native : Array Reply) (last : Bool)
    (recorded : ∀ current ∈ packets, (⟨.inl current,table (.inl current)⟩ : Sigma Answers) ∈ exposed)
    (assembled : ∀ current ∈ packets,
      fromCapture addresses ref program original saved current (fun key => table key.val) =
        some (literalCallerData p original root ring t native current.2.coord))
    (raws : ∀ current ∈ packets,
      grouped current.2.coord (table (.inl current)) = literalRaw ring t current.2.coord)
    (consecutive : ∀ i (hi : i+1 < packets.length),
      position (packets[i+1]'hi).2.coord = position (packets[i]'(by omega)).2.coord + 1)
    (initial : ∀ current, packets.head? = some current → current.2.coord = .initial)
    (terminal : ∀ current, packets.getLast? = some current →
      literalState p original root ring t native current.2.coord = last)
    (nonempty : packets ≠ []) :
    StatePath (Restoration.model p Q iv boundary (builder addresses ref program original saved))
      table exposed false last := by
  classical
  apply PCSBCSLiteralStatePath.of_round_links _ table exposed (packets.map Sum.inl) false last
  · intro key member
    obtain ⟨current,hcurrent,hkey⟩ := List.mem_map.mp member
    rw [← hkey]
    exact recorded current hcurrent
  · intro i hi
    have bound : i+1 < packets.length := by simpa only [List.length_map] using hi
    let first := packets[i]'(by omega)
    let second := packets[i+1]'bound
    have firstMem : first ∈ packets := List.getElem_mem _
    have secondMem : second ∈ packets := List.getElem_mem _
    have positions := consecutive i bound
    have different : second.2.coord ≠ .initial := by
      intro equal
      rw [equal,position_initial] at positions
      omega
    have predecessorSame : predecessor second.2.coord
        (noninitial_positive second.2.coord different) = first.2.coord := by
      apply CausalPrefix.position_injective
      rw [predecessor_position]
      change position second.2.coord = position first.2.coord + 1 at positions
      omega
    simp only [List.getElem_map]
    rw [node_after addresses ref program original saved first table root ring t native
      (assembled first firstMem) (raws first firstMem),
      node_before addresses ref program original saved second table root ring t native
      (assembled second secondMem) different,predecessorSame]
  · intro key head
    cases packets with
    | nil => simp at head
    | cons current rest =>
      simp only [List.map_cons,List.head?_cons,Option.some.injEq] at head
      subst key
      exact node_initial addresses ref program original saved current table root ring t native
        (assembled current (by simp)) (initial current rfl)
  · intro key final
    have mapped : (packets.map (Sum.inl : EnteredPacket p Q iv boundary → Keys)).getLast? =
        packets.getLast?.map Sum.inl := List.getLast?_map
    rw [mapped] at final
    obtain ⟨current,atLast,same⟩ := Option.map_eq_some_iff.mp final
    subst key
    have member : current ∈ packets := List.mem_of_getLast? atLast
    rw [node_after addresses ref program original saved current table root ring t native
      (assembled current member) (raws current member)]
    exact terminal current atLast
  · intro empty
    have noPackets : packets = [] := List.map_eq_nil_iff.mp empty
    exact (nonempty noPackets).elim

/-- The terminal Boolean is derived from actual native PCS experiment
acceptance and failure of the actual original-claims extractor. -/
theorem accepted_failure_path_of_snapshots {R : Type} {n : Nat}
    (addresses : Keys → List Reference) (ref : Reference)
    (program : Sampling Keys Answers R n) (original : CallerInput p)
    (saved : AnchoredHeaderCodec.Record) (table : Table Keys Answers)
    (packets : List (EnteredPacket p Q iv boundary)) (exposed : List (Sigma Answers))
    (root : BaseOracle) (ring : RingPCSGame.Prefix) (t : Tape (ParameterBounds.config p))
    (strategy : RingPCSGame.Prefix → Strategy)
    (recorded : ∀ current ∈ packets, (⟨.inl current,table (.inl current)⟩ : Sigma Answers) ∈ exposed)
    (assembled : ∀ current ∈ packets,
      fromCapture addresses ref program original saved current (fun key => table key.val) =
        some (literalCallerData p original root ring t
          (PCSRoundByRoundTranscriptState.replies
            (ExecutionShapes.Input p original.lanes root
              (OriginalClaimsChecker.input original.prepared root ring).claims) (strategy ring) t)
            current.2.coord))
    (raws : ∀ current ∈ packets,
      grouped current.2.coord (table (.inl current)) = literalRaw ring t current.2.coord)
    (consecutive : ∀ i (hi : i+1 < packets.length),
      position (packets[i+1]'hi).2.coord = position (packets[i]'(by omega)).2.coord + 1)
    (initial : ∀ current, packets.head? = some current → current.2.coord = .initial)
    (terminal : ∀ current, packets.getLast? = some current →
      current.2.coord = lastCoordinate (ParameterBounds.config p))
    (nonempty : packets ≠ [])
    (accepted : CausalGame.experiment (OriginalClaimsChecker.input original.prepared root ring)
      (strategy ring) t = true)
    (failure : ¬ ∃ w,
      PCSRoundByRoundKnowledge.extract p original.lanes original.family original.points
        original.anchorPoint original.anchorValue root = some w ∧
      PCSRewindSource.ExplainsOriginal (ParameterBounds.config p) original.lanes root
        original.family original.points original.anchorPoint original.anchorValue w) :
    StatePath (Restoration.model p Q iv boundary (builder addresses ref program original saved))
      table exposed false true := by
  apply path_of_snapshots addresses ref program original saved table packets exposed root ring t
    _ true recorded assembled raws consecutive initial _ nonempty
  intro current atLast
  rw [terminal current atLast]
  exact literal_accepted_extraction_failure_final p original.lanes original.family original.points
    original.anchorPoint original.anchorValue original.prepared root strategy original.familyCap
    original.claimCap ring t accepted failure

#print axioms replies_exact
#print axioms incoming_exact
#print axioms fromCapture_exact
#print axioms node_after
#print axioms node_before
#print axioms node_initial
#print axioms path_of_snapshots
#print axioms accepted_failure_path_of_snapshots
end Whir.PCSBCSCapturedSourceStatePath
