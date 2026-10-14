import Whir.PCSBCSNativeCapturedOracles
import Whir.PCSBCSNativePacketCodec
import Whir.AnchoredPhysicalPreparation

/-! Literal full-packet source answers and the actual terminal native tape.
The unused suffix of each full output block is retained in the table; only the
checked contiguous-byte decoder projects it to a challenge. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace Whir.PCSBCSNativeCapturedTape
open Concrete Protocol FiatShamirGame DuplexModeGame DuplexFraming
open PublicMerkleProgram WHIRSourceChronology WHIRPhysicalVerifier WHIRPhysicalReplay
open RawOracleCoupling.Concrete CausalProbability PCSBCSChallengeOracle
open PCSRoundByRoundTranscriptState AnchoredPhysicalDriver
open PCSBCSRestorationHazard

private theorem record_initial_eq {p : ParameterBounds.Profile} (a b : WireState p)
    (same : a.initial = b.initial) (q : Coordinate (ParameterBounds.config p))
    (x : StackWHIRReplay.Sample q) :
    (recordSample a q x).initial = (recordSample b q x).initial := by
  cases q <;> simp only [recordSample,same]

private theorem install_initial {p : ParameterBounds.Profile} (state : WireState p)
    (q : Coordinate (ParameterBounds.config p)) (x : StackWHIRReplay.Sample q)
    (first : q = .initial) :
    ∃ seed, (recordSample state q x).initial = some seed ∧
      literalRaw seed.1 (set q state.tape (StackWHIRReplay.projectSample q x)) q = x := by
  subst q
  exact ⟨x,rfl,by simp only [literalRaw,get_set]; rfl⟩

private theorem install_later {p : ParameterBounds.Profile} (state : WireState p)
    (seed : RingPCSGame.Prefix × E) (q : Coordinate (ParameterBounds.config p))
    (x : StackWHIRReplay.Sample q) (later : q ≠ .initial) :
    literalRaw seed.1 (set q state.tape (StackWHIRReplay.projectSample q x)) q = x := by
  cases q <;> simp_all only [ne_eq,not_true_eq_false,literalRaw,get_set,StackWHIRReplay.projectSample,id_eq]

private theorem literal_set_ne {c : Config} (seed : RingPCSGame.Prefix) (tape : CausalGame.Tape c)
    (q r : Coordinate c) (x : Sample q) (unequal : r ≠ q) :
    literalRaw seed (set q tape x) r = literalRaw seed tape r := by
  cases r <;> simp only [literalRaw,get_set_ne q _ tape x unequal]

private theorem ideal_construction {R Seed State : Type} {B : Nat}
    (sim : Simulator B Seed State) (ro : RawKey B → Digest32) (iv : Digest32)
    (state : State) (program : Program R) (remaining : Nat) (limit : remaining ≤ B)
    (counted : DuplexModeGame.Counts remaining program) :
    ∀ q valid answer, (⟨.construction q valid,answer⟩ : Observation) ∈
      (runIdeal sim ro iv state program remaining limit counted).view.observations →
      ∃ bounded : pathCost q ≤ B, answer = ro (constructionKey B iv q bounded) := by
  induction program generalizing state remaining with
  | done result => simp [runIdeal]
  | ask query next ih =>
    cases query with
    | primitive purpose input =>
      intro q valid answer member
      simp only [runIdeal,DuplexModeGame.prepend,List.mem_cons] at member
      rcases member with same | later
      · cases same
      · exact ih _ _ _ _ _ _ _ _ later
    | construction coordinate admitted =>
      intro q valid answer member
      simp only [runIdeal,DuplexModeGame.prepend,List.mem_cons] at member
      rcases member with same | later
      · cases same
        exact ⟨counted.1.trans limit,rfl⟩
      · exact ih _ _ _ _ _ _ _ _ later

private theorem readPacket_observed_aux {R : Type} {n : Nat} (request : Fin n → Query)
    (next : (Fin n → Digest32) → Program R) (observations : List Observation) (result : R)
    (run : Runs (WHIRModeProgram.readPacket n request next) observations result) :
    ∃ raw suffix, Runs (next raw) suffix result ∧
      ∀ b, (⟨request b,raw b⟩ : Observation) ∈ observations := by
  induction n generalizing observations with
  | zero => exact ⟨Fin.elim0,observations,run,fun b => Fin.elim0 b⟩
  | succ n ih =>
    simp only [WHIRModeProgram.readPacket] at run
    cases run with
    | ask first rest =>
      obtain ⟨raw,suffix,last,observed⟩ := ih _ _ _ rest
      refine ⟨Fin.cases first raw,suffix,last,?_⟩
      intro b
      refine Fin.cases ?_ (fun i => ?_) b
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (observed i)

private theorem readPacket_observed {n : Nat} (request : Fin n → Query)
    (raw : Fin n → Digest32) (observations : List Observation)
    (run : Runs (WHIRModeProgram.readPacket n request Program.done) observations raw) :
    ∀ b, (⟨request b,raw b⟩ : Observation) ∈ observations := by
  obtain ⟨value,suffix,last,observed⟩ := readPacket_observed_aux request Program.done observations raw run
  cases last
  exact observed

theorem readPackets_observed {cap : Nat} {R : Type}
    (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q : Nat)
    (p : ParameterBounds.Profile) (lanes : Nat) (proofs : Array MerkleTransport.PrunedMerklePaths)
    (packets : List (RawWHIRKeys.Packet ctx Q))
    (profiles : ∀ packet ∈ packets, packet.val.profile = p) (state : WireState p)
    (next : WireState p → List (Sigma (GroupAnswer ctx Q)) → Source cap (Option R))
    (observations : List Observation) (result : R)
    (run : Runs (erase (readPhysicalPackets ctx stack Q p lanes proofs none
      packets profiles state next)) observations (some result)) :
    ∃ final history suffix, Trace ctx stack Q p lanes proofs packets state final history ∧
      Runs (erase (next final history)) suffix (some result) ∧
      ∀ packet raw, (⟨.inl packet,raw⟩ : Sigma (GroupAnswer ctx Q)) ∈ history →
        ∀ b, (⟨WHIRModeFinal.request ctx Q packet b,raw b⟩ : Observation) ∈ observations := by
  induction packets generalizing state next observations with
  | nil => exact ⟨state,[],observations,.nil state,run,by simp⟩
  | cons packet packets ih =>
    simp only [readPhysicalPackets] at run
    cases parsed : absorbResponse state (packet.val.messages.headD ⟨[],none⟩) with
    | none => simp only [parsed,erase] at run; cases run
    | some value =>
      obtain ⟨absorbed,root⟩ := value
      simp only [parsed] at run
      split at run
      · rename_i guards
        rw [announce_erase,sourceLift_erase] at run
        obtain ⟨before,nonce,after,whole,_,continued⟩ := (Runs.bind_iff _ _).mp run
        cases boundNonce : afterNonce absorbed nonce with
        | none => simp only [boundNonce,erase] at continued; cases continued
        | some bound =>
          simp only [boundNonce] at continued
          split at continued
          · rename_i accepted
            rw [sourceLift_erase] at continued
            obtain ⟨beforeRaw,raw,afterRaw,rawWhole,readRaw,read⟩ := (Runs.bind_iff _ _).mp continued
            rw [sourceLift_erase] at read
            obtain ⟨beforeOpen,opened,afterOpen,openWhole,opening,rest⟩ := (Runs.bind_iff _ _).mp read
            cases opened with
            | none => cases rest
            | some checked =>
              obtain ⟨final,history,suffix,traced,last,observed⟩ := ih _ _ _ _ rest
              refine ⟨final,⟨.inl packet,raw⟩::history,suffix,
                .cons (profiles packet (by simp))
                  (.run parsed guards.1 guards.2 boundNonce accepted opening) traced,last,?_⟩
              intro current answer member b
              rcases List.mem_cons.mp member with same | older
              · cases same
                rw [whole,rawWhole]
                exact List.mem_append_right _ (List.mem_append_left _
                  (readPacket_observed _ _ _ (by rwa [readPacket_eq] at readRaw) b))
              · rw [whole,rawWhole,openWhole]
                exact List.mem_append_right _ (List.mem_append_right _
                  (List.mem_append_right _ (observed current answer older b)))
          · cases continued
      · cases run

private theorem step_fields {ctx : RawWHIRKeys.Context} {stack : ctx.mode = .stack} {Q : Nat}
    {p : ParameterBounds.Profile} {lanes : Nat} {proofs : Array MerkleTransport.PrunedMerklePaths}
    {packet : RawWHIRKeys.Packet ctx Q} {profile : packet.val.profile = p}
    {state out : WireState p} {raw : GroupAnswer ctx Q (.inl packet)}
    (step : Step ctx stack Q p lanes proofs packet profile state raw out) :
    out.tape = set (packetQuery ctx Q p packet profile) state.tape
      (StackWHIRReplay.projectSample _ (packetSample ctx stack Q p packet profile raw)) ∧
    out.initial = (recordSample state (packetQuery ctx Q p packet profile)
      (packetSample ctx stack Q p packet profile raw)).initial := by
  cases step with
  | run parsed size shape boundNonce accepted opened =>
    obtain ⟨_,absorbedTape,_,absorbedInitial⟩ := absorbResponse_rows _ _ _ _ parsed
    obtain ⟨nonceTape,_,_,_,nonceInitial⟩ := afterNonce_fields _ _ _ boundNonce
    obtain ⟨_,tape,_,initial,_,_⟩ := takeSample_fields _ _ _ _ _ _ _ opened
    constructor
    · dsimp only [withOutput]
      rw [tape,recordSample_tape,nonceTape,absorbedTape]
    · dsimp only [withOutput]
      rw [initial]
      exact record_initial_eq _ _ (nonceInitial.trans absorbedInitial) _ _

private theorem trace_packets {ctx : RawWHIRKeys.Context} {stack : ctx.mode = .stack} {Q : Nat}
    {p : ParameterBounds.Profile} {lanes : Nat} {proofs : Array MerkleTransport.PrunedMerklePaths}
    {packets : List (RawWHIRKeys.Packet ctx Q)} {state out : WireState p} {history}
    (trace : Trace ctx stack Q p lanes proofs packets state out history) :
    ∀ packet raw, (⟨.inl packet,raw⟩ : Sigma (GroupAnswer ctx Q)) ∈ history → packet ∈ packets := by
  induction trace with
  | nil => simp
  | cons profile step rest ih =>
    intro packet raw member
    rcases List.mem_cons.mp member with same | older
    · cases same; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih _ _ older)

private theorem chain_lengths {ctx : RawWHIRKeys.Context} {Q : Nat}
    {packet : RawWHIRKeys.Packet ctx Q} {packets : List (RawWHIRKeys.Packet ctx Q)}
    (chain : Chain ctx Q packet packets) :
    ∀ current ∈ packets, current.val.messages.length ≤ packet.val.messages.length := by
  induction chain with
  | initial packet single => simp
  | @next packet previous packets head prior messages statement profile ih =>
    intro current member
    rcases List.mem_append.mp member with older | same
    · have le := ih current older
      simp only [messages,List.length_cons]
      omega
    · have equal := List.mem_singleton.mp same
      subst current
      exact Nat.le_refl _

theorem trace_literals {ctx : RawWHIRKeys.Context} {stack : ctx.mode = .stack} {Q : Nat}
    {p : ParameterBounds.Profile} {lanes : Nat} {proofs : Array MerkleTransport.PrunedMerklePaths}
    {packet : RawWHIRKeys.Packet ctx Q} {packets : List (RawWHIRKeys.Packet ctx Q)}
    {out : WireState p} {history} (root : Digest32)
    (chain : Chain ctx Q packet packets)
    (trace : Trace ctx stack Q p lanes proofs packets (initialWireState p root) out history) :
    ∃ seed, out.initial = some seed ∧
      ∀ current raw (_member : (⟨.inl current,raw⟩ : Sigma (GroupAnswer ctx Q)) ∈ history)
        (profile : current.val.profile = p),
        literalRaw seed.1 out.tape (packetQuery ctx Q p current profile) =
          packetSample ctx stack Q p current profile raw := by
  induction chain generalizing out history with
  | initial packet single =>
    cases trace with
    | cons profile step rest =>
      cases rest
      have first := packetQuery_initial ctx Q p packet profile (by simp [single])
      obtain ⟨tape,initial⟩ := step_fields step
      obtain ⟨seed,seedState,sample⟩ := install_initial _ _ _ first
      refine ⟨seed,initial.trans seedState,?_⟩
      intro current raw member aligned
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      cases member
      rw [tape]
      exact sample
  | @next packet previous packets head prior messages statement profile ih =>
    obtain ⟨middle,before,after,hist,first,last⟩ := Trace.append_inv _ _ trace
    cases last with
    | cons aligned step rest =>
      cases rest
      obtain ⟨seed,seedState,literals⟩ := ih first
      have later : packetQuery ctx Q p packet aligned ≠ .initial := by
        intro zero
        have pos := packetQuery_position ctx Q p packet aligned
        rw [zero] at pos
        have positive := List.length_pos_iff.mpr previous.property.2.1
        simp only [messages,List.length_cons] at pos
        simp [position,visibleCoordinates] at pos
        omega
      obtain ⟨tape,initial⟩ := step_fields step
      have seedOut : out.initial = some seed := by
        rw [initial,recordSample_noninitial _ _ _ later,seedState]
      refine ⟨seed,seedOut,?_⟩
      intro current raw member currentProfile
      rw [hist] at member
      rcases List.mem_append.mp member with older | same
      · have length := chain_lengths prior current (trace_packets first current raw older)
        have unequal : packetQuery ctx Q p current currentProfile ≠ packetQuery ctx Q p packet aligned := by
          intro equal
          have eqpos := congrArg position equal
          rw [packetQuery_position,packetQuery_position,messages,List.length_cons] at eqpos
          have positive := List.length_pos_iff.mpr current.property.2.1
          omega
        have unchanged : literalRaw seed.1 out.tape (packetQuery ctx Q p current currentProfile) =
            literalRaw seed.1 middle.tape (packetQuery ctx Q p current currentProfile) := by
          rw [tape]
          exact literal_set_ne _ _ _ _ _ unequal
        exact unchanged.trans (literals current raw older currentProfile)
      · simp only [List.mem_singleton] at same
        cases same
        rw [tape]
        exact install_later _ seed _ _ later

theorem trace_answers {ctx : RawWHIRKeys.Context} {stack : ctx.mode = .stack} {Q : Nat}
    {p : ParameterBounds.Profile} {lanes : Nat} {proofs : Array MerkleTransport.PrunedMerklePaths}
    {packets : List (RawWHIRKeys.Packet ctx Q)} {state out : WireState p} {history}
    (trace : Trace ctx stack Q p lanes proofs packets state out history) :
    ∀ packet ∈ packets, ∃ raw, (⟨.inl packet,raw⟩ : Sigma (GroupAnswer ctx Q)) ∈ history := by
  induction trace with
  | nil => simp
  | cons profile step rest ih =>
    intro packet member
    rcases List.mem_cons.mp member with same | older
    · subst packet
      exact ⟨_,List.mem_cons_self⟩
    · obtain ⟨raw,member⟩ := ih packet older
      exact ⟨raw,List.mem_cons_of_mem _ member⟩

theorem completion_data {ctx : RawWHIRKeys.Context} {Q B : Nat}
    (a : RawWHIRKeys.Packet ctx Q) (b : RawWHIRKeys.Packet ctx B) (same : a.val = b.val) :
    (completion ctx Q a).map Subtype.val = (completion ctx B b).map Subtype.val := by
  simp only [completion,RawWHIRKeys.ancestors,List.map_append,List.map_singleton,List.map_ofFn]
  simp only [RawWHIRKeys.dropPacket,same]
  simp only [Function.comp_apply,Fin.val_cast]
  rfl

theorem entered_ext {p : ParameterBounds.Profile} {B : Nat} {iv : Digest32} {boundary : Nat}
    (a b : EnteredPacket p B iv boundary) (entry : a.1.val = b.1.val)
    (messages : a.2.messages = b.2.messages) : a = b := by
  have equal : a.1 = b.1 := Subtype.ext entry
  cases a
  cases b
  cases equal
  have equal := CanonicalPacket.messages_injective messages
  cases equal
  rfl

theorem entered_query (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack)
    (Q B : Nat) (packet : RawWHIRKeys.Packet ctx Q)
    (bounded : pathCost (RawWHIRKeys.coordinate ctx packet.val 0) ≤ B)
    {p : ParameterBounds.Profile} {entry : FramedHistory}
    (profile : packet.val.profile = p) (aligned : RawWHIRKeys.entry ctx packet.val = entry) :
    packetQuery ctx Q p packet profile =
      (PCSBCSNativePacketBridge.enteredPacketAt ctx stack B
        (PCSBCSNativePacketVisit.packetAtBound ctx Q B packet bounded) profile aligned).2.coord := by
  cases profile
  cases aligned
  rfl

theorem literal_cast {c : Config} (seed : RingPCSGame.Prefix) (tape : CausalGame.Tape c)
    (q r : Coordinate c) (same : q = r) :
    Eq.mp (congrArg PCSBCSRounds.Raw same) (literalRaw seed tape q) = literalRaw seed tape r := by
  cases same
  rfl

theorem observed_grouped (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack)
    (Q B : Nat) (packet : RawWHIRKeys.Packet ctx Q)
    (bounded : pathCost (RawWHIRKeys.coordinate ctx packet.val 0) ≤ B)
    {p : ParameterBounds.Profile} {entry : FramedHistory}
    (profile : packet.val.profile = p) (aligned : RawWHIRKeys.entry ctx packet.val = entry)
    (seed : DuplexPublicSimulator.Seed) (ro : RawKey B → Digest32)
    (raw : GroupAnswer ctx Q (.inl packet))
    (answers : ∀ b : Fin (RawWHIRKeys.blocks ctx packet.val),
      ∃ bound : pathCost (RawWHIRKeys.coordinate ctx packet.val b.val) ≤ B,
      raw b = ro (constructionKey B ctx.iv (RawWHIRKeys.coordinate ctx packet.val b.val) bound)) :
    let current := PCSBCSNativePacketBridge.enteredPacketAt ctx stack B
      (PCSBCSNativePacketVisit.packetAtBound ctx Q B packet bounded) profile aligned
    grouped current.2.coord
      ((EnteredPacket.partition (p := p) (Q := B) (iv := ctx.iv) (boundary := entry.frames.length)).split
        (PublicCompressionCouplingMixed.oracle seed ro) (.inl current)) =
      Eq.mp (congrArg PCSBCSRounds.Raw (entered_query ctx stack Q B packet bounded profile aligned))
        (packetSample ctx stack Q p packet profile raw) := by
  cases profile
  cases aligned
  let packetB := PCSBCSNativePacketVisit.packetAtBound ctx Q B packet bounded
  let rawB : GroupAnswer ctx B (.inl packetB) := raw
  have full :
      (EnteredPacket.partition (p := packet.val.profile) (Q := B) (iv := ctx.iv)
        (boundary := (RawWHIRKeys.entry ctx packet.val).frames.length)).split
        (PublicCompressionCouplingMixed.oracle seed ro)
        (.inl (PCSBCSNativePacketBridge.enteredPacket ctx stack B packetB)) =
      PCSBCSNativePacketCodec.nativeFullBlocksEquiv ctx stack B packetB rawB := by
    funext b
    change ro ((PCSBCSNativePacketBridge.sourcePacket ctx stack B packetB).key b) = _
    rw [PCSBCSNativePacketBridge.sourcePacket_key,PCSBCSNativePacketCodec.nativeFullBlocksEquiv_apply]
    obtain ⟨bound,equal⟩ := answers ⟨b.val,by
      change b.val < RawWHIRKeys.blocks ctx packetB.val
      rw [PCSBCSNativePacketBridge.packet_blocks_pcs ctx stack B packetB]
      exact b.isLt⟩
    exact equal.symm
  change grouped (PCSBCSNativePacketBridge.query ctx B packetB)
    ((EnteredPacket.partition (p := packet.val.profile) (Q := B) (iv := ctx.iv)
      (boundary := (RawWHIRKeys.entry ctx packet.val).frames.length)).split
      (PublicCompressionCouplingMixed.oracle seed ro)
      (.inl (PCSBCSNativePacketBridge.enteredPacket ctx stack B packetB))) =
    WHIRRawReplay.decodePacket ctx stack B packetB rawB
  rw [full,PCSBCSNativePacketCodec.decodePacket_eq_grouped]

theorem done_eq {R : Type} {left right : R} {trace : List Observation}
    (run : Runs (.done left) trace right) : left = right := by
  cases run
  rfl

section Driver
variable (cap : Nat) (model : WHIRCallerSupport.ProductionLayout)
    (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q : Nat)
    (packet : RawWHIRKeys.Packet ctx Q) (saved : AnchoredHeaderCodec.Record)
    (proofs : Array MerkleTransport.PrunedMerklePaths) (B : Nat)
    (limit : sourceBudget ctx Q packet ≤ B)
    (seed : DuplexPublicSimulator.Seed) (ro : RawKey B → Digest32)

/-- Actual source acceptance forces full native schedule length, including the
hidden terminal sample. No terminal coordinate or tape geometry is assumed. -/
theorem mixed_success_depth (a : Accepted ctx Q cap packet saved)
    (success : (AnchoredMixedIdealSourceAcceptance.mixedView cap .fresh model ctx stack Q packet saved proofs
      ctx.iv B limit seed ro).result.value = some a) :
    packet.val.messages.length = WHIRHistory.depth (ParameterBounds.config packet.val.profile) := by
  obtain ⟨run,_,_⟩ := AnchoredMixedIdealSourceAcceptance.mixedView_runs cap .fresh model ctx stack Q packet
    saved proofs ctx.iv B limit seed ro
  rw [success] at run
  obtain ⟨_,_,_,trace,_⟩ := AnchoredPhysicalExecution.verifySource_execution cap .fresh model ctx stack Q packet
    saved proofs _ a run
  exact AnchoredPhysicalPreparation.accepted_completed_depth a
    (trace_completed saved.root (completion_chain ctx Q packet) trace)

/-- Every whole packet is decoded from its actual independent raw construction
answers. This source fact needs no Merkle quietness or replay certificate. -/
theorem mixed_success_literal_packets (a : Accepted ctx Q cap packet saved)
    (success : (AnchoredMixedIdealSourceAcceptance.mixedView cap .fresh model ctx stack Q packet saved proofs
      ctx.iv B limit seed ro).result.value = some a) :
    ∃ initial, a.wire.initial = some initial ∧
      ∀ current (member : current ∈ completion ctx Q packet),
        ∃ bounded : pathCost (RawWHIRKeys.coordinate ctx current.val 0) ≤ B,
          let entered := PCSBCSNativePacketBridge.enteredPacketAt ctx stack B
            (PCSBCSNativePacketVisit.packetAtBound ctx Q B current bounded)
            (completion_profiles ctx Q packet current member)
            (PCSBCSNativePacketBridge.completion_entries ctx Q packet current member)
          grouped entered.2.coord (PCSBCSCapturedIdealNativeAcceptance.table ctx Q packet B seed ro (.inl entered)) =
            literalRaw initial.1 a.wire.tape entered.2.coord := by
  let view := AnchoredMixedIdealSourceAcceptance.mixedView cap .fresh model ctx stack Q packet saved proofs
    ctx.iv B limit seed ro
  obtain ⟨run,_,_⟩ := AnchoredMixedIdealSourceAcceptance.mixedView_runs cap .fresh model ctx stack Q packet
    saved proofs ctx.iv B limit seed ro
  rw [success] at run
  obtain ⟨configured,same,before,after,request,whole,count,queries,parsed,physical⟩ :=
    AnchoredPhysicalExecution.verifySource_success cap .fresh model ctx stack Q packet saved proofs _ a run
  obtain ⟨final,history,suffix,trace,last,observed⟩ := readPackets_observed ctx stack Q packet.val.profile
    saved.shape.lanes proofs _ _ _ _ after a physical
  obtain ⟨_,wireEq,historyEq⟩ := AnchoredPhysicalExecution.finish_success ctx Q cap packet saved configured
    request final history _ a (done_eq last)
  have trace' : Trace ctx stack Q packet.val.profile saved.shape.lanes proofs (completion ctx Q packet)
      (initialWireState packet.val.profile saved.root) a.wire a.history := by
    simpa only [← wireEq,← historyEq] using trace
  obtain ⟨initial,initialState,literals⟩ := trace_literals saved.root (completion_chain ctx Q packet) trace'
  refine ⟨initial,initialState,?_⟩
  intro current member
  obtain ⟨raw,inHistory⟩ := trace_answers trace current member
  have actual : ∀ b, (⟨WHIRModeFinal.request ctx Q current b,raw b⟩ : Observation) ∈ view.observations := by
    intro b
    rw [whole]
    exact List.mem_append_right _ (observed current raw inHistory b)
  have answers : ∀ b : Fin (RawWHIRKeys.blocks ctx current.val),
      ∃ bound : pathCost (RawWHIRKeys.coordinate ctx current.val b.val) ≤ B,
      raw b = ro (constructionKey B ctx.iv (RawWHIRKeys.coordinate ctx current.val b.val) bound) := by
    intro b
    have answer := ideal_construction (DuplexPublicSimulator.simulator B) ro ctx.iv ⟨seed,[]⟩
      (WHIRSourceChronology.compile (AnchoredPhysicalDriver.verifySource cap .fresh model ctx stack Q packet saved proofs))
      (sourceBudget ctx Q packet) limit
      ((WHIRSourceChronology.compile_counted _ _).mpr
        (AnchoredPhysicalDriver.verifySource_counted cap .fresh model ctx stack Q packet saved proofs))
      _ _ (raw b) (by
        simpa only [view,AnchoredMixedIdealSourceAcceptance.mixedView,PublicCompressionCouplingMixed.compile_actual,
          WHIRModeFinal.request]
          using actual b)
    exact answer
  obtain ⟨bounded,recorded⟩ := PCSBCSNativePacketVisit.mixed_success_recorded cap model ctx stack Q packet
    saved proofs B limit seed ro a success current member
  refine ⟨bounded,?_⟩
  have groupedEq := observed_grouped ctx stack Q B current bounded
    (completion_profiles ctx Q packet current member)
    (PCSBCSNativePacketBridge.completion_entries ctx Q packet current member) seed ro raw answers
  have literal := literals current raw (by simpa only [← historyEq] using inHistory)
    (completion_profiles ctx Q packet current member)
  have lifted := congrArg
    (Eq.mp (congrArg PCSBCSRounds.Raw (entered_query ctx stack Q B current bounded
      (completion_profiles ctx Q packet current member)
      (PCSBCSNativePacketBridge.completion_entries ctx Q packet current member)))) literal
  have castEq := literal_cast initial.1 a.wire.tape _ _
    (entered_query ctx stack Q B current bounded
      (completion_profiles ctx Q packet current member)
      (PCSBCSNativePacketBridge.completion_entries ctx Q packet current member))
  exact groupedEq.trans (lifted.symm.trans castEq)

/-- Exact chronological completion, recorded whole packets, and literal raw
challenges, all derived from the fresh source run at its observed aggregate cap. -/
theorem mixed_success_tape (a : Accepted ctx Q cap packet saved)
    (success : (AnchoredMixedIdealSourceAcceptance.mixedView cap .fresh model ctx stack Q packet saved proofs
      ctx.iv B limit seed ro).result.value = some a) :
    ∃ initial : RingPCSGame.Prefix × E, ∃ bounded : pathCost (RawWHIRKeys.coordinate ctx packet.val 0) ≤ B,
      let packetB := PCSBCSNativePacketVisit.packetAtBound ctx Q B packet bounded
      let final := PCSBCSNativePacketBridge.enteredPacket ctx stack B packetB
      a.wire.initial = some initial ∧
      packet.val.messages.length = WHIRHistory.depth (ParameterBounds.config packet.val.profile) ∧
      final.2.coord = lastCoordinate (ParameterBounds.config packet.val.profile) ∧
      PCSBCSNativePacketBridge.completionPackets ctx stack B packetB =
        PCSBCSCapturedSourceStatePath.packets final ∧
      (∀ current ∈ PCSBCSCapturedSourceStatePath.packets final,
        (⟨.inl current,PCSBCSCapturedIdealNativeAcceptance.table ctx Q packet B seed ro (.inl current)⟩ :
          Sigma PCSBCSSourceRootCapture.Answer) ∈
          (TypedOracleCompiler.Sampling.execute (PCSBCSCapturedIdealNativeAcceptance.table ctx Q packet B seed ro)
            (PCSBCSCapturedIdealNativeAcceptance.allocationProgram cap model ctx stack Q packet saved proofs B limit)).2) ∧
      (∀ current ∈ PCSBCSCapturedSourceStatePath.packets final,
        grouped current.2.coord (PCSBCSCapturedIdealNativeAcceptance.table ctx Q packet B seed ro (.inl current)) =
          literalRaw initial.1 a.wire.tape current.2.coord) := by
  classical
  obtain ⟨initial,initialState,literals⟩ := mixed_success_literal_packets cap model ctx stack Q packet
    saved proofs B limit seed ro a success
  have self : packet ∈ completion ctx Q packet := List.mem_append_right _ (List.mem_singleton_self _)
  obtain ⟨bounded,_⟩ := PCSBCSNativePacketVisit.mixed_success_recorded cap model ctx stack Q packet saved
    proofs B limit seed ro a success packet self
  let packetB := PCSBCSNativePacketVisit.packetAtBound ctx Q B packet bounded
  let final := PCSBCSNativePacketBridge.enteredPacket ctx stack B packetB
  have depth := mixed_success_depth cap model ctx stack Q packet saved proofs B limit seed ro a success
  have ordering := PCSBCSNativePacketBridge.completionPackets_eq_of_length ctx stack B packetB depth
  have packetMember : ∀ current ∈ PCSBCSCapturedSourceStatePath.packets final,
      ∃ native, ∃ member : native ∈ completion ctx Q packet,
        ∃ bound : pathCost (RawWHIRKeys.coordinate ctx native.val 0) ≤ B,
          current = PCSBCSNativePacketBridge.enteredPacketAt ctx stack B
            (PCSBCSNativePacketVisit.packetAtBound ctx Q B native bound)
            (completion_profiles ctx Q packet native member)
            (PCSBCSNativePacketBridge.completion_entries ctx Q packet native member) := by
    intro current member
    rw [← ordering] at member
    obtain ⟨attached,_,equal⟩ := List.mem_map.mp member
    have nativeMember : attached.val.val ∈ (completion ctx Q packet).map Subtype.val := by
      rw [completion_data packet packetB rfl]
      exact List.mem_map.mpr ⟨attached.val,attached.property,rfl⟩
    obtain ⟨native,member,same⟩ := List.mem_map.mp nativeMember
    obtain ⟨bound,_⟩ := PCSBCSNativePacketVisit.mixed_success_recorded cap model ctx stack Q packet saved
      proofs B limit seed ro a success native member
    refine ⟨native,member,bound,?_⟩
    rw [← equal]
    apply entered_ext
    · rw [PCSBCSNativePacketBridge.enteredPacketAt_entry,PCSBCSNativePacketBridge.enteredPacketAt_entry]
      rfl
    · rw [PCSBCSNativePacketBridge.enteredPacketAt_messages,PCSBCSNativePacketBridge.enteredPacketAt_messages]
      exact congrArg RawWHIRKeys.PacketData.messages same.symm
  refine ⟨initial,bounded,initialState,depth,
    PCSBCSNativePacketBridge.query_eq_last_of_length ctx B packetB depth,ordering,?_,?_⟩
  · intro current member
    obtain ⟨native,nativeMem,bound,equal⟩ := packetMember current member
    subst current
    obtain ⟨bound',recorded⟩ := PCSBCSNativePacketVisit.mixed_success_recorded cap model ctx stack Q packet saved
      proofs B limit seed ro a success native nativeMem
    exact recorded
  · intro current member
    obtain ⟨native,nativeMem,bound,equal⟩ := packetMember current member
    subst current
    obtain ⟨bound',raw⟩ := literals native nativeMem
    exact raw

/-- The same actual Γ and full tape as the canonically restored causal replay.
Only actual-opening primitive bad-event exclusion is used for that replay;
the raw-table identity and terminal geometry were independently source-derived. -/
theorem mixed_success_experiment_tape (a : Accepted ctx Q cap packet saved) (familyCap : cap ≤ 2^64)
    (success : (AnchoredMixedIdealSourceAcceptance.mixedView cap .fresh model ctx stack Q packet saved proofs
      ctx.iv B limit seed ro).result.value = some a)
    (quiet : ∀ opening ∈ a.wire.openings,
      ¬ PublicMerkleBinding.OpenPrimitiveBad seed
        (PCSBCSNativeCapturedRows.openingLog cap model ctx stack Q packet saved proofs B limit seed ro opening)
        opening.root opening.result.paths) :
    ∃ replay : StackWHIRReplay.Replay packet.val.profile cap, ∃ proof,
      ∃ bounded : pathCost (RawWHIRKeys.coordinate ctx packet.val 0) ≤ B,
      let packetB := PCSBCSNativePacketVisit.packetAtBound ctx Q B packet bounded
      let final := PCSBCSNativePacketBridge.enteredPacket ctx stack B packetB
      replay.original = PCSBCSNativeOracleReplay.original a
        (PCSBCSNativeCapturedOracles.base cap model ctx stack Q packet saved proofs B limit seed ro) ∧
      a.wire.initial = some replay.initial ∧ a.wire.tape.1 = replay.initial.2 ∧
      replay.whir.replies.map WHIRPhysicalErasure.eraseReply = a.wire.replies ∧
      CausalGame.opening (ParameterBounds.config packet.val.profile)
        (CausalGame.challenges (ParameterBounds.config packet.val.profile) a.wire.tape)
        replay.whir.replies = .ok proof ∧
      WHIRPhysicalHistory.decodeStack packet.val.profile cap
        (fun _ => some (PCSBCSNativeOracleReplay.original a
          (PCSBCSNativeCapturedOracles.base cap model ctx stack Q packet saved proofs B limit seed ro)))
        (PCSBCSNativeCapturedOracles.roots cap model ctx stack Q packet saved proofs B limit seed ro)
        (fun i => a.wire.rows[i]!)
        ⟨packet.val.statement,packet.val.messages,(localHistory ctx stack Q packet.val.profile a.history).tail⟩ =
        some replay ∧
      CausalGame.experiment (PCSBCSNativeOracleReplay.input a
        (PCSBCSNativeCapturedOracles.base cap model ctx stack Q packet saved proofs B limit seed ro) replay.initial.1)
        (CausalStrategy.indexedStrategy replay.whir.replies) a.wire.tape = true ∧
      packet.val.messages.length = WHIRHistory.depth (ParameterBounds.config packet.val.profile) ∧
      final.2.coord = lastCoordinate (ParameterBounds.config packet.val.profile) ∧
      PCSBCSNativePacketBridge.completionPackets ctx stack B packetB =
        PCSBCSCapturedSourceStatePath.packets final ∧
      (∀ current ∈ PCSBCSCapturedSourceStatePath.packets final,
        (⟨.inl current,PCSBCSCapturedIdealNativeAcceptance.table ctx Q packet B seed ro (.inl current)⟩ :
          Sigma PCSBCSSourceRootCapture.Answer) ∈
          (TypedOracleCompiler.Sampling.execute (PCSBCSCapturedIdealNativeAcceptance.table ctx Q packet B seed ro)
            (PCSBCSCapturedIdealNativeAcceptance.allocationProgram cap model ctx stack Q packet saved proofs B limit)).2) ∧
      (∀ current ∈ PCSBCSCapturedSourceStatePath.packets final,
        grouped current.2.coord (PCSBCSCapturedIdealNativeAcceptance.table ctx Q packet B seed ro (.inl current)) =
          literalRaw replay.initial.1 a.wire.tape current.2.coord) := by
  obtain ⟨replay,proof,original,initial,lambda,replies,parsed,decoded,accepted⟩ :=
    PCSBCSNativeCapturedOracles.mixed_success_experiment cap model ctx stack Q packet saved proofs B limit
      seed ro a familyCap success quiet
  obtain ⟨sourceInitial,bounded,sourceSeed,depth,terminal,ordering,recorded,raws⟩ :=
    mixed_success_tape cap model ctx stack Q packet saved proofs B limit seed ro a success
  have same : sourceInitial = replay.initial := Option.some.inj (sourceSeed.symm.trans initial)
  subst sourceInitial
  exact ⟨replay,proof,bounded,original,initial,lambda,replies,parsed,decoded,accepted,depth,terminal,ordering,recorded,raws⟩

end Driver
#print axioms mixed_success_depth
#print axioms mixed_success_literal_packets
#print axioms mixed_success_tape
#print axioms mixed_success_experiment_tape


end Whir.PCSBCSNativeCapturedTape
