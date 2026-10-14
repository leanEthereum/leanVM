import Whir.PCSBCSNativeCapturedReplyTransport
import Whir.PCSBCSWholeNativePacketCoverage
import Whir.PCSBCSNativeCompleteAlarm
import Whir.PCSBCSNativePhysicalFreeze

/-! Whole historical first-address captures. Every getter below uses the actual
allocation program, retaining arbitrary earlier ordinary and construction asks.
Native replay and strict reply transport use this same capture, not a fresh
verifier cache. Per-opening exclusions are low-level mixed-experiment premises;
the complete-alarm module discharges them for the actual real execution. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
namespace Whir.PCSBCSWholeNativeCaptureTransport
open Concrete Protocol FiatShamirGame DuplexModeGame TypedOracleCompiler
open MerkleTransport MerkleTransport.Commitments PublicMerkleLog
open WHIRPhysicalVerifier WHIRPhysicalReplay AnchoredPhysicalDriver
open PCSBCSSourceRootReferences PCSBCSMerkleRootCache
open PCSBCSCapturedNativeReplyBridge PCSBCSCapturedNativePhaseQuery
open PCSBCSSourceFrozenAccessor PCSBCSFrozenOracleRows
open PCSBCSNativeCapturedReplyTransport
open PCSBCSCapturedSourceAcceptance

section Capture
variable {ctx : RawWHIRKeys.Context} {stack : ctx.mode = .stack} {Q cap : Nat}
    (packet : RawWHIRKeys.Packet ctx Q) (saved : AnchoredHeaderCodec.Record)
    {B boundary : Nat} {R : Type} {count : Nat}
    (program : Sampling
      (PCSBCSSourceRootCapture.Key (p := packet.val.profile) (Q := B) (iv := ctx.iv) (boundary := boundary))
      PCSBCSSourceRootCapture.Answer R count)
    (seed : PrimitiveOracle) (ro : RawKey B → Digest32)

noncomputable abbrev addresses :=
  PCSBCSCapturedSourceTransport.address (p := packet.val.profile) (Q := B) (iv := ctx.iv)
    (boundary := boundary)
noncomputable abbrev table :=
  (PCSBCSChallengeOracle.EnteredPacket.partition (p := packet.val.profile) (Q := B)
    (iv := ctx.iv) (boundary := boundary)).split (PublicCompressionCouplingMixed.oracle seed ro)
noncomputable def referenceLog (ref : Reference) : PublicLog :=
  sourceLog (addresses packet) ref program (table packet seed ro)
noncomputable def openingLog (opening : QueryOpening packet.val.profile) : PublicLog :=
  referenceLog packet program seed ro (PCSBCSNativeRootRoles.openingRole saved opening)
noncomputable def logFor (root : Digest32) (level : Nat) : PublicLog :=
  referenceLog packet program seed ro ⟨root,PCSBCSNativeRootRoles.nativeShape packet.val.profile saved level⟩

noncomputable def base : CausalGame.BaseOracle :=
  WHIRPhysicalRows.compactBaseOracle (hash seed)
    ⟨recordDomain (records (logFor packet saved program seed ro saved.root 0)),[]⟩
    saved.root (ParameterBounds.length (ParameterBounds.config packet.val.profile) 0).log2
    (ParameterBounds.length (ParameterBounds.config packet.val.profile) 0)
    (leafWords packet.val.profile 0) saved.shape.lanes

noncomputable def roots : WHIRReplay.Roots := fun root level =>
  frozenQueryOracle (hash seed)
    ⟨recordDomain (records (logFor packet saved program seed ro root level)),[]⟩
    root packet.val.profile level (2^(ParameterBounds.config packet.val.profile).folds[0]!)

theorem roots_rectangular (root : Digest32) (level : Nat) :
    oracleValid (roots packet saved program seed ro root level)
      (ParameterBounds.length (ParameterBounds.config packet.val.profile) level)
      (2^(ParameterBounds.config packet.val.profile).folds[level]!) = true := by
  have shape := frozenQueryOracle_valid (hash seed)
    ⟨recordDomain (records (logFor packet saved program seed ro root level)),[]⟩
    root packet.val.profile level (2^(ParameterBounds.config packet.val.profile).folds[0]!) (by rfl)
  by_cases zero : level = 0
  · simpa only [roots,zero,ite_true] using shape
  · simpa only [roots,ite_eq_right zero] using shape

theorem base_valid (fits : saved.shape.lanes ≤ 2^(ParameterBounds.config packet.val.profile).folds[0]!) :
    oracleValid (CausalGame.liftRoot (base packet saved program seed ro))
      (2^((ParameterBounds.config packet.val.profile).logN-(ParameterBounds.config packet.val.profile).folds[0]!+
        (ParameterBounds.config packet.val.profile).rates[0]!)) saved.shape.lanes = true := by
  have shape := WHIRPhysicalVerifier.compactBaseOracle_valid (hash seed)
    ⟨recordDomain (records (logFor packet saved program seed ro saved.root 0)),[]⟩
    saved.root (ParameterBounds.length (ParameterBounds.config packet.val.profile) 0).log2
    (ParameterBounds.length (ParameterBounds.config packet.val.profile) 0)
    (2^(ParameterBounds.config packet.val.profile).folds[0]!) saved.shape.lanes fits
  simpa only [base,leafWords,ite_true,ParameterBounds.length,
    PCSBCSNativeRootRoles.production_initial_remaining] using shape

theorem opening_log (opening : QueryOpening packet.val.profile) :
    openingLog packet saved program seed ro opening =
      logFor packet saved program seed ro opening.root opening.level.val := rfl

theorem referenceLog_authentic (ref : Reference) :
    AuthenticLog seed (referenceLog packet program seed ro ref) :=
  PCSBCSMerkleSeedProjection.sourceLog_authentic seed ro (addresses packet) ref program


/-- Every selected native row binds to its actual whole first-mention log. -/
theorem native_boundRows (model : WHIRCallerSupport.ProductionLayout)
    (proofs : Array PrunedMerklePaths) (observations : List Observation)
    (a : Accepted ctx Q cap packet saved)
    (run : PublicMerkleProgram.Runs (WHIRSourceChronology.erase
      (AnchoredPhysicalDriver.verifySource cap .fresh model ctx stack Q packet saved proofs))
      observations (some a))
    (consistent : AnchoredIdealPhysicalAcceptance.PrimitiveConsistent seed observations)
    (quiet : ∀ opening ∈ a.wire.openings,
      ¬ PublicMerkleBinding.OpenPrimitiveBad seed (openingLog packet saved program seed ro opening)
        opening.root opening.result.paths) :
    WHIRPhysicalRoots.BoundRows (base packet saved program seed ro)
      (roots packet saved program seed ro) a.wire := by
  obtain ⟨_,_,_,trace,observed⟩ := AnchoredPhysicalExecution.verifySource_execution
    cap .fresh model ctx stack Q packet saved proofs observations a run
  intro opening member
  obtain ⟨proof,_,accepted,_⟩ := AnchoredIdealPhysicalAcceptance.observed_real
    (observed opening member) seed ctx.iv consistent
  let log := openingLog packet saved program seed ro opening
  have auth : AuthenticLog seed log := referenceLog_authentic packet program seed ro _
  have good := (WHIRPhysicalVerifier.openQuery_binding seed ctx.iv log auth
    ⟨recordDomain (records log),[]⟩ rfl packet.val.profile opening.level saved.shape.lanes
    proof opening.root opening.sample opening.result accepted).resolve_right (quiet opening member)
  dsimp only [log] at good
  rw [opening_log packet saved program seed ro opening] at good
  by_cases zero : opening.level.val = 0
  · have rootEq := PCSBCSNativeCapturedOracles.verifySource_initial_root
      cap model ctx stack Q packet saved proofs a observations run opening member zero
    simpa only [zero,rootEq,ite_true,base,frozenQueryOracle] using good
  · simpa only [roots,frozenQueryOracle,ite_eq_right zero] using good

theorem native_experiment (model : WHIRCallerSupport.ProductionLayout)
    (proofs : Array PrunedMerklePaths) (observations : List Observation)
    (a : Accepted ctx Q cap packet saved)
    (run : PublicMerkleProgram.Runs (WHIRSourceChronology.erase
      (AnchoredPhysicalDriver.verifySource cap .fresh model ctx stack Q packet saved proofs))
      observations (some a))
    (consistent : AnchoredIdealPhysicalAcceptance.PrimitiveConsistent seed observations)
    (quiet : ∀ opening ∈ a.wire.openings,
      ¬ PublicMerkleBinding.OpenPrimitiveBad seed (openingLog packet saved program seed ro opening)
        opening.root opening.result.paths) :
    ∃ replay : StackWHIRReplay.Replay packet.val.profile cap, ∃ proof,
      replay.original = PCSBCSNativeOracleReplay.original a (base packet saved program seed ro) ∧
      a.wire.initial = some replay.initial ∧ a.wire.tape.1 = replay.initial.2 ∧
      replay.whir.replies.map WHIRPhysicalErasure.eraseReply = a.wire.replies ∧
      CausalGame.opening (ParameterBounds.config packet.val.profile)
        (CausalGame.challenges (ParameterBounds.config packet.val.profile) a.wire.tape)
        replay.whir.replies = .ok proof ∧
      WHIRPhysicalHistory.decodeStack packet.val.profile cap
        (fun _ => some (PCSBCSNativeOracleReplay.original a (base packet saved program seed ro)))
        (roots packet saved program seed ro) (fun i => a.wire.rows[i]!)
        ⟨packet.val.statement,packet.val.messages,(localHistory ctx stack Q packet.val.profile a.history).tail⟩ =
        some replay ∧
      CausalGame.experiment (PCSBCSNativeOracleReplay.input a
        (base packet saved program seed ro) replay.initial.1)
        (CausalStrategy.indexedStrategy replay.whir.replies) a.wire.tape = true := by
  obtain ⟨_,_,lanesEq,_,_⟩ := AnchoredPhysicalExecution.verifySource_execution
    cap .fresh model ctx stack Q packet saved proofs observations a run
  have fits : saved.shape.lanes ≤ 2^(ParameterBounds.config packet.val.profile).folds[0]! := by
    rw [← lanesEq]
    exact a.request.lane_bound
  exact PCSBCSNativeOracleReplay.verifySource_experiment .fresh model proofs observations a run
    (base packet saved program seed ro) (roots packet saved program seed ro)
    (base_valid packet saved program seed ro fits)
    (roots_rectangular packet saved program seed ro)
    (native_boundRows packet saved program seed ro model proofs observations a run consistent quiet)

/-- Parsed next roles have exactly the shape used by the captured root getter. -/
theorem next_log (i : Fin (ParameterBounds.config packet.val.profile).folds.size)
    (j : Fin (ParameterBounds.config packet.val.profile).folds[i.val]!)
    (m : WHIRHistory.Pending) (ref : Reference)
    (parsed : parsePhase (ParameterBounds.config packet.val.profile) (.fold i j) m (i.val+1) 2 = some ref) :
    referenceLog packet program seed ro ref =
      logFor packet saved program seed ro
        ref.root (i.val+1) := by
  have shape := (parsePhase_admitted _ _ _ _ _ _ parsed).2.2.2
  unfold logFor
  congr 1
  cases ref
  congr 1

/-- The full next table is the projection of the same literal captured prefix.
No later whole-cache equality is present, even as an intermediate hypothesis. -/
theorem next_projection (i : Fin (ParameterBounds.config packet.val.profile).folds.size)
    (j : Fin (ParameterBounds.config packet.val.profile).folds[i.val]!)
    (m : WHIRHistory.Pending) (ref : Reference)
    (parsed : parsePhase (ParameterBounds.config packet.val.profile) (.fold i j) m (i.val+1) 2 = some ref)
    (clean : ¬ OutputCollision (referenceLog packet program seed ro ref)) :
    extensionOracle (WHIRPhysicalRows.compactBaseOracle (hash seed)
      ⟨recordDomain (records (referenceLog packet program seed ro ref)),[]⟩
      ref.root ref.shape.height (2^ref.shape.height)
      ref.shape.leafWords ref.shape.occupied) =
      some (roots packet saved program seed ro
        ref.root (i.val+1)) := by
  have projection := (parsed_next_projection seed
    (referenceLog packet program seed ro ref)
    packet.val.profile i j m ref parsed
    (referenceLog_authentic packet program seed ro ref) clean).1
  rw [next_log packet saved program seed ro i j m ref parsed] at projection ⊢
  simpa only [roots, frozenQueryOracle, Nat.add_eq_zero_iff,
    Nat.one_ne_zero, and_false, ↓reduceIte] using projection

theorem native_query
    (a : Accepted ctx Q cap packet saved)
    (model : WHIRCallerSupport.ProductionLayout) (proofs : Array PrunedMerklePaths)
    (observations : List Observation)
    (run : PublicMerkleProgram.Runs (WHIRSourceChronology.erase
      (AnchoredPhysicalDriver.verifySource cap .fresh model ctx stack Q packet saved proofs))
      observations (some a))
    (consistent : AnchoredIdealPhysicalAcceptance.PrimitiveConsistent seed observations)
    (final current : PCSBCSChallengeOracle.EnteredPacket packet.val.profile B ctx.iv
      boundary)
    (messages : final.2.messages = packet.val.messages)
    (member : current ∈ PCSBCSCapturedSourceStatePath.packets final)
    (ring : RingPCSGame.Prefix)
    (raws : ∀ sourcePacket ∈ PCSBCSCapturedSourceStatePath.packets final,
      PCSBCSChallengeOracle.grouped sourcePacket.2.coord
        ((table packet seed ro) (.inl sourcePacket)) =
        PCSBCSRestorationHazard.literalRaw ring a.wire.tape sourcePacket.2.coord)
    (opening : QueryOpening packet.val.profile) (opened : opening ∈ a.wire.openings)
    (earlier : CausalProbability.position (.query opening.level :
      CausalProbability.Coordinate (ParameterBounds.config packet.val.profile)) <
        CausalProbability.position current.2.coord)
    (m : WHIRHistory.Pending) (digest : Digest32) (introMessage : Message E) :
    SourceEvidence (addresses packet)
      program (table packet seed ro)
      seed current.2.coord saved current.2.messages
      (PCSBCSSourcePacketTape.strictPrefix current (fun key => (table packet seed ro) key.val))
      m digest (.query opening.level) (.query opening.result.rows introMessage) ∨
      PublicMerkleBinding.OpenPrimitiveBad seed
        (openingLog packet saved program seed ro opening)
        opening.root opening.result.paths := by
  obtain ⟨_,_,lanesEq,trace,observed⟩ := AnchoredPhysicalExecution.verifySource_execution
    cap .fresh model ctx stack Q packet saved proofs _ a run
  have chain := completion_chain ctx Q packet
  have reference := (trace_queryRoles saved a.configuration.1 a.configuration.2 chain trace opening opened).2
  have earlierPrefix := packets_query_prefix final current member (.query opening.level) earlier
  rw [← messages,← earlierPrefix] at reference
  have sample := (WHIRPhysicalRoots.trace_samples saved.root chain trace opening opened).2
  have past := strictPrefix_of_raws final current member (table packet seed ro) ring a.wire.tape raws
  have sampleAt : PCSBCSSourcePacketTape.strictPrefix current
      (fun key => (table packet seed ro) key.val) (.query opening.level) earlier =
      opening.sample := by
    rw [past]
    exact sample
  obtain ⟨proof,_,accepted,_⟩ := AnchoredIdealPhysicalAcceptance.observed_real
    (observed opening opened) seed ctx.iv consistent
  have fits : saved.shape.lanes ≤ 2^(ParameterBounds.config packet.val.profile).folds[0]! := by
    rw [← lanesEq]
    exact a.request.lane_bound
  have evidence := source_query_of_native (addresses packet) program (table packet seed ro)
    seed current.2.coord saved current.2.messages
    (PCSBCSSourcePacketTape.strictPrefix current (fun key => (table packet seed ro) key.val))
    m digest opening.level introMessage earlier (PCSBCSNativeRootRoles.openingRole saved opening)
    reference (referenceLog_authentic packet program seed ro _) fits proof opening.result
    (by simpa only [sampleAt,PCSBCSNativeRootRoles.openingRole] using accepted)
  exact evidence

theorem source_of_parser
    (current : CausalProbability.Coordinate (ParameterBounds.config packet.val.profile))
    (messages : List WHIRHistory.Pending) (past : WHIRFiatShamir.Prefix current)
    (q : CausalProbability.Coordinate (ParameterBounds.config packet.val.profile))
    (m : WHIRHistory.Pending) (native : CausalGame.Reply) (rows : WHIRPhysicalHistory.Rows)
    (earlier : CausalProbability.position q < CausalProbability.position current)
    (parsed : WHIRPhysicalHistory.reply
      (roots packet saved program seed ro)
      rows q m = some native)
    (clean : ∀ ref, ¬ OutputCollision
      (referenceLog packet program seed ro ref))
    (queries : ∀ (i : Fin (ParameterBounds.config packet.val.profile).folds.size) (introMessage : Message E),
      CausalProbability.position (.query i :
        CausalProbability.Coordinate (ParameterBounds.config packet.val.profile)) <
          CausalProbability.position current →
      SourceEvidence (addresses packet)
        program (table packet seed ro)
        seed current saved messages past m DuplexRefinement.zeroDigest (.query i) (.query (rows i.val) introMessage)) :
    ∃ digest, WHIRHistory.replyScalars q digest native = some m.scalars ∧
      SourceEvidence (addresses packet)
        program (table packet seed ro)
        seed current saved messages past m digest q native := by
  cases q with
  | initial =>
    obtain ⟨message,decoded,equal⟩ := Option.map_eq_some_iff.mp parsed
    subst native
    exact ⟨DuplexRefinement.zeroDigest,congrArg some (decodeMessage_fields _ _ decoded).symm,.initial message⟩
  | tail j =>
    obtain ⟨message,decoded,equal⟩ := Option.map_eq_some_iff.mp parsed
    subst native
    exact ⟨DuplexRefinement.zeroDigest,congrArg some (decodeMessage_fields _ _ decoded).symm,.tail j message⟩
  | query i =>
    obtain ⟨message,decoded,equal⟩ := Option.map_eq_some_iff.mp parsed
    subst native
    exact ⟨DuplexRefinement.zeroDigest,congrArg some (decodeMessage_fields _ _ decoded).symm,
      queries i message earlier⟩
  | ood i j =>
    cases m with
    | mk scalars nonce =>
      cases scalars with
      | nil => cases parsed
      | cons value rest =>
        cases rest with
        | nil => cases parsed
        | cons a rest =>
          cases rest with
          | nil => cases parsed
          | cons b rest =>
            cases rest with
            | cons c rest => cases parsed
            | nil =>
              cases Option.some.inj parsed
              exact ⟨DuplexRefinement.zeroDigest,rfl,.ood i j ⟨value,⟨a,b⟩⟩⟩
  | fold i j =>
    cases m with
    | mk scalars nonce =>
      cases scalars with
      | nil => cases parsed
      | cons a rest =>
        cases rest with
        | nil => cases parsed
        | cons b rest =>
          by_cases last : j.val+1 = (ParameterBounds.config packet.val.profile).folds[i.val]!
          · by_cases later : i.val+1 < (ParameterBounds.config packet.val.profile).folds.size
            · cases rest with
              | nil => simp [WHIRPhysicalHistory.reply,WHIRHistory.decodeReplyScalars,last,later] at parsed
              | cons r rest =>
                cases rest with
                | nil => simp [WHIRPhysicalHistory.reply,WHIRHistory.decodeReplyScalars,last,later] at parsed
                | cons s rest =>
                  cases rest with
                  | cons extra rest =>
                    simp [WHIRPhysicalHistory.reply,WHIRHistory.decodeReplyScalars,last,later] at parsed
                  | nil =>
                    simp only [WHIRPhysicalHistory.reply,WHIRHistory.decodeReplyScalars,
                      last,↓reduceIte,later] at parsed
                    obtain ⟨digest,decoded,equal⟩ := Option.map_eq_some_iff.mp parsed
                    subst native
                    let ref : Reference := ⟨digest,phaseShape (ParameterBounds.config packet.val.profile) (i.val+1)⟩
                    have reference : parsePhase (ParameterBounds.config packet.val.profile) (.fold i j)
                        ⟨[a,b,r,s],nonce⟩ (i.val+1) 2 = some ref := by
                      simp [parsePhase,last,later,parseRootScalars,decoded,ref]
                    have auth := referenceLog_authentic packet program seed ro ref
                    have projection := next_projection packet saved program seed ro
                      i j ⟨[a,b,r,s],nonce⟩ ref reference (clean ref)
                    have pair := ByteCodec.hashToScalars_scalarsToHash (r,s) digest decoded
                    refine ⟨digest,?_,?_⟩
                    · simp only [WHIRHistory.replyScalars,last,↓reduceIte,WHIRHistory.boundaryScalars,
                        later,WHIRHistory.messageScalars,WHIRHistory.rootScalars,pair]
                      rfl
                    · exact .next i j ⟨a,b⟩ _ last later ref
                        (referenceLog packet program seed ro ref)
                        reference rfl (Nat.le_refl _) auth (clean ref) projection
            · simp only [WHIRPhysicalHistory.reply,WHIRHistory.decodeReplyScalars,last,
                ↓reduceIte,ite_eq_right later] at parsed
              split at parsed
              · rename_i width
                cases Option.some.inj parsed
                refine ⟨DuplexRefinement.zeroDigest,?_,.terminal i j ⟨a,b⟩ rest.toArray last later ?_⟩
                · simp [WHIRHistory.replyScalars,last,WHIRHistory.boundaryScalars,later,
                    WHIRHistory.messageScalars]
                · simpa only [List.size_toArray] using width
              · cases parsed
          · simp only [WHIRPhysicalHistory.reply,WHIRHistory.decodeReplyScalars,
              ite_eq_right last] at parsed
            split at parsed
            · rename_i empty
              subst rest
              cases Option.some.inj parsed
              exact ⟨DuplexRefinement.zeroDigest,by simp only [WHIRHistory.replyScalars,
                ite_eq_right last,WHIRHistory.messageScalars,List.append_nil],.middle i j ⟨a,b⟩ last⟩
            · cases parsed

theorem native_replyTransport_of_decode
    (a : Accepted ctx Q cap packet saved)
    (model : WHIRCallerSupport.ProductionLayout) (proofs : Array PrunedMerklePaths)
    (observations : List Observation)
    (run : PublicMerkleProgram.Runs (WHIRSourceChronology.erase
      (AnchoredPhysicalDriver.verifySource cap .fresh model ctx stack Q packet saved proofs))
      observations (some a))
    (consistent : AnchoredIdealPhysicalAcceptance.PrimitiveConsistent seed observations)
    (replay : StackWHIRReplay.Replay packet.val.profile cap)
    (decoded : WHIRPhysicalHistory.decodeStack packet.val.profile cap
      (fun _ => some (PCSBCSNativeOracleReplay.original a
        (base packet saved program seed ro)))
      (roots packet saved program seed ro)
      (fun i => a.wire.rows[i]!)
      ⟨packet.val.statement,packet.val.messages,
        (localHistory ctx stack Q packet.val.profile a.history).tail⟩ = some replay)
    (final : PCSBCSChallengeOracle.EnteredPacket packet.val.profile B ctx.iv
      boundary)
    (messages : final.2.messages = packet.val.messages)
    (raws : ∀ current ∈ PCSBCSCapturedSourceStatePath.packets final,
      PCSBCSChallengeOracle.grouped current.2.coord ((table packet seed ro) (.inl current)) =
        PCSBCSRestorationHazard.literalRaw replay.initial.1 a.wire.tape current.2.coord)
    (quiet : ∀ opening ∈ a.wire.openings,
      ¬ PublicMerkleBinding.OpenPrimitiveBad seed
        (openingLog packet saved program seed ro opening)
        opening.root opening.result.paths)
    (clean : ∀ ref, ¬ OutputCollision
      (referenceLog packet program seed ro ref)) :
    ∀ current ∈ PCSBCSCapturedSourceStatePath.packets final,
      PCSBCSCapturedSourceAcceptance.ReplyTransport (addresses packet)
        program (table packet seed ro)
        seed saved current replay.whir.replies := by
  obtain ⟨_,_,_,trace,_⟩ := AnchoredPhysicalExecution.verifySource_execution
    cap .fresh model ctx stack Q packet saved proofs _ a run
  have chain := completion_chain ctx Q packet
  let original := PCSBCSNativeOracleReplay.original a
    (base packet saved program seed ro)
  obtain ⟨initial,_,rest⟩ := Option.bind_eq_some_iff.mp decoded
  obtain ⟨whir,parsedWhir,equal⟩ := Option.bind_eq_some_iff.mp rest
  have equal : (⟨original,initial,whir⟩ : StackWHIRReplay.Replay packet.val.profile cap) = replay :=
    Option.some.inj equal
  have whirEq : whir = replay.whir := congrArg StackWHIRReplay.Replay.whir equal
  have parsed := parses_of_decode packet.val.profile (StackWHIRReplay.localCatalog original initial)
    (roots packet saved program seed ro)
    (fun i => a.wire.rows[i]!) packet.val.statement packet.val.messages
    ((localHistory ctx stack Q packet.val.profile a.history).tail.map StackWHIRReplay.projectEntry)
    replay.whir (by
      rw [← whirEq]
      exact parsedWhir)
  have size : replay.whir.replies.size = CausalProbability.position final.2.coord := by
    rw [parsed.size,← messages,PCSBCSChallengeOracle.CanonicalPacket.messages_length final.2]
    omega
  intro current member j earlier
  have bound : j < replay.whir.replies.size := by
    rw [size]
    exact Nat.lt_of_lt_of_le earlier (packets_position_le final current member)
  obtain ⟨q,m,previous,sample,scheduled,atMessage,atReply,inAncestors⟩ := parsed.replyAt j bound
  have qPosition := PCSBCSCapturedSourceAcceptance.schedule_coordinate_position j q scheduled
  have prior : CausalProbability.position q < CausalProbability.position current.2.coord := by
    rw [qPosition]
    exact earlier
  have currentMessage : current.2.messages.reverse[j+1]? = some m := by
    rw [packets_message_at final current member j earlier,messages]
    exact atMessage
  obtain ⟨digest,scalars,evidence⟩ := source_of_parser packet saved program seed ro
    current.2.coord current.2.messages
    (PCSBCSSourcePacketTape.strictPrefix current (fun key => (table packet seed ro) key.val))
    q m replay.whir.replies[j]! (fun i => a.wire.rows[i]!) prior atReply clean (by
      intro i introMessage earlierQuery
      have queryBound : CausalProbability.position (.query i :
          CausalProbability.Coordinate (ParameterBounds.config packet.val.profile)) < replay.whir.replies.size := by
        rw [size]
        exact Nat.lt_of_lt_of_le earlierQuery (packets_position_le final current member)
      obtain ⟨coordinate,message,old,x,atCoordinate,_,_,inPast⟩ :=
        parsed.replyAt (CausalProbability.position (.query i :
          CausalProbability.Coordinate (ParameterBounds.config packet.val.profile))) queryBound
      have same : coordinate = .query i := Option.some.inj
        (atCoordinate.symm.trans (WHIRHistory.schedule_get_position (.query i)))
      subst coordinate
      have recorded := WHIRPhysicalRoots.projectEntry_query_mem
        (localHistory ctx stack Q packet.val.profile a.history).tail old i x inPast
      have recorded : (old,⟨.query i,x⟩) ∈ localHistory ctx stack Q packet.val.profile a.history :=
        List.mem_of_mem_tail recorded
      obtain ⟨opening,opened,level,sample⟩ := WHIRPhysicalRoots.trace_recorded trace _ recorded
      have row := (WHIRPhysicalRoots.trace_rooted saved.root trace opening opened).2
      cases opening with
      | mk level' root x' result =>
        dsimp only at level sample row
        subst level'
        have rowEq : a.wire.rows[i.val]! = result.rows := by
          rw [getElem!_def,row]
        have source := (native_query packet saved program seed ro a model proofs observations run consistent
          final current messages member replay.initial.1 raws ⟨i,root,x',result⟩ opened earlierQuery
          m DuplexRefinement.zeroDigest introMessage).resolve_right
          (quiet ⟨i,root,x',result⟩ opened)
        rw [rowEq]
        exact source)
  exact ⟨q,m,digest,scheduled,currentMessage,scalars,evidence⟩

theorem base_eq_sourceRoot (profile : profileShape packet.val.profile saved.shape) :
    base packet saved program seed ro =
      sourceRoot seed (addresses packet) ⟨saved.root,initialShape saved.shape⟩ program (table packet seed ro) := by
  have shape := PCSBCSNativeRootRoles.nativeShape_opening packet.val.profile saved profile 0
  have length : 2^((ParameterBounds.length (ParameterBounds.config packet.val.profile) 0).log2) =
      ParameterBounds.length (ParameterBounds.config packet.val.profile) 0 := by
    simp [ParameterBounds.length]
  unfold base sourceRoot
  have ref : (⟨saved.root,PCSBCSNativeRootRoles.nativeShape packet.val.profile saved 0⟩ : Reference) =
      ⟨saved.root,initialShape saved.shape⟩ := rfl
  change WHIRPhysicalRows.compactBaseOracle (hash seed)
    ⟨recordDomain (records (referenceLog packet program seed ro
      ⟨saved.root,PCSBCSNativeRootRoles.nativeShape packet.val.profile saved 0⟩)),[]⟩ saved.root
      (ParameterBounds.length (ParameterBounds.config packet.val.profile) 0).log2
      (ParameterBounds.length (ParameterBounds.config packet.val.profile) 0)
      (leafWords packet.val.profile 0) saved.shape.lanes = _
  rw [ref]
  have shape' : initialShape saved.shape =
      ⟨(ParameterBounds.length (ParameterBounds.config packet.val.profile) 0).log2,
        leafWords packet.val.profile 0,saved.shape.lanes⟩ := by
    simpa only [PCSBCSNativeRootRoles.nativeShape,ite_true] using shape
  simp only [shape',referenceLog,length]

/-- The complete strict incoming captured caller, with the same actual whole
root and the same canonical full native replies. -/
def CapturedAssembly (original : PCSBCSCallerBinding.CallerInput packet.val.profile)
    (current : PCSBCSChallengeOracle.EnteredPacket packet.val.profile B ctx.iv boundary)
    (ring : RingPCSGame.Prefix) (tape : CausalGame.Tape (ParameterBounds.config packet.val.profile))
    (native : Array CausalGame.Reply) : Prop :=
  ∃ parsed,
    PCSBCSSourceFrozenReplies.replies current.2.coord saved
      (PCSBCSSourceCallerSnapshot.capturedRegistry (addresses packet) program current
        (fun key => (table packet seed ro) key.val))
      current.2.messages
      (PCSBCSSourcePacketTape.strictPrefix current (fun key => (table packet seed ro) key.val)) =
        some parsed ∧
    parsed = PCSRoundByRoundTranscriptState.priorAnswers native (CausalProbability.position current.2.coord) ∧
    PCSBCSRestorationHazard.incomingTrace
      (PCSBCSSourcePacketTape.ringPrefix current (fun key => (table packet seed ro) key.val))
      (PCSBCSSourcePacketTape.tape current (fun key => (table packet seed ro) key.val)) parsed current.2.coord =
      PCSBCSRestorationHazard.incomingTrace ring tape native current.2.coord ∧
    PCSBCSSourceCallerSnapshot.fromCapture (addresses packet)
      ⟨saved.root,initialShape saved.shape⟩ program original saved current
      (fun key => (table packet seed ro) key.val) =
      some (PCSBCSRestorationHazard.literalCallerData packet.val.profile original
        (sourceRoot seed (addresses packet) ⟨saved.root,initialShape saved.shape⟩ program (table packet seed ro))
        ring tape native current.2.coord)

theorem native_assembly
    (a : Accepted ctx Q cap packet saved) (model : WHIRCallerSupport.ProductionLayout)
    (original : PCSBCSCallerBinding.CallerInput packet.val.profile) (claims : AnchoredSourceCaller.Claims)
    (caller : AnchoredSourceFreshCaller.decode model.layout saved (RawWHIRKeys.entry ctx packet.val)
      (PCSBCSSourceCallerAnswers.answers (table (boundary := boundary) packet seed ro)) = some claims)
    (final current : PCSBCSChallengeOracle.EnteredPacket packet.val.profile B ctx.iv boundary)
    (entry : final.1.val = RawWHIRKeys.entry ctx packet.val)
    (member : current ∈ PCSBCSCapturedSourceStatePath.packets final)
    (recorded : (⟨.inl current,(table packet seed ro) (.inl current)⟩ :
      Sigma PCSBCSSourceRootCapture.Answer) ∈ (Sampling.execute (table packet seed ro) program).2)
    (ring : RingPCSGame.Prefix) (tape : CausalGame.Tape (ParameterBounds.config packet.val.profile))
    (native : Array CausalGame.Reply)
    (raws : ∀ sourcePacket ∈ PCSBCSCapturedSourceStatePath.packets final,
      PCSBCSChallengeOracle.grouped sourcePacket.2.coord ((table packet seed ro) (.inl sourcePacket)) =
        PCSBCSRestorationHazard.literalRaw ring tape sourcePacket.2.coord)
    (transport : PCSBCSCapturedSourceAcceptance.ReplyTransport (addresses packet) program
      (table packet seed ro) seed saved current native)
    (clean : ∀ ref, ¬ OutputCollision (referenceLog packet program seed ro ref)) :
    CapturedAssembly packet saved program seed ro original current ring tape native := by
  have currentEntry : current.1.val = RawWHIRKeys.entry ctx packet.val :=
    (congrArg Subtype.val (PCSBCSCapturedSourceStatePath.packets_entry final current member)).trans entry
  have roles := PCSBCSCapturedSourceAcceptance.roles_from_transport
    (addresses packet) program (table packet seed ro) seed saved current native transport
  have addressRoles := PCSBCSCapturedSourceTransport.address_packet model.layout saved
    (PCSBCSSourceCallerAnswers.answers (table (boundary := boundary) packet seed ro)) current
    a.configuration.1 a.configuration.2 claims (by simpa only [currentEntry] using caller) roles
  have visited : (.inl current) ∈ ((Sampling.execute (table packet seed ro) program).2.map Sigma.fst) :=
    List.mem_map.mpr ⟨_,recorded,rfl⟩
  let ref : Reference := ⟨saved.root,initialShape saved.shape⟩
  let log := referenceLog packet program seed ro ref
  have mentioned : ref ∈ addresses packet (.inl current) := by
    change ref ∈ PCSBCSCapturedSourceTransport.address (.inl current)
    rw [addressRoles]
    exact List.mem_cons_self
  have root := source_registry_enabled (addresses packet) program (table packet seed ro)
    current ref mentioned visited
  have root : PCSBCSSourceCallerSnapshot.capturedRegistry (addresses packet) program current
      (fun key => (table packet seed ro) key.val) ref = some (freeze log ref.root ref.shape) := root
  have inverses := PCSBCSCapturedSourceAcceptance.source_inverse
    (addresses packet) program (table packet seed ro) seed saved current native addressRoles visited transport
  obtain ⟨parsed,assembled⟩ := PCSBCSCapturedSourceTransport.replies_complete current.2.coord saved
    (PCSBCSSourceCallerSnapshot.capturedRegistry (addresses packet) program current
      (fun key => (table packet seed ro) key.val)) current.2.messages
    (PCSBCSSourcePacketTape.strictPrefix current (fun key => (table packet seed ro) key.val)) (by
      intro j earlier
      obtain ⟨inverted,found,_⟩ := Option.map_eq_some_iff.mp (inverses j earlier)
      exact ⟨inverted,found⟩)
  have parsedEq := PCSBCSCapturedSourceStatePath.replies_exact current.2.coord saved _ _ _ native parsed assembled inverses
  have priorRaws : ∀ earlier : current.Earlier,
      PCSBCSSourcePacketTape.rawPrefix current (fun key => (table packet seed ro) key.val)
        earlier.val earlier.property = PCSBCSRestorationHazard.literalRaw ring tape earlier.val := by
    intro earlier
    rw [PCSBCSSourcePacketTape.rawPrefix_table]
    exact raws _ (PCSBCSCapturedSourceStatePath.predecessor_mem_packets final current member earlier)
  have incoming := PCSBCSCapturedSourceStatePath.incoming_exact current
    (table packet seed ro) ring tape native parsed parsedEq priorRaws
  have snapshot := PCSBCSCapturedSourceStatePath.fromCapture_exact (addresses packet) ref
    program original saved current (table packet seed ro) (freeze log ref.root ref.shape) root
    ring tape native priorRaws inverses
  have rawEq : (freeze log ref.root ref.shape).raw =
      sourceRoot seed (addresses packet) ⟨saved.root,initialShape saved.shape⟩ program (table packet seed ro) :=
    (next_image_provenance seed log ref (referenceLog_authentic packet program seed ro ref) (clean ref)).2
  rw [rawEq] at snapshot
  exact ⟨parsed,assembled,parsedEq,incoming,snapshot⟩

theorem original_bound (model : WHIRCallerSupport.ProductionLayout)
    (input : PCSBCSCallerBinding.CallerInput packet.val.profile)
    (reconstructed : PCSBCSSourceCallerOriginal.original packet.val.profile model.layout saved
      (RawWHIRKeys.entry ctx packet.val)
      (PCSBCSSourceCallerAnswers.answers (table (boundary := boundary) packet seed ro)) = some input) :
    ∃ claims : AnchoredSourceCaller.Claims,
      AnchoredSourceFreshCaller.decode model.layout saved (RawWHIRKeys.entry ctx packet.val)
        (PCSBCSSourceCallerAnswers.answers (table (boundary := boundary) packet seed ro)) = some claims ∧
      BoundOriginal input saved claims := by
  obtain ⟨claims,fc,cc,prepared,decoded,recordEq,rootEq,_,rfl⟩ :=
    PCSBCSSourceCallerOriginal.original_exact packet.val.profile model.layout saved
      (RawWHIRKeys.entry ctx packet.val)
      (PCSBCSSourceCallerAnswers.answers (table (boundary := boundary) packet seed ro)) input reconstructed
  refine ⟨claims,decoded,recordEq,rootEq,rfl,?_,rfl,rfl,rfl⟩
  exact List.ofFn_getElem

/-- Witnesses and consequences, never certificates supplied to the endpoint. -/
structure CaptureResult (model : WHIRCallerSupport.ProductionLayout)
    (a : Accepted ctx Q cap packet saved) where
  original : PCSBCSCallerBinding.CallerInput packet.val.profile
  claims : AnchoredSourceCaller.Claims
  replay : StackWHIRReplay.Replay packet.val.profile cap
  proof : Opening
  final : PCSBCSChallengeOracle.EnteredPacket packet.val.profile B ctx.iv boundary
  entry : final.1.val = RawWHIRKeys.entry ctx packet.val
  messages : final.2.messages = packet.val.messages
  terminal : final.2.coord = PCSRoundByRoundTranscriptState.lastCoordinate (ParameterBounds.config packet.val.profile)
  depth : packet.val.messages.length = WHIRHistory.depth (ParameterBounds.config packet.val.profile)
  original_decoded : PCSBCSSourceCallerOriginal.original packet.val.profile model.layout saved
    (RawWHIRKeys.entry ctx packet.val)
    (PCSBCSSourceCallerAnswers.answers (table (boundary := boundary) packet seed ro)) = some original
  caller_decoded : AnchoredSourceFreshCaller.decode model.layout saved (RawWHIRKeys.entry ctx packet.val)
    (PCSBCSSourceCallerAnswers.answers (table (boundary := boundary) packet seed ro)) = some claims
  bound_original : BoundOriginal original saved claims
  bound_rows : WHIRPhysicalRoots.BoundRows (base packet saved program seed ro)
    (roots packet saved program seed ro) a.wire
  replay_original : replay.original = PCSBCSNativeOracleReplay.original a (base packet saved program seed ro)
  initial : a.wire.initial = some replay.initial
  lambda : a.wire.tape.1 = replay.initial.2
  erased : replay.whir.replies.map WHIRPhysicalErasure.eraseReply = a.wire.replies
  opening : CausalGame.opening (ParameterBounds.config packet.val.profile)
    (CausalGame.challenges (ParameterBounds.config packet.val.profile) a.wire.tape) replay.whir.replies = .ok proof
  canonical : WHIRPhysicalHistory.decodeStack packet.val.profile cap
    (fun _ => some (PCSBCSNativeOracleReplay.original a (base packet saved program seed ro)))
    (roots packet saved program seed ro) (fun i => a.wire.rows[i]!)
    ⟨packet.val.statement,packet.val.messages,(localHistory ctx stack Q packet.val.profile a.history).tail⟩ = some replay
  explains : ∀ root ring, OriginalClaimsChecker.input original.prepared root ring =
    PCSBCSNativeOracleReplay.input a root ring
  experiment : CausalGame.experiment
    (OriginalClaimsChecker.input original.prepared
      (sourceRoot seed (addresses packet) ⟨saved.root,initialShape saved.shape⟩ program (table packet seed ro))
      replay.initial.1) (CausalStrategy.indexedStrategy replay.whir.replies) a.wire.tape = true
  native_replies : nativeReplies original
    (sourceRoot seed (addresses packet) ⟨saved.root,initialShape saved.shape⟩ program (table packet seed ro))
    (fun _ => CausalStrategy.indexedStrategy replay.whir.replies) replay.initial.1 a.wire.tape = replay.whir.replies
  recorded : ∀ current ∈ PCSBCSCapturedSourceStatePath.packets final,
    (⟨.inl current,(table packet seed ro) (.inl current)⟩ : Sigma PCSBCSSourceRootCapture.Answer) ∈
      (Sampling.execute (table packet seed ro) program).2
  raws : ∀ current ∈ PCSBCSCapturedSourceStatePath.packets final,
    PCSBCSChallengeOracle.grouped current.2.coord ((table packet seed ro) (.inl current)) =
      PCSBCSRestorationHazard.literalRaw replay.initial.1 a.wire.tape current.2.coord
  transport : ∀ current ∈ PCSBCSCapturedSourceStatePath.packets final,
    ReplyTransport (addresses packet) program (table packet seed ro) seed saved current replay.whir.replies
  assembly : ∀ current ∈ PCSBCSCapturedSourceStatePath.packets final,
    CapturedAssembly packet saved program seed ro original current replay.initial.1 a.wire.tape replay.whir.replies
  mentioned : ∀ opening ∈ a.wire.openings, ∃ events,
    PCSBCSFirstRootDisclosure.firstMention (addresses packet)
      (PCSBCSNativeRootRoles.openingRole saved opening) program (table packet seed ro) = some events

theorem openingReference_eq_role (profile : profileShape packet.val.profile saved.shape)
    (opening : QueryOpening packet.val.profile) :
    PCSBCSCapturedIdealNativeAcceptance.openingReference ctx Q packet opening saved.shape.lanes =
      PCSBCSNativeRootRoles.openingRole saved opening := by
  unfold PCSBCSCapturedIdealNativeAcceptance.openingReference PCSBCSNativeRootRoles.openingRole
  rw [PCSBCSNativeRootRoles.nativeShape_opening packet.val.profile saved profile opening.level.val]

end Capture

section Whole
variable (cap : Nat) (registry : WHIRPhysicalDriver.ProductionRegistry) (Q : Nat)
    (attacker : WHIRSourceChronology.Source cap (AnchoredPhysicalAfter.Input registry.context Q))
    (A B : Nat) (limit : A ≤ B)
    (counted : DuplexModeGame.Counts A (PCSBCSNativePhysicalFreeze.wholeProgram cap registry Q attacker))
    (seed : PrimitiveOracle) (ro : RawKey B → Digest32)

noncomputable abbrev wholeAllocation (a : AnchoredPhysicalAfter.Accepted registry.context Q cap) :=
  PCSBCSNativePhysicalFreeze.allocationProgram (p := a.input.packet.val.profile) (iv := registry.context.iv)
    (boundary := (RawWHIRKeys.entry registry.context a.input.packet.val).frames.length)
    (PCSBCSNativePhysicalFreeze.wholeProgram cap registry Q attacker) A limit counted

noncomputable abbrev wholeOpeningLog (a : AnchoredPhysicalAfter.Accepted registry.context Q cap)
    (opening : QueryOpening a.input.packet.val.profile) :=
  openingLog a.input.packet a.input.record (wholeAllocation cap registry Q attacker A B limit counted a)
    seed ro opening

noncomputable abbrev wholeReferenceLog (a : AnchoredPhysicalAfter.Accepted registry.context Q cap)
    (ref : Reference) :=
  referenceLog a.input.packet (wholeAllocation cap registry Q attacker A B limit counted a) seed ro ref

/-- Original decoding uses the actual caller preparation and the genuine
previous construction-output answers from the same whole table. -/
theorem mixed_success_original (a : AnchoredPhysicalAfter.Accepted registry.context Q cap)
    (familyCap : cap ≤ 2^64)
    (success : (PCSBCSWholeNativePacketCoverage.mixedView cap registry Q attacker A B limit counted seed ro).result.value =
      some a) :
    ∃ input : PCSBCSCallerBinding.CallerInput a.input.packet.val.profile,
      PCSBCSSourceCallerOriginal.original a.input.packet.val.profile
        (registry.packetModel Q a.input.packet).layout a.input.record
        (RawWHIRKeys.entry registry.context a.input.packet.val)
        (PCSBCSSourceCallerAnswers.answers (table
          (boundary := (RawWHIRKeys.entry registry.context a.input.packet.val).frames.length)
          a.input.packet seed ro)) = some input ∧
      input.m = a.native.request.claims.count ∧
      ∀ root ring, OriginalClaimsChecker.input input.prepared root ring =
        PCSBCSNativeOracleReplay.input a.native root ring := by
  obtain ⟨_,after,_,_,run,_⟩ := PCSBCSWholeNativePacketCoverage.mixed_success_native_segment
    cap registry Q attacker A B limit counted seed ro a success
  obtain ⟨_,shape,_,_,_,_,_,_,_,_⟩ := AnchoredPhysicalExecution.verifySource_success cap .fresh
    (registry.packetModel Q a.input.packet) registry.context rfl Q
    a.input.packet a.input.record a.input.proofs after a.native run
  obtain ⟨before,parsed,earlier⟩ := PCSBCSWholeNativePacketCoverage.mixed_success_caller_preparation
    cap registry Q attacker A B limit counted seed ro a success
  obtain ⟨input,reconstructed,count,statement⟩ := PCSBCSNativeCallerOriginal.request_original
    cap a.input.packet.val.profile (registry.packetModel Q a.input.packet) a.input.record
    a.native.configuration shape (RawWHIRKeys.entry registry.context a.input.packet.val)
    (WHIRPhysicalCaller.latestAnswers before) a.native.request familyCap parsed
  refine ⟨input,?_,count,statement⟩
  rw [← reconstructed]
  apply PCSBCSSourceCallerOriginal.original_prior_only
  intro q member
  rw [earlier q member]
  rfl

/-- Exact whole mixed-source endpoint. No accepted original, parsed replay,
sampled-row equality, raw-tape equality or reply-transport certificate is a
premise. The two primitive exclusions are deliberately low-level mixed-game
events; the actual real endpoint below derives both from one complete alarm. -/
theorem mixed_success_capture_replyTransport
    (a : AnchoredPhysicalAfter.Accepted registry.context Q cap) (familyCap : cap ≤ 2^64)
    (success : (PCSBCSWholeNativePacketCoverage.mixedView cap registry Q attacker A B limit counted seed ro).result.value =
      some a)
    (quiet : ∀ opening ∈ a.native.wire.openings,
      ¬ PublicMerkleBinding.OpenPrimitiveBad seed
        (wholeOpeningLog cap registry Q attacker A B limit counted seed ro a opening)
        opening.root opening.result.paths)
    (clean : ∀ ref, ¬ OutputCollision
      (wholeReferenceLog cap registry Q attacker A B limit counted seed ro a ref)) :
    Nonempty (CaptureResult (stack := rfl) a.input.packet a.input.record
      (wholeAllocation cap registry Q attacker A B limit counted a) seed ro
      (registry.packetModel Q a.input.packet) a.native) := by
  let program := wholeAllocation cap registry Q attacker A B limit counted a
  obtain ⟨_,after,_,_,run,consistent⟩ := PCSBCSWholeNativePacketCoverage.mixed_success_native_segment
    cap registry Q attacker A B limit counted seed ro a success
  obtain ⟨input,reconstructed,_,statement⟩ := mixed_success_original
    cap registry Q attacker A B limit counted seed ro a familyCap success
  obtain ⟨claims,caller,bound⟩ := original_bound a.input.packet a.input.record seed ro
    (registry.packetModel Q a.input.packet) input reconstructed
  obtain ⟨replay,proof,replayOriginal,initial,lambda,erased,parsed,canonical,accepted⟩ :=
    native_experiment a.input.packet a.input.record program seed ro
      (registry.packetModel Q a.input.packet) a.input.proofs after a.native run consistent quiet
  have acceptedOriginal : CausalGame.experiment
      (OriginalClaimsChecker.input input.prepared (base a.input.packet a.input.record program seed ro)
        replay.initial.1) (CausalStrategy.indexedStrategy replay.whir.replies) a.native.wire.tape = true := by
    have same := statement (base a.input.packet a.input.record program seed ro) replay.initial.1
    have lanesEq : input.lanes = a.input.record.shape.lanes := congrArg CausalGame.Public.lanes same
    have claimsEq := congrArg CausalGame.Public.claims same
    change CausalGame.experiment
      ⟨ParameterBounds.config a.input.packet.val.profile,input.lanes,
        base a.input.packet a.input.record program seed ro,
        (OriginalClaimsChecker.input input.prepared
          (base a.input.packet a.input.record program seed ro) replay.initial.1).claims⟩
      (CausalStrategy.indexedStrategy replay.whir.replies) a.native.wire.tape = true
    rw [claimsEq,lanesEq]
    exact accepted
  rw [base_eq_sourceRoot a.input.packet a.input.record program seed ro a.native.configuration.2] at acceptedOriginal
  obtain ⟨seed0,bounded,seedState,depth,terminal,ordering,recorded,raws⟩ :=
    PCSBCSWholeNativePacketCoverage.mixed_success_tape cap registry Q attacker A B limit counted seed ro a success
  have seedEq : seed0 = replay.initial := Option.some.inj (seedState.symm.trans initial)
  subst seed0
  let packetB := PCSBCSNativePacketVisit.packetAtBound registry.context Q B a.input.packet bounded
  let final := PCSBCSNativePacketBridge.enteredPacket registry.context rfl B packetB
  have messages : final.2.messages = a.input.packet.val.messages := rfl
  have entry : final.1.val = RawWHIRKeys.entry registry.context a.input.packet.val := rfl
  have nativeEq := PCSBCSNativeSourceOriginal.nativeReplies_indexed input
    (sourceRoot seed (addresses a.input.packet) ⟨a.input.record.root,initialShape a.input.record.shape⟩
      program (table a.input.packet seed ro)) replay.initial.1 a.native.wire.tape replay.whir.replies proof parsed
  have transports := native_replyTransport_of_decode a.input.packet a.input.record program seed ro
    a.native (registry.packetModel Q a.input.packet) a.input.proofs after run consistent
    replay canonical final messages raws quiet clean
  refine ⟨{
    original := input, claims := claims, replay := replay, proof := proof, final := final
    entry := entry, messages := messages, terminal := terminal, depth := depth
    original_decoded := reconstructed, caller_decoded := caller, bound_original := bound
    bound_rows := native_boundRows a.input.packet a.input.record program seed ro
      (registry.packetModel Q a.input.packet) a.input.proofs after a.native run consistent quiet
    replay_original := replayOriginal, initial := initial, lambda := lambda, erased := erased
    opening := parsed, canonical := canonical, explains := statement, experiment := acceptedOriginal
    native_replies := nativeEq, recorded := recorded, raws := raws, transport := transports
    assembly := ?_, mentioned := ?_ }⟩
  · intro current member
    exact native_assembly a.input.packet a.input.record program seed ro a.native
      (registry.packetModel Q a.input.packet) input claims caller final current entry member
      (recorded current member) replay.initial.1 a.native.wire.tape replay.whir.replies
      raws (transports current member) clean
  · intro opening member
    obtain ⟨events,mentioned⟩ := PCSBCSWholeNativePacketCoverage.mixed_success_opening_firstMention
      cap registry Q attacker A B limit counted seed ro a success opening member
    rw [openingReference_eq_role a.input.packet a.input.record a.native.configuration.2 opening] at mentioned
    exact ⟨events,mentioned⟩

end Whole

/-- The complete alarm excludes collisions in every actual first-mention
capture. Missing captures have the literal empty log. No collision exclusion
is supplied separately to the real endpoint. -/
theorem actualSourceLog_clean {p : ParameterBounds.Profile} {B boundary : Nat} {iv : Digest32}
    {R : Type} (C : PrimitiveOracle) (program : Program R)
    (A : Nat) (limit : A ≤ B) (counted : DuplexModeGame.Counts A program)
    (policy : PublicMerkleProbability.RootPolicy)
    (quiet : PublicMerkleProbability.traceAlarm policy []
      (PublicCompressionProgram.primitiveLog C iv program A counted) = false)
    (ref : Reference) :
    ¬ OutputCollision (PCSBCSNativePhysicalFreeze.actualSourceLog
      (p := p) (iv := iv) (boundary := boundary) C program A limit counted ref) := by
  have emptyAuth : AuthenticLog C [] := by intro n d member; cases member
  have emptyClean : ¬ OutputCollision [] := by rintro ⟨a,b,d,member,_⟩; cases member
  have totalClean := PublicMerkleProbability.traceAlarm_clean C policy []
    (PublicCompressionProgram.primitiveLog C iv program A counted) emptyAuth
    (PublicCompressionProgram.primitiveLog_authentic C iv program A counted) emptyClean quiet
  cases found : PCSBCSFirstRootDisclosure.firstMention
      (PCSBCSCapturedSourceTransport.address (p := p) (Q := B) (iv := iv) (boundary := boundary)) ref
      (PCSBCSNativePhysicalFreeze.allocationProgram (p := p) (boundary := boundary) program A limit counted)
      (PCSBCSNativePhysicalFreeze.actualTable (p := p) (B := B) (iv := iv) (boundary := boundary) C) with
  | none =>
    simp only [PCSBCSNativePhysicalFreeze.actualSourceLog,sourceLog,found,Option.getD_none]
    simpa only [PCSBCSSourceRootCapture.ordinaryPrefix,List.foldl_nil] using emptyClean
  | some events =>
    obtain ⟨frozen⟩ := PCSBCSNativePhysicalFreeze.actual_firstMention_freeze C program A limit counted ref events found
    intro collision
    apply totalClean
    apply PublicMerkleProbability.collision_mono _ collision
    intro event member
    apply List.mem_append_left
    apply List.mem_reverse.mpr
    rw [frozen.split]
    exact List.mem_append_left _ (frozen.captured event member)

section ActualWhole
variable (cap : Nat)
    (nativeRegistry : {r : WHIRPhysicalDriver.ProductionRegistry //
      r.context.iv = PCSBCSSourceCoordinateDecoder.seedIV}) (Q : Nat)
    (attacker : WHIRSourceChronology.Source cap (AnchoredPhysicalAfter.Input nativeRegistry.val.context Q))
    (A B : Nat) (limit : A ≤ B)
    (counted : DuplexModeGame.Counts A (PCSBCSNativePhysicalFreeze.wholeProgram cap nativeRegistry.val Q attacker))
local notation "whole" => PCSBCSNativePhysicalFreeze.wholeProgram cap nativeRegistry.val Q attacker

/-- Actual whole native success gives every captured replay/reply consequence
under the same single complete primitive alarm used by the probability layer.
First-mention, physical freeze, scanner admission and full opening plans are
derived, not endpoint premises. -/
theorem actual_success_capture_replyTransport
    (rootRegistry : AnchoredHeaderRoots.Public) (C : PrimitiveOracle)
    (a : AnchoredPhysicalAfter.Accepted nativeRegistry.val.context Q cap)
    (familyCap : cap ≤ 2^64)
    (success : (runReal C nativeRegistry.val.context.iv whole).view.result.value = some a)
    (quiet : PublicMerkleProbability.traceAlarm
      (PCSBCSSourcePrimitiveRootBudget.targets a.input.packet.val.profile B
        (RawWHIRKeys.entry nativeRegistry.val.context a.input.packet.val).frames.length rootRegistry) []
      (PublicCompressionProgram.primitiveLog C nativeRegistry.val.context.iv whole A counted) = false) :
    Nonempty (CaptureResult (stack := rfl) a.input.packet a.input.record
      (wholeAllocation cap nativeRegistry.val Q attacker A B limit counted a)
      C (WHIRRealSimulator.rawTable B C) (nativeRegistry.val.packetModel Q a.input.packet) a.native) := by
  have mixedSuccess : (PCSBCSWholeNativePacketCoverage.mixedView
      cap nativeRegistry.val Q attacker A B limit counted C (WHIRRealSimulator.rawTable B C)).result.value = some a := by
    rw [PCSBCSWholeNativePacketCoverage.actual_mixedView]
    exact success
  apply mixed_success_capture_replyTransport cap nativeRegistry.val Q attacker A B limit counted
    C (WHIRRealSimulator.rawTable B C) a familyCap mixedSuccess
  · intro opening member
    have mentioned := PCSBCSWholeNativePacketCoverage.actual_success_opening_firstMention
      cap nativeRegistry.val Q attacker A B limit counted C a success opening member
    rw [openingReference_eq_role a.input.packet a.input.record a.native.configuration.2 opening] at mentioned
    rw [nativeRegistry.property] at mentioned
    obtain ⟨events,mentioned⟩ := mentioned
    have evaluated := PCSBCSNativePhysicalFreeze.whole_success_evaluated
      cap nativeRegistry.val Q attacker C A counted a success opening member
    have quiet' : PublicMerkleProbability.traceAlarm
        (PCSBCSSourcePrimitiveRootBudget.targets a.input.packet.val.profile B
          (RawWHIRKeys.entry nativeRegistry.val.context a.input.packet.val).frames.length rootRegistry) []
        (PublicCompressionProgram.primitiveLog C PCSBCSSourceCoordinateDecoder.seedIV whole A counted) = false := by
      simpa only [nativeRegistry.property] using quiet
    have excluded := PCSBCSNativeCompleteAlarm.firstMention_opening_quiet
      a.input.packet.val.profile B (RawWHIRKeys.entry nativeRegistry.val.context a.input.packet.val).frames.length
      rootRegistry C whole A limit counted (PCSBCSNativeRootRoles.openingRole a.input.record opening)
      events mentioned quiet' opening.result.paths
      (by intro path present bytes input; exact (evaluated path present bytes input).1)
      (by
        intro path present bytes input event found
        simpa only [nativeRegistry.property] using (evaluated path present bytes input).2 event found)
    change ¬ PublicMerkleBinding.OpenPrimitiveBad C
      (PCSBCSNativePhysicalFreeze.actualSourceLog (p := a.input.packet.val.profile)
        (iv := nativeRegistry.val.context.iv)
        (boundary := (RawWHIRKeys.entry nativeRegistry.val.context a.input.packet.val).frames.length)
        C whole A limit counted (PCSBCSNativeRootRoles.openingRole a.input.record opening))
      opening.root opening.result.paths
    simpa only [PCSBCSNativeRootRoles.openingRole,nativeRegistry.property] using excluded
  · intro ref
    exact actualSourceLog_clean C whole A limit counted _ quiet ref

end ActualWhole

section CountedWhole
variable (cap : Nat)
    (nativeRegistry : {r : WHIRPhysicalDriver.ProductionRegistry //
      r.context.iv = PCSBCSSourceCoordinateDecoder.seedIV}) (Q : Nat)
    (attacker : WHIRSourceChronology.Source cap (AnchoredPhysicalAfter.Input nativeRegistry.val.context Q))
    (a b : Nat) (attackerCounted : WHIRSourceChronology.Counts a attacker)
    (nativeBudget : WHIRSourceBackfill.AllResults
      (fun input => sourceBudget nativeRegistry.val.context Q input.packet ≤ b)
      (WHIRSourceChronology.erase attacker))
local notation "whole" => PCSBCSNativePhysicalFreeze.wholeProgram cap nativeRegistry.val Q attacker
local notation "counted" => PCSBCSNativePhysicalFreeze.whole_counted
  cap nativeRegistry.val Q attacker a b attackerCounted nativeBudget

/-- Production-budget form: the whole count is derived from the arbitrary
attacker's count and the genuine verifier budget on its reachable inputs. -/
theorem counted_whole_success_capture_replyTransport (B : Nat) (limit : a+b ≤ B)
    (rootRegistry : AnchoredHeaderRoots.Public) (C : PrimitiveOracle)
    (accepted : AnchoredPhysicalAfter.Accepted nativeRegistry.val.context Q cap)
    (familyCap : cap ≤ 2^64)
    (success : (runReal C nativeRegistry.val.context.iv whole).view.result.value = some accepted)
    (quiet : PublicMerkleProbability.traceAlarm
      (PCSBCSSourcePrimitiveRootBudget.targets accepted.input.packet.val.profile B
        (RawWHIRKeys.entry nativeRegistry.val.context accepted.input.packet.val).frames.length rootRegistry) []
      (PublicCompressionProgram.primitiveLog C nativeRegistry.val.context.iv whole (a+b) counted) = false) :
    Nonempty (CaptureResult (stack := rfl) accepted.input.packet accepted.input.record
      (wholeAllocation cap nativeRegistry.val Q attacker (a+b) B limit counted accepted)
      C (WHIRRealSimulator.rawTable B C)
      (nativeRegistry.val.packetModel Q accepted.input.packet) accepted.native) :=
  actual_success_capture_replyTransport cap nativeRegistry Q attacker (a+b) B limit counted
    rootRegistry C accepted familyCap success quiet
end CountedWhole

#print axioms native_boundRows
#print axioms native_experiment
#print axioms native_replyTransport_of_decode
#print axioms mixed_success_original
#print axioms mixed_success_capture_replyTransport
#print axioms actualSourceLog_clean
#print axioms actual_success_capture_replyTransport
#print axioms counted_whole_success_capture_replyTransport
end Whir.PCSBCSWholeNativeCaptureTransport
