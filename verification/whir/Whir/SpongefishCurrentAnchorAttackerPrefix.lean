import Whir.SpongefishCurrentPhysicalRootCapture
import Whir.SpongefishCurrentInitializedMode
import Whir.AnchoredMixedAttackerPrefixObserver

/-! Current raw32 first-root anchoring. Only the generic bounded-coordinate
partition and its finite-oracle math are reused from the historical modules;
the historical saved-header parser/registry is not used. Every output key with
the current 104-byte suffix freezes the same physical root before its answer,
including off-vector blocks and adversarial prequeries. The source lowering is
unchanged. Supported Profile alignment is explicit caller metadata, not an
additional source guard. This is not a native original-claim knowledge theorem. -/
namespace Whir.SpongefishCurrentAnchorAttackerPrefix
open Concrete FiatShamirGame DuplexFraming DuplexModeGame TypedOracleCompiler
open ParameterBounds AnchoredByteStreamGroups AnchoredFiatShamirSecurityCodec
open PublicMerkleLog PCSBCSMerkleRootCache
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Exactly the existing mathematical Profile/list domain. -/
structure Supported (p : Profile) (shape : SpongefishSessionAdapter.Shape) : Prop where
  valid : shape.Valid
  dimension : shape.logN = (config p).logN
  batch : shape.logBatch = (config p).folds[0]!
  rate : shape.logRate = (config p).rates[0]!

/-- A computable current predicate; no historical framing or root input. -/
def accept (shape : SpongefishSessionAdapter.Shape) (history : FramedHistory) : Bool :=
  (SpongefishCurrentAnchorHeader.fromHistory shape history).isSome

abbrev Packet (p : Profile) (Q : Nat) (iv : Digest32)
    (shape : SpongefishSessionAdapter.Shape) :=
  AnchoredByteStreamCausal.Packet Q (config p).logN iv (accept shape)

def root {p : Profile} {Q : Nat} {iv : Digest32}
    (shape : SpongefishSessionAdapter.Shape) (packet : Packet p Q iv shape) : Digest32 :=
  (SpongefishCurrentAnchorHeader.fromHistory shape packet.val.history).getD DuplexRefinement.zeroDigest

theorem packet_header {p : Profile} {Q : Nat} {iv : Digest32}
    (shape : SpongefishSessionAdapter.Shape) (packet : Packet p Q iv shape) :
    SpongefishCurrentAnchorHeader.fromHistory shape packet.val.history = some (root shape packet) := by
  have found := packet.property
  cases parsed : SpongefishCurrentAnchorHeader.fromHistory shape packet.val.history with
  | none => simp [accept,parsed] at found
  | some digest => simp [root,parsed]

/-- All consecutive output blocks, not just the native first draw, carry the
same current root. The physical recognizer also recognizes output blocks beyond
this vector, which remain outside the vector partition. -/
theorem packet_key_header {p : Profile} {Q : Nat} {iv : Digest32}
    (shape : SpongefishSessionAdapter.Shape) (packet : Packet p Q iv shape)
    (i : Fin (blockCount (config p).logN)) :
    SpongefishCurrentAnchorHeader.rawHeader shape iv (key packet.val i) = some (root shape packet) := by
  simp [SpongefishCurrentAnchorHeader.rawHeader,key_decodes,coordinate,packet_header]

theorem packet_key_member {p : Profile} {Q : Nat} {iv : Digest32}
    (shape : SpongefishSessionAdapter.Shape) (packet : Packet p Q iv shape)
    (i : Fin (blockCount (config p).logN)) :
    SpongefishCurrentPhysicalRootCapture.reference shape (root shape packet) ∈
      SpongefishCurrentPhysicalRootCapture.addresses shape iv (.inr (key packet.val i)) := by
  have found := SpongefishCurrentPhysicalRootCapture.recognize_output shape iv
    (coordinate packet.val i) (packet.val.admissible i) (packet.val.bounded i)
    i.val rfl (root shape packet) (packet_header shape packet)
  simp [SpongefishCurrentPhysicalRootCapture.addresses,key,found]

/-- Historical grouping stores completed pairs newest-first; physical capture
uses chronological Sigma events. This conversion never fabricates an answer. -/
def events {Q : Nat} (past : AnchoredMixedAttackerPrefix.History Q) :
    List (SpongefishCurrentPhysicalRootCapture.Event Q) :=
  past.reverse.map (fun e => ⟨e.1,e.2⟩)

def candidate {Q : Nat} (shape : SpongefishSessionAdapter.Shape) (iv : Digest32)
    (digest : Digest32) (past : AnchoredMixedAttackerPrefix.History Q) : Frozen :=
  let prior := events past
  let ref := SpongefishCurrentPhysicalRootCapture.reference shape digest
  freeze (SpongefishCurrentPhysicalRootCapture.ordinaryLog
    ((SpongefishCurrentPhysicalRootCapture.firstPrefix shape iv ref prior).getD prior))
    digest (SpongefishCurrentPhysicalRootCapture.physicalShape shape)

/-- Preparation consults only the literal earliest completed prefix. -/
def prepare {p : Profile} {Q : Nat} {iv : Digest32}
    (shape : SpongefishSessionAdapter.Shape) (supported : Supported p shape)
    (past : AnchoredMixedAttackerPrefix.History Q) (packet : Packet p Q iv shape) :
    AnchoredFiatShamirSecurity.PreAnchor p :=
  ⟨shape.lanes,(candidate shape iv (root shape packet) past).raw,
    ⟨supported.valid.2.2.2.2.1,by
      rw [← supported.batch]
      exact supported.valid.2.2.2.2.2⟩⟩

def policy {p : Profile} {Q : Nat} {iv : Digest32}
    (shape : SpongefishSessionAdapter.Shape) (supported : Supported p shape)
    (advertise : AnchoredMixedAttackerPrefix.History Q → Packet p Q iv shape →
      Joint (config p).logN → E) :
    AnchoredMixedAttackerPrefix.Grouped.Policy p Q iv (accept shape) :=
  ⟨prepare shape supported,advertise⟩

theorem candidate_before_every_reply {Q : Nat}
    (shape : SpongefishSessionAdapter.Shape) (iv digest : Digest32)
    (past : AnchoredMixedAttackerPrefix.History Q)
    (key : PublicCompressionCouplingMixed.Key Q) (answer : Digest32)
    (later : List (SpongefishCurrentPhysicalRootCapture.Event Q))
    (mention : SpongefishCurrentPhysicalRootCapture.reference shape digest ∈
      SpongefishCurrentPhysicalRootCapture.addresses shape iv key) :
    SpongefishCurrentPhysicalRootCapture.capture shape iv
      (SpongefishCurrentPhysicalRootCapture.reference shape digest)
      (events past ++ ⟨key,answer⟩ :: later) = some (candidate shape iv digest past) :=
  SpongefishCurrentPhysicalRootCapture.current_capture shape iv _ _ _ _ mention

theorem candidate_strict {Q : Nat} (shape : SpongefishSessionAdapter.Shape)
    (iv digest : Digest32) (past : AnchoredMixedAttackerPrefix.History Q) :
    ((SpongefishCurrentPhysicalRootCapture.firstPrefix shape iv
      (SpongefishCurrentPhysicalRootCapture.reference shape digest) (events past)).getD
      (events past)).length < (events past).length+1 :=
  SpongefishCurrentPhysicalRootCapture.current_reply_strict shape iv _ _

theorem repeated_physical_reference {Q : Nat} (shape : SpongefishSessionAdapter.Shape)
    (iv : Digest32) (ref : PCSBCSSourceRootReferences.Reference)
    (prior later : List (SpongefishCurrentPhysicalRootCapture.Event Q)) (frozen : Frozen)
    (found : SpongefishCurrentPhysicalRootCapture.capture shape iv ref prior = some frozen) :
    SpongefishCurrentPhysicalRootCapture.capture shape iv ref (prior ++ later) = some frozen :=
  SpongefishCurrentPhysicalRootCapture.capture_extension shape iv ref prior later frozen found

/-- The nonempty raw32 root read resets the consumed cursor. -/
private theorem header_consumed (c : DuplexRefinement.Compression)
    (cur header : SpongefishPCSRoundFrames.Cursor) (shape : SpongefishSessionAdapter.Shape)
    (digest : Digest32)
    (readHeader : SpongefishCurrentAnchorHeader.readHeader c cur shape = some (header,digest)) :
    header.pending.consumed = 0 := by
  unfold SpongefishCurrentAnchorHeader.readHeader at readHeader
  split at readHeader
  · contradiction
  · obtain ⟨middle,_,last⟩ := Option.bind_eq_some_iff.mp readHeader
    unfold SpongefishPCSRoundFrames.read at last
    obtain ⟨⟨value,rest⟩,_,equal⟩ := Option.bind_eq_some_iff.mp last
    have same := Option.some.inj equal
    have cursor := congrArg Prod.fst same
    dsimp only at cursor
    rw [← cursor]
    simp [SpongefishPCSRoundFrames.bind,SpongefishPCSRoundFrames.WireKind.codec,
      SpongefishPCSRoundFrames.Codec.bytes,SpongefishPCSRoundFrames.rootCodec]

/-- Every coordinate of the retained current E-vector is derived from its
literal consecutive raw32 construction replies. No `r.point = sampled` input. -/
theorem receive_point_coordinates {Q : Nat} (c : DuplexRefinement.Compression)
    (iv : Digest32) (cur next : SpongefishPCSRoundFrames.Cursor)
    (shape : SpongefishSessionAdapter.Shape) (r : SpongefishSessionAdapter.Record)
    (accepted : SpongefishCurrentCommitmentReceive.receive c cur shape = some (next,r))
    (represented : SpongefishPCSRoundFrames.RepresentsCurrent c iv cur.pending cur.state)
    (framed : SpongefishCurrentModeQueries.FrameDomain cur.pending)
    (bounded : ∀ (header : SpongefishPCSRoundFrames.Cursor),
      SpongefishCurrentAnchorHeader.readHeader c cur shape = some (header,r.root) →
      ∀ i : Fin (blockCount shape.logN),
        pathCost (SpongefishCurrentModeQueries.coordinate header.pending i.val) ≤ Q) :
    ∃ header, ∃ point : Fin shape.logN → E,
      SpongefishCurrentAnchorHeader.readHeader c cur shape = some (header,r.root) ∧
      r.point = List.ofFn point ∧
      point = AnchoredFiatShamirSecurityCodec.point shape.logN (fun i =>
        DuplexRefinement.evalCoordinate c iv
          (SpongefishCurrentModeQueries.coordinate header.pending i.val)) := by
  obtain ⟨header,sampled,bytes,pt,readHeader,encoded,pointEq,readValue,squeezed,source⟩ :=
    SpongefishCurrentCommitmentReceive.receive_anchor_source (Q := Q) c iv cur next shape r
      accepted represented framed
  refine ⟨header,pt,readHeader,pointEq,?_⟩
  have reset := header_consumed c cur header shape r.root readHeader
  funext j
  rw [AnchoredFiatShamirSecurityCodec.point_bytes]
  have byte (i : Fin 24) :
      ByteCodec.encodeE (pt j) i =
        DuplexRefinement.evalCoordinate c iv
          (SpongefishCurrentModeQueries.coordinate header.pending ((24*j.val+i.val)/32))
          ⟨(24*j.val+i.val)%32,Nat.mod_lt _ (by decide)⟩ := by
    have within : 24*j.val+i.val < 24*shape.logN := by have := j.isLt; have := i.isLt; omega
    have block : (24*j.val+i.val)/32 < blockCount shape.logN := by
      have := block_capacity shape.logN
      omega
    have work := bounded header readHeader ⟨(24*j.val+i.val)/32,block⟩
    have actual := (source (24*j.val+i.val) within (by simpa [reset] using work)).2.2
    have div : (j.val*24+i.val)/24 = j.val := by have := i.isLt; omega
    have mod : i.val%24 = i.val := Nat.mod_eq_of_lt i.isLt
    simpa [encoded,SpongefishPCSRoundFrames.Codec.bytes,SpongefishPCSRoundFrames.vectorCodec,
      SpongefishPCSRoundFrames.vectorEncode,reset,Nat.mul_comm,div,mod] using actual
  have chunk : (fun i : Fin 24 =>
    DuplexRefinement.evalCoordinate c iv
      (SpongefishCurrentModeQueries.coordinate header.pending ((24*j.val+i.val)/32))
      ⟨(24*j.val+i.val)%32,Nat.mod_lt _ (by decide)⟩) =
    ByteCodec.encodeE (pt j) := funext (fun i => (byte i).symm)
  rw [chunk]
  exact (ByteCodec.decodeE_encodeE (pt j)).symm

noncomputable local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Exact finite raw-table point law for consecutive full raw32 replies. The
generic joint equivalence also retains all residual bytes and outside keys. -/
theorem current_joint_point_law {Q dimension : Nat} {iv : Digest32}
    (shape : SpongefishSessionAdapter.Shape)
    (packet : AnchoredByteStreamCausal.Packet Q dimension iv (accept shape))
    (payoff : (Fin dimension → E) → ℚ) :
    average (fun table : RawKey Q → Digest32 =>
      payoff (AnchoredFiatShamirSecurityCodec.point dimension (fun i => table (key packet.val i)))) =
      average payoff := by
  have law := RawOracleCoupling.average_equiv (rawParts packet.val)
    (fun parts => payoff (AnchoredFiatShamirSecurityCodec.point dimension parts.1))
  have product := WHIRObservableSecurity.average_product
    (fun parts : Blocks dimension × (Outside packet.val → Digest32) =>
      payoff (AnchoredFiatShamirSecurityCodec.point dimension parts.1))
  have reduced : average (fun parts : Blocks dimension × (Outside packet.val → Digest32) =>
      payoff (AnchoredFiatShamirSecurityCodec.point dimension parts.1)) =
      average (fun blocks : Blocks dimension => payoff (AnchoredFiatShamirSecurityCodec.point dimension blocks)) := by
    simpa only [average_const] using product
  have vector := RawOracleCoupling.average_equiv (vectorParts dimension)
    (fun answer => payoff answer.1)
  have vectorProduct := WHIRObservableSecurity.average_product
    (fun answer : Joint dimension => payoff answer.1)
  have vectorReduced : average (fun answer : Joint dimension => payoff answer.1) = average payoff := by
    simpa only [average_const] using vectorProduct
  exact law.trans (reduced.trans (vector.trans vectorReduced))


/-- Adaptive prequeries are covered by the same exact whole-run memo coupling,
not a freshness premise at the later native draw. Preparation uses the earliest
physical root snapshot even if that root was mentioned outside this packet. -/
theorem current_aggregate_ambiguity {p : Profile} {Q n : Nat} {iv : Digest32} {R : Type}
    (shape : SpongefishSessionAdapter.Shape) (supported : Supported p shape)
    (advertise : AnchoredMixedAttackerPrefix.History Q → Packet p Q iv shape →
      Joint (config p).logN → E)
    (source : Sampling (PublicCompressionCouplingMixed.Key Q) (fun _ => Digest32) R n) :
    Soundness.uniformProb (Finset.univ.filter fun table : PublicCompressionCouplingMixed.Key Q → Digest32 =>
      AnchoredFiatShamirSecurity.Dirty
        (AnchoredMixedAttackerPrefix.Grouped.execution (policy shape supported advertise) source table).1.2) ≤
      (n : ℚ)/2^124 :=
  AnchoredMixedAttackerPrefix.Grouped.prepared_raw_table_ambiguity (policy shape supported advertise) source

/-- Exact adaptive distribution, including prequeries, complete public source
answers, immutable records and memoized full block vectors. Freshness belongs
at first contact with the vector, not at a subsequent native draw. -/
theorem current_adaptive_distribution {p : Profile} {Q n : Nat} {iv : Digest32} {R : Type}
    (shape : SpongefishSessionAdapter.Shape) (supported : Supported p shape)
    (advertise : AnchoredMixedAttackerPrefix.History Q → Packet p Q iv shape →
      Joint (config p).logN → E)
    (source : Sampling (PublicCompressionCouplingMixed.Key Q) (fun _ => Digest32) R n)
    (payoff : (R × AnchoredMixedAttackerPrefix.Grouped.Records
      (p := p) (Q := Q) (iv := iv) (accept := accept shape)) ×
      AnchoredMixedAttackerPrefix.Grouped.GroupCache
        (p := p) (Q := Q) (iv := iv) (accept := accept shape) → ℚ) :
    average (fun table : PublicCompressionCouplingMixed.Key Q → Digest32 =>
      payoff (AnchoredMixedAttackerPrefix.Grouped.execution (policy shape supported advertise) source table)) =
    Sampling.expectation payoff (RawOracleCoupling.memo
      (AnchoredMixedAttackerPrefix.Grouped.compile (policy shape supported advertise) source [] [])
      (fun _ => none)) :=
  AnchoredMixedAttackerPrefix.Grouped.prepared_full_distribution (policy shape supported advertise) source payoff


/-- Entire actual source View, including failed callbacks and all full answers,
is unchanged by the mathematical observer. -/
theorem current_source_view {p : Profile} {Q : Nat} {iv : Digest32} {R : Type}
    (shape : SpongefishSessionAdapter.Shape) (supported : Supported p shape)
    (advertise : AnchoredMixedAttackerPrefix.History Q → Packet p Q iv shape →
      Joint (config p).logN → E)
    (C : PrimitiveOracle) (ro : RawKey Q → Digest32)
    (program : Program R) (remaining : Nat) (cap : remaining ≤ Q) (counted : Counts remaining program) :
    (AnchoredMixedAttackerPrefix.Grouped.execution (policy shape supported advertise)
      (PublicCompressionCouplingMixed.compile Q iv [] program remaining cap counted)
      (PublicCompressionCouplingMixed.oracle C ro)).1.1 =
      (runIdeal (DuplexPublicSimulator.simulator Q) ro iv ⟨C,[]⟩ program remaining cap counted).view := by
  rw [AnchoredMixedAttackerPrefix.Grouped.execution_result,PublicCompressionCouplingMixed.compile_actual]

/-- Physical source work, including rejected prefixes and repeated requests,
is charged by Counts; ideal raw lookup count is not substituted for it. -/
theorem current_all_source_work {Q : Nat} {iv : Digest32} {R : Type}
    (C : PrimitiveOracle) (ro : RawKey Q → Digest32) (program : Program R)
    (remaining : Nat) (cap : remaining ≤ Q) (counted : Counts remaining program) :
    let view := Sampling.eval (PublicCompressionCouplingMixed.oracle C ro)
      (PublicCompressionCouplingMixed.compile Q iv [] program remaining cap counted)
    AnchoredMixedAttackerPrefix.constructionRequests view.observations ≤
      AnchoredMixedAttackerPrefix.constructionWork view.observations ∧
    AnchoredMixedAttackerPrefix.primitiveRequests view.observations +
      AnchoredMixedAttackerPrefix.constructionWork view.observations ≤ remaining := by
  dsimp only
  rw [PublicCompressionCouplingMixed.compile_actual]
  refine ⟨AnchoredMixedAttackerPrefix.constructionRequests_le_work _,?_⟩
  rw [AnchoredMixedAttackerPrefix.work_decomposition]
  exact PublicCompressionCouplingMixed.runIdeal_viewCost Q C ro iv [] program remaining cap counted


theorem current_source_ambiguity {p : Profile} {Q : Nat} {iv : Digest32} {R : Type}
    (shape : SpongefishSessionAdapter.Shape) (supported : Supported p shape)
    (advertise : AnchoredMixedAttackerPrefix.History Q → Packet p Q iv shape →
      Joint (config p).logN → E)
    (program : Program R) (remaining : Nat) (cap : remaining ≤ Q) (counted : Counts remaining program) :
    Soundness.uniformProb (Finset.univ.filter fun table : PublicCompressionCouplingMixed.Key Q → Digest32 =>
      AnchoredFiatShamirSecurity.Dirty (AnchoredMixedAttackerPrefix.Grouped.execution
        (policy shape supported advertise)
        (PublicCompressionCouplingMixed.compile Q iv [] program remaining cap counted) table).1.2) ≤
      (remaining : ℚ)/2^124 := current_aggregate_ambiguity shape supported advertise _

/-- The literal mixed compile supplies its earliest-root prefix, not an
externally asserted first mention or root/table equality certificate. -/
theorem current_source_capture {Q : Nat} {R : Type}
    (shape : SpongefishSessionAdapter.Shape) (iv : Digest32)
    (ref : PCSBCSSourceRootReferences.Reference) (C : PrimitiveOracle) (ro : RawKey Q → Digest32)
    (program : Program R) (remaining : Nat) (cap : remaining ≤ Q) (counted : Counts remaining program) :
    let compiled := PublicCompressionCouplingMixed.compile Q iv [] program remaining cap counted
    SpongefishCurrentPhysicalRootCapture.publicCapture (B := Q) shape iv ref
      (Sampling.eval (PublicCompressionCouplingMixed.oracle C ro) compiled) =
      SpongefishCurrentPhysicalRootCapture.capture shape iv ref
        (Sampling.execute (PublicCompressionCouplingMixed.oracle C ro) compiled).2 :=
  SpongefishCurrentPhysicalRootCapture.publicCapture_source shape iv ref C ro program remaining cap counted

/-- Rejected attacker-prefix work is charged by the actual all-source Counts. -/
theorem initialized_prefix_ambiguity {p : Profile} {Q : Nat}
    (shape : SpongefishSessionAdapter.Shape) (supported : Supported p shape)
    (parameter : Digest32) (tag instanceBytes : List Byte)
    (prefixProgram : Program SpongefishCurrentInitializedMode.Input)
    (calls : List SpongefishPCSRoundFrames.Call) (A : Nat) (attacker : Counts A prefixProgram)
    (cap : A + SpongefishCurrentInitializedMode.budget tag instanceBytes calls ≤ Q)
    (advertise : AnchoredMixedAttackerPrefix.History Q → Packet p Q parameter shape →
      Joint (config p).logN → E) :
    Soundness.uniformProb (Finset.univ.filter fun table : PublicCompressionCouplingMixed.Key Q → Digest32 =>
      AnchoredFiatShamirSecurity.Dirty (AnchoredMixedAttackerPrefix.Grouped.execution
        (policy shape supported advertise)
        (PublicCompressionCouplingMixed.compile Q parameter []
          (SpongefishCurrentInitializedMode.afterPrefix parameter tag instanceBytes prefixProgram calls)
          (A+SpongefishCurrentInitializedMode.budget tag instanceBytes calls) cap
          (SpongefishCurrentInitializedMode.afterPrefix_counted parameter tag instanceBytes prefixProgram calls A attacker))
        table).1.2) ≤ ((A+SpongefishCurrentInitializedMode.budget tag instanceBytes calls : Nat) : ℚ)/2^124 :=
  current_source_ambiguity shape supported advertise _ _ cap _

/-- Existing capped list math applies without a caller-supplied list. -/
theorem candidate_list_bound {p : Profile} {Q : Nat} {iv : Digest32}
    (shape : SpongefishSessionAdapter.Shape) (supported : Supported p shape)
    (past : AnchoredMixedAttackerPrefix.History Q) (packet : Packet p Q iv shape) :
    (InitialCandidates.witnesses (config p) (prepare shape supported past packet).lanes
      (prepare shape supported past packet).root).card ≤ 2^32 :=
  InitialCandidates.production_witnesses_card p _ _

/-- The candidate is the fixed physical full-image/suffix extraction, with
the Profile's exact domain size; its list bound is not a shape certificate. -/
theorem candidate_geometry {p : Profile} {Q : Nat} {iv : Digest32}
    (shape : SpongefishSessionAdapter.Shape) (supported : Supported p shape)
    (past : AnchoredMixedAttackerPrefix.History Q) (packet : Packet p Q iv shape) :
    (prepare shape supported past packet).root.size =
      2^((config p).logN-(config p).folds[0]!+(config p).rates[0]!) ∧
    ∀ row ∈ (prepare shape supported past packet).root.toList, row.size = shape.lanes := by
  have rectangular := freeze_shape
    (SpongefishCurrentPhysicalRootCapture.ordinaryLog
      ((SpongefishCurrentPhysicalRootCapture.firstPrefix shape iv
        (SpongefishCurrentPhysicalRootCapture.reference shape (root shape packet)) (events past)).getD
          (events past)))
    (root shape packet) (SpongefishCurrentPhysicalRootCapture.physicalShape shape)
    (SpongefishCurrentPhysicalRootCapture.occupied_guard shape supported.valid).2.1
  simpa only [prepare,candidate,SpongefishCurrentPhysicalRootCapture.physicalShape,
    PCSBCSSourceRootReferences.initialShape,supported.dimension,supported.batch,supported.rate] using rectangular


/-- Source authenticity is derived from actual compile draws, including an
arbitrary independent raw table. Construction answers are never Merkle records. -/
theorem current_captured_authentic {Q : Nat} {R : Type}
    (shape : SpongefishSessionAdapter.Shape) (iv : Digest32)
    (ref : PCSBCSSourceRootReferences.Reference) (C : PrimitiveOracle) (ro : RawKey Q → Digest32)
    (program : Program R) (remaining : Nat) (cap : remaining ≤ Q) (counted : Counts remaining program)
    (frozen : Frozen)
    (found : SpongefishCurrentPhysicalRootCapture.publicCapture (B := Q) shape iv ref
      (Sampling.eval (PublicCompressionCouplingMixed.oracle C ro)
        (PublicCompressionCouplingMixed.compile Q iv [] program remaining cap counted)) = some frozen) :
    AuthenticLog C frozen.queryPrefix := by
  rw [current_source_capture] at found
  exact SpongefishCurrentPhysicalRootCapture.captured_source_authentic shape iv ref C ro _ frozen found

/-- The cache/source collision guard is a consequence of the SAME complete
physical trace alarm. This generic observer lemma has no historical parser. -/
theorem current_source_quiet {Q : Nat} {R : Type} (C : PrimitiveOracle)
    (iv : Digest32) (program : Program R) (remaining : Nat) (cap : remaining ≤ Q)
    (counted : Counts remaining program) (roots : PublicMerkleProbability.RootPolicy)
    (quiet : PublicMerkleProbability.traceAlarm roots []
      (PublicCompressionProgram.primitiveLog C iv program remaining counted) = false) :
    ¬ OutputCollision (PCSBCSMerkleSeedProjection.ordinaryObservations
      (Sampling.eval (PublicCompressionCouplingMixed.oracle C (WHIRRealSimulator.rawTable Q C))
        (PublicCompressionCouplingMixed.compile Q iv [] program remaining cap counted)).observations) :=
  AnchoredMixedAttackerPrefixObserver.ordinary_quiet_of_alarm C iv program remaining cap counted roots quiet

/-- Exact public/source capture equality above needs no collision charge.
For getter authentication the same physical alarm also covers fresh targets.
These are the existing monitor's explicit physical-boundary metadata: literal
prefix inclusion/saturation, root registration before answers, and evaluation
of opening plans. Establishing them for the native original accepted path is
not asserted by this interface. No frozen-root/table equality is an input. -/
theorem current_getter_of_alarm {R : Type}
    (C : PrimitiveOracle) (iv : Digest32) (program : Program R)
    (remaining : Nat) (counted : Counts remaining program)
    (roots : PublicMerkleProbability.RootPolicy) (grow : PublicMerkleProbability.RootsGrow roots)
    (shape : SpongefishSessionAdapter.Shape) (valid : shape.Valid) (digest : Digest32)
    (before after log : PublicLog)
    (splitTrace : PublicCompressionProgram.primitiveLog C iv program remaining counted = before ++ after)
    (included : ∀ e ∈ log, e ∈ before)
    (saturated : ∀ n d, (n,d) ∈ before → tag n = 0 → (n,d) ∈ log)
    (registered : digest ∈ roots before.reverse)
    (proof : MerkleTransport.PrunedMerklePaths) (queries : List Nat)
    (output : List MerkleTransport.RawPath)
    (accepted : proof.open (hash C) digest
      (2^(SpongefishCurrentPhysicalRootCapture.physicalShape shape).height) queries shape.lanes
      (SpongefishCurrentPhysicalRootCapture.physicalShape shape).leafWords = some output)
    (bounds : ∀ p ∈ output, ∀ bytes ∈ p.opening.inputs (MerkleTransport.hashing (hash C)),
      bytes.length < 2^56)
    (plans : ∀ p ∈ output, ∀ bytes ∈ p.opening.inputs (MerkleTransport.hashing (hash C)),
      ∀ e ∈ PublicMerkleLog.plan C bytes,
        e ∈ PublicCompressionProgram.primitiveLog C iv program remaining counted)
    (quiet : PublicMerkleProbability.traceAlarm roots []
      (PublicCompressionProgram.primitiveLog C iv program remaining counted) = false) :
    ∀ p ∈ output, ∃ row cell,
      row.length = shape.lanes ∧
      p.leafData = MerkleBinding.leafImage 0
        (SpongefishCurrentPhysicalRootCapture.physicalShape shape).leafWords row ∧
      (freeze log digest (SpongefishCurrentPhysicalRootCapture.physicalShape shape)).cells[p.leafIndex]? =
        some cell ∧
      cell.image = p.leafData.toArray ∧ cell.compact = row.toArray ∧
      cell.available = true ∧ cell.paddingValid = true := by
  have auth := PublicCompressionProgram.primitiveLog_authentic C iv program remaining counted
  have logAuth : AuthenticLog C log := by
    intro n d member
    apply auth n d
    rw [splitTrace]
    exact List.mem_append_left _ (included _ member)
  rcases SpongefishCurrentPhysicalRootCapture.opened_getter_or_bad C log logAuth shape valid
    digest proof queries output accepted (fun p hp bytes hb => by
      have small := bounds p hp bytes hb
      exact small.trans_le (by norm_num)) with good | bad
  · exact good
  · have alarm := PublicMerkleProbability.opening_alarm C roots grow _ auth
      ⟨before,after,log,digest,output,splitTrace,included,saturated,registered,bounds,plans,bad⟩
    rw [quiet] at alarm
    cases alarm

/-- Getter authentication for the actual computed current first-root capture.
The freeze/table equality is proved from capture, never supplied by a caller.
Only the physical monitor's boundary/plan metadata remains explicit. -/
theorem current_captured_getter {Q : Nat} {R : Type}
    (C : PrimitiveOracle) (ro : RawKey Q → Digest32) (iv : Digest32)
    (program : Program R) (remaining : Nat) (cap : remaining ≤ Q) (counted : Counts remaining program)
    (roots : PublicMerkleProbability.RootPolicy) (grow : PublicMerkleProbability.RootsGrow roots)
    (shape : SpongefishSessionAdapter.Shape) (valid : shape.Valid) (digest : Digest32)
    (frozen : Frozen)
    (found : SpongefishCurrentPhysicalRootCapture.publicCapture (B := Q) shape iv
      (SpongefishCurrentPhysicalRootCapture.reference shape digest)
      (Sampling.eval (PublicCompressionCouplingMixed.oracle C ro)
        (PublicCompressionCouplingMixed.compile Q iv [] program remaining cap counted)) = some frozen)
    (before after : PublicLog)
    (splitTrace : PublicCompressionProgram.primitiveLog C iv program remaining counted = before ++ after)
    (included : ∀ e ∈ frozen.queryPrefix, e ∈ before)
    (saturated : ∀ n d, (n,d) ∈ before → tag n = 0 → (n,d) ∈ frozen.queryPrefix)
    (registered : digest ∈ roots before.reverse)
    (proof : MerkleTransport.PrunedMerklePaths) (queries : List Nat)
    (output : List MerkleTransport.RawPath)
    (accepted : proof.open (hash C) digest
      (2^(SpongefishCurrentPhysicalRootCapture.physicalShape shape).height) queries shape.lanes
      (SpongefishCurrentPhysicalRootCapture.physicalShape shape).leafWords = some output)
    (bounds : ∀ p ∈ output, ∀ bytes ∈ p.opening.inputs (MerkleTransport.hashing (hash C)),
      bytes.length < 2^56)
    (plans : ∀ p ∈ output, ∀ bytes ∈ p.opening.inputs (MerkleTransport.hashing (hash C)),
      ∀ e ∈ PublicMerkleLog.plan C bytes,
        e ∈ PublicCompressionProgram.primitiveLog C iv program remaining counted)
    (quiet : PublicMerkleProbability.traceAlarm roots []
      (PublicCompressionProgram.primitiveLog C iv program remaining counted) = false) :
    ∀ p ∈ output, ∃ row cell,
      row.length = shape.lanes ∧
      p.leafData = MerkleBinding.leafImage 0
        (SpongefishCurrentPhysicalRootCapture.physicalShape shape).leafWords row ∧
      frozen.cells[p.leafIndex]? = some cell ∧
      cell.image = p.leafData.toArray ∧ cell.compact = row.toArray ∧
      cell.available = true ∧ cell.paddingValid = true := by
  rw [current_source_capture] at found
  obtain ⟨prior,event,later,_,_,_,literal,_,_⟩ :=
    SpongefishCurrentPhysicalRootCapture.capture_provenance shape iv _ _ frozen found
  have fixed : frozen = freeze frozen.queryPrefix digest
      (SpongefishCurrentPhysicalRootCapture.physicalShape shape) := by
    rw [literal]
    rfl
  have good := current_getter_of_alarm C iv program remaining counted roots grow shape valid digest
    before after frozen.queryPrefix splitTrace included saturated registered proof queries output
    accepted bounds plans quiet
  intro p member
  obtain ⟨row,cell,width,image,lookup,full,compact,available,padding⟩ := good p member
  refine ⟨row,cell,width,image,?_,full,compact,available,padding⟩
  rw [fixed]
  exact lookup


#print axioms packet_key_member
#print axioms candidate_before_every_reply
#print axioms candidate_strict
#print axioms repeated_physical_reference
#print axioms receive_point_coordinates
#print axioms current_joint_point_law
#print axioms current_aggregate_ambiguity
#print axioms current_source_view
#print axioms current_source_ambiguity
#print axioms current_source_capture
#print axioms initialized_prefix_ambiguity
#print axioms candidate_list_bound
#print axioms current_captured_authentic
#print axioms current_source_quiet
#print axioms current_getter_of_alarm
#print axioms current_captured_getter
#print axioms current_adaptive_distribution
#print axioms current_all_source_work
#print axioms candidate_geometry

end Whir.SpongefishCurrentAnchorAttackerPrefix
