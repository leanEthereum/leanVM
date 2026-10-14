import Whir.PCSBCSNativeCapturedOracles
import Whir.PCSBCSNativeCapturedTape
import Whir.PCSBCSNativeSourceOriginal

/-! Historical native captured-prefix reply joins. The next-root getter below
uses the very same first-address log as source inversion. It never identifies
an earlier capture with a later physical Merkle registry. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
namespace Whir.PCSBCSNativeCapturedReplyTransport
open Concrete Protocol FiatShamirGame DuplexModeGame TypedOracleCompiler
open MerkleTransport MerkleTransport.Commitments PublicMerkleLog
open WHIRPhysicalVerifier WHIRPhysicalReplay AnchoredPhysicalDriver
open PCSBCSSourceRootReferences PCSBCSMerkleRootCache
open PCSBCSCapturedNativeReplyBridge PCSBCSCapturedNativePhaseQuery
open PCSBCSSourceFrozenAccessor PCSBCSFrozenOracleRows

/-- Actual physical root-role lookup implies source phase parsing at that
literal packet, including partially occupied initial shapes. -/
theorem phaseReference_of_roles {ctx : RawWHIRKeys.Context} {Q : Nat}
    {p : ParameterBounds.Profile} (saved : AnchoredHeaderCodec.Record)
    (packet : RawWHIRKeys.Packet ctx Q) (state : WireState p)
    (valid : saved.Valid) (profile : profileShape p saved.shape)
    (roles : PCSBCSNativeRootRoles.RootRoles saved packet state)
    (level : Nat) (root : Digest32) (found : state.roots[level]? = some root) :
    phaseReference (ParameterBounds.config p) saved packet.val.messages level =
      some ⟨root,PCSBCSNativeRootRoles.nativeShape p saved level⟩ := by
  have indexed :
      (PCSBCSNativeRootRoles.nativeReferences p saved state.roots)[level]? =
        some ⟨root,PCSBCSNativeRootRoles.nativeShape p saved level⟩ := by
    simp [PCSBCSNativeRootRoles.nativeReferences, List.getElem?_map,
      List.getElem?_zipIdx, found]
  rw [roles.references] at indexed
  cases level with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at indexed
    rw [← indexed]
    simp only [phaseReference, ↓reduceIte, parseInitial_roundtrip saved valid]
    exact ite_eq_left profile
  | succ level =>
    simp only [List.getElem?_cons_succ] at indexed
    have shape : PCSBCSNativeRootRoles.nativeShape p saved (level+1) =
        phaseShape (ParameterBounds.config p) (level+1) := by
      simp [PCSBCSNativeRootRoles.nativeShape]
    simp only [phaseReference, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
      ↓reduceIte, roles.admitted, Nat.add_sub_cancel, indexed]
    simp [shape, sameShape]

/-- Each retained query has the reference of its own chronological input
packet, not the root-role list of a later packet. -/
def QueryRoles {p : ParameterBounds.Profile} (saved : AnchoredHeaderCodec.Record)
    (messages : List WHIRHistory.Pending) (state : WireState p) : Prop :=
  ∀ opening ∈ state.openings,
    CausalProbability.position (.query opening.level : CausalProbability.Coordinate
      (ParameterBounds.config p)) < messages.length ∧
    phaseReference (ParameterBounds.config p) saved
      (messages.reverse.take (CausalProbability.position (.query opening.level :
        CausalProbability.Coordinate (ParameterBounds.config p))+1)).reverse opening.level.val =
      some (PCSBCSNativeRootRoles.openingRole saved opening)

theorem QueryRoles.cons {p : ParameterBounds.Profile} {saved : AnchoredHeaderCodec.Record}
    {messages : List WHIRHistory.Pending} {state : WireState p}
    (roles : QueryRoles saved messages state) (m : WHIRHistory.Pending) :
    QueryRoles saved (m::messages) state := by
  intro opening member
  obtain ⟨bound,reference⟩ := roles opening member
  refine ⟨by simpa only [List.length_cons] using Nat.lt_succ_of_lt bound, ?_⟩
  have count : CausalProbability.position (.query opening.level :
      CausalProbability.Coordinate (ParameterBounds.config p))+1 ≤ messages.reverse.length := by
    simpa only [List.length_reverse] using Nat.succ_le_of_lt bound
  simpa only [List.reverse_cons, List.take_append, Nat.sub_eq_zero_of_le count,
    List.take_zero, List.append_nil] using reference

theorem takeSample_queryRoles {ctx : RawWHIRKeys.Context} {Q : Nat}
    {p : ParameterBounds.Profile} (saved : AnchoredHeaderCodec.Record)
    (packet : RawWHIRKeys.Packet ctx Q) (proofs : Array PrunedMerklePaths)
    (state out : WireState p)
    (q : CausalProbability.Coordinate (ParameterBounds.config p)) (x : StackWHIRReplay.Sample q)
    (trace : List Observation) (run : PublicMerkleProgram.Runs
      (takeSample saved.shape.lanes proofs state q x) trace (some out))
    (valid : saved.Valid) (profile : profileShape p saved.shape)
    (position : CausalProbability.position q+1 = packet.val.messages.length)
    (prior : QueryRoles saved packet.val.messages state)
    (roles : PCSBCSNativeRootRoles.RootRoles saved packet out) :
    QueryRoles saved packet.val.messages out := by
  cases q with
  | query i =>
    simp only [takeSample] at run
    split at run
    · cases hp : proofs[i.val]? <;> cases hr : state.roots[i.val]?
      · simp only [hp,hr] at run; cases run
      · simp only [hp,hr] at run; cases run
      · simp only [hp,hr] at run; cases run
      · simp only [hp,hr] at run
        obtain ⟨before,opened,after,_,_,continued⟩ := (PublicMerkleProgram.Runs.bind_iff _ _).mp run
        cases opened with
        | none => cases continued
        | some opened =>
          cases continued
          intro opening member
          rcases List.mem_cons.mp member with rfl | member
          · refine ⟨by dsimp only; omega, ?_⟩
            have full : (packet.val.messages.reverse.take
                (CausalProbability.position (.query i :
                  CausalProbability.Coordinate (ParameterBounds.config p))+1)).reverse =
                packet.val.messages := by
              rw [position]
              rw [← List.length_reverse (as := packet.val.messages), List.take_length, List.reverse_reverse]
            rw [full]
            exact phaseReference_of_roles saved packet _ valid profile roles i.val _ hr
          · exact prior opening member
    · cases run
  | initial => cases run; exact prior
  | fold i j => cases run; exact prior
  | ood i j => cases run; exact prior
  | tail j => cases run; exact prior

theorem step_queryRoles {ctx : RawWHIRKeys.Context} {stack : ctx.mode = .stack} {Q : Nat}
    {p : ParameterBounds.Profile} (saved : AnchoredHeaderCodec.Record)
    {proofs : Array PrunedMerklePaths} {packet : RawWHIRKeys.Packet ctx Q}
    {profile : packet.val.profile = p} {state out : WireState p}
    {raw : RawOracleCoupling.Concrete.GroupAnswer ctx Q (.inl packet)}
    (step : Step ctx stack Q p saved.shape.lanes proofs packet profile state raw out)
    (valid : saved.Valid) (geometry : profileShape p saved.shape)
    (prior : QueryRoles saved packet.val.messages state)
    (roles : PCSBCSNativeRootRoles.RootRoles saved packet out) :
    QueryRoles saved packet.val.messages out := by
  cases step with
  | run parsed size shape boundNonce accepted opened =>
    have absorbOpenings := PCSBCSNativeRootRoles.absorbResponse_openings _ _ _ _ parsed
    have nonceOpenings := (PCSBCSNativeRootRoles.afterNonce_roots _ _ _ boundNonce).2
    apply takeSample_queryRoles saved packet _ _ _ _ _ _ opened valid geometry
    · have positive := List.length_pos_iff.mpr packet.property.2.1
      have atPosition := packetQuery_position ctx Q p packet profile
      omega
    · intro opening member
      rw [nonceOpenings,absorbOpenings] at member
      exact prior opening member
    · exact ⟨roles.count,roles.references,roles.admitted,roles.openings⟩

/-- Native execution derives every query's prefix reference, including the
initial partial occupancy and all full extension phases. -/
theorem trace_queryRoles {ctx : RawWHIRKeys.Context} {stack : ctx.mode = .stack} {Q : Nat}
    {p : ParameterBounds.Profile} (saved : AnchoredHeaderCodec.Record)
    {proofs : Array PrunedMerklePaths} {packet : RawWHIRKeys.Packet ctx Q}
    {packets : List (RawWHIRKeys.Packet ctx Q)} {out : WireState p} {history}
    (valid : saved.Valid) (profile : profileShape p saved.shape)
    (chain : Chain ctx Q packet packets)
    (trace : Trace ctx stack Q p saved.shape.lanes proofs packets
      (initialWireState p saved.root) out history) :
    QueryRoles saved packet.val.messages out := by
  induction chain generalizing out history with
  | initial packet single =>
    cases trace with
    | cons packetProfile step rest =>
      cases rest
      apply step_queryRoles saved step valid profile
      · intro opening member
        cases member
      · exact PCSBCSNativeRootRoles.roles_initial saved single step
  | next m prior messages statement packetProfile ih =>
    obtain ⟨middle,before,after,hist,first,last⟩ := Trace.append_inv _ _ trace
    cases last with
    | cons finalProfile step rest =>
      cases rest
      apply step_queryRoles saved step valid profile
      · rw [messages]
        exact (ih first).cons m
      · exact PCSBCSNativeRootRoles.roles_next saved m messages
          (trace_completed saved.root prior first)
          (PCSBCSNativeRootRoles.trace_rootRoles saved prior first) step

/-- The one tape input consists of actual whole construction-packet answers.
The current answer is never read when reconstructing its incoming prefix. -/
theorem strictPrefix_of_raws {p : ParameterBounds.Profile} {Q : Nat}
    {iv : Digest32} {boundary : Nat}
    (final current : PCSBCSChallengeOracle.EnteredPacket p Q iv boundary)
    (member : current ∈ PCSBCSCapturedSourceStatePath.packets final)
    (table : PCSBCSSourcePacketTape.Table (p := p) (Q := Q) (iv := iv) (boundary := boundary))
    (ring : RingPCSGame.Prefix) (tape : CausalGame.Tape (ParameterBounds.config p))
    (raws : ∀ packet ∈ PCSBCSCapturedSourceStatePath.packets final,
      PCSBCSChallengeOracle.grouped packet.2.coord (table (.inl packet)) =
        PCSBCSRestorationHazard.literalRaw ring tape packet.2.coord) :
    PCSBCSSourcePacketTape.strictPrefix current (fun key => table key.val) =
      WHIRFiatShamir.Prefix.ofTape current.2.coord tape := by
  funext q earlier
  change PCSBCSSourcePacketTape.project q
    (PCSBCSChallengeOracle.grouped q (table (.inl (current.predecessor ⟨q,earlier⟩)))) =
      CausalProbability.get q tape
  have raw := raws _ (PCSBCSCapturedSourceStatePath.predecessor_mem_packets final current member ⟨q,earlier⟩)
  change PCSBCSChallengeOracle.grouped q _ = PCSBCSRestorationHazard.literalRaw ring tape q at raw
  rw [raw]
  cases q <;> rfl

theorem packets_query_prefix {p : ParameterBounds.Profile} {Q : Nat}
    {iv : Digest32} {boundary : Nat}
    (final current : PCSBCSChallengeOracle.EnteredPacket p Q iv boundary)
    (member : current ∈ PCSBCSCapturedSourceStatePath.packets final)
    (q : CausalProbability.Coordinate (ParameterBounds.config p))
    (earlier : CausalProbability.position q < CausalProbability.position current.2.coord) :
    current.2.messages.reverse.take (CausalProbability.position q+1) =
      final.2.messages.reverse.take (CausalProbability.position q+1) := by
  obtain ⟨r,_,equal⟩ := List.mem_map.mp member
  subst current
  by_cases before : CausalProbability.position r < CausalProbability.position final.2.coord
  · have same : PCSBCSCapturedSourceStatePath.packetAt final r = final.predecessor ⟨r,before⟩ :=
      dite_eq_left before
    rw [same] at earlier ⊢
    change (final.2.messages.drop
      (CausalProbability.position final.2.coord-CausalProbability.position r)).reverse.take
        (CausalProbability.position q+1) = _
    rw [List.reverse_drop, List.take_take]
    have size := PCSBCSChallengeOracle.CanonicalPacket.messages_length final.2
    have limit : CausalProbability.position q+1 ≤ final.2.messages.length -
        (CausalProbability.position final.2.coord-CausalProbability.position r) := by
      change CausalProbability.position q < CausalProbability.position r at earlier
      omega
    rw [Nat.min_eq_left limit]
  · rw [show PCSBCSCapturedSourceStatePath.packetAt final r = final from dite_eq_right before]

/-- Successful physical-history parsing, retaining only the fields used by
the strict chronological reply transport. This is derived from the decoder. -/
inductive Parses (p : ParameterBounds.Profile) (catalog : WHIRReplay.Catalog p)
    (roots : WHIRReplay.Roots) (rows : WHIRPhysicalHistory.Rows) (statement : Digest32) :
    List WHIRHistory.Pending →
      List (WHIRHistory.Pending × Sigma (@CausalProbability.Sample (ParameterBounds.config p))) →
      WHIRReplay.Replay p → Prop where
  | initial {m input} :
      Parses p catalog roots rows statement [m] [] ⟨input,WHIRReplay.zeroTape p,#[]⟩
  | next {m previous older past q x before response}
      (prior : Parses p catalog roots rows statement (previous::older) past before)
      (position : CausalProbability.position q = older.length)
      (parsed : WHIRPhysicalHistory.reply roots rows q m = some response) :
      Parses p catalog roots rows statement (m::previous::older) ((previous,⟨q,x⟩)::past)
        ⟨before.statement,CausalProbability.set q before.tape x,before.replies.push response⟩

theorem parses_of_decode (p : ParameterBounds.Profile) (catalog : WHIRReplay.Catalog p)
    (roots : WHIRReplay.Roots) (rows : WHIRPhysicalHistory.Rows) (statement : Digest32)
    (messages : List WHIRHistory.Pending)
    (ancestors : List (WHIRHistory.Pending × Sigma (@CausalProbability.Sample (ParameterBounds.config p))))
    (out : WHIRReplay.Replay p)
    (decoded : WHIRPhysicalHistory.decodeHistory p catalog roots rows statement messages ancestors = some out) :
    Parses p catalog roots rows statement messages ancestors out := by
  induction messages generalizing ancestors out with
  | nil => cases decoded
  | cons m messages ih =>
    cases messages with
    | nil =>
      cases ancestors with
      | cons entry rest => cases decoded
      | nil =>
        simp only [WHIRPhysicalHistory.decodeHistory] at decoded
        split at decoded
        · cases found : catalog statement with
          | none => simp [found] at decoded
          | some input =>
            simp [found] at decoded
            subst out
            exact .initial
        · cases decoded
    | cons previous older =>
      cases ancestors with
      | nil => cases decoded
      | cons entry past =>
        rcases entry with ⟨previous',q,x⟩
        simp only [WHIRPhysicalHistory.decodeHistory] at decoded
        split at decoded
        · rename_i same
          subst previous'
          split at decoded
          · split at decoded
            · rename_i atPosition
              split at decoded
              · split at decoded
                · cases prior : WHIRPhysicalHistory.decodeHistory p catalog roots rows statement
                      (previous::older) past with
                  | none => simp [prior] at decoded
                  | some before =>
                    simp only [prior,WHIRPhysicalHistory.step] at decoded
                    obtain ⟨response,parsed,equal⟩ := Option.map_eq_some_iff.mp decoded
                    subst out
                    exact .next (ih past before prior) atPosition parsed
                · cases decoded
              · cases decoded
            · cases decoded
          · cases decoded
        · cases decoded

theorem Parses.size {p : ParameterBounds.Profile} {catalog : WHIRReplay.Catalog p}
    {roots : WHIRReplay.Roots} {rows : WHIRPhysicalHistory.Rows} {statement messages ancestors out}
    (parsed : Parses p catalog roots rows statement messages ancestors out) :
    out.replies.size = messages.length-1 := by
  induction parsed with
  | initial => rfl
  | next prior position decoded ih =>
    simp only [Array.size_push,List.length_cons] at ih ⊢
    omega

theorem Parses.replyAt {p : ParameterBounds.Profile} {catalog : WHIRReplay.Catalog p}
    {roots : WHIRReplay.Roots} {rows : WHIRPhysicalHistory.Rows} {statement messages ancestors out}
    (parsed : Parses p catalog roots rows statement messages ancestors out)
    (j : Nat) (earlier : j < out.replies.size) :
    ∃ q m previous x,
      (WHIRHistory.schedule (ParameterBounds.config p))[j]? = some q ∧
      messages.reverse[j+1]? = some m ∧
      WHIRPhysicalHistory.reply roots rows q m = some out.replies[j]! ∧
      (previous,⟨q,x⟩) ∈ ancestors := by
  induction parsed generalizing j with
  | initial => simp only [Array.size_empty] at earlier; omega
  | @next m previous older past q x before response prior position decoded ih =>
    have size := prior.size
    simp only [List.length_cons,Nat.add_sub_cancel] at size
    by_cases last : j = before.replies.size
    · subst j
      have atPosition : CausalProbability.position q = before.replies.size := position.trans size.symm
      refine ⟨q,m,previous,x,?_,?_,?_,List.mem_cons_self⟩
      · rw [← atPosition]
        exact WHIRHistory.schedule_get_position q
      · rw [size]
        simp [List.reverse_cons]
      · simpa only [getElem!_pos (before.replies.push response) before.replies.size
          (by simp),Array.getElem_push_eq] using decoded
    · have bound : j < before.replies.size := by simp only [Array.size_push] at earlier; omega
      obtain ⟨coordinate,message,old,sample,scheduled,atMessage,atReply,inPast⟩ := ih j bound
      refine ⟨coordinate,message,old,sample,scheduled,?_,?_,List.mem_cons_of_mem _ inPast⟩
      · rw [List.reverse_cons,List.getElem?_append_left (by
          simp only [List.length_reverse,List.length_cons]
          omega)]
        exact atMessage
      · have atIndex : (before.replies.push response)[j]! = before.replies[j]! := by
          rw [getElem!_pos _ j (by simp; omega),getElem!_pos _ j bound,Array.getElem_push_lt bound]
        rw [atIndex]
        exact atReply

theorem packets_position_le {p : ParameterBounds.Profile} {Q : Nat}
    {iv : Digest32} {boundary : Nat}
    (final current : PCSBCSChallengeOracle.EnteredPacket p Q iv boundary)
    (member : current ∈ PCSBCSCapturedSourceStatePath.packets final) :
    CausalProbability.position current.2.coord ≤ CausalProbability.position final.2.coord := by
  obtain ⟨q,_,equal⟩ := List.mem_map.mp member
  subst current
  by_cases earlier : CausalProbability.position q < CausalProbability.position final.2.coord
  · rw [show PCSBCSCapturedSourceStatePath.packetAt final q = final.predecessor ⟨q,earlier⟩ from
      dite_eq_left earlier]
    exact Nat.le_of_lt earlier
  · rw [show PCSBCSCapturedSourceStatePath.packetAt final q = final from dite_eq_right earlier]

theorem packets_message_at {p : ParameterBounds.Profile} {Q : Nat}
    {iv : Digest32} {boundary : Nat}
    (final current : PCSBCSChallengeOracle.EnteredPacket p Q iv boundary)
    (member : current ∈ PCSBCSCapturedSourceStatePath.packets final)
    (j : Nat) (earlier : j < CausalProbability.position current.2.coord) :
    current.2.messages.reverse[j+1]? = final.2.messages.reverse[j+1]? := by
  obtain ⟨q,_,equal⟩ := List.mem_map.mp member
  subst current
  by_cases before : CausalProbability.position q < CausalProbability.position final.2.coord
  · have same : PCSBCSCapturedSourceStatePath.packetAt final q = final.predecessor ⟨q,before⟩ :=
      dite_eq_left before
    rw [same] at earlier ⊢
    change (final.2.messages.drop
      (CausalProbability.position final.2.coord-CausalProbability.position q)).reverse[j+1]? = _
    rw [List.reverse_drop,List.getElem?_take]
    have size := PCSBCSChallengeOracle.CanonicalPacket.messages_length final.2
    have bound : j+1 < final.2.messages.length -
        (CausalProbability.position final.2.coord-CausalProbability.position q) := by
      change j < CausalProbability.position q at earlier
      omega
    rw [ite_eq_left bound]
  · rw [show PCSBCSCapturedSourceStatePath.packetAt final q = final from dite_eq_right before]

section Driver
variable (cap : Nat) (model : WHIRCallerSupport.ProductionLayout)
    (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q : Nat)
    (packet : RawWHIRKeys.Packet ctx Q) (saved : AnchoredHeaderCodec.Record)
    (proofs : Array PrunedMerklePaths) (B : Nat)
    (limit : sourceBudget ctx Q packet ≤ B)
    (seed : DuplexPublicSimulator.Seed) (ro : RawKey B → Digest32)

noncomputable abbrev addresses :=
  PCSBCSCapturedSourceTransport.address (p := packet.val.profile) (Q := B) (iv := ctx.iv)
    (boundary := (RawWHIRKeys.entry ctx packet.val).frames.length)

noncomputable abbrev program :=
  PCSBCSCapturedIdealNativeAcceptance.allocationProgram cap model ctx stack Q packet saved proofs B limit

noncomputable abbrev table := PCSBCSCapturedIdealNativeAcceptance.table ctx Q packet B seed ro

/-- Ordinary authentication follows from the actual mixed table's seed summand,
including captures preceding root announcements. It is not a row-equality input. -/
theorem referenceLog_authentic (ref : Reference) :
    AuthenticLog seed (PCSBCSNativeCapturedRows.referenceLog cap model ctx stack Q packet saved proofs
      B limit seed ro ref) := by
  exact PCSBCSMerkleSeedProjection.sourceLog_authentic seed ro
    (addresses ctx Q packet B) ref
    (program cap model ctx stack Q packet saved proofs B limit)

/-- Parsed next roles have exactly the shape used by the captured root getter. -/
theorem next_log (i : Fin (ParameterBounds.config packet.val.profile).folds.size)
    (j : Fin (ParameterBounds.config packet.val.profile).folds[i.val]!)
    (m : WHIRHistory.Pending) (ref : Reference)
    (parsed : parsePhase (ParameterBounds.config packet.val.profile) (.fold i j) m (i.val+1) 2 = some ref) :
    PCSBCSNativeCapturedRows.referenceLog cap model ctx stack Q packet saved proofs B limit seed ro ref =
      PCSBCSNativeCapturedOracles.logFor cap model ctx stack Q packet saved proofs B limit seed ro
        ref.root (i.val+1) := by
  have shape := (parsePhase_admitted _ _ _ _ _ _ parsed).2.2.2
  unfold PCSBCSNativeCapturedOracles.logFor
  congr 1
  cases ref
  congr 1

/-- The full next table is the projection of the same literal captured prefix.
No later whole-cache equality is present, even as an intermediate hypothesis. -/
theorem next_projection (i : Fin (ParameterBounds.config packet.val.profile).folds.size)
    (j : Fin (ParameterBounds.config packet.val.profile).folds[i.val]!)
    (m : WHIRHistory.Pending) (ref : Reference)
    (parsed : parsePhase (ParameterBounds.config packet.val.profile) (.fold i j) m (i.val+1) 2 = some ref)
    (clean : ¬ OutputCollision (PCSBCSNativeCapturedRows.referenceLog cap model ctx stack Q packet saved
      proofs B limit seed ro ref)) :
    extensionOracle (WHIRPhysicalRows.compactBaseOracle (hash seed)
      ⟨recordDomain (records (PCSBCSNativeCapturedRows.referenceLog cap model ctx stack Q packet saved
        proofs B limit seed ro ref)),[]⟩ ref.root ref.shape.height (2^ref.shape.height)
      ref.shape.leafWords ref.shape.occupied) =
      some (PCSBCSNativeCapturedOracles.roots cap model ctx stack Q packet saved proofs B limit seed ro
        ref.root (i.val+1)) := by
  have projection := (parsed_next_projection seed
    (PCSBCSNativeCapturedRows.referenceLog cap model ctx stack Q packet saved proofs B limit seed ro ref)
    packet.val.profile i j m ref parsed
    (referenceLog_authentic cap model ctx stack Q packet saved proofs B limit seed ro ref) clean).1
  rw [next_log cap model ctx stack Q packet saved proofs B limit seed ro i j m ref parsed] at projection ⊢
  simpa only [PCSBCSNativeCapturedOracles.roots, frozenQueryOracle, Nat.add_eq_zero_iff,
    Nat.one_ne_zero, and_false, ↓reduceIte] using projection

/-- A real native opening against its parser-admitted reference supplies source
query evidence or the exact captured-prefix opening bad event used by BoundRows.
Neither full occupancy nor captured/native row equality is an input. -/
theorem query_evidence
    (current : CausalProbability.Coordinate (ParameterBounds.config packet.val.profile))
    (messages : List WHIRHistory.Pending) (past : WHIRFiatShamir.Prefix current)
    (m : WHIRHistory.Pending) (digest : Digest32)
    (i : Fin (ParameterBounds.config packet.val.profile).folds.size) (a : Message E)
    (earlier : CausalProbability.position (.query i : CausalProbability.Coordinate
      (ParameterBounds.config packet.val.profile)) < CausalProbability.position current)
    (ref : Reference)
    (reference : phaseReference (ParameterBounds.config packet.val.profile) saved
      (messages.reverse.take (CausalProbability.position (.query i : CausalProbability.Coordinate
        (ParameterBounds.config packet.val.profile))+1)).reverse i.val = some ref)
    (fits : saved.shape.lanes ≤ 2^(ParameterBounds.config packet.val.profile).folds[0]!)
    (proof : PrunedMerklePaths) (out : Opened)
    (accepted : (runReal seed ctx.iv
      (openQuery packet.val.profile i saved.shape.lanes proof ref.root (past (.query i) earlier))).view.result =
        some out) :
    SourceEvidence (addresses ctx Q packet B)
      (program cap model ctx stack Q packet saved proofs B limit) (table ctx Q packet B seed ro)
      seed current saved messages past m digest (.query i) (.query out.rows a) ∨
      PublicMerkleBinding.OpenPrimitiveBad seed
        (PCSBCSNativeCapturedRows.referenceLog cap model ctx stack Q packet saved proofs B limit seed ro ref)
        ref.root out.paths := by
  exact source_query_of_native (addresses ctx Q packet B)
    (program cap model ctx stack Q packet saved proofs B limit) (table ctx Q packet B seed ro)
    seed current saved messages past m digest i a earlier ref reference
    (referenceLog_authentic cap model ctx stack Q packet saved proofs B limit seed ro ref)
    fits proof out accepted
/-- Every actual accepted native query transports to every later literal
construction packet. Reference, authentication, sampled queries and semantic
rows are derived from the run. The sole tape premise is whole-packet raw
agreement; the bad alternative is the parent's exact openingLog event. -/
theorem mixed_success_query
    (a : Accepted ctx Q cap packet saved)
    (success : (AnchoredMixedIdealSourceAcceptance.mixedView cap .fresh model ctx stack Q packet saved
      proofs ctx.iv B limit seed ro).result.value = some a)
    (final current : PCSBCSChallengeOracle.EnteredPacket packet.val.profile B ctx.iv
      (RawWHIRKeys.entry ctx packet.val).frames.length)
    (messages : final.2.messages = packet.val.messages)
    (member : current ∈ PCSBCSCapturedSourceStatePath.packets final)
    (ring : RingPCSGame.Prefix)
    (raws : ∀ sourcePacket ∈ PCSBCSCapturedSourceStatePath.packets final,
      PCSBCSChallengeOracle.grouped sourcePacket.2.coord
        ((table ctx Q packet B seed ro) (.inl sourcePacket)) =
        PCSBCSRestorationHazard.literalRaw ring a.wire.tape sourcePacket.2.coord)
    (opening : QueryOpening packet.val.profile) (opened : opening ∈ a.wire.openings)
    (earlier : CausalProbability.position (.query opening.level :
      CausalProbability.Coordinate (ParameterBounds.config packet.val.profile)) <
        CausalProbability.position current.2.coord)
    (m : WHIRHistory.Pending) (digest : Digest32) (introMessage : Message E) :
    SourceEvidence (addresses ctx Q packet B)
      (program cap model ctx stack Q packet saved proofs B limit) (table ctx Q packet B seed ro)
      seed current.2.coord saved current.2.messages
      (PCSBCSSourcePacketTape.strictPrefix current (fun key => (table ctx Q packet B seed ro) key.val))
      m digest (.query opening.level) (.query opening.result.rows introMessage) ∨
      PublicMerkleBinding.OpenPrimitiveBad seed
        (PCSBCSNativeCapturedRows.openingLog cap model ctx stack Q packet saved proofs B limit seed ro opening)
        opening.root opening.result.paths := by
  obtain ⟨run,_,consistent⟩ := AnchoredMixedIdealSourceAcceptance.mixedView_runs
    cap .fresh model ctx stack Q packet saved proofs ctx.iv B limit seed ro
  rw [success] at run
  obtain ⟨_,_,lanesEq,trace,observed⟩ := AnchoredPhysicalExecution.verifySource_execution
    cap .fresh model ctx stack Q packet saved proofs _ a run
  have chain := completion_chain ctx Q packet
  have reference := (trace_queryRoles saved a.configuration.1 a.configuration.2 chain trace opening opened).2
  have earlierPrefix := packets_query_prefix final current member (.query opening.level) earlier
  rw [← messages,← earlierPrefix] at reference
  have sample := (WHIRPhysicalRoots.trace_samples saved.root chain trace opening opened).2
  have past := strictPrefix_of_raws final current member (table ctx Q packet B seed ro) ring a.wire.tape raws
  have sampleAt : PCSBCSSourcePacketTape.strictPrefix current
      (fun key => (table ctx Q packet B seed ro) key.val) (.query opening.level) earlier =
      opening.sample := by
    rw [past]
    exact sample
  obtain ⟨proof,_,accepted,_⟩ := AnchoredIdealPhysicalAcceptance.observed_real
    (observed opening opened) seed ctx.iv consistent
  have fits : saved.shape.lanes ≤ 2^(ParameterBounds.config packet.val.profile).folds[0]! := by
    rw [← lanesEq]
    exact a.request.lane_bound
  have evidence := query_evidence cap model ctx stack Q packet saved proofs B limit seed ro
    current.2.coord current.2.messages
    (PCSBCSSourcePacketTape.strictPrefix current (fun key => (table ctx Q packet B seed ro) key.val))
    m digest opening.level introMessage earlier (PCSBCSNativeRootRoles.openingRole saved opening)
    reference fits proof opening.result (by simpa only [sampleAt,PCSBCSNativeRootRoles.openingRole] using accepted)
  have log : PCSBCSNativeCapturedRows.referenceLog cap model ctx stack Q packet saved proofs B limit seed ro
      (PCSBCSNativeRootRoles.openingRole saved opening) =
      PCSBCSNativeCapturedRows.openingLog cap model ctx stack Q packet saved proofs B limit seed ro opening := by
    exact (PCSBCSNativeCapturedOracles.opening_log cap model ctx stack Q packet saved proofs B limit seed ro
      a.configuration.2 opening).symm
  rw [log] at evidence
  exact evidence

theorem decodeMessage_fields (xs : List E) (message : Message E)
    (parsed : WHIRHistory.decodeMessage xs = some message) :
    xs = WHIRHistory.messageScalars message := by
  cases xs with
  | nil => cases parsed
  | cons a rest =>
    cases rest with
    | nil => cases parsed
    | cons b rest =>
      cases rest with
      | cons c rest => cases parsed
      | nil =>
        cases Option.some.inj parsed
        rfl

private theorem source_of_parser
    (current : CausalProbability.Coordinate (ParameterBounds.config packet.val.profile))
    (messages : List WHIRHistory.Pending) (past : WHIRFiatShamir.Prefix current)
    (q : CausalProbability.Coordinate (ParameterBounds.config packet.val.profile))
    (m : WHIRHistory.Pending) (native : CausalGame.Reply) (rows : WHIRPhysicalHistory.Rows)
    (earlier : CausalProbability.position q < CausalProbability.position current)
    (parsed : WHIRPhysicalHistory.reply
      (PCSBCSNativeCapturedOracles.roots cap model ctx stack Q packet saved proofs B limit seed ro)
      rows q m = some native)
    (clean : ∀ ref, ¬ OutputCollision
      (PCSBCSNativeCapturedRows.referenceLog cap model ctx stack Q packet saved proofs B limit seed ro ref))
    (queries : ∀ (i : Fin (ParameterBounds.config packet.val.profile).folds.size) (introMessage : Message E),
      CausalProbability.position (.query i :
        CausalProbability.Coordinate (ParameterBounds.config packet.val.profile)) <
          CausalProbability.position current →
      SourceEvidence (addresses ctx Q packet B)
        (program cap model ctx stack Q packet saved proofs B limit) (table ctx Q packet B seed ro)
        seed current saved messages past m DuplexRefinement.zeroDigest (.query i) (.query (rows i.val) introMessage)) :
    ∃ digest, WHIRHistory.replyScalars q digest native = some m.scalars ∧
      SourceEvidence (addresses ctx Q packet B)
        (program cap model ctx stack Q packet saved proofs B limit) (table ctx Q packet B seed ro)
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
                    have auth := referenceLog_authentic cap model ctx stack Q packet saved proofs B limit seed ro ref
                    have projection := next_projection cap model ctx stack Q packet saved proofs B limit seed ro
                      i j ⟨[a,b,r,s],nonce⟩ ref reference (clean ref)
                    have pair := ByteCodec.hashToScalars_scalarsToHash (r,s) digest decoded
                    refine ⟨digest,?_,?_⟩
                    · simp only [WHIRHistory.replyScalars,last,↓reduceIte,WHIRHistory.boundaryScalars,
                        later,WHIRHistory.messageScalars,WHIRHistory.rootScalars,pair]
                      rfl
                    · exact .next i j ⟨a,b⟩ _ last later ref
                        (PCSBCSNativeCapturedRows.referenceLog cap model ctx stack Q packet saved proofs B limit seed ro ref)
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

/-- Deterministic reply join for the canonical replay decoder. Physical scalar
normal forms, chronological messages, query proofs and next tables are derived;
only the separately owned whole-packet raw join and primitive event exclusions
remain premises. The decoder equation is supplied by the native run endpoint. -/
theorem replyTransport_of_canonical_decode
    (a : Accepted ctx Q cap packet saved)
    (success : (AnchoredMixedIdealSourceAcceptance.mixedView cap .fresh model ctx stack Q packet saved
      proofs ctx.iv B limit seed ro).result.value = some a)
    (replay : StackWHIRReplay.Replay packet.val.profile cap)
    (decoded : WHIRPhysicalHistory.decodeStack packet.val.profile cap
      (fun _ => some (PCSBCSNativeOracleReplay.original a
        (PCSBCSNativeCapturedOracles.base cap model ctx stack Q packet saved proofs B limit seed ro)))
      (PCSBCSNativeCapturedOracles.roots cap model ctx stack Q packet saved proofs B limit seed ro)
      (fun i => a.wire.rows[i]!)
      ⟨packet.val.statement,packet.val.messages,
        (localHistory ctx stack Q packet.val.profile a.history).tail⟩ = some replay)
    (final : PCSBCSChallengeOracle.EnteredPacket packet.val.profile B ctx.iv
      (RawWHIRKeys.entry ctx packet.val).frames.length)
    (messages : final.2.messages = packet.val.messages)
    (raws : ∀ current ∈ PCSBCSCapturedSourceStatePath.packets final,
      PCSBCSChallengeOracle.grouped current.2.coord ((table ctx Q packet B seed ro) (.inl current)) =
        PCSBCSRestorationHazard.literalRaw replay.initial.1 a.wire.tape current.2.coord)
    (quiet : ∀ opening ∈ a.wire.openings,
      ¬ PublicMerkleBinding.OpenPrimitiveBad seed
        (PCSBCSNativeCapturedRows.openingLog cap model ctx stack Q packet saved proofs B limit seed ro opening)
        opening.root opening.result.paths)
    (clean : ∀ ref, ¬ OutputCollision
      (PCSBCSNativeCapturedRows.referenceLog cap model ctx stack Q packet saved proofs B limit seed ro ref)) :
    ∀ current ∈ PCSBCSCapturedSourceStatePath.packets final,
      PCSBCSCapturedSourceAcceptance.ReplyTransport (addresses ctx Q packet B)
        (program cap model ctx stack Q packet saved proofs B limit) (table ctx Q packet B seed ro)
        seed saved current replay.whir.replies := by
  obtain ⟨run,_,_⟩ := AnchoredMixedIdealSourceAcceptance.mixedView_runs
    cap .fresh model ctx stack Q packet saved proofs ctx.iv B limit seed ro
  rw [success] at run
  obtain ⟨_,_,_,trace,_⟩ := AnchoredPhysicalExecution.verifySource_execution
    cap .fresh model ctx stack Q packet saved proofs _ a run
  have chain := completion_chain ctx Q packet
  let original := PCSBCSNativeOracleReplay.original a
    (PCSBCSNativeCapturedOracles.base cap model ctx stack Q packet saved proofs B limit seed ro)
  obtain ⟨initial,_,rest⟩ := Option.bind_eq_some_iff.mp decoded
  obtain ⟨whir,parsedWhir,equal⟩ := Option.bind_eq_some_iff.mp rest
  have equal : (⟨original,initial,whir⟩ : StackWHIRReplay.Replay packet.val.profile cap) = replay :=
    Option.some.inj equal
  have whirEq : whir = replay.whir := congrArg StackWHIRReplay.Replay.whir equal
  have parsed := parses_of_decode packet.val.profile (StackWHIRReplay.localCatalog original initial)
    (PCSBCSNativeCapturedOracles.roots cap model ctx stack Q packet saved proofs B limit seed ro)
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
  obtain ⟨digest,scalars,evidence⟩ := source_of_parser cap model ctx stack Q packet saved proofs B limit seed ro
    current.2.coord current.2.messages
    (PCSBCSSourcePacketTape.strictPrefix current (fun key => (table ctx Q packet B seed ro) key.val))
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
        have source := (mixed_success_query cap model ctx stack Q packet saved proofs B limit seed ro a success
          final current messages member replay.initial.1 raws ⟨i,root,x',result⟩ opened earlierQuery
          m DuplexRefinement.zeroDigest introMessage).resolve_right
          (quiet ⟨i,root,x',result⟩ opened)
        rw [rowEq]
        exact source)
  exact ⟨q,m,digest,scheduled,currentMessage,scalars,evidence⟩

/-- The literal captured assembly contains exactly the strict native replies,
the actual earlier sampled challenges, and the initial captured source root. -/
def CapturedAssembly (original : PCSBCSCallerBinding.CallerInput packet.val.profile)
    (current : PCSBCSChallengeOracle.EnteredPacket packet.val.profile B ctx.iv
      (RawWHIRKeys.entry ctx packet.val).frames.length)
    (ring : RingPCSGame.Prefix) (tape : CausalGame.Tape (ParameterBounds.config packet.val.profile))
    (native : Array CausalGame.Reply) : Prop :=
  ∃ parsed,
    PCSBCSSourceFrozenReplies.replies current.2.coord saved
      (PCSBCSSourceCallerSnapshot.capturedRegistry (addresses ctx Q packet B)
        (program cap model ctx stack Q packet saved proofs B limit) current
        (fun key => (table ctx Q packet B seed ro) key.val))
      current.2.messages
      (PCSBCSSourcePacketTape.strictPrefix current (fun key => (table ctx Q packet B seed ro) key.val)) =
        some parsed ∧
    parsed = PCSRoundByRoundTranscriptState.priorAnswers native (CausalProbability.position current.2.coord) ∧
    PCSBCSRestorationHazard.incomingTrace
      (PCSBCSSourcePacketTape.ringPrefix current (fun key => (table ctx Q packet B seed ro) key.val))
      (PCSBCSSourcePacketTape.tape current (fun key => (table ctx Q packet B seed ro) key.val)) parsed current.2.coord =
      PCSBCSRestorationHazard.incomingTrace ring tape native current.2.coord ∧
    PCSBCSSourceCallerSnapshot.fromCapture (addresses ctx Q packet B)
      ⟨saved.root,initialShape saved.shape⟩ (program cap model ctx stack Q packet saved proofs B limit)
      original saved current (fun key => (table ctx Q packet B seed ro) key.val) =
      some (PCSBCSRestorationHazard.literalCallerData packet.val.profile original
        (PCSBCSNativeSourceOriginal.sourceBase cap model ctx stack Q packet saved proofs B limit seed ro)
        ring tape native current.2.coord)

private theorem captured_assembly
    (a : Accepted ctx Q cap packet saved)
    (original : PCSBCSCallerBinding.CallerInput packet.val.profile) (claims : AnchoredSourceCaller.Claims)
    (caller : AnchoredSourceFreshCaller.decode model.layout saved (RawWHIRKeys.entry ctx packet.val)
      (PCSBCSSourceCallerAnswers.answers (table ctx Q packet B seed ro)) = some claims)
    (final current : PCSBCSChallengeOracle.EnteredPacket packet.val.profile B ctx.iv
      (RawWHIRKeys.entry ctx packet.val).frames.length)
    (entry : final.1.val = RawWHIRKeys.entry ctx packet.val)
    (member : current ∈ PCSBCSCapturedSourceStatePath.packets final)
    (recorded : (⟨.inl current,(table ctx Q packet B seed ro) (.inl current)⟩ :
      Sigma PCSBCSSourceRootCapture.Answer) ∈
      (Sampling.execute (table ctx Q packet B seed ro)
        (program cap model ctx stack Q packet saved proofs B limit)).2)
    (ring : RingPCSGame.Prefix) (tape : CausalGame.Tape (ParameterBounds.config packet.val.profile))
    (native : Array CausalGame.Reply)
    (raws : ∀ sourcePacket ∈ PCSBCSCapturedSourceStatePath.packets final,
      PCSBCSChallengeOracle.grouped sourcePacket.2.coord ((table ctx Q packet B seed ro) (.inl sourcePacket)) =
        PCSBCSRestorationHazard.literalRaw ring tape sourcePacket.2.coord)
    (transport : PCSBCSCapturedSourceAcceptance.ReplyTransport (addresses ctx Q packet B)
      (program cap model ctx stack Q packet saved proofs B limit) (table ctx Q packet B seed ro)
      seed saved current native)
    (clean : ∀ ref, ¬ OutputCollision
      (PCSBCSNativeCapturedRows.referenceLog cap model ctx stack Q packet saved proofs B limit seed ro ref)) :
    CapturedAssembly cap model ctx stack Q packet saved proofs B limit seed ro original current ring tape native := by
  have currentEntry : current.1.val = RawWHIRKeys.entry ctx packet.val :=
    (congrArg Subtype.val (PCSBCSCapturedSourceStatePath.packets_entry final current member)).trans entry
  have roles := PCSBCSCapturedSourceAcceptance.roles_from_transport
    (addresses ctx Q packet B)
    (program cap model ctx stack Q packet saved proofs B limit) (table ctx Q packet B seed ro)
    seed saved current native transport
  have addressRoles := PCSBCSCapturedSourceTransport.address_packet model.layout saved
    (PCSBCSSourceCallerAnswers.answers (table ctx Q packet B seed ro)) current
    a.configuration.1 a.configuration.2 claims (by simpa only [currentEntry] using caller) roles
  have visited : (.inl current) ∈
      ((Sampling.execute (table ctx Q packet B seed ro)
        (program cap model ctx stack Q packet saved proofs B limit)).2.map Sigma.fst) :=
    List.mem_map.mpr ⟨_,recorded,rfl⟩
  let ref : Reference := ⟨saved.root,initialShape saved.shape⟩
  let log := PCSBCSNativeCapturedRows.referenceLog cap model ctx stack Q packet saved proofs B limit seed ro ref
  have mentioned : ref ∈ addresses ctx Q packet B (.inl current) := by
    change ref ∈ PCSBCSCapturedSourceTransport.address (.inl current)
    rw [addressRoles]
    exact List.mem_cons_self
  have root := source_registry_enabled (addresses ctx Q packet B)
    (program cap model ctx stack Q packet saved proofs B limit) (table ctx Q packet B seed ro)
    current ref mentioned visited
  have root : PCSBCSSourceCallerSnapshot.capturedRegistry (addresses ctx Q packet B)
      (program cap model ctx stack Q packet saved proofs B limit) current
      (fun key => (table ctx Q packet B seed ro) key.val) ref = some (freeze log ref.root ref.shape) := root
  have inverses := PCSBCSCapturedSourceAcceptance.source_inverse
    (addresses ctx Q packet B)
    (program cap model ctx stack Q packet saved proofs B limit) (table ctx Q packet B seed ro)
    seed saved current native addressRoles visited transport
  obtain ⟨parsed,assembled⟩ := PCSBCSCapturedSourceTransport.replies_complete current.2.coord saved
    (PCSBCSSourceCallerSnapshot.capturedRegistry (addresses ctx Q packet B)
      (program cap model ctx stack Q packet saved proofs B limit) current
      (fun key => (table ctx Q packet B seed ro) key.val)) current.2.messages
    (PCSBCSSourcePacketTape.strictPrefix current (fun key => (table ctx Q packet B seed ro) key.val))
    (by
      intro j earlier
      obtain ⟨inverted,found,_⟩ := Option.map_eq_some_iff.mp (inverses j earlier)
      exact ⟨inverted,found⟩)
  have parsedEq := PCSBCSCapturedSourceStatePath.replies_exact current.2.coord saved _ _ _ native parsed assembled inverses
  have priorRaws : ∀ earlier : current.Earlier,
      PCSBCSSourcePacketTape.rawPrefix current (fun key => (table ctx Q packet B seed ro) key.val)
        earlier.val earlier.property = PCSBCSRestorationHazard.literalRaw ring tape earlier.val := by
    intro earlier
    rw [PCSBCSSourcePacketTape.rawPrefix_table]
    exact raws _ (PCSBCSCapturedSourceStatePath.predecessor_mem_packets final current member earlier)
  have incoming := PCSBCSCapturedSourceStatePath.incoming_exact current
    (table ctx Q packet B seed ro) ring tape native parsed parsedEq priorRaws
  have snapshot := PCSBCSCapturedSourceStatePath.fromCapture_exact
    (addresses ctx Q packet B) ref
    (program cap model ctx stack Q packet saved proofs B limit) original saved current
    (table ctx Q packet B seed ro) (freeze log ref.root ref.shape) root ring tape native priorRaws inverses
  have rawEq : (freeze log ref.root ref.shape).raw =
      PCSBCSNativeSourceOriginal.sourceBase cap model ctx stack Q packet saved proofs B limit seed ro :=
    (next_image_provenance seed log ref
      (referenceLog_authentic cap model ctx stack Q packet saved proofs B limit seed ro ref) (clean ref)).2
  rw [rawEq] at snapshot
  exact ⟨parsed,assembled,parsedEq,incoming,snapshot⟩

/-- Actual mixed-source composition for every literal recorded construction
packet. Both the native strategy and the captured snapshots use the canonically
restored replies. Arbitrary partial initial occupancy is retained. The only
cryptographic exclusions are the actual openingLog bad events and captured
ordinary-prefix output collisions; no FS probability bound is asserted. -/
theorem mixed_success_replyTransport
    (a : Accepted ctx Q cap packet saved) (familyCap : cap ≤ 2^64)
    (success : (AnchoredMixedIdealSourceAcceptance.mixedView cap .fresh model ctx stack Q packet saved
      proofs ctx.iv B limit seed ro).result.value = some a)
    (quiet : ∀ opening ∈ a.wire.openings,
      ¬ PublicMerkleBinding.OpenPrimitiveBad seed
        (PCSBCSNativeCapturedRows.openingLog cap model ctx stack Q packet saved proofs B limit seed ro opening)
        opening.root opening.result.paths)
    (clean : ∀ ref, ¬ OutputCollision
      (PCSBCSNativeCapturedRows.referenceLog cap model ctx stack Q packet saved proofs B limit seed ro ref)) :
    ∃ (original : PCSBCSCallerBinding.CallerInput packet.val.profile)
      (claims : AnchoredSourceCaller.Claims) (replay : StackWHIRReplay.Replay packet.val.profile cap)
      (proof : Opening) (bounded : DuplexFraming.pathCost (RawWHIRKeys.coordinate ctx packet.val 0) ≤ B),
      let packetB := PCSBCSNativePacketVisit.packetAtBound ctx Q B packet bounded
      let final := PCSBCSNativePacketBridge.enteredPacket ctx stack B packetB
      let native := PCSBCSCapturedSourceAcceptance.nativeReplies original
        (PCSBCSNativeSourceOriginal.sourceBase cap model ctx stack Q packet saved proofs B limit seed ro)
        (fun _ => CausalStrategy.indexedStrategy replay.whir.replies) replay.initial.1 a.wire.tape
      PCSBCSSourceCallerOriginal.original packet.val.profile model.layout saved (RawWHIRKeys.entry ctx packet.val)
        (PCSBCSSourceCallerAnswers.answers (table ctx Q packet B seed ro)) = some original ∧
      AnchoredSourceFreshCaller.decode model.layout saved (RawWHIRKeys.entry ctx packet.val)
        (PCSBCSSourceCallerAnswers.answers (table ctx Q packet B seed ro)) = some claims ∧
      PCSBCSCapturedSourceAcceptance.BoundOriginal original saved claims ∧
      final.2.coord = PCSRoundByRoundTranscriptState.lastCoordinate (ParameterBounds.config packet.val.profile) ∧
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
      CausalGame.experiment
        (OriginalClaimsChecker.input original.prepared
          (PCSBCSNativeSourceOriginal.sourceBase cap model ctx stack Q packet saved proofs B limit seed ro)
          replay.initial.1) (CausalStrategy.indexedStrategy replay.whir.replies) a.wire.tape = true ∧
      native = replay.whir.replies ∧
      (∀ current ∈ PCSBCSCapturedSourceStatePath.packets final,
        PCSBCSChallengeOracle.grouped current.2.coord ((table ctx Q packet B seed ro) (.inl current)) =
          PCSBCSRestorationHazard.literalRaw replay.initial.1 a.wire.tape current.2.coord) ∧
      (∀ current ∈ PCSBCSCapturedSourceStatePath.packets final,
        PCSBCSCapturedSourceAcceptance.ReplyTransport (addresses ctx Q packet B)
          (program cap model ctx stack Q packet saved proofs B limit) (table ctx Q packet B seed ro)
          seed saved current native) ∧
      (∀ current ∈ PCSBCSCapturedSourceStatePath.packets final,
        CapturedAssembly cap model ctx stack Q packet saved proofs B limit seed ro
          original current replay.initial.1 a.wire.tape native) := by
  obtain ⟨original,claims,replay,proof,reconstructed,caller,bound,initial,lambda,erased,parsed,canonical,accepted⟩ :=
    PCSBCSNativeSourceOriginal.mixed_success_original_experiment
      cap model ctx stack Q packet saved proofs B limit seed ro a familyCap success quiet
  obtain ⟨seed0,bounded,seedState,depth,terminal,ordering,recorded,raws⟩ :=
    PCSBCSNativeCapturedTape.mixed_success_tape cap model ctx stack Q packet saved proofs B limit seed ro a success
  have seedEq : seed0 = replay.initial := Option.some.inj (seedState.symm.trans initial)
  subst seed0
  let packetB := PCSBCSNativePacketVisit.packetAtBound ctx Q B packet bounded
  let final := PCSBCSNativePacketBridge.enteredPacket ctx stack B packetB
  have messages : final.2.messages = packet.val.messages := rfl
  have entry : final.1.val = RawWHIRKeys.entry ctx packet.val := rfl
  have nativeEq := PCSBCSNativeSourceOriginal.nativeReplies_indexed original
    (PCSBCSNativeSourceOriginal.sourceBase cap model ctx stack Q packet saved proofs B limit seed ro)
    replay.initial.1 a.wire.tape replay.whir.replies proof parsed
  have transport := replyTransport_of_canonical_decode cap model ctx stack Q packet saved proofs B limit seed ro
    a success replay canonical final messages raws quiet clean
  refine ⟨original,claims,replay,proof,bounded,reconstructed,caller,bound,terminal,initial,lambda,
    erased,parsed,canonical,accepted,nativeEq,raws,?_,?_⟩
  · rw [nativeEq]
    exact transport
  · rw [nativeEq]
    intro current member
    exact captured_assembly cap model ctx stack Q packet saved proofs B limit seed ro a original claims caller
      final current entry member (recorded current member) replay.initial.1 a.wire.tape replay.whir.replies
      raws (transport current member) clean

end Driver

#print axioms phaseReference_of_roles
#print axioms trace_queryRoles
#print axioms strictPrefix_of_raws
#print axioms packets_query_prefix
#print axioms referenceLog_authentic
#print axioms next_log
#print axioms next_projection
#print axioms query_evidence
#print axioms mixed_success_query
#print axioms replyTransport_of_canonical_decode
#print axioms mixed_success_replyTransport
end Whir.PCSBCSNativeCapturedReplyTransport
