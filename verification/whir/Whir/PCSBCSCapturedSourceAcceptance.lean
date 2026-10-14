import Whir.PCSBCSCapturedSourceStatePath
import Whir.PCSBCSCapturedNativeReplyBridge

/-! Accepting PCS-only source adapter. Root0 is the full-table projection of
actual ordinary records preceding its first literal address mention, NOT an
independent hidden oracle string. SourceEvidence exposes exact native tag,
shape, phase-codec and primitive/opening transport conditions. This theorem is
not universal Rust refinement, and does not assume semantic equivalence or a
Fiat-Shamir probability certificate. The probabilistic obligations remain the
finite first-disclosure n*rbrError term (physical indexed compilation n=Q), the
separate existing Merkle primitive bad events, and compression/construction coupling. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
namespace Whir.PCSBCSCapturedSourceAcceptance
open Concrete Protocol CausalGame CausalProbability FiatShamirGame WHIRHistory
open PCSBCSChallengeOracle PCSBCSSourceRootReferences PCSBCSMerkleRootCache
open PCSBCSSourceCallerSnapshot PCSBCSSourceReplyInversion
open PCSBCSCallerBinding PCSBCSRestorationHazard PCSRoundByRoundTranscriptState
open TypedOracleCompiler TypedFiatShamirGame PCSStateRestoration.Latent
open PCSBCSCapturedSourceStatePath PCSBCSCapturedSourceTransport PCSBCSCapturedNativeReplyBridge
open PublicMerkleLog
open MerkleTransport.Commitments

variable {p : ParameterBounds.Profile} {Q : Nat} {iv : Digest32} {boundary : Nat}
local notation "Keys" => PCSBCSSourceRootCapture.Key
  (p := p) (Q := Q) (iv := iv) (boundary := boundary)
local notation "Answers" => PCSBCSSourceRootCapture.Answer
  (p := p) (Q := Q) (iv := iv) (boundary := boundary)

/-- Literal public-input binding only, not truth of the claims. The fixed
original input is kept independent of every whole packet answer. -/
def BoundOriginal (original : CallerInput p) (saved : AnchoredHeaderCodec.Record)
    (claims : AnchoredSourceCaller.Claims) : Prop :=
  claims.record = saved ∧ claims.caller.root = saved.root ∧
  original.lanes = saved.shape.lanes ∧ List.ofFn original.family = claims.caller.families ∧
  original.points = claims.caller.points ∧ original.anchorPoint = saved.point.toArray ∧
  original.anchorValue = saved.value


/-- The native full-table projection preserves unavailable ghost defaults. Only
accepted opened rows obtain authenticity; full rectangularity alone does not. -/
noncomputable def sourceRoot {R : Type} {n : Nat}
    (C : DuplexModeGame.PrimitiveOracle) (addresses : Keys → List Reference) (ref : Reference)
    (program : Sampling Keys Answers R n) (table : Table Keys Answers) : BaseOracle :=
  WHIRPhysicalRows.compactBaseOracle (hash C)
    ⟨recordDomain (records (sourceLog addresses ref program table)),[]⟩
      ref.root ref.shape.height (2^ref.shape.height) ref.shape.leafWords ref.shape.occupied

/-- Exactly the replies of the native PCS-only source machine on its projected
Root0 input and independently bound original caller. -/
def nativeReplies (original : CallerInput p) (root : BaseOracle)
    (strategy : RingPCSGame.Prefix → Strategy) (ring : RingPCSGame.Prefix)
    (t : Tape (ParameterBounds.config p)) : Array Reply :=
  PCSRoundByRoundTranscriptState.replies
    (ExecutionShapes.Input p original.lanes root
      (OriginalClaimsChecker.input original.prepared root ring).claims) (strategy ring) t

theorem captured_sourceRoot {R : Type} {n : Nat}
    (C : DuplexModeGame.PrimitiveOracle) (addresses : Keys → List Reference) (ref : Reference)
    (program : Sampling Keys Answers R n) (table : Table Keys Answers) (f : Frozen)
    (captured : PCSBCSSourceRootCapture.capture addresses ref program table = some f)
    (auth : AuthenticLog C (sourceLog addresses ref program table))
    (clean : ¬ OutputCollision (sourceLog addresses ref program table)) :
    f.raw = sourceRoot C addresses ref program table := by
  obtain ⟨events,found,frozen,_⟩ := PCSBCSSourceRootCapture.capture_provenance
    addresses ref program table f captured
  have log : sourceLog addresses ref program table = PCSBCSSourceRootCapture.ordinaryPrefix events := by
    simp only [sourceLog,found,Option.getD_some]
  rw [frozen]
  unfold sourceRoot
  rw [log]
  exact (next_image_provenance C _ ref (log ▸ auth) (log ▸ clean)).2

open Classical in
/-- The actual native initial projection ignores every bit of the selected
whole packet, not only its consumed challenge bytes. -/
theorem sourceRoot_current_independent {R : Type} {n : Nat}
    (C : DuplexModeGame.PrimitiveOracle) (addresses : Keys → List Reference) (ref : Reference)
    (program : Sampling Keys Answers R n) (current : EnteredPacket p Q iv boundary)
    (table : Table Keys Answers) (mentioned : ref ∈ addresses (.inl current))
    (full : Fin (PCSBCSChallengeOracle.blocks (PCSBCSRounds.rawWidth current.2.coord)) → Digest32) :
    sourceRoot C addresses ref program (Function.update table (.inl current) full) =
      sourceRoot C addresses ref program table := by
  have same : sourceLog addresses ref program (Function.update table (.inl current) full) =
      sourceLog addresses ref program table := by
    unfold sourceLog
    rw [PCSBCSFirstRootDisclosure.first_mention_answer_independent
      addresses (.inl current) ref mentioned program table full]
  unfold sourceRoot
  rw [same]

/-- Native source parser evidence at the actual chronological positions. These
are primitive/shape/source-codec hypotheses, never constructed accessor,
canonical reply, or whole-prefix completeness hypotheses. -/
def ReplyTransport {R : Type} {n : Nat}
    (addresses : Keys → List Reference) (program : Sampling Keys Answers R n)
    (table : Table Keys Answers) (C : DuplexModeGame.PrimitiveOracle) (saved : AnchoredHeaderCodec.Record)
    (current : EnteredPacket p Q iv boundary) (native : Array Reply) : Prop :=
  ∀ j, j < position current.2.coord →
    ∃ q m digest,
      (schedule (ParameterBounds.config p))[j]? = some q ∧
      current.2.messages.reverse[j+1]? = some m ∧
      replyScalars q digest native[j]! = some m.scalars ∧
      SourceEvidence addresses program table C current.2.coord saved current.2.messages
        (PCSBCSSourcePacketTape.strictPrefix current (fun key => table key.val)) m digest q native[j]!

/-- Every scheduled next-root scalar role is admitted by the actual source
reply transport. There is no separate root-parser completeness premise. -/
theorem roles_from_transport {R : Type} {count : Nat}
    (addresses : Keys → List Reference) (program : Sampling Keys Answers R count)
    (table : Table Keys Answers) (C : DuplexModeGame.PrimitiveOracle)
    (saved : AnchoredHeaderCodec.Record) (current : EnteredPacket p Q iv boundary)
    (native : Array Reply) (transport : ReplyTransport addresses program table C saved current native) :
    phaseRolesAdmitted (ParameterBounds.config p) current.2.messages = true := by
  unfold phaseRolesAdmitted
  rw [List.all_eq_true]
  rintro ⟨m,n⟩ member
  dsimp only
  by_cases initial : n = 0
  · simp only [initial,↓reduceIte]
  · simp only [initial,↓reduceIte]
    have indexed := List.mk_mem_zipIdx_iff_getElem?.mp member
    have inside : n < current.2.messages.length := by
      have size := (List.getElem?_eq_some_iff.mp indexed).1
      simpa only [List.length_reverse] using size
    have positionEq := current.2.2.position_eq
    have earlier : n-1 < position current.2.coord := by
      change current.2.messages.length-1 = position current.2.coord at positionEq
      omega
    obtain ⟨q,message,digest,coordinate,atMessage,_,evidence⟩ := transport (n-1) earlier
    have previous : n-1+1 = n := by omega
    rw [previous] at atMessage
    have same : message = m := Option.some.inj (atMessage.symm.trans indexed)
    subst message
    rw [coordinate]
    simp only [Option.getD_some]
    generalize replySame : native[n-1]! = reply at evidence
    cases evidence with
    | initial a => rfl
    | ood i j a => rfl
    | tail j a => rfl
    | middle i j a notLast =>
        have guard : ¬ (j.val+1 = (ParameterBounds.config p).folds[i.val]! ∧
            i.val+1 < (ParameterBounds.config p).folds.size) := fun h => notLast h.1
        simp only [guard,↓reduceIte]
    | terminal i j a residual last terminal width => simp [terminal]
    | next i j a native last later ref log reference captured fits auth clean projection =>
        simp [last,later,reference]
    | query i a native earlier ref log reference captured fits codec qs derived
        numLeaves proof output height auth accepted bounds quiet projection => rfl

theorem schedule_coordinate_position {c : Config} (n : Nat) (q : Coordinate c)
    (coordinate : (schedule c)[n]? = some q) : position q = n := by
  obtain ⟨inside,stored⟩ := List.getElem?_eq_some_iff.mp coordinate
  rw [← stored]
  exact position_schedule_get c ⟨n,inside⟩

theorem source_inverse {R : Type} {n : Nat}
    (addresses : Keys → List Reference) (program : Sampling Keys Answers R n)
    (table : Table Keys Answers) (C : DuplexModeGame.PrimitiveOracle) (saved : AnchoredHeaderCodec.Record)
    (current : EnteredPacket p Q iv boundary) (native : Array Reply)
    (addressRoles : addresses (.inl current) =
      ⟨saved.root,initialShape saved.shape⟩ :: phaseReferences (ParameterBounds.config p) current.2.messages)
    (visited : (.inl current : Keys) ∈ ((Sampling.execute table program).2.map Sigma.fst))
    (transport : ReplyTransport addresses program table C saved current native)
    (j : Nat) (earlier : j < position current.2.coord) :
    (PCSBCSSourceFrozenAccessor.inverseAt current.2.coord saved
      (capturedRegistry addresses program current (fun key => table key.val)) current.2.messages
      (PCSBCSSourcePacketTape.strictPrefix current (fun key => table key.val)) j).map Inverted.reply = some native[j]! := by
  obtain ⟨q,m,digest,coordinate,message,scalars,evidence⟩ := transport j earlier
  have prior : position q < position current.2.coord := by
    rw [schedule_coordinate_position j q coordinate]
    exact earlier
  rw [inverseAt_source_native addresses program table C current saved
    (PCSBCSSourcePacketTape.strictPrefix current (fun key => table key.val)) j q m digest
    native[j]! coordinate message prior scalars addressRoles visited evidence]
  rfl

/-- Complete deterministic adapter: public byte-only root addresses, actual
visited literal source prefixes and capture, independently bound caller, exact
native earlier replies, derived adjacent identities, initial false, and accepted
extraction-failure terminal true construct the latent restoration StatePath.
No unqueried-entry caller coverage, path link, or inverse success is assumed. -/
theorem accepted_failure_statePath {R : Type} {n : Nat}
    (C : DuplexModeGame.PrimitiveOracle) (layout : WHIRCallerClaims.CallerLayout)
    (saved : AnchoredHeaderCodec.Record) (answers : FiatShamirGame.Coordinate → Digest32)
    (program : Sampling Keys Answers R n) (table : Table Keys Answers)
    (final : EnteredPacket p Q iv boundary) (original : CallerInput p)
    (claims : AnchoredSourceCaller.Claims)
    (valid : saved.Valid) (profile : profileShape p saved.shape)
    (caller : AnchoredSourceFreshCaller.decode layout saved final.1.val answers = some claims)
    (bound : BoundOriginal original saved claims)
    (terminal : final.2.coord = lastCoordinate (ParameterBounds.config p))
    (recorded : ∀ current ∈ packets final,
      (⟨.inl current,table (.inl current)⟩ : Sigma Answers) ∈ (Sampling.execute table program).2)
    (auth : AuthenticLog C (sourceLog address
      ⟨saved.root,initialShape saved.shape⟩ program table))
    (clean : ¬ OutputCollision (sourceLog address
      ⟨saved.root,initialShape saved.shape⟩ program table))
    (ring : RingPCSGame.Prefix) (t : Tape (ParameterBounds.config p))
    (strategy : RingPCSGame.Prefix → Strategy)
    (raws : ∀ current ∈ packets final,
      grouped current.2.coord (table (.inl current)) = literalRaw ring t current.2.coord)
    (transport : ∀ current ∈ packets final,
      ReplyTransport address program table C saved current
        (nativeReplies original
          (sourceRoot C address ⟨saved.root,initialShape saved.shape⟩ program table)
          strategy ring t))
    (accepted : experiment (OriginalClaimsChecker.input original.prepared
      (sourceRoot C address ⟨saved.root,initialShape saved.shape⟩ program table) ring)
      (strategy ring) t = true)
    (failure : ¬ ∃ w,
      PCSRoundByRoundKnowledge.extract p original.lanes original.family original.points original.anchorPoint
        original.anchorValue (sourceRoot C address ⟨saved.root,initialShape saved.shape⟩ program table) = some w ∧
      PCSRewindSource.ExplainsOriginal (ParameterBounds.config p) original.lanes
        (sourceRoot C address ⟨saved.root,initialShape saved.shape⟩ program table)
        original.family original.points original.anchorPoint original.anchorValue w) :
    BoundOriginal original saved claims ∧
    (∀ current ∈ packets final, ∃ data,
      fromCapture address ⟨saved.root,initialShape saved.shape⟩ program
        original saved current (fun key => table key.val) = some data ∧ data.original = original ∧
      data.observed.root =
        sourceRoot C address ⟨saved.root,initialShape saved.shape⟩ program table ∧
      data.observed.trace = incomingTrace ring t
        (nativeReplies original
          (sourceRoot C address ⟨saved.root,initialShape saved.shape⟩ program table)
          strategy ring t) current.2.coord) ∧
    StatePath (Restoration.model p Q iv boundary
      (builder address ⟨saved.root,initialShape saved.shape⟩ program original saved))
      table (Sampling.execute table program).2 false true := by
  have addressRoles (current : EnteredPacket p Q iv boundary) (member : current ∈ packets final) :
      address (.inl current) =
        ⟨saved.root,initialShape saved.shape⟩ :: phaseReferences (ParameterBounds.config p) current.2.messages :=
    address_packet layout saved answers current valid profile claims
      (by rw [packets_entry final current member]; exact caller)
      (roles_from_transport _ _ _ C _ current _ (transport current member))
  have mentions (current : EnteredPacket p Q iv boundary) (member : current ∈ packets final) :
      (⟨saved.root,initialShape saved.shape⟩ : Reference) ∈ address (.inl current) := by
    rw [addressRoles current member]
    exact List.mem_cons_self
  have finalMember := final_mem_packets final
  have visited : (.inl final : Keys) ∈ ((Sampling.execute table program).2.map Sigma.fst) :=
    List.mem_map.mpr ⟨⟨.inl final,table (.inl final)⟩,recorded final finalMember,rfl⟩
  obtain ⟨frozen,captured⟩ := PCSBCSSourceRootCapture.capture_exists
    address ⟨saved.root,initialShape saved.shape⟩ (.inl final)
    (mentions final finalMember) program table visited
  have root := captured_sourceRoot C address ⟨saved.root,initialShape saved.shape⟩
    program table frozen captured auth clean
  have assembled (current : EnteredPacket p Q iv boundary) (member : current ∈ packets final) :=
    fromCapture_exact address ⟨saved.root,initialShape saved.shape⟩ program
      original saved current table frozen
      (by rw [capturedRegistry_enabled _ _ _ _ _ (mentions current member)]; exact captured)
      ring t _ (by
        intro earlier
        rw [PCSBCSSourcePacketTape.rawPrefix_table]
        exact raws (current.predecessor earlier) (predecessor_mem_packets final current member earlier))
      (source_inverse _ _ _ C _ _ _ (addressRoles current member)
        (List.mem_map.mpr ⟨⟨.inl current,table (.inl current)⟩,recorded current member,rfl⟩)
        (transport current member))
  simp only [root] at assembled
  refine ⟨bound,?_,?_⟩
  · intro current member
    exact ⟨_,assembled current member,rfl,rfl,rfl⟩
  · exact accepted_failure_path_of_snapshots address
      ⟨saved.root,initialShape saved.shape⟩ program original saved table (packets final)
      (Sampling.execute table program).2 _ ring t strategy recorded assembled raws
      (packets_consecutive final terminal) (packets_initial final terminal)
      (packets_terminal final terminal) (packets_nonempty final) accepted failure

#print axioms captured_sourceRoot
#print axioms source_inverse
#print axioms accepted_failure_statePath
#print axioms sourceRoot_current_independent
#print axioms roles_from_transport
end Whir.PCSBCSCapturedSourceAcceptance
