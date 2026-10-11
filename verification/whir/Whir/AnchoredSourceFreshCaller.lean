import Whir.AnchoredSourceCaller

/-! Fresh-session scalar projection of the anchored caller. The trusted record is
an input, never received or reconstructed: only the historical payload followed
by its complete binding frame is parsed. This module proves parser/physical
compression correspondence, not packet-driver equivalence, algebraic acceptance,
or concrete BLAKE2s security. `none` deliberately forgets the native error and
consumed cursor; only successful parses have the exact consumption theorem below.
Native metadata validation and error/consumption refinement belong to the driver. -/
namespace Whir.AnchoredSourceFreshCaller
open Concrete FiatShamirGame WHIRCallerClaims AnchoredHeaderCodec
open WHIRCallerGeometry

/-- Keep the original payload schedule, removing exactly its original root and
CPU announcements. No original prelude, header, or anchor sample is replayed. -/
def callerShape (layout : CallerLayout) (saved : Record) : List WHIRCallerShape.EventShape :=
  (WHIRCallerClaims.callerShape layout).drop (rootScalarCount layout) ++
    AnchoredSourceCaller.reads (openingScalars saved).length

def entryLength (layout : CallerLayout) (saved : Record) : Nat :=
  WHIRCallerShape.entryCount (callerShape layout saved)

def outputCap (layout : CallerLayout) (saved : Record) : Nat :=
  WHIRCallerShape.callerOutputCap (callerShape layout saved)

/-- The returned record and root are literally the saved inputs; attacker tokens
can only supply the existing payload and a frame checked against that record. -/
def sourceClaims (layout : CallerLayout) (saved : Record) :
    CallerParser AnchoredSourceCaller.Claims := do
  let (families,points) ← AnchoredSourceCaller.payload layout
  AnchoredSourceCaller.binding saved
  pure ⟨saved,⟨saved.root,families,points⟩⟩

/-- Exact event shape and full consumption are both required. A successful
payload with an inserted original header, resampled anchor, or leftover tokens
cannot bypass either guard. -/
def interpret (layout : CallerLayout) (saved : Record) (tokens : List CallerToken) :
    Option AnchoredSourceCaller.Claims := do
  if tokensShape tokens ≠ callerShape layout saved then none else do
    let (claims,rest) ← sourceClaims layout saved tokens
    if rest.isEmpty then some claims else none

def decode (layout : CallerLayout) (saved : Record) (entry : FramedHistory)
    (answers : Coordinate → Digest32) : Option AnchoredSourceCaller.Claims := do
  let tokens ← entryTokens entry answers
  interpret layout saved tokens

def physical (compression : DuplexRefinement.Compression) (iv : Digest32)
    (layout : CallerLayout) (saved : Record) (entry : FramedHistory) :
    Option AnchoredSourceCaller.Claims := do
  let tokens ← WHIRCallerClaims.sourceTokens compression iv entry
  interpret layout saved tokens

/-- Equality holds for successes and failures, including malformed exact frame
recovery. This does not identify native error constructors or failure cursors. -/
theorem decode_physical (compression : DuplexRefinement.Compression) (iv : Digest32)
    (layout : CallerLayout) (saved : Record) (entry : FramedHistory)
    (answers : Coordinate → Digest32)
    (observed : ∀ q ∈ WHIRCallerOutputs.callerOutputs entry,
      answers q = DuplexRefinement.evalCoordinate compression iv q) :
    decode layout saved entry answers = physical compression iv layout saved entry := by
  simp only [decode,physical,entryTokens_source compression iv entry answers observed]

/-- Literal equality is required even when an altered frame has the same scalar
count and therefore the same fresh event shape. -/
theorem binding_frame_rejected (saved : Record) (frame : List E)
    (suffix : List CallerToken) (length : frame.length = (openingScalars saved).length)
    (changed : frame ≠ openingScalars saved) :
    AnchoredSourceCaller.binding saved (frame.map CallerToken.sent ++ suffix) = none := by
  change ((readScalars (openingScalars saved).length
    (frame.map CallerToken.sent ++ suffix)).bind
      (fun pair => check (pair.1 == openingScalars saved) pair.2)) = none
  rw [← length,readScalars_sent]
  simp [check,changed]

/-- Binding succeeds after exactly the shared payload, without replaying any
part of the original receive operation. The suffix is retained by the state
parser and rejected by the exact `interpret` guard if nonempty. -/
theorem sourceClaims_bound (layout : CallerLayout) (saved : Record)
    (tokens suffix : List CallerToken)
    (families : List RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (payload : AnchoredSourceCaller.payload layout tokens =
      some ((families,points),(openingScalars saved).map CallerToken.sent ++ suffix)) :
    sourceClaims layout saved tokens =
      some (⟨saved,⟨saved.root,families,points⟩⟩,suffix) := by
  change ((AnchoredSourceCaller.payload layout tokens).bind
    (fun pair => ((AnchoredSourceCaller.binding saved pair.2).bind
      (fun bound => some ((⟨saved,⟨saved.root,pair.1.1,pair.1.2⟩⟩ :
        AnchoredSourceCaller.Claims),bound.2))))) = _
  rw [payload]
  simp only [Option.bind_some,AnchoredSourceCaller.binding_exact]

theorem interpret_exact (layout : CallerLayout) (saved : Record)
    (tokens : List CallerToken) (claims : AnchoredSourceCaller.Claims) :
    interpret layout saved tokens = some claims ↔
      tokensShape tokens = callerShape layout saved ∧
        sourceClaims layout saved tokens = some (claims,[]) := by
  unfold interpret
  by_cases shape : tokensShape tokens = callerShape layout saved
  · simp only [shape,ne_eq,not_true_eq_false,↓reduceIte]
    cases parsed : sourceClaims layout saved tokens with
    | none => simp
    | some result =>
      rcases result with ⟨value,rest⟩
      cases rest with
      | nil => simp
      | cons token rest => simp
  · simp [shape]

theorem interpret_shape_rejected (layout : CallerLayout) (saved : Record)
    (tokens : List CallerToken) (mismatch : tokensShape tokens ≠ callerShape layout saved) :
    interpret layout saved tokens = none := by
  simp [interpret,mismatch]

theorem interpret_leftover_rejected (layout : CallerLayout) (saved : Record)
    (tokens rest : List CallerToken) (claims : AnchoredSourceCaller.Claims)
    (parsed : sourceClaims layout saved tokens = some (claims,rest)) (leftover : rest ≠ []) :
    interpret layout saved tokens = none := by
  unfold interpret
  split
  · rfl
  · simp only [parsed]
    cases rest with
    | nil => contradiction
    | cons token rest => rfl

/-- Every accepted entry decodes to the exact fresh shape and leaves no scalar,
draw, or nonce token. Frame decoding additionally checks exact entry identity. -/
theorem decode_exact (layout : CallerLayout) (saved : Record) (entry : FramedHistory)
    (answers : Coordinate → Digest32) (claims : AnchoredSourceCaller.Claims)
    (accepted : decode layout saved entry answers = some claims) :
    ∃ tokens, entryTokens entry answers = some tokens ∧
      tokensShape tokens = callerShape layout saved ∧
      sourceClaims layout saved tokens = some (claims,[]) := by
  cases trace : entryTokens entry answers with
  | none => simp [decode,trace] at accepted
  | some tokens =>
    have interpreted : interpret layout saved tokens = some claims := by
      simpa [decode,trace] using accepted
    exact ⟨tokens,rfl,(interpret_exact layout saved tokens claims).mp interpreted⟩

theorem sourceClaims_retained (layout : CallerLayout) (saved : Record) :
    Ensures (sourceClaims layout saved) (fun claims =>
      claims.record = saved ∧ claims.caller.root = saved.root) := by
  unfold sourceClaims
  refine ensures_bind_any _ _ _ ?_
  intro result
  refine ensures_bind_any _ _ _ ?_
  intro _
  exact ensures_pure _ _ ⟨rfl,rfl⟩

theorem decode_retained (layout : CallerLayout) (saved : Record) (entry : FramedHistory)
    (answers : Coordinate → Digest32) (claims : AnchoredSourceCaller.Claims)
    (accepted : decode layout saved entry answers = some claims) :
    claims.record = saved ∧ claims.caller.root = saved.root := by
  obtain ⟨tokens,_,_,parsed⟩ := decode_exact layout saved entry answers claims accepted
  exact sourceClaims_retained layout saved tokens claims [] parsed

theorem sourceClaims_geometry (C R : Nat → Nat → Prop) (columnDown : Downward C)
    (ringDown : Downward R) (layout : CallerLayout) (geometry : LayoutGeometry C R layout)
    (saved : Record) : Ensures (sourceClaims layout saved) (fun claims =>
      ClaimsValid C R (callerPlacements layout) claims.caller) := by
  unfold sourceClaims
  refine ensures_bind _ _ _ _
    (AnchoredSourceCaller.payload_geometry C R columnDown ringDown layout geometry) ?_
  intro result valid
  refine ensures_bind_any _ _ _ ?_
  intro _
  exact ensures_pure _ _ valid

theorem decode_geometry (model : WHIRCallerSupport.ProductionLayout) (saved : Record)
    (entry : FramedHistory) (answers : Coordinate → Digest32)
    (claims : AnchoredSourceCaller.Claims)
    (accepted : decode model.layout saved entry answers = some claims) :
    ClaimsValid (fun i d => WHIRCallerSupport.columnFits model.sources i d = true)
      (fun o d => WHIRCallerSupport.ringFits model.sources o d = true)
      (callerPlacements model.layout) claims.caller := by
  obtain ⟨tokens,_,_,parsed⟩ := decode_exact model.layout saved entry answers claims accepted
  exact sourceClaims_geometry _ _ (WHIRCallerSupport.columnFits_mono model.sources)
    (WHIRCallerSupport.ringFits_mono model.sources) model.layout model.geometry saved
    tokens claims [] parsed

theorem decode_nativeShapes (model : WHIRCallerSupport.ProductionLayout)
    (p : ParameterBounds.Profile) (lanes : Nat)
    (metadata : openingMatches p lanes model.layout = true)
    (laneBound : lanes ≤ 2^(ParameterBounds.config p).folds[0]!) (saved : Record)
    (entry : FramedHistory) (answers : Coordinate → Digest32)
    (claims : AnchoredSourceCaller.Claims)
    (accepted : decode model.layout saved entry answers = some claims) :
    SuccinctRingWeight.FamilyShape (ParameterBounds.config p).logN
      (fun i : Fin claims.caller.families.length => claims.caller.families[i]) ∧
    (∀ point ∈ claims.caller.points.toList,
      SuccinctPointWeight.Shape (ParameterBounds.config p).logN point) := by
  exact WHIRCallerSupport.geometry_nativeShapes model p lanes metadata laneBound claims.caller
    (decode_geometry model saved entry answers claims accepted)

/-- The same geometry/support helper as the original caller, including the saved
anchor as an occupied-prefix claim, rather than a fabricated full-cube claim. -/
theorem decode_anchored_shapes (model : WHIRCallerSupport.ProductionLayout)
    (p : ParameterBounds.Profile) (lanes : Nat)
    (metadata : openingMatches p lanes model.layout = true)
    (laneBound : lanes ≤ 2^(ParameterBounds.config p).folds[0]!) (saved : Record)
    (entry : FramedHistory) (answers : Coordinate → Digest32)
    (decoded : AnchoredSourceCaller.Claims)
    (accepted : decode model.layout saved entry answers = some decoded)
    (seed : RingPCSGame.Prefix) (lambda : E) :
    let c := ParameterBounds.config p
    let claims := (RingPCSGame.transformedClaims (2^c.logN)
      (fun j : Fin decoded.caller.families.length => decoded.caller.families[j])
        decoded.caller.points seed).push
          ⟨CommitmentAnchor.weight c lanes saved.point.toArray,saved.value⟩
    (claims.all (fun claim => Protocol.shapeValid c lanes claim.weight) = true) ∧
      Protocol.shapeValid c lanes (CausalGame.batchClaims (2^c.logN) claims lambda).weight = true :=
  AnchoredSourceCaller.geometry_anchored_shapes model p lanes metadata laneBound decoded
    (decode_geometry model saved entry answers decoded accepted) seed lambda saved.point.toArray saved.value

end Whir.AnchoredSourceFreshCaller
