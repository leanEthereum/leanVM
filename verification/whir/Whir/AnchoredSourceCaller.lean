import Whir.AnchoredHeaderCodec
import Whir.WHIRCallerSource
import Whir.WHIRCallerSupport
import Whir.CommitmentAnchor

/-! The 32c CPU/recursion scalar projection retains the existing production payload interpreter and its public layouts. It reads one original header, derives one anchor point from the prior byte stream, retains its value, and compares the complete record at the stack boundary before opening batching. Original context is the native captured input to this parser, not a serialized claim or a caller-selected output cache. -/
namespace Whir.AnchoredSourceCaller
open Concrete FiatShamirGame WHIRCallerClaims AnchoredHeaderCodec

def shape (layout : CallerLayout) : Shape :=
  ⟨callerMu layout,6,callerRate layout,callerLanes layout⟩

/-- These are the source's range guards. No unmerged selector-alignment guard is introduced. -/
def prelude : CallerLayout → CallerParser Unit
  | .recursion _ => pure ()
  | .cpu layout => do
      check (layout.tables.length == 11)
      readAnnouncements (layout.tables.map CpuTableLayout.tau ++ [layout.logInvRate])
      let clock ← readScalar
      check (clock.c1 == 0 && clock.c2 == 0 && clock.c0.toNat / 2^40 == 1 && clock.c0.toNat % 32 == 0)

def receive (layout : CallerLayout) (original : Context) : CallerParser Record := do
  check (decide (shape layout).Valid)
  let header ← readScalars 5
  let some root := parseHeader (shape layout) header | return ← (fun _ => none)
  let point ← drawScalars (shape layout).logN
  let value ← readScalar
  pure ⟨shape layout,root,original,point,value⟩

def payload : CallerLayout → CallerParser (List RingPCSGame.FamilyClaim × Array RingPCSGame.PointClaim)
  | .recursion layout => recPayload layout
  | .cpu layout => cpuPayload layout

/-- Literal equality is checked on every transported record scalar before the caller may produce its final opening input. -/
def binding (record : Record) : CallerParser Unit := do
  let frame ← readScalars (openingScalars record).length
  check (frame == openingScalars record)

structure Claims where
  record : Record
  caller : CallerClaims

/-- This source projection covers the immutable original record and every original production claim; the anchor is retained separately for the occupied-prefix verifier, not disguised as a full-cube PointClaim. -/
def sourceClaims (layout : CallerLayout) (original : Context) : CallerParser Claims := do
  prelude layout
  let record ← receive layout original
  let (families,points) ← payload layout
  binding record
  pure ⟨record,⟨record.root,families,points⟩⟩

def reads (n : Nat) : List WHIRCallerShape.EventShape := List.replicate n (.absorb 24)
def draws (n : Nat) : List WHIRCallerShape.EventShape := List.replicate n (.squeeze 24)

/-- The actual extra anchor run and full retransmitted original context are counted. The old payload schedule is retained, not a second caller convention. -/
def callerShape (layout : CallerLayout) (pendingBytes : Nat) : List WHIRCallerShape.EventShape :=
  reads (rootScalarCount layout-2) ++ reads 5 ++ draws (shape layout).logN ++ reads 1 ++
    (WHIRCallerClaims.callerShape layout).drop (rootScalarCount layout) ++
    reads (10+(shape layout).logN+(pendingBytes+23)/24)

def entryLength (layout : CallerLayout) (pendingBytes : Nat) : Nat :=
  WHIRCallerShape.entryCount (callerShape layout pendingBytes)

def outputCap (layout : CallerLayout) (pendingBytes : Nat) : Nat :=
  WHIRCallerShape.callerOutputCap (callerShape layout pendingBytes)

/-- An exact caller parse rejects all leftover tokens, including a second resampled anchor or a substituted opening record. -/
def interpret (layout : CallerLayout) (original : Context) (tokens : List CallerToken) : Option Claims := do
  if tokensShape tokens ≠ callerShape layout original.pendingBytes then none else do
    let (claims,rest) ← sourceClaims layout original tokens
    if rest.isEmpty then some claims else none

def decode (layout : CallerLayout) (original : Context) (entry : FramedHistory)
    (answers : Coordinate → Digest32) : Option Claims := do
  let tokens ← entryTokens entry answers
  interpret layout original tokens

def physical (compression : DuplexRefinement.Compression) (iv : Digest32)
    (layout : CallerLayout) (original : Context) (entry : FramedHistory) : Option Claims := do
  let tokens ← WHIRCallerClaims.sourceTokens compression iv entry
  interpret layout original tokens

theorem decode_physical (compression : DuplexRefinement.Compression) (iv : Digest32)
    (layout : CallerLayout) (original : Context) (entry : FramedHistory)
    (answers : Coordinate → Digest32)
    (observed : ∀ q ∈ WHIRCallerOutputs.callerOutputs entry,
      answers q = DuplexRefinement.evalCoordinate compression iv q) :
    decode layout original entry answers = physical compression iv layout original entry := by
  simp only [decode,physical,entryTokens_source compression iv entry answers observed]

theorem binding_exact (record : Record) (suffix : List CallerToken) :
    binding record ((openingScalars record).map CallerToken.sent ++ suffix) = some ((),suffix) := by
  change ((readScalars (openingScalars record).length
    ((openingScalars record).map CallerToken.sent ++ suffix)).bind
      (fun pair => check (pair.1 == openingScalars record) pair.2)) = some ((),suffix)
  rw [readScalars_sent]
  simp [check]
  rfl

open WHIRCallerGeometry

theorem payload_geometry (C R : Nat → Nat → Prop) (columnDown : Downward C) (ringDown : Downward R)
    (layout : CallerLayout) (geometry : LayoutGeometry C R layout) :
    Ensures (payload layout) (PayloadValid C R (callerPlacements layout)) := by
  cases layout with
  | cpu layout => exact cpuPayload_geometry C R columnDown ringDown layout geometry
  | recursion layout => exact recPayload_geometry C R columnDown ringDown layout geometry

theorem sourceClaims_geometry (C R : Nat → Nat → Prop) (columnDown : Downward C) (ringDown : Downward R)
    (layout : CallerLayout) (geometry : LayoutGeometry C R layout) (original : Context) :
    Ensures (sourceClaims layout original) (fun claims => ClaimsValid C R (callerPlacements layout) claims.caller) := by
  unfold sourceClaims
  refine ensures_bind_any _ _ _ ?_
  intro _
  refine ensures_bind_any _ _ _ ?_
  intro record
  refine ensures_bind _ _ _ _ (payload_geometry C R columnDown ringDown layout geometry) ?_
  intro result valid
  refine ensures_bind_any _ _ _ ?_
  intro _
  exact ensures_pure _ _ valid

theorem decode_geometry (model : WHIRCallerSupport.ProductionLayout) (original : Context)
    (entry : FramedHistory) (answers : Coordinate → Digest32) (claims : Claims)
    (accepted : decode model.layout original entry answers = some claims) :
    ClaimsValid (fun i d => WHIRCallerSupport.columnFits model.sources i d = true)
      (fun o d => WHIRCallerSupport.ringFits model.sources o d = true)
      (callerPlacements model.layout) claims.caller := by
  cases trace : entryTokens entry answers with
  | none => simp [decode,trace] at accepted
  | some tokens =>
    have interpreted : interpret model.layout original tokens = some claims := by
      simpa [decode,trace] using accepted
    unfold interpret at interpreted
    split at interpreted
    · contradiction
    · cases parsed : sourceClaims model.layout original tokens with
      | none => simp [parsed] at interpreted
      | some result =>
        simp only [parsed] at interpreted
        change (if result.2.isEmpty then some result.1 else none) = some claims at interpreted
        split at interpreted
        · cases Option.some.inj interpreted
          exact sourceClaims_geometry _ _ (WHIRCallerSupport.columnFits_mono model.sources)
            (WHIRCallerSupport.ringFits_mono model.sources) model.layout model.geometry original
            tokens result.1 result.2 parsed
        · contradiction

/-- Native dimensions and occupied support come from the same constructed production layout as the historical payload, not an assumed claim-coverage predicate. -/
theorem decode_nativeShapes (model : WHIRCallerSupport.ProductionLayout) (p : ParameterBounds.Profile)
    (lanes : Nat) (metadata : openingMatches p lanes model.layout = true)
    (laneBound : lanes ≤ 2^(ParameterBounds.config p).folds[0]!)
    (original : Context) (entry : FramedHistory) (answers : Coordinate → Digest32) (claims : Claims)
    (accepted : decode model.layout original entry answers = some claims) :
    SuccinctRingWeight.FamilyShape (ParameterBounds.config p).logN
      (fun i : Fin claims.caller.families.length => claims.caller.families[i]) ∧
    (∀ point ∈ claims.caller.points.toList, SuccinctPointWeight.Shape (ParameterBounds.config p).logN point) := by
  exact WHIRCallerSupport.geometry_nativeShapes model p lanes metadata laneBound claims.caller
    (decode_geometry model original entry answers claims accepted)

theorem geometry_anchored_shapes (model : WHIRCallerSupport.ProductionLayout) (p : ParameterBounds.Profile)
    (lanes : Nat) (metadata : openingMatches p lanes model.layout = true)
    (laneBound : lanes ≤ 2^(ParameterBounds.config p).folds[0]!)
    (decoded : Claims)
    (geometry : WHIRCallerGeometry.ClaimsValid
      (fun i d => WHIRCallerSupport.columnFits model.sources i d = true)
      (fun o d => WHIRCallerSupport.ringFits model.sources o d = true) (callerPlacements model.layout) decoded.caller)
    (seed : RingPCSGame.Prefix) (lambda : E) (point : Array E) (value : E) :
    let c := ParameterBounds.config p
    let claims := (RingPCSGame.transformedClaims (2^c.logN)
      (fun j : Fin decoded.caller.families.length => decoded.caller.families[j]) decoded.caller.points seed).push
        ⟨CommitmentAnchor.weight c lanes point,value⟩
    (claims.all (fun claim => Protocol.shapeValid c lanes claim.weight) = true) ∧
      Protocol.shapeValid c lanes (CausalGame.batchClaims (2^c.logN) claims lambda).weight = true := by
  obtain ⟨rings,points⟩ := WHIRCallerSupport.geometry_support model decoded.caller geometry
  have occupied := WHIRCallerSupport.openingMatches_occupied model.layout p lanes metadata
  let c := ParameterBounds.config p
  let claims := (RingPCSGame.transformedClaims (2^c.logN)
    (fun j : Fin decoded.caller.families.length => decoded.caller.families[j]) decoded.caller.points seed).push
      ⟨CommitmentAnchor.weight c lanes point,value⟩
  have supported : ∀ claim ∈ claims.toList, claim.weight.size = 2^c.logN ∧
      ∀ i, lanes*2^(c.logN-c.folds[0]!) ≤ i → i < 2^c.logN → claim.weight[i]! = 0 := by
    intro claim member
    simp only [claims,Array.toList_push,List.mem_append,List.mem_singleton] at member
    rcases member with member | last
    · refine ⟨WHIRCallerSupport.transformed_claim_size _ _ _ _ claim member,?_⟩
      intro i lower upper
      exact WHIRCallerSupport.transformed_claim_support _ (callerWords model.layout) _ _ seed
        (fun j => rings _ (by simp)) points claim member i (occupied.trans lower) upper
    · subst claim
      refine ⟨by simp [CommitmentAnchor.weight],?_⟩
      intro i lower upper
      simp [CommitmentAnchor.weight,ArrayLayout.getElem!_tab _ _ _ upper,Nat.not_lt_of_le lower]
      rfl
  constructor
  · apply Array.all_eq_true'.mpr
    intro claim member
    have supported := supported claim (by simpa [claims,c] using member)
    exact WHIRCallerSupport.shapeValid_of_support c lanes claim.weight
      (ParameterBounds.production_config_valid p).1
      (WHIRCallerSupport.openingMatches_positive model.layout p lanes metadata) laneBound supported.1
      (fun i lower upper => supported.2 i lower (by simpa [supported.1] using upper))
  · apply WHIRCallerSupport.shapeValid_of_support c lanes _
      (ParameterBounds.production_config_valid p).1
      (WHIRCallerSupport.openingMatches_positive model.layout p lanes metadata) laneBound
      (InitialBatching.batchClaims_size _ _ _)
    intro i lower upper
    apply InitialBatching.batchClaims_zero_tail (2^c.logN) (lanes*2^(c.logN-c.folds[0]!)) claims lambda _ i lower
      (by simpa only [InitialBatching.batchClaims_size] using upper)
    intro j i lower upper
    exact (supported claims[j] (by simp)).2 i lower upper

theorem decode_anchored_shapes (model : WHIRCallerSupport.ProductionLayout) (p : ParameterBounds.Profile)
    (lanes : Nat) (metadata : openingMatches p lanes model.layout = true)
    (laneBound : lanes ≤ 2^(ParameterBounds.config p).folds[0]!)
    (original : Context) (entry : FramedHistory) (answers : Coordinate → Digest32) (decoded : Claims)
    (accepted : decode model.layout original entry answers = some decoded)
    (seed : RingPCSGame.Prefix) (lambda : E) (point : Array E) (value : E) :
    let c := ParameterBounds.config p
    let claims := (RingPCSGame.transformedClaims (2^c.logN)
      (fun j : Fin decoded.caller.families.length => decoded.caller.families[j]) decoded.caller.points seed).push
        ⟨CommitmentAnchor.weight c lanes point,value⟩
    (claims.all (fun claim => Protocol.shapeValid c lanes claim.weight) = true) ∧
      Protocol.shapeValid c lanes (CausalGame.batchClaims (2^c.logN) claims lambda).weight = true :=
  geometry_anchored_shapes model p lanes metadata laneBound decoded
    (decode_geometry model original entry answers decoded accepted) seed lambda point value

theorem config_initial_rate : ∀ p : ParameterBounds.Profile,
    (ParameterBounds.config p).rates[0]! = p.2.val+1 := by
  decide +kernel
end Whir.AnchoredSourceCaller
