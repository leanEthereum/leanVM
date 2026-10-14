import Whir.AnchoredSourceFreshCaller
import Whir.PCSBCSCallerBinding

/-! Original caller inputs are constructed from the actual fresh source decoder.
The two cardinality guards delimit the proof model, not production validation.
Preparation uses the existing executable original-claims checker, including the
independently saved anchor; no claim truth or hash security is asserted. -/
set_option autoImplicit false
namespace Whir.PCSBCSSourceCallerOriginal
open Concrete FiatShamirGame WHIRCallerClaims AnchoredHeaderCodec
open PCSBCSCallerBinding

/-- The exact indexed family returned by the source payload parser. -/
def indexedFamily (claims : AnchoredSourceCaller.Claims) :
    Fin claims.caller.families.length → RingPCSGame.FamilyClaim :=
  fun j => claims.caller.families[j]

/-- Decode the actual framed source, check the proof-model domain, and run the
existing preparation algorithm on its original claims and saved anchor. -/
def original (p : ParameterBounds.Profile) (layout : CallerLayout) (saved : Record)
    (entry : FramedHistory) (answers : Coordinate → Digest32) : Option (CallerInput p) := do
  let claims ← AnchoredSourceFreshCaller.decode layout saved entry answers
  if familyCap : claims.caller.families.length ≤ 2^64 then
    if claimCap : claims.caller.points.size + 2 ≤ 2^64 then do
      let prepared ← OriginalClaimsChecker.prepare (ParameterBounds.config p) saved.shape.lanes
        (indexedFamily claims) claims.caller.points saved.point.toArray saved.value
      pure ⟨saved.shape.lanes,claims.caller.families.length,indexedFamily claims,
        claims.caller.points,saved.point.toArray,saved.value,prepared,familyCap,claimCap⟩
    else none
  else none

/-- Success identifies the exact constructor record, not merely an extensionally
matching family callback, and exposes the actual preparation result. -/
theorem original_exact (p : ParameterBounds.Profile) (layout : CallerLayout) (saved : Record)
    (entry : FramedHistory) (answers : Coordinate → Digest32) (input : CallerInput p)
    (accepted : original p layout saved entry answers = some input) :
    ∃ (claims : AnchoredSourceCaller.Claims)
      (familyCap : claims.caller.families.length ≤ 2^64)
      (claimCap : claims.caller.points.size + 2 ≤ 2^64)
      (prepared : OriginalClaimsChecker.Prepared (ParameterBounds.config p) saved.shape.lanes
        claims.caller.families.length (indexedFamily claims) claims.caller.points
        saved.point.toArray saved.value),
      AnchoredSourceFreshCaller.decode layout saved entry answers = some claims ∧
      claims.record = saved ∧ claims.caller.root = saved.root ∧
      OriginalClaimsChecker.prepare (ParameterBounds.config p) saved.shape.lanes
        (indexedFamily claims) claims.caller.points saved.point.toArray saved.value = some prepared ∧
      input = ⟨saved.shape.lanes,claims.caller.families.length,indexedFamily claims,
        claims.caller.points,saved.point.toArray,saved.value,prepared,familyCap,claimCap⟩ := by
  unfold original at accepted
  obtain ⟨claims,decoded,continued⟩ := Option.bind_eq_some_iff.mp accepted
  split at continued
  next familyCap =>
    split at continued
    next claimCap =>
      obtain ⟨prepared,preparedEq,result⟩ := Option.bind_eq_some_iff.mp continued
      obtain ⟨recordEq,rootEq⟩ := AnchoredSourceFreshCaller.decode_retained
        layout saved entry answers claims decoded
      exact ⟨claims,familyCap,claimCap,prepared,decoded,recordEq,rootEq,preparedEq,
        (Option.some.inj result).symm⟩
    next => cases continued
  next => cases continued

/-- All caller-bound fields are literal source/saved fields. -/
theorem original_bound (p : ParameterBounds.Profile) (layout : CallerLayout) (saved : Record)
    (entry : FramedHistory) (answers : Coordinate → Digest32) (input : CallerInput p)
    (accepted : original p layout saved entry answers = some input) :
    input.lanes = saved.shape.lanes ∧ input.anchorPoint = saved.point.toArray ∧
    input.anchorValue = saved.value ∧
    ∃ claims : AnchoredSourceCaller.Claims,
      AnchoredSourceFreshCaller.decode layout saved entry answers = some claims ∧
      claims.record = saved ∧ claims.caller.root = saved.root ∧
      ∃ h : input.m = claims.caller.families.length,
        input.family = (fun j => indexedFamily claims (Fin.cast h j)) ∧
        input.points = claims.caller.points := by
  obtain ⟨claims,fc,cc,prepared,decoded,recordEq,rootEq,_,rfl⟩ :=
    original_exact p layout saved entry answers input accepted
  exact ⟨rfl,rfl,rfl,claims,decoded,recordEq,rootEq,rfl,rfl,rfl⟩

/-- The returned dependent prepared value is the result of the existing
algorithm on the returned caller fields, not a proof-only clone. -/
theorem original_prepared (p : ParameterBounds.Profile) (layout : CallerLayout) (saved : Record)
    (entry : FramedHistory) (answers : Coordinate → Digest32) (input : CallerInput p)
    (accepted : original p layout saved entry answers = some input) :
    OriginalClaimsChecker.prepare (ParameterBounds.config p) input.lanes input.family input.points
      input.anchorPoint input.anchorValue = some input.prepared := by
  obtain ⟨claims,fc,cc,prepared,_,_,_,preparedEq,rfl⟩ :=
    original_exact p layout saved entry answers input accepted
  exact preparedEq

/-- Equality holds for the complete dependent constructor result, including
failures, when only unobserved source answers change. -/
theorem original_prior_only (p : ParameterBounds.Profile) (layout : CallerLayout) (saved : Record)
    (entry : FramedHistory) (a b : Coordinate → Digest32)
    (agree : ∀ q ∈ WHIRCallerOutputs.callerOutputs entry, a q = b q) :
    original p layout saved entry a = original p layout saved entry b := by
  have decoded : AnchoredSourceFreshCaller.decode layout saved entry a =
      AnchoredSourceFreshCaller.decode layout saved entry b := by
    simp only [AnchoredSourceFreshCaller.decode,
      entryTokens_prior_only entry a b agree]
  simp only [original,decoded]

#print axioms original_exact
#print axioms original_bound
#print axioms original_prepared
#print axioms original_prior_only
end Whir.PCSBCSSourceCallerOriginal
