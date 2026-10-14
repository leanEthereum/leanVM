import Whir.PCSBCSSourceCallerOriginal
import Whir.PCSBCSCallerSourcePolynomialBound
import Whir.PCSBCSPublicLogParserCost
import Whir.CountedCandidateCheckOriginalResources

/-! Accounting for the exact fresh caller decoder and original preparation.
Answer calls are counted per recovered byte, not per block. Opaque saved-record
and CPU output accessors retain their explicit OutputCosts. Indexed family
lookup traverses its actual list; the preparation charge includes this scan.
The units are physical immutable input access and logical source/field work,
not external callback CPU time or native compiler instructions. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Whir.PCSBCSSourceCallerOriginalCost
open Concrete FiatShamirGame WHIRCallerClaims AnchoredHeaderCodec
open PCSBCSCallerPayloadCost
open PCSBCSSourceCallerOriginal PCSBCSCallerBinding

/-- Preserve the actual decoded claims, answer-access count and parser work. -/
def decodeCount (layout : CallerLayout) (saved : Record) (entry : FramedHistory)
    (answers : Coordinate → Digest32) (cost : OutputCosts) :
    Option AnchoredSourceCaller.Claims × Nat × Nat :=
  let tokens := PCSBCSPublicLogParserCost.entryTokensCount entry answers
  match tokens.1 with
  | none => (none,tokens.2.1,tokens.2.2+1)
  | some ts =>
    let parsed := freshInterpret layout saved cost ts
    (parsed.value,tokens.2.1,tokens.2.2+parsed.work+1)

theorem decodeCount_value (layout : CallerLayout) (saved : Record) (entry : FramedHistory)
    (answers : Coordinate → Digest32) (cost : OutputCosts) :
    (decodeCount layout saved entry answers cost).1 =
      AnchoredSourceFreshCaller.decode layout saved entry answers := by
  simp only [decodeCount,AnchoredSourceFreshCaller.decode,
    PCSBCSPublicLogParserCost.entryTokensCount_value]
  cases entryTokens entry answers <;> simp [freshInterpret_erasure]

/-- Reached claims dimensions are public-data sizes, also when preparation
fails. No output or soundness condition is used to discard malformed input. -/
def dimensions (layout : CallerLayout) (saved : Record) (entry : FramedHistory)
    (answers : Coordinate → Digest32) : Nat × Nat :=
  match AnchoredSourceFreshCaller.decode layout saved entry answers with
  | none => (0,0)
  | some claims => (claims.caller.families.length,claims.caller.points.size)

def originalCount (p : ParameterBounds.Profile) (layout : CallerLayout) (saved : Record)
    (entry : FramedHistory) (answers : Coordinate → Digest32) (cost : OutputCosts) :
    Option (CallerInput p) × Nat × Nat :=
  let parsed := decodeCount layout saved entry answers cost
  match parsed.1 with
  | none => (none,parsed.2.1,parsed.2.2+1)
  | some claims =>
    if familyCap : claims.caller.families.length ≤ 2^64 then
      if claimCap : claims.caller.points.size+2 ≤ 2^64 then
        let prepared := OriginalClaimsChecker.countedPrepare (ParameterBounds.config p) saved.shape.lanes
          (indexedFamily claims) claims.caller.points saved.point.toArray saved.value
        (prepared.1.map (fun value =>
          ⟨saved.shape.lanes,claims.caller.families.length,indexedFamily claims,
            claims.caller.points,saved.point.toArray,saved.value,value,familyCap,claimCap⟩),
          parsed.2.1,parsed.2.2+prepared.2.total*(claims.caller.families.length+1)+4)
      else (none,parsed.2.1,parsed.2.2+4)
    else (none,parsed.2.1,parsed.2.2+4)

theorem originalCount_value (p : ParameterBounds.Profile) (layout : CallerLayout) (saved : Record)
    (entry : FramedHistory) (answers : Coordinate → Digest32) (cost : OutputCosts) :
    (originalCount p layout saved entry answers cost).1 = original p layout saved entry answers := by
  simp only [originalCount,original,decodeCount_value]
  cases AnchoredSourceFreshCaller.decode layout saved entry answers with
  | none => rfl
  | some claims =>
    dsimp only [Bind.bind,Option.bind]
    split
    · split
      · simp only [OriginalClaimsChecker.countedPrepare_value]
        cases OriginalClaimsChecker.prepare (ParameterBounds.config p) saved.shape.lanes
          (indexedFamily claims) claims.caller.points saved.point.toArray saved.value <;> rfl
      · rfl
    · rfl

/-- Callback prices are exact reached getter traces. They are not a constant
cost hypothesis on an arbitrary source getter. -/
def getterCharge (layout : CallerLayout) (saved : Record) (entry : FramedHistory)
    (answers : Coordinate → Digest32) (cost : OutputCosts) : Nat :=
  match PCSBCSPublicLogParserCost.entryTokensCount entry answers |>.1 with
  | none => 0
  | some tokens => (freshInterpretGetterTrace layout saved tokens).price cost

def parserPolynomial (P S : Nat) : Nat :=
  PCSBCSPublicLogParserCost.entryParserPolynomial P+freshInterpretWorkPolynomial S+1

theorem decodeCount_bound (layout : CallerLayout) (saved : Record) (entry : FramedHistory)
    (answers : Coordinate → Digest32) (cost : OutputCosts) (P S : Nat)
    (entryCap : PCSBCSPublicLogParserCost.framesSize entry.frames ≤ P)
    (layoutCap : layoutVolume layout ≤ S) (recordCap : recordPublicSize saved ≤ S)
    (tokensCap : P*P ≤ S) :
    (decodeCount layout saved entry answers cost).2.1 ≤ P*P ∧
    (decodeCount layout saved entry answers cost).2.2 ≤
      parserPolynomial P S+getterCharge layout saved entry answers cost := by
  obtain ⟨calls,work⟩ := PCSBCSPublicLogParserCost.entryTokensCount_bound entry answers P entryCap
  unfold decodeCount getterCharge
  dsimp only
  cases tokens : (PCSBCSPublicLogParserCost.entryTokensCount entry answers).1 with
  | none => dsimp only; unfold parserPolynomial; constructor <;> omega
  | some ts =>
    have length := (PCSBCSPublicLogParserCost.entryTokensCount_length entry answers P entryCap ts tokens).trans tokensCap
    have caller := freshInterpret_work_polynomial layout saved cost ts S layoutCap recordCap length
    dsimp only
    unfold parserPolynomial
    constructor <;> omega

def originalPolynomial (p : ParameterBounds.Profile) (P S M T : Nat) : Nat :=
  parserPolynomial P S+
    OriginalClaimsChecker.preparationPolynomial (2^(ParameterBounds.config p).logN) M T*(M+1)+4

theorem originalCount_bound (p : ParameterBounds.Profile) (layout : CallerLayout) (saved : Record)
    (entry : FramedHistory) (answers : Coordinate → Digest32) (cost : OutputCosts) (P S : Nat)
    (entryCap : PCSBCSPublicLogParserCost.framesSize entry.frames ≤ P)
    (layoutCap : layoutVolume layout ≤ S) (recordCap : recordPublicSize saved ≤ S)
    (tokensCap : P*P ≤ S) :
    (originalCount p layout saved entry answers cost).2.1 ≤ P*P ∧
    (originalCount p layout saved entry answers cost).2.2 ≤
      originalPolynomial p P S (dimensions layout saved entry answers).1
        (dimensions layout saved entry answers).2+getterCharge layout saved entry answers cost := by
  obtain ⟨calls,work⟩ := decodeCount_bound layout saved entry answers cost P S
    entryCap layoutCap recordCap tokensCap
  unfold originalCount
  dsimp only
  cases parsed : (decodeCount layout saved entry answers cost).1 with
  | none => dsimp only; unfold originalPolynomial; constructor <;> omega
  | some claims =>
    have actual := (decodeCount_value layout saved entry answers cost).symm.trans parsed
    have prep := OriginalClaimsChecker.countedPrepare_total (ParameterBounds.config p) saved.shape.lanes
      (indexedFamily claims) claims.caller.points saved.point.toArray saved.value
    have weighted := Nat.mul_le_mul_right (claims.caller.families.length+1) prep
    simp only [dimensions,actual,originalPolynomial]
    split
    · split
      · dsimp only; constructor <;> omega
      · dsimp only; constructor <;> omega
    · dsimp only; constructor <;> omega

theorem originalCount_dimensions (p : ParameterBounds.Profile) (layout : CallerLayout) (saved : Record)
    (entry : FramedHistory) (answers : Coordinate → Digest32) (cost : OutputCosts)
    (input : CallerInput p) (returned : (originalCount p layout saved entry answers cost).1 = some input) :
    input.lanes = saved.shape.lanes ∧
      dimensions layout saved entry answers = (input.m,input.points.size) := by
  have actual := (originalCount_value p layout saved entry answers cost).symm.trans returned
  obtain ⟨claims,fc,cc,prepared,decoded,_,_,_,same⟩ :=
    PCSBCSSourceCallerOriginal.original_exact p layout saved entry answers input actual
  subst input
  simp [dimensions,decoded]

#print axioms originalCount_value
#print axioms originalCount_bound
end Whir.PCSBCSSourceCallerOriginalCost
