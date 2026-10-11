import Whir.PCSBCSRestorationCertificate

/-! The source application must fix the complete original caller input and incoming public trace independently of the queried packet's answer. Values can be absorbed/public and points can be earlier verifier coins; this law does not pretend every coordinate was serialized. Actual source reconstruction must prove the law, not assume original claims true. -/
namespace Whir.PCSBCSCallerBinding
open Concrete Protocol CausalGame CausalProbability ParameterBounds
open PCSRoundByRoundKnowledge PCSBCSRestorationHazard
open PCSStateRestoration.Adaptive

set_option autoImplicit false

structure CallerInput (p : Profile) where
  lanes : Nat
  m : Nat
  family : Fin m → RingPCSGame.FamilyClaim
  points : Array RingPCSGame.PointClaim
  anchorPoint : Array E
  anchorValue : E
  prepared : OriginalClaimsChecker.Prepared (config p) lanes m family points anchorPoint anchorValue
  familyCap : m ≤ 2^64
  claimCap : points.size + 2 ≤ 2^64

structure CallerData (p : Profile) where
  original : CallerInput p
  observed : PublicData (config p)

noncomputable def fixedCertificate (p : Profile) (input : CallerInput p) :=
  certificate p input.lanes input.family input.points input.anchorPoint input.anchorValue input.prepared

noncomputable def callerCertificate (p : Profile) :
    Certificate (Coordinate (config p)) PCSBCSRounds.Raw (CallerData p) where
  before data q := (fixedCertificate p data.original).before data.observed q
  after data q answer := (fixedCertificate p data.original).after data.observed q answer

theorem caller_fiber (p : Profile) (data : CallerData p) (q : Coordinate (config p))
    (undoomed : (callerCertificate p).before data q = false) :
    Soundness.uniformProb (Finset.univ.filter fun answer : PCSBCSRounds.Raw q =>
      (callerCertificate p).after data q answer = true) ≤ rbrError := by
  classical
  change Soundness.uniformProb (Finset.univ.filter fun answer : PCSBCSRounds.Raw q =>
    (fixedCertificate p data.original).after data.observed q answer = true) ≤ rbrError
  change (fixedCertificate p data.original).before data.observed q = false at undoomed
  by_cases initial : q = .initial
  · subst q
    exact initial_fiber p data.original.lanes data.original.family data.original.points
      data.original.anchorPoint data.original.anchorValue data.original.prepared
      data.original.familyCap data.original.claimCap data.observed
  · exact noninitial_fiber p data.original.lanes data.original.family data.original.points
      data.original.anchorPoint data.original.anchorValue data.original.prepared
      data.original.claimCap data.observed q initial undoomed

abbrev Table (p : Profile) (Key : Type) (coordinate : Key → Coordinate (config p)) :=
  (key : Key) → PCSBCSRounds.Raw (coordinate key)

/-- This is the explicit source precondition, not a primitive soundness premise:
changing only the current packet answer cannot change the original caller input,
its frozen root or strictly incoming trace. Earlier latent coins may be used. -/
def CallerBoundBeforeDraw (p : Profile) {Key : Type} [DecidableEq Key]
    (coordinate : Key → Coordinate (config p))
    (snapshot : Key → Table p Key coordinate → CallerData p) : Prop :=
  ∀ key table answer, snapshot key (Function.update table key answer) = snapshot key table

/-- The actual varying-table fiber reduces to the proved additive RBR fiber
only under the named caller-binding law. This theorem does not assert that the
public generic Rust stack API absorbs a supplied statement. -/
theorem caller_source_fiber (p : Profile) {Key : Type} [DecidableEq Key]
    (coordinate : Key → Coordinate (config p))
    (snapshot : Key → Table p Key coordinate → CallerData p)
    (callerBinding : CallerBoundBeforeDraw p coordinate snapshot)
    (key : Key) (table : Table p Key coordinate)
    (undoomed : (callerCertificate p).before (snapshot key table) (coordinate key) = false) :
    Soundness.uniformProb (Finset.univ.filter fun answer : PCSBCSRounds.Raw (coordinate key) =>
      (callerCertificate p).after (snapshot key (Function.update table key answer)) (coordinate key) answer = true) ≤
        rbrError := by
  classical
  have same :
      (Finset.univ.filter fun answer : PCSBCSRounds.Raw (coordinate key) =>
        (callerCertificate p).after (snapshot key (Function.update table key answer)) (coordinate key) answer = true) =
      (Finset.univ.filter fun answer : PCSBCSRounds.Raw (coordinate key) =>
        (callerCertificate p).after (snapshot key table) (coordinate key) answer = true) := by
    congr 1
    funext answer
    rw [callerBinding key table answer]
  rw [same]
  exact caller_fiber p (snapshot key table) (coordinate key) undoomed

#print axioms caller_fiber
#print axioms caller_source_fiber
end Whir.PCSBCSCallerBinding
