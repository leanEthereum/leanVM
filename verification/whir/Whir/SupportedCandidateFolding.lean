import Whir.SupportedCandidateExtraction

/-! Same-target reconstruction along an explicitly supplied actual fold schedule.
Each schedule step excludes exactly the same-set MCA RowBad event; no new
existence or honest-prover assumption is introduced. -/
namespace Whir.SupportedCandidateExtraction
open Concrete Protocol CandidateFolding MutualAgreement

variable {F I : Type*} [Field F] [Fintype F] [Inhabited F] [CharP F 2]

/-- The function index is the actual composition of executable coefficient folds.
The schedule carries all MCA exclusions separately from decoder proximity. -/
inductive SafeFoldSchedule {k : Nat} (top : Bool)
    (enc : (Fin k → F) →ₗ[F] (I → F)) (C : Submodule F (I → F)) (threshold : Nat) :
    {start finish : Nat} → (Fin start → I → F) → (Fin finish → I → F) →
      (Array F → Array F) → Prop
  | done {lanes : Nat} (oracle : Fin lanes → I → F) :
      SafeFoldSchedule top enc C threshold oracle oracle id
  | step {lanes finish : Nat} (oracle : Fin (lanes * 2) → I → F) (z : F)
      (good : ¬ RowBad foldGenerator C threshold
        ![fun lane => oracle (evenLane lane), fun lane => oracle (oddLane lane)] z)
      {last : Fin finish → I → F} {transform : Array F → Array F}
      (rest : SafeFoldSchedule top enc C threshold (foldOracle oracle z) last transform) :
      SafeFoldSchedule top enc C threshold oracle last
        (fun a => transform (foldValues a (foldBlock top k) z))

/-- The GIVEN target is lifted, not replaced by another final-list candidate. -/
theorem same_target_lifts {k start finish : Nat} (top : Bool)
    (enc : (Fin k → F) →ₗ[F] (I → F)) (C : Submodule F (I → F))
    (rangeEq : LinearMap.range enc = C) (threshold : Nat)
    (oracle : Fin start → I → F) (last : Fin finish → I → F)
    (transform : Array F → Array F)
    (schedule : SafeFoldSchedule top enc C threshold oracle last transform)
    (target : Array F) (member : target ∈ arrayCandidates top enc last threshold) :
    ∃ original ∈ arrayCandidates top enc oracle threshold, transform original = target := by
  induction schedule with
  | done oracle => exact ⟨target, member, rfl⟩
  | step oracle z good rest ih =>
    obtain ⟨middle, hmiddle, hequal⟩ := ih member
    obtain ⟨original, horiginal, hfold⟩ := array_lifts top enc C rangeEq oracle threshold z good
      middle hmiddle
    exact ⟨original, horiginal, by simpa only [← hfold] using hequal⟩

/-- Once instantiated at the initial committed rows, lifting yields a literal
occupied K witness whose folded image is exactly the fixed OOD-selected target. -/
theorem initial_same_target (input : CausalGame.Public)
    (foldBound : input.config.folds[0]! ≤ input.config.logN)
    (laneBound : input.lanes ≤ laneCount input.config)
    (depth : input.config.logN - input.config.folds[0]! + input.config.rates[0]! ≤ 64)
    (threshold : width input.config - 1 < ParameterBounds.threshold input.config 0)
    {finish : Nat} (last : Fin finish → Fin (blockLength input.config) → E)
    (transform : Array E → Array E)
    (schedule : SafeFoldSchedule true
      (concreteEncoder (input.config.logN - input.config.folds[0]!)
        input.config.rates[0]!)
      (LinearMap.range (concreteEncoder
        (input.config.logN - input.config.folds[0]!) input.config.rates[0]!))
      (ParameterBounds.threshold input.config 0)
      (fun lane q => E.ofK (InitialCandidates.fullRow input.config input.lanes input.root lane q))
      last transform)
    (target : Array E)
    (member : target ∈ arrayCandidates true
      (concreteEncoder (input.config.logN - input.config.folds[0]!)
        input.config.rates[0]!) last (ParameterBounds.threshold input.config 0)) :
    ∃ w ∈ InitialCandidates.witnesses input.config input.lanes input.root,
      transform (CausalGame.paddedWitness input.config input.lanes w) = target := by
  obtain ⟨original, horiginal, equal⟩ := same_target_lifts true _ _ rfl _ _ _ _ schedule target member
  have initial : original ∈ InitialCandidates.extensionCandidates input.config input.lanes input.root :=
    horiginal
  have reconstruction := InitialCandidates.reconstruction input.config input.lanes input.root
    foldBound laneBound depth threshold original initial
  refine ⟨InitialCandidates.project input.config input.lanes original,
    Finset.mem_image.mpr ⟨original, initial, rfl⟩, ?_⟩
  simpa only [← reconstruction] using equal

#print axioms same_target_lifts
#print axioms initial_same_target
end Whir.SupportedCandidateExtraction
