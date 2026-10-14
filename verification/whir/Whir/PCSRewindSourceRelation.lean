import Whir.PCSRewindSourceProgram
import Whir.CountedCandidateCheckOriginalCorrectness

/-! Deterministic source output correctness includes the fixed Root0 candidate
relation, all uncompressed family slices, all ordinary/strided claims, and the
same literal retained anchor. It is stronger than observing Option.some. -/
namespace Whir.PCSRewindSource
open Concrete Protocol CausalGame KnowledgeExtraction OriginalClaimsChecker

structure ExplainsOriginal {m : Nat} (c : Config) (lanes : Nat) (root : BaseOracle)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E) (w : Witness c lanes) : Prop where
  rootCandidate : w ∈ InitialCandidates.witnesses c lanes root
  original : RingPCSGame.Honest c lanes family points w
  anchor : CommitmentAnchor.value c lanes w anchorPoint = anchorValue

/-- Every actual returned output explains the original source statement and
belongs to the original Root0 list. No probability/certificate premise appears. -/
theorem run_output_explains {m : Nat} (profile : ParameterBounds.Profile) (attempts rounds lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E) (root : BaseOracle)
    (strategy : RingPCSGame.Prefix → Strategy) (seed : RepeatedSeed profile attempts rounds)
    (w : Witness (ParameterBounds.config profile) lanes)
    (output : (run profile attempts rounds lanes family points anchorPoint anchorValue root strategy seed).output = some w) :
    ExplainsOriginal (ParameterBounds.config profile) lanes root family points anchorPoint anchorValue w := by
  cases prepared : prepare (ParameterBounds.config profile) lanes family points anchorPoint anchorValue with
  | none => simp [run, prepared] at output
  | some cached =>
    simp only [run, prepared] at output
    have member := (runAttempts_root profile rounds lanes family points anchorPoint anchorValue cached root strategy
      cached.guards.2.2.2.1 (List.ofFn seed) w output).1
    have original := (check_iff cached w).mp
      (runAttempts_checked profile rounds lanes family points anchorPoint anchorValue cached root strategy
        (List.ofFn seed) w output)
    exact ⟨member, original.1, original.2⟩

/-- A returned word outside the Root0 relation or violating ANY original
functional is impossible, not hidden in a no-output probability predicate. -/
theorem run_ne_wrong_output {m : Nat} (profile : ParameterBounds.Profile) (attempts rounds lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E) (root : BaseOracle)
    (strategy : RingPCSGame.Prefix → Strategy) (seed : RepeatedSeed profile attempts rounds)
    (w : Witness (ParameterBounds.config profile) lanes)
    (wrong : ¬ ExplainsOriginal (ParameterBounds.config profile) lanes root family points anchorPoint anchorValue w) :
    (run profile attempts rounds lanes family points anchorPoint anchorValue root strategy seed).output ≠ some w := by
  intro returned
  exact wrong (run_output_explains _ _ _ _ _ _ _ _ _ _ _ w returned)

#print axioms run_output_explains
#print axioms run_ne_wrong_output
end Whir.PCSRewindSource
