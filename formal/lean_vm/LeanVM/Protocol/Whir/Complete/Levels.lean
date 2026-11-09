/-
  LeanVM.Protocol.Whir.Complete.Levels

  The honest WHIR levels follow the verifier's: the fold rounds, a non-final level's commitment,
  out-of-domain values, queries and glue, and the final level's check and tail sumcheck.
-/

module

public import LeanVM.Protocol.Whir.Complete.Rounds
public import LeanVM.Protocol.Whir.Complete.Script

namespace LeanVM.Protocol.Whir.Complete

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.Compile
  LeanVM.Protocol.Whir LeanVM.Prover LeanVM.Prover.Enc Finset

@[expose] public section

/-- **One fold round follows the verifier's.** -/
theorem follows_foldRoundA (f w : Array E) (s : ℕ) (sv : WhirState) (cs : Commits) :
    Follows (fun cs' (a : Array E × Array E) (b : WhirState × FoldRound) ↦ cs' = cs ∧
        ∃ θ γ α β u₀ v₀ c₀ v₁ c₁,
          roundTableA f w s (premixA f s θ) (mulXA (premixA f s θ) (s / 2)) = [u₀, v₀, c₀, v₁, c₁] ∧
          b.2 = ⟨θ, α, β⟩ ∧
          b.1 = { sv with claim := (1 + γ) * (u₀ + α * v₀ + β * c₀) +
              γ * ((sv.claim + v₀ + θ * u₀) + α * v₁ + β * c₁), gammas := sv.gammas ++ [γ] } ∧
          a = (foldLanesA f s (premixA f s θ) (mulXA (premixA f s θ) (s / 2)) α β,
            foldPairsA γ w))
      (foldRoundA f w s) (foldRound sv) cs := by
  simp only [foldRoundA, foldRound, Script.grindBits, VerifierProgram.grindProofOfWork,
    Whir.foldGrindingBits, roundTableA, Script.bind_eq, VerifierProgram.bind_eq, Script.pure_eq,
    VerifierProgram.pure_eq, Script.grindS, Script.sampleE, Script.sendList,
    VerifierProgram.readScalar, VerifierProgram.sampleChallenge, Script.bind, VerifierProgram.bind]
  intro θ γ α β
  exact ⟨rfl, θ, γ, α, β, _, _, _, _, _, rfl, rfl, rfl, rfl⟩

end
end LeanVM.Protocol.Whir.Complete
