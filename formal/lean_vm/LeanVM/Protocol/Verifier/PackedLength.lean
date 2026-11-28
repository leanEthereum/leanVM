/-
  LeanVM.Protocol.Verifier.PackedLength

  A packed draw gives as many challenges as it is asked for.
-/

module

public import Statement.Verifier.Transcript

/-!
# Packed draws' lengths

`samplesPacked F sponge n` (`Sponge::samples_packed`, `transcript.rs`) returns `n` challenges
(`length_samplesPacked`): the ground challenge and up to six of the grind's permutation, then
whole permutations with enough fuel (`length_squeezePackedChunks`).
-/

namespace LeanVM.Protocol.Compile.VerifierProgram

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

/-- A packed squeeze with enough fuel gives the challenges asked for. -/
theorem length_squeezePackedChunks (F : KeccakState → Id KeccakState) :
    ∀ (fuel : ℕ) (sponge : Sponge) (missing : ℕ), missing ≤ fuel →
      (squeezePackedChunks F fuel sponge missing).run.1.length = missing
  | 0, _, missing, h => by
    obtain rfl : missing = 0 := by omega
    simp [squeezePackedChunks]
  | _ + 1, _, 0, _ => by simp [squeezePackedChunks]
  | fuel + 1, sponge, missing + 1, h => by
    simp only [squeezePackedChunks, Id.run_bind, Id.run_pure, List.length_append,
      List.length_map, List.length_range]
    rw [length_squeezePackedChunks F fuel _ _ (by omega)]
    omega

/-- **A packed draw gives the challenges asked for.** -/
theorem length_samplesPacked (F : KeccakState → Id KeccakState) (sponge : Sponge) (n : ℕ) :
    (samplesPacked F sponge n).run.1.length = n := by
  rcases n with _ | c
  · simp [samplesPacked, squeezePackedChunks]
  · rcases hg : sponge.ground with _ | g
    · simp only [samplesPacked, hg, Id.run_bind, Id.run_pure, List.length_append, List.length_nil,
        Nat.sub_zero, zero_add]
      exact length_squeezePackedChunks F _ _ _ le_rfl
    · simp only [samplesPacked, hg, Id.run_bind, Id.run_pure, List.length_append,
        List.length_cons, List.length_map, List.length_take, List.length_range]
      rw [length_squeezePackedChunks F _ _ _ le_rfl]
      omega

end

end LeanVM.Protocol.Compile.VerifierProgram
