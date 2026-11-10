import Rv64Verifier.Proofs.Walk.R20A

/-!
# `walk` R20: `verify_keccak`'s inputs are never empty

`returns_verifyKeccak`: the openings' point starts with the four sumcheck challenges, and the
slices are `K`'s `kBits` scalars.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol Rv64Verifier.Model Rv64Verifier.Model.Gkr

theorem returns_verifyKeccak (shape : KeccakShape) (inst output : List E) :
    Returns (verifyKeccakRust shape inst output) fun o ↦
      4 ≤ o.inputs.1.length ∧ o.inputs.2.length = Verifier.kBits := by
  unfold verifyKeccakRust
  repeat' (first
    | (refine Returns.bind (Returns.sumcheck _ _ _) fun r hr ↦ ?_; rcases r with ⟨low, value⟩)
    | (refine Returns.bind (Returns.nextScalars _) fun sl hsl ↦ ?_)
    | (refine Returns.pure ?_)
    | (refine Returns.bindAll fun r ↦ ?_)
    | split
    | dsimp only)
  all_goals (simp only [List.length_append, List.length_replicate] at hr ⊢; exact ⟨by omega, hsl⟩)

end Rv64Verifier.Proofs.Walk
