import Rv64Verifier.Proofs.Field.Contracts
import Rv64Verifier.Field.BaseMul

/-!
# `base_mul`'s contract

`Field/BaseMul.lean`'s run, in `BaseMulSpec`'s terms.
-/

namespace Rv64Verifier.Proofs.Field.BaseMulFun
open RiscvZkvm.Rv64 Rv64Verifier.FieldContracts Rv64Verifier.Field

/-- **`base_mul` multiplies in `K`.** -/
theorem base_mul_fun : BaseMulSpec := by
  intro s hpc hpre
  have hsp := hpre.stack.bounds (by decide) (by decide)
  have hP := hpre.pool.apart
  have hpre' : BaseMul.Pre s := ⟨hpre.stack.valid, by
    rw [show ClmulLow.M3 = poolWord by decide]; exact hpre.pool.word, by
    simp only [ClmulLow.poolAddr]; addr_omega [hsp, hP]⟩
  obtain ⟨t, ht, hpc', ha0, hregs, hframe⟩ := Rv64Verifier.Field.BaseMul.base_mul_spec s hpc hpre'
  refine ⟨t, ⟨_, ht⟩, Or.inl ⟨hpc', fun r hr ↦ hregs r (List.mem_cons_of_mem _ hr), ?_, ?_⟩⟩
  · rw [ha0, ← Model.baseMul_eq]
    rfl
  · intro a ha
    apply hframe
    intro i hi heq
    apply ha
    rw [heq]
    addr_omega [hsp, hi]

end Rv64Verifier.Proofs.Field.BaseMulFun
