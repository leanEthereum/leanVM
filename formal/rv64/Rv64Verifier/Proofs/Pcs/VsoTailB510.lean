import Rv64Verifier.Proofs.Pcs.VsoTailMirror

/-!
# `verify_stacked_opening`'s level tail: the last level or the next

`0x8000b510` compares the level at `S - 856` with the last level's index at `S - 888`: the final
level's tail at `0x8000b8ec`, or the back edge at `0x8000b51c`.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- **The branch at `0x8000b510`.** -/
theorem b510 {s z : MachineState} {ℓ : ℕ} (hpre : VsoPre s) (hpc : z.pc = 0x8000b510)
    (hsp : z.getReg .x2 = s.getReg .x2 - 1040)
    (h856 : z.getMem (s.getReg .x2 - 856) = BitVec.ofNat 64 ℓ)
    (h888 : z.getMem (s.getReg .x2 - 888) = BitVec.ofNat 64 (K0 s + 1)) (hℓ : ℓ < K0 s + 2) :
    ∃ z', Reaches Image.code z z' ∧ (∀ a, z'.getMem a = z.getMem a) ∧
      (∀ q ∈ calleeSaved, z'.getReg q = z.getReg q) ∧
      z'.getReg .x1 = BitVec.ofNat 64 (K0 s + 1) ∧
      ((ℓ = K0 s + 1 ∧ z'.pc = 0x8000b8ec) ∨ (ℓ ≠ K0 s + 1 ∧ z'.pc = 0x8000b51c)) := by
  have hb := bounds hpre
  have hK := K0_lt s
  obtain ⟨z', r, h⟩ := Sym.BlockSpec.reaches b8000b510_spec hpc (by
    rv_eval [hsp]; and_intros <;> valid_access hpre.stack.valid [hb])
  have e184 : z.getMem (z.getReg .x2 + 184) = BitVec.ofNat 64 ℓ := by
    rw [hsp, show s.getReg .x2 - 1040 + 184 = s.getReg .x2 - 856 by rv_eval [], h856]
  have e152 : z.getMem (z.getReg .x2 + 152) = BitVec.ofNat 64 (K0 s + 1) := by
    rw [hsp, show s.getReg .x2 - 1040 + 152 = s.getReg .x2 - 888 by rv_eval [], h888]
  refine ⟨z', r, b8000b510_mem_same h, fun q hq ↦ b8000b510_keeps h q (mem_of_calleeSaved hq _),
    by rw [b8000b510_x1 h, e152], ?_⟩
  by_cases hl : ℓ = K0 s + 1
  · exact Or.inl ⟨hl, b8000b510_pc_taken h (by rw [e184, e152, hl])⟩
  · refine Or.inr ⟨hl, b8000b510_pc_not_taken h (by
      rw [e184, e152]; intro he
      have := congrArg BitVec.toNat he
      simp only [BitVec.toNat_ofNat] at this
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
      exact hl this)⟩

end Rv64Verifier.Proofs.Pcs.Vso
