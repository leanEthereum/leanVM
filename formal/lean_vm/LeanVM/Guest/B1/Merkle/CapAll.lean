/-
  LeanVM.Guest.B1.Merkle.CapAll

  B1 for the deployed `verify_merkle_cap` specializations, cap depths 2 to 8.
-/

module

public import LeanVM.Guest.B1.Merkle.Cap
public import LeanVM.Guest.B1.Common.Find

/-!
# `verify_merkle_cap__L2 .. L8` (TRIAGE #34)

Each body is `mcBody (2^D)` by kernel evaluation (`stmtsEqb_sound`); `merkle_cap_iffL` gives
the meaning.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem core1122_body : Fn.body Data.core1021 = mcBody (2 ^ 2) := stmtsEqb_sound (by decide +kernel)
theorem core1110_body : Fn.body Data.core1008 = mcBody (2 ^ 3) := stmtsEqb_sound (by decide +kernel)
theorem core1112_body : Fn.body Data.core1010 = mcBody (2 ^ 4) := stmtsEqb_sound (by decide +kernel)
theorem core1114_body : Fn.body Data.core1012 = mcBody (2 ^ 5) := stmtsEqb_sound (by decide +kernel)
theorem core1130_body : Fn.body Data.core1014 = mcBody (2 ^ 6) := stmtsEqb_sound (by decide +kernel)
theorem core1120_body : Fn.body Data.core1031 = mcBody (2 ^ 7) := stmtsEqb_sound (by decide +kernel)
theorem core1108_body : Fn.body Data.core1235 = mcBody (2 ^ 8) := stmtsEqb_sound (by decide +kernel)

theorem merkle_cap_at {name : String} {f : Fn} (D : ℕ) (hD : 2 ≤ D)
    (hfind : coreProgram.find? name = some f) (hparams : f.params = [.n 0, .n 1])
    (hbody : f.body = mcBody (2 ^ D)) (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd name args rets ↔ MeaningVerifyMerkleCap D rd args rets := by
  have hL : 4 ≤ 2 ^ D := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hD)
  have hL2 : 2 ^ D % 2 = 0 := by
    obtain ⟨e, rfl⟩ : ∃ e, D = e + 1 := ⟨D - 1, by omega⟩
    rw [pow_succ, Nat.mul_mod_left]
  rw [meaningCapL_iff]
  exact merkle_cap_iffL (2 ^ D) hL hL2 hfind hparams hbody rd args rets

set_option maxRecDepth 100000 in
/-- **`verify_merkle_cap`'s core IR is its meaning**, at the deployed cap depths. -/
theorem verify_merkle_cap_holds : verify_merkle_cap_Spec := by
  intro p hp
  simp only [merkleCapNames, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact merkle_cap_at 2 le_rfl (coreProgram_find?_at (j := 1021) rfl)
      rfl core1122_body
  · exact merkle_cap_at 3 (by omega) (coreProgram_find?_at (j := 1008) rfl)
      rfl core1110_body
  · exact merkle_cap_at 4 (by omega) (coreProgram_find?_at (j := 1010) rfl)
      rfl core1112_body
  · exact merkle_cap_at 5 (by omega) (coreProgram_find?_at (j := 1012) rfl)
      rfl core1114_body
  · exact merkle_cap_at 6 (by omega) (coreProgram_find?_at (j := 1014) rfl)
      rfl core1130_body
  · exact merkle_cap_at 7 (by omega) (coreProgram_find?_at (j := 1031) rfl)
      rfl core1120_body
  · exact merkle_cap_at 8 (by omega) (coreProgram_find?_at (j := 1235) rfl)
      rfl core1108_body

end
end LeanVM.Guest.B1
