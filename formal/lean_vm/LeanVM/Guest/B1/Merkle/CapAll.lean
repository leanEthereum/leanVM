/-
  LeanVM.Guest.B1.Merkle.CapAll

  B1 for the deployed `verify_merkle_cap` specializations, cap depths 4 to 8.
-/

module

public import LeanVM.Guest.B1.Merkle.Cap

/-!
# `verify_merkle_cap__L4 .. L8` (TRIAGE #34)

Each body is `mcBody (2^D)` by kernel evaluation (`stmtsEqb_sound`); `merkle_cap_iffL` gives
the meaning.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem core501_body : Fn.body Data.core1112 = mcBody (2 ^ 4) := stmtsEqb_sound (by decide +kernel)
theorem core399_body : Fn.body Data.core1114 = mcBody (2 ^ 5) := stmtsEqb_sound (by decide +kernel)
theorem core395_body : Fn.body Data.core1130 = mcBody (2 ^ 6) := stmtsEqb_sound (by decide +kernel)
theorem core510_body : Fn.body Data.core1120 = mcBody (2 ^ 7) := stmtsEqb_sound (by decide +kernel)
theorem core390_body : Fn.body Data.core1108 = mcBody (2 ^ 8) := stmtsEqb_sound (by decide +kernel)

theorem merkle_cap_at {name : String} {f : Fn} (D : ℕ) (hD : 4 ≤ D)
    (hfind : coreProgram.find? name = some f) (hparams : f.params = [.n 0, .n 1])
    (hbody : f.body = mcBody (2 ^ D)) (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd name args rets ↔ MeaningVerifyMerkleCap D rd args rets := by
  have hL : 16 ≤ 2 ^ D := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hD)
  have hL2 : 2 ^ D % 2 = 0 := by
    obtain ⟨e, rfl⟩ : ∃ e, D = e + 1 := ⟨D - 1, by omega⟩
    rw [pow_succ, Nat.mul_mod_left]
  rw [meaningCapL_iff]
  exact merkle_cap_iffL (2 ^ D) hL hL2 hfind hparams hbody rd args rets

set_option maxRecDepth 100000 in
/-- **`verify_merkle_cap`'s core IR is its meaning**, at the five deployed cap depths. -/
theorem verify_merkle_cap_holds : verify_merkle_cap_Spec := by
  intro p hp
  simp only [merkleCapNames, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact merkle_cap_at 4 le_rfl (Program.find?_of_indexOf? (j := 1112) (by decide +kernel) rfl)
      rfl core501_body
  · exact merkle_cap_at 5 (by omega) (Program.find?_of_indexOf? (j := 1114) (by decide +kernel) rfl)
      rfl core399_body
  · exact merkle_cap_at 6 (by omega) (Program.find?_of_indexOf? (j := 1130) (by decide +kernel) rfl)
      rfl core395_body
  · exact merkle_cap_at 7 (by omega) (Program.find?_of_indexOf? (j := 1120) (by decide +kernel) rfl)
      rfl core510_body
  · exact merkle_cap_at 8 (by omega) (Program.find?_of_indexOf? (j := 1108) (by decide +kernel) rfl)
      rfl core390_body

end
end LeanVM.Guest.B1
