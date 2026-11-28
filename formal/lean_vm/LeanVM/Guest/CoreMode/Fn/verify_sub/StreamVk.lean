/-
  LeanVM.Guest.CoreMode.Fn.verify_sub.StreamVk

  `verify_sub`'s cursor past `verify_keccak`, exactly: `cursor@4 = cursor@3·g^(144 + 24(h - 3) + 1106)` at the Keccak
  table's height `kb[7] = g^h` (`vs_c2920x`, from `vk_retCur`).
-/

module

public import LeanVM.Guest.CoreMode.Fn.verify_sub.StreamCur
public import LeanVM.Guest.CoreMode.Fn.verify_sub.VkCarry
public import LeanVM.Guest.CoreMode.Fn.verify_keccak.Cur

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.B1
open LeanVM.Guest.B1.VerifySub LeanVM.Protocol.Verifier

public section

/-- **The cursor past `verify_keccak`**: `cursor@4 = cursor@3·g^(144 + 24(h - 3) + 1106)` (`kb[7] = g^h`,
`9 ≤ h ≤ 24`). -/
theorem vs_c2920x {bytecode : List K} {κ : ℕ} {L : MemoryImage κ} {C : CallRel} {V : FrameMap} {σ : Val}
    {rets : List E} (R : VsRun bytecode L C V σ rets) :
    ∃ h, 9 ≤ h ∧ h ≤ 24 ∧ σ (.n 120) = gen ^ h ∧
      σ (.n 2920) = σ (.n 1076) * gen ^ (144 + (24 * (h - 3) + 1106)) := by
  have hK := R.slice vsKeccakT_eq
  simp only [vsKeccakT, Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil] at hK
  obtain ⟨-, -, k2909, k2910, -, -, -, -, kcall, -⟩ := hK
  simp only [Atom.Holds] at k2909 k2910
  have e := vk_retCur (R.hle _ _ _ kcall)
  simp only [List.getD_cons_succ, List.getD_cons_zero] at e
  obtain ⟨h, h1, h2, h120⟩ := vsHeight5_range R.sizesOk
  have h9 : 9 ≤ h := h1
  replace h120 : σ (.n 120) = gen ^ h := h120
  refine ⟨h, h9, h2, h120, ?_⟩
  have e2910 : σ (.n 2910) = σ (.n 1076) * gen ^ 144 := by rw [k2910, k2909, word_g144]
  obtain ⟨t, rfl⟩ : ∃ t, h = t + 3 := ⟨h - 3, by omega⟩
  apply mul_right_cancel₀ (Value.gen_pow_ne_zero 72)
  rw [e, e2910, h120, Nat.add_sub_cancel]
  ring

end

end LeanVM.Guest.EndExec
