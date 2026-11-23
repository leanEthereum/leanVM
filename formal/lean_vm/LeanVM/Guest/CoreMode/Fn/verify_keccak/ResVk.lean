/-
  LeanVM.Guest.CoreMode.Fn.verify_keccak.ResVk

  `verify_keccak`'s values at an honest frame: its table's log-height, its cursor, the pack rounds'
  split, and its layers' returned cursors.
-/

module

public import LeanVM.Guest.CoreMode.Fn.keccak_layer.ResStL
public import LeanVM.Guest.CoreMode.Fn.check_opening_terminal.ResE
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_keccak»

/-!
# `verify_keccak`'s returned cursors

`vk_rets`: step `s` of `verify_keccak`'s body gets back from its layer the cursor
`1 + (s + 1)·(84 + 2(τ - 3))` words past its own (`vk_curs`, `layer_ret`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.VerifySub
open LeanVM.Guest.B2C (cellJ fsN idxOf)
open LeanVM.Guest.Bridge (FnAl)
open LeanVM.Guest.Res (topAtoms)
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Prover.Exec

public section

/-- **`verify_keccak`'s returned cursors**: step `s`'s layer returns the cursor
`1 + (s + 1)·(84 + 2(τ - 3))` words past `verify_keccak`'s. -/
theorem vk_rets {rd : Reader} {C : CallRel} (hC : CallRel.Le C (coreProgram.Rel rd)) {σ : Val}
    {kret : List E → Prop} {τ : ℕ} (hτ1 : 9 ≤ τ) (hτ2 : τ ≤ 28) (htg : σ (.n (val% «verify_keccak» "tau_g")) = gen ^ τ)
    {body : List Stmt} (hbd : body = vkT) (hb : Stmt.HoldsList C rd σ body False kret) :
    ∀ s < 12, σ ((vkCall s).2.2.getD 5 (.n (val% «verify_keccak» "fs0@1"))) = σ (.n (val% «verify_keccak» "cursor@1")) * gen ^ (1 + (s + 1) * (84 + 2 * (τ - 3))) := by
  obtain ⟨h33, h47, hcur⟩ := vk_curs hC hτ1 hτ2 htg hbd hb
  subst hbd
  rw [vkT, holdsList_append, holdsList_append, holdsList_append, holdsList_append, holdsList_append] at hb
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hb⟩ := vkHeadT_holds hτ1 hτ2 htg hb
  rw [holdsList_noRet _ vkFirstT_noRet] at hb
  replace hb := hb.2
  rw [holdsList_noRet _ vkStepsT_noRet] at hb
  obtain ⟨-, hc⟩ := holdsList_mem vkStepsT_noRet hb.1
  intro s hs
  have hcl := hc _ _ _ (vkCall_mem hs)
  have hf := List.all_eq_true.mp vkCall_facts s (List.mem_range.mpr hs)
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨hl16, h7⟩, h9⟩, h10⟩, -⟩, hl6⟩, -⟩, hname⟩ := hf
  rw [hname] at hcl
  have hfirst : (if s = 0 then 1 else 0) < 2 := by split <;> omega
  obtain ⟨ws, hws⟩ := layer_ret hfirst (y := τ - 3) (by omega) (hC _ _ _ hcl)
    (by rw [getD_map_V (by omega), h9]; exact h33) (by rw [getD_map_V (by omega), h10]; exact h47)
  have hlw : ws.length = 5 := by
    have := congrArg List.length hws
    simp only [List.length_map, List.length_append, List.length_singleton] at this
    omega
  have e := congrArg (·.getD ws.length 0) hws
  rw [getD_snoc, hlw, getD_map_V (by omega), getD_map_V (by omega), h7, hcur s hs, mul_assoc,
    ← pow_add] at e
  rw [e]
  congr 2
  ring

variable {A : String → FnAl} {r : Ref} {K : Mode.Cert} {i : ℕ} {e : Bridge.Ent} {j : ℕ}

end

end LeanVM.Guest.EndExec
