/-
  LeanVM.Guest.EndExecRVk

  `verify_keccak`'s values at an honest frame: its table's log-height, its cursor, the pack rounds'
  split, and its layers' returned cursors.
-/

module

public import LeanVM.Guest.EndExecRStL
public import LeanVM.Guest.EndExecRE

/-!
# `verify_keccak`'s values

`vk_rets`: step `s` of `verify_keccak`'s body gets back from its layer the cursor
`1 + (s + 1)·(84 + 2(τ - 3))` words past its own (`vk_curs`, `layer_ret`).
`vk_vals`: at an honest frame of `verify_keccak`, `VkQ` (`vkQ_all`), the head's values
(`vkHeadT_holds`: `pack_g = g^(τ - 4)`, `y_g = g^(τ - 3)`, the pack rounds' step and remainder) and the
returned cursors. `vk_cells`: the frame holds `tau_g`, the stream, `pack_g`, `y_g`, `step_g` and
`rem_g`. `split_vk`: `y_g = step_g^8·rem_g` is a split (`SplitAt`).
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
    {kret : List E → Prop} {τ : ℕ} (hτ1 : 9 ≤ τ) (hτ2 : τ ≤ 28) (htg : σ (.n 6) = gen ^ τ)
    {body : List Stmt} (hbd : body = vkT) (hb : Stmt.HoldsList C rd σ body False kret) :
    ∀ s < 12, σ ((vkCall s).2.2.getD 5 (.n 0)) = σ (.n 5) * gen ^ (1 + (s + 1) * (84 + 2 * (τ - 3))) := by
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

theorem vk_idx : idxOf name% «verify_keccak» = some (fn_idx% «verify_keccak») := by
  decide +kernel

/-- `verify_keccak`'s head atoms on every path: `pack_g`, `y_g`, `step_g`, `rem_g`. -/
theorem vk_atoms_top :
    let as := topAtoms (coreOf (fn_idx% «verify_keccak»)).body
    as.contains (.mul (.n 19) (.n 6) (.n 18)) = true ∧ as.contains (.mul (.n 21) (.n 19) (.n 20)) = true ∧
      as.contains (.mul (.n 35) (.n 30) (.n 34)) = true ∧ as.contains (.mul (.n 49) (.n 44) (.n 48)) = true := by
  decide +kernel

/-- `verify_keccak`'s cells: `tau_g`, the cursor, the stream, `pack_g`, `y_g`, `step_g`, `rem_g`. -/
theorem vk_cellsJ :
    let c := cellJ (fn_idx% «verify_keccak»)
    c (.n 6) = 8 ∧ c (.n 5) = 7 ∧ c (.n 12) = 14 ∧ c (.n 19) = 38 ∧ c (.n 21) = 45 ∧ c (.n 35) = 52 ∧
      c (.n 49) = 61 ∧ 738 < fsN (fn_idx% «verify_keccak») := by
  decide +kernel

variable {A : String → FnAl} {r : Ref} {K : Mode.Cert} {i : ℕ} {e : Bridge.Ent} {j : ℕ}

/-- **`verify_keccak`'s values at an honest frame.** -/
theorem vk_vals (t : TopAt A r K i e j) (hr : r.Ok) (hname : (coreOf j).name = name% «verify_keccak») :
    j = fn_idx% «verify_keccak» ∧ ∃ p τ, 9 ≤ τ ∧ τ ≤ 28 ∧ p + vkNeed τ ≤ 8192 ∧
      e.σ (.n 5) = e.σ (.n 12) * gen ^ p ∧ e.σ (.n 6) = gen ^ τ ∧ e.σ (.n 19) = gen ^ (τ - 4) ∧
      e.σ (.n 21) = gen ^ (τ - 3) ∧ e.σ (.n 35) = gen ^ ((τ - 3) / krStep) ∧
      e.σ (.n 49) = gen ^ ((τ - 3) % krStep) ∧
      ∀ s < 12, e.σ ((vkCall s).2.2.getD 5 (.n 0)) = e.σ (.n 5) * gen ^ (1 + (s + 1) * (84 + 2 * (τ - 3))) := by
  obtain ⟨f, bufs, kids, hJ, hfj, hfn⟩ := t.found
  rw [hname] at hfn
  subst hfn
  have hj : j = fn_idx% «verify_keccak» := by
    have := t.idx
    rw [hJ] at this
    exact Option.some.inj (this.symm.trans vk_idx)
  refine ⟨hj, ?_⟩
  have hcf : coreOf j = fn% «verify_keccak» := Option.some.inj (hfj.symm.trans find_vk)
  obtain ⟨p, τ, e5, e6, hτ9, hτ28, hroom⟩ := vkQ_all hr e.I t.inst e.σ bufs kids hJ
  obtain ⟨args, rets, hv⟩ := inst_valid' hr t.inst hJ
  have hfs : ∀ f', 1 ≤ B2C.fs f' := fun f' ↦ by
    unfold B2C.fs; split <;> simp [B2C.mainFrame, Data.mainCells, Data.jtSlots]
  obtain ⟨-, hb⟩ := Res.holds_of_valid hfs hv find_vk
  obtain ⟨h35, h49, -⟩ := vk_curs (fun _ _ _ h ↦ Res.KidRel.rel h) hτ9 hτ28 e6 vk_body hb
  have hrets := vk_rets (fun _ _ _ h ↦ Res.KidRel.rel h) hτ9 hτ28 e6 vk_body hb
  have hb' := hb
  rw [vk_body, vkT, holdsList_append, holdsList_append, holdsList_append, holdsList_append,
    holdsList_append] at hb'
  obtain ⟨h19, h21, -⟩ := vkHeadT_holds hτ9 hτ28 e6 hb'
  exact ⟨p, τ, hτ9, hτ28, hroom, e5, e6, h19, h21, h35, h49, hrets⟩

/-- **`verify_keccak`'s frame cells** hold their values. -/
theorem vk_cells (t : TopAt A r K i e j) (hr : r.Ok) (hname : (coreOf j).name = name% «verify_keccak») :
    let M := refMem r.img
    M (e.I.fp + 8) = e.σ (.n 6) ∧ M (e.I.fp + 14) = e.σ (.n 12) ∧ M (e.I.fp + 38) = e.σ (.n 19) ∧
      M (e.I.fp + 45) = e.σ (.n 21) ∧ M (e.I.fp + 52) = e.σ (.n 35) ∧ M (e.I.fp + 61) = e.σ (.n 49) := by
  obtain ⟨f, bufs, kids, hJ, hfj, hfn⟩ := t.found
  rw [hname] at hfn
  subst hfn
  have hcf : coreOf j = fn% «verify_keccak» := Option.some.inj (hfj.symm.trans find_vk)
  obtain rfl := (vk_vals t hr hname).1
  obtain ⟨c6, -, c12, c19, c21, c35, c49, hfs⟩ := vk_cellsJ
  obtain ⟨vs, hw, hF, -⟩ := t.events hr
  obtain ⟨a19, a21, a35, a49⟩ := vk_atoms_top
  have hp : ∀ k, k < 13 → V.n k ∈ (coreOf (fn_idx% «verify_keccak»)).params := fun k hk ↦ by
    rw [hcf, vk_params]
    simpa using hk
  have cell : ∀ {a : Atom} {x : V}, (topAtoms (coreOf (fn_idx% «verify_keccak»)).body).contains a = true →
      x ∈ atomUses a → 2 ≤ cellJ (fn_idx% «verify_keccak») x → cellJ (fn_idx% «verify_keccak») x < 739 →
      refMem r.img (e.I.fp + cellJ (fn_idx% «verify_keccak») x) = e.σ x := fun ha hx h2 hl ↦
    t.cell hr hF (namedOf_atom (topAtoms_on_path hw (List.contains_iff_mem.mp ha)) hx) h2 (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := t.cell hr hF (List.mem_append_left _ (List.mem_append_left _ (hp 6 (by omega))))
      (by rw [c6]; omega) (by rw [c6]; omega)
    rwa [c6] at this
  · have := t.cell hr hF (List.mem_append_left _ (List.mem_append_left _ (hp 12 (by omega))))
      (by rw [c12]; omega) (by rw [c12]; omega)
    rwa [c12] at this
  · have := cell a19 (x := .n 19) (by simp [atomUses]) (by rw [c19]; omega) (by rw [c19]; omega)
    rwa [c19] at this
  · have := cell a21 (x := .n 21) (by simp [atomUses]) (by rw [c21]; omega) (by rw [c21]; omega)
    rwa [c21] at this
  · have := cell a35 (x := .n 35) (by simp [atomUses]) (by rw [c35]; omega) (by rw [c35]; omega)
    rwa [c35] at this
  · have := cell a49 (x := .n 49) (by simp [atomUses]) (by rw [c49]; omega) (by rw [c49]; omega)
    rwa [c49] at this

/-- **`verify_keccak`'s split**: `y_g = step_g^8·rem_g`. -/
theorem split_vk {A : String → FnAl} :
    SplitAt A (fn_idx% «verify_keccak») (.n 35) (.n 49) (.n 21) 8 := by
  intro r K i e hr t
  have hn : (coreOf (fn_idx% «verify_keccak»)).name = name% «verify_keccak» := by decide +kernel
  obtain ⟨-, p, τ, hτ9, hτ28, -, -, -, -, h21, h35, h49, -⟩ := vk_vals t hr hn
  obtain ⟨-, -, -, m21, m35, m49⟩ := vk_cells t hr hn
  obtain ⟨-, -, -, -, c21, c35, c49, -⟩ := vk_cellsJ
  have hk : krStep = 8 := rfl
  rw [hk] at h35 h49
  refine ⟨(τ - 3) / 8, (τ - 3) % 8, ?_, ?_, ?_, by omega⟩
  · rw [c35, m35, h35, ofK_gpow]
  · rw [c49, m49, h49, ofK_gpow]
  · rw [c21, m21, h21, ofK_gpow, Nat.div_add_mod]

end

end LeanVM.Guest.EndExec
