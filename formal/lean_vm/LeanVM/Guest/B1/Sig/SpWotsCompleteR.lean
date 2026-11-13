/-
  LeanVM.Guest.B1.Sig.SpWotsCompleteR

  `sp_wots` is complete in the guest's numbering (`sp_wots_complete_cells`): the template's
  completeness (`sp_wots_completeT`) carried through the renaming `spRen`, undone by `spUn` on
  every value the template names.
-/

module

public import LeanVM.Guest.B1.Sig.SpWotsComplete
public import LeanVM.Guest.B1.Sig.SpWotsData1
public import LeanVM.Guest.B1.Sig.SpWotsRen0
public import LeanVM.Guest.B1.Sig.SpWotsRen1
public import LeanVM.Guest.B1.Sig.SpWotsRen2
public import LeanVM.Guest.B1.Sig.SpWotsRen3

/-!
# `sp_wots`, complete, in the guest's numbering

The guest's body is the template renamed (`spBody = renameList spRen spBodyT`), so it holds of
`σ` when the template holds of `σ ∘ spRen` (`Stmt.holdsList_rename`). `spUn` numbers the guest's
values back (`spRi`: two more for each step without an address constant below), and undoes `spRen`
on every value of the template (`spUn_spRen`, checked by the kernel): a valuation of the template
`σ'` gives `σ' ∘ spUn`, whose `∘ spRen` agrees with `σ'` where the template reads.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

variable {C : CallRel} {rd : Reader}

theorem spRi_small {j : Nat} (hj : j ≤ 29) : spRi j = j := by
  unfold spRi spZeroR
  rw [show List.countP (fun x => decide (x < j)) [29, 146, 241, 324, 391, 486, 569, 640, 695, 778,
    849, 908, 951, 1018, 1073, 1116] = 0 by
      rw [List.countP_eq_zero]
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      simp only [decide_eq_true_eq, not_lt]
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;> omega]
  simp

/-- **`spUn` undoes `spRen`** on every value the template names (`SpWotsRen0` to `SpWotsRen3`). -/
theorem spUn_spRen : ∀ v ∈ Stmt.valsList spBodyT, spUn (spRen v) = v := by
  have h127 : ∀ v ∈ Stmt.valsList (spBodyT.drop 127), spUnOK v = true := by
    rw [spBodyT_split, List.drop_left' (by rw [spHeadT_length]), spLeafK_of, spPadCell]
    exact List.all_eq_true.mp spRen_tail
  have h120 := vals_drop_step spRen_run_120 h127
  have h112 := vals_drop_step spRen_run_112 h120
  have h104 := vals_drop_step spRen_run_104 h112
  have h96 := vals_drop_step spRen_run_96 h104
  have h88 := vals_drop_step spRen_run_88 h96
  have h80 := vals_drop_step spRen_run_80 h88
  have h72 := vals_drop_step spRen_run_72 h80
  have h64 := vals_drop_step spRen_run_64 h72
  have h56 := vals_drop_step spRen_run_56 h64
  have h48 := vals_drop_step spRen_run_48 h56
  have h40 := vals_drop_step spRen_run_40 h48
  have h32 := vals_drop_step spRen_run_32 h40
  have h24 := vals_drop_step spRen_run_24 h32
  have h16 := vals_drop_step spRen_run_16 h24
  have h8 := vals_drop_step spRen_run_8 h16
  have h0 := vals_drop_step spRen_run_0 h8
  intro v hv
  exact spUnOK_iff (h0 v (by rwa [List.drop_zero]))

/-- **`sp_wots` is complete**: for any `pp`, `a0`, `a1`, digits below `4` of sum `128` and chain
values, on a memory of at least `64` words, its body holds of some valuation whose arguments are
`pp`, `a0`, `a1` and the digits' encoding (`spX`), returning the one-time leaf of the values
(`spLeafCell`). -/
theorem sp_wots_complete_cells {pp a0 a1 : E} {d : Nat → Nat} (hd : ∀ i, d i < 4)
    (hsum : ∑ i ∈ Finset.range 64, d i = 128) {vals : Nat → E} (hm : MemOK rd 64) :
    ∃ σ : Val, σ (.n 0) = pp ∧ σ (.n 1) = a0 ∧ σ (.n 2) = a1 ∧ σ (.n 3) = eOfNat128 (spX d 64) ∧
      Stmt.HoldsList C rd σ (fn% «sp_wots»).body False (fun rs => rs = [spLeafCell pp a0 a1 d vals]) := by
  obtain ⟨σ', h0, h1, h2, h3, hh⟩ := sp_wots_completeT (C := C) (pp := pp) (a0 := a0) (a1 := a1) (vals := vals) hd hsum hm
  have e : ∀ j ≤ 29, (σ' ∘ spUn) (.n j) = σ' (.n j) := fun j hj => by
    simp [spUn, spRi_small hj, V.n]
  refine ⟨σ' ∘ spUn, by rw [e 0 (by norm_num), h0], by rw [e 1 (by norm_num), h1],
    by rw [e 2 (by norm_num), h2], by rw [e 3 (by norm_num), h3], ?_⟩
  rw [spBody_eq, spBody, Stmt.holdsList_rename]
  refine (holdsList_congr spBodyT (fun v hv => ?_) _ _).mpr hh
  simp only [Function.comp_apply, spUn_spRen v hv]

end
end LeanVM.Guest.B1.Sig
