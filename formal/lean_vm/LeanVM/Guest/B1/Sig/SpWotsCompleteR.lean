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
  have h122 := vals_drop_step spRen_slice_122 h127
  have h117 := vals_drop_step spRen_slice_117 h122
  have h112 := vals_drop_step spRen_slice_112 h117
  have h107 := vals_drop_step spRen_slice_107 h112
  have h102 := vals_drop_step spRen_slice_102 h107
  have h97 := vals_drop_step spRen_slice_97 h102
  have h92 := vals_drop_step spRen_slice_92 h97
  have h87 := vals_drop_step spRen_slice_87 h92
  have h82 := vals_drop_step spRen_slice_82 h87
  have h77 := vals_drop_step spRen_slice_77 h82
  have h72 := vals_drop_step spRen_slice_72 h77
  have h67 := vals_drop_step spRen_slice_67 h72
  have h62 := vals_drop_step spRen_slice_62 h67
  have h57 := vals_drop_step spRen_slice_57 h62
  have h52 := vals_drop_step spRen_slice_52 h57
  have h47 := vals_drop_step spRen_slice_47 h52
  have h42 := vals_drop_step spRen_slice_42 h47
  have h37 := vals_drop_step spRen_slice_37 h42
  have h32 := vals_drop_step spRen_slice_32 h37
  have h27 := vals_drop_step spRen_slice_27 h32
  have h22 := vals_drop_step spRen_slice_22 h27
  have h12 := vals_drop_step spRen_slice_12 h22
  have h0 := vals_drop_step spRen_slice_0 h12
  intro v hv
  exact spUnOK_iff (h0 v (by rwa [List.drop_zero]))

/-- **`sp_wots` is complete**: for canonical `pp`, `a0`, `a1`, digits below `4` of sum `128` and
canonical chain values, on a memory of at least `64` words, its body holds of some valuation whose
arguments are `pp`, `a0`, `a1` and the digits' encoding (`spX`), returning the one-time leaf of the
values (`spLeafCell`). -/
theorem sp_wots_complete_cells {pp a0 a1 : E} (hpp : IsCanonical128 pp) (ha0 : IsCanonical128 a0)
    (ha1 : IsCanonical128 a1) {d : Nat → Nat} (hd : ∀ i, d i < 4)
    (hsum : ∑ i ∈ Finset.range 64, d i = 128) {vals : Nat → E} (hv : ∀ i, IsCanonical128 (vals i))
    (hm : MemOK rd 64) :
    ∃ σ : Val, σ (.n 0) = pp ∧ σ (.n 1) = a0 ∧ σ (.n 2) = a1 ∧ σ (.n 3) = eOfNat128 (spX d 64) ∧
      Stmt.HoldsList C rd σ Data.core19.body False (fun rs => rs = [spLeafCell pp a0 a1 d vals]) := by
  obtain ⟨σ', h0, h1, h2, h3, hh⟩ := sp_wots_completeT (C := C) hpp ha0 ha1 hd hsum hv hm
  have e : ∀ j ≤ 29, (σ' ∘ spUn) (.n j) = σ' (.n j) := fun j hj => by
    simp [spUn, spRi_small hj, V.n]
  refine ⟨σ' ∘ spUn, by rw [e 0 (by norm_num), h0], by rw [e 1 (by norm_num), h1],
    by rw [e 2 (by norm_num), h2], by rw [e 3 (by norm_num), h3], ?_⟩
  rw [spBody_eq, spBody, Stmt.holdsList_rename]
  refine (holdsList_congr spBodyT (fun v hv => ?_) _ _).mpr hh
  simp only [Function.comp_apply, spUn_spRen v hv]

end
end LeanVM.Guest.B1.Sig
