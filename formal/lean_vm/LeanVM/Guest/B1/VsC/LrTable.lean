/-
  LeanVM.Guest.B1.VsC.LrTable

  Every specialization's `level_residual` loops complete, by the kernel's checks over `lrTable`.
-/

module

public import LeanVM.Guest.B1.VsC.LrC2

/-!
# `level_residual`'s loops, every specialization

`lr_checks`: the kernel decides `lr1Checks` and `lr2Checks` for each `lrTable` entry, so each
entry's two loops complete from every iteration (`lr1_loop`, `lr2_loop`) and every valid tree of
them has its shape (`lr1_shape`, `lr2_shape`).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Whir

@[expose] public section

theorem lr_checks_0 : lr1Checks 10 6 3 "__loop0_level_residual__L10_L6_L3" = true ∧ lr2Checks 10 6 3 "__loop1_level_residual__L10_L6_L3" = true := by
  decide +kernel

theorem lr_checks_1 : lr1Checks 6 4 2 "__loop0_level_residual__L6_L4_L2" = true ∧ lr2Checks 6 4 2 "__loop1_level_residual__L6_L4_L2" = true := by
  decide +kernel

theorem lr_checks_2 : lr1Checks 11 6 3 "__loop0_level_residual__L11_L6_L3" = true ∧ lr2Checks 11 6 3 "__loop1_level_residual__L11_L6_L3" = true := by
  decide +kernel

theorem lr_checks_3 : lr1Checks 7 4 2 "__loop0_level_residual__L7_L4_L2" = true ∧ lr2Checks 7 4 2 "__loop1_level_residual__L7_L4_L2" = true := by
  decide +kernel

theorem lr_checks_4 : lr1Checks 12 6 3 "__loop0_level_residual__L12_L6_L3" = true ∧ lr2Checks 12 6 3 "__loop1_level_residual__L12_L6_L3" = true := by
  decide +kernel

theorem lr_checks_5 : lr1Checks 8 4 2 "__loop0_level_residual__L8_L4_L2" = true ∧ lr2Checks 8 4 2 "__loop1_level_residual__L8_L4_L2" = true := by
  decide +kernel

theorem lr_checks_6 : lr1Checks 13 6 3 "__loop0_level_residual__L13_L6_L3" = true ∧ lr2Checks 13 6 3 "__loop1_level_residual__L13_L6_L3" = true := by
  decide +kernel

theorem lr_checks_7 : lr1Checks 9 4 2 "__loop0_level_residual__L9_L4_L2" = true ∧ lr2Checks 9 4 2 "__loop1_level_residual__L9_L4_L2" = true := by
  decide +kernel

theorem lr_checks_8 : lr1Checks 14 6 3 "__loop0_level_residual__L14_L6_L3" = true ∧ lr2Checks 14 6 3 "__loop1_level_residual__L14_L6_L3" = true := by
  decide +kernel

theorem lr_checks_9 : lr1Checks 10 4 2 "__loop0_level_residual__L10_L4_L2" = true ∧ lr2Checks 10 4 2 "__loop1_level_residual__L10_L4_L2" = true := by
  decide +kernel

theorem lr_checks_10 : lr1Checks 15 6 3 "__loop0_level_residual__L15_L6_L3" = true ∧ lr2Checks 15 6 3 "__loop1_level_residual__L15_L6_L3" = true := by
  decide +kernel

theorem lr_checks_11 : lr1Checks 11 4 2 "__loop0_level_residual__L11_L4_L2" = true ∧ lr2Checks 11 4 2 "__loop1_level_residual__L11_L4_L2" = true := by
  decide +kernel

theorem lr_checks_12 : lr1Checks 16 6 3 "__loop0_level_residual__L16_L6_L3" = true ∧ lr2Checks 16 6 3 "__loop1_level_residual__L16_L6_L3" = true := by
  decide +kernel

theorem lr_checks_13 : lr1Checks 12 4 2 "__loop0_level_residual__L12_L4_L2" = true ∧ lr2Checks 12 4 2 "__loop1_level_residual__L12_L4_L2" = true := by
  decide +kernel

theorem lr_checks_14 : lr1Checks 17 6 3 "__loop0_level_residual__L17_L6_L3" = true ∧ lr2Checks 17 6 3 "__loop1_level_residual__L17_L6_L3" = true := by
  decide +kernel

theorem lr_checks_15 : lr1Checks 13 4 2 "__loop0_level_residual__L13_L4_L2" = true ∧ lr2Checks 13 4 2 "__loop1_level_residual__L13_L4_L2" = true := by
  decide +kernel

theorem lr_checks_16 : lr1Checks 18 6 3 "__loop0_level_residual__L18_L6_L3" = true ∧ lr2Checks 18 6 3 "__loop1_level_residual__L18_L6_L3" = true := by
  decide +kernel

theorem lr_checks_17 : lr1Checks 14 4 2 "__loop0_level_residual__L14_L4_L2" = true ∧ lr2Checks 14 4 2 "__loop1_level_residual__L14_L4_L2" = true := by
  decide +kernel

theorem lr_checks_18 : lr1Checks 19 6 3 "__loop0_level_residual__L19_L6_L3" = true ∧ lr2Checks 19 6 3 "__loop1_level_residual__L19_L6_L3" = true := by
  decide +kernel

theorem lr_checks_19 : lr1Checks 15 4 2 "__loop0_level_residual__L15_L4_L2" = true ∧ lr2Checks 15 4 2 "__loop1_level_residual__L15_L4_L2" = true := by
  decide +kernel

theorem lr_checks_20 : lr1Checks 20 6 3 "__loop0_level_residual__L20_L6_L3" = true ∧ lr2Checks 20 6 3 "__loop1_level_residual__L20_L6_L3" = true := by
  decide +kernel

theorem lr_checks_21 : lr1Checks 16 4 2 "__loop0_level_residual__L16_L4_L2" = true ∧ lr2Checks 16 4 2 "__loop1_level_residual__L16_L4_L2" = true := by
  decide +kernel

theorem lr_checks_22 : lr1Checks 21 6 3 "__loop0_level_residual__L21_L6_L3" = true ∧ lr2Checks 21 6 3 "__loop1_level_residual__L21_L6_L3" = true := by
  decide +kernel

theorem lr_checks_23 : lr1Checks 17 4 2 "__loop0_level_residual__L17_L4_L2" = true ∧ lr2Checks 17 4 2 "__loop1_level_residual__L17_L4_L2" = true := by
  decide +kernel

theorem lr_checks_24 : lr1Checks 22 6 3 "__loop0_level_residual__L22_L6_L3" = true ∧ lr2Checks 22 6 3 "__loop1_level_residual__L22_L6_L3" = true := by
  decide +kernel

theorem lr_checks_25 : lr1Checks 18 4 2 "__loop0_level_residual__L18_L4_L2" = true ∧ lr2Checks 18 4 2 "__loop1_level_residual__L18_L4_L2" = true := by
  decide +kernel

theorem lr_checks_26 : lr1Checks 23 6 3 "__loop0_level_residual__L23_L6_L3" = true ∧ lr2Checks 23 6 3 "__loop1_level_residual__L23_L6_L3" = true := by
  decide +kernel

theorem lr_checks_27 : lr1Checks 19 4 2 "__loop0_level_residual__L19_L4_L2" = true ∧ lr2Checks 19 4 2 "__loop1_level_residual__L19_L4_L2" = true := by
  decide +kernel

theorem lr_checks_28 : lr1Checks 24 6 3 "__loop0_level_residual__L24_L6_L3" = true ∧ lr2Checks 24 6 3 "__loop1_level_residual__L24_L6_L3" = true := by
  decide +kernel

theorem lr_checks_29 : lr1Checks 20 4 2 "__loop0_level_residual__L20_L4_L2" = true ∧ lr2Checks 20 4 2 "__loop1_level_residual__L20_L4_L2" = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **The kernel's checks of every `level_residual` loop**, entry by entry. -/
theorem lr_checks : ∀ e ∈ lrTable, lr1Checks e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 = true ∧
    lr2Checks e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2.2 = true :=
  List.forall_mem_cons.2 ⟨lr_checks_0,
  List.forall_mem_cons.2 ⟨lr_checks_1,
  List.forall_mem_cons.2 ⟨lr_checks_2,
  List.forall_mem_cons.2 ⟨lr_checks_3,
  List.forall_mem_cons.2 ⟨lr_checks_4,
  List.forall_mem_cons.2 ⟨lr_checks_5,
  List.forall_mem_cons.2 ⟨lr_checks_6,
  List.forall_mem_cons.2 ⟨lr_checks_7,
  List.forall_mem_cons.2 ⟨lr_checks_8,
  List.forall_mem_cons.2 ⟨lr_checks_9,
  List.forall_mem_cons.2 ⟨lr_checks_10,
  List.forall_mem_cons.2 ⟨lr_checks_11,
  List.forall_mem_cons.2 ⟨lr_checks_12,
  List.forall_mem_cons.2 ⟨lr_checks_13,
  List.forall_mem_cons.2 ⟨lr_checks_14,
  List.forall_mem_cons.2 ⟨lr_checks_15,
  List.forall_mem_cons.2 ⟨lr_checks_16,
  List.forall_mem_cons.2 ⟨lr_checks_17,
  List.forall_mem_cons.2 ⟨lr_checks_18,
  List.forall_mem_cons.2 ⟨lr_checks_19,
  List.forall_mem_cons.2 ⟨lr_checks_20,
  List.forall_mem_cons.2 ⟨lr_checks_21,
  List.forall_mem_cons.2 ⟨lr_checks_22,
  List.forall_mem_cons.2 ⟨lr_checks_23,
  List.forall_mem_cons.2 ⟨lr_checks_24,
  List.forall_mem_cons.2 ⟨lr_checks_25,
  List.forall_mem_cons.2 ⟨lr_checks_26,
  List.forall_mem_cons.2 ⟨lr_checks_27,
  List.forall_mem_cons.2 ⟨lr_checks_28,
  List.forall_mem_cons.2 ⟨lr_checks_29,
  List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end
end LeanVM.Guest.B1.VsC
