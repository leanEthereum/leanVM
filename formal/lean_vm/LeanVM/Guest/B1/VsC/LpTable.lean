/-
  LeanVM.Guest.B1.VsC.LpTable

  Every `level_positions` loop's template facts, by the kernel, one entry of `lpTable` at a time.
-/

module

public import LeanVM.Guest.B1.VsC.LpLoopA
public import LeanVM.Guest.B1.Bits.QueryWindowsT

/-!
# `level_positions`' loops, every specialization

`lpEntryOk d cd loop`: the loop's template facts (`lpLChecks`) and the decode
`decode_query_windows__L{d}_L{cd}` among `queryWindowsShapes`. `lp_checks`: every `lpTable` entry's,
one `decide +kernel` an entry.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Whir

@[expose] public section

/-- The facts each `level_positions` specialization's proof reads of its loop and decode. -/
def lpEntryOk (d cd : ℕ) (loop : String) : Bool :=
  lpLChecks d cd loop && decide ((dqwName d cd, d, cd) ∈ queryWindowsShapes)

theorem lp_checks_0 : lpEntryOk 11 5 "__loop0_level_positions__L11_L5" = true := by
  decide +kernel

theorem lp_checks_1 : lpEntryOk 12 6 "__loop0_level_positions__L12_L6" = true := by
  decide +kernel

theorem lp_checks_2 : lpEntryOk 13 7 "__loop0_level_positions__L13_L7" = true := by
  decide +kernel

theorem lp_checks_3 : lpEntryOk 14 2 "__loop0_level_positions__L14_L2" = true := by
  decide +kernel

theorem lp_checks_4 : lpEntryOk 10 4 "__loop0_level_positions__L10_L4" = true := by
  decide +kernel

theorem lp_checks_5 : lpEntryOk 9 3 "__loop0_level_positions__L9_L3" = true := by
  decide +kernel

theorem lp_checks_6 : lpEntryOk 15 3 "__loop0_level_positions__L15_L3" = true := by
  decide +kernel

theorem lp_checks_7 : lpEntryOk 16 4 "__loop0_level_positions__L16_L4" = true := by
  decide +kernel

theorem lp_checks_8 : lpEntryOk 14 8 "__loop0_level_positions__L14_L8" = true := by
  decide +kernel

theorem lp_checks_9 : lpEntryOk 17 5 "__loop0_level_positions__L17_L5" = true := by
  decide +kernel

theorem lp_checks_10 : lpEntryOk 18 6 "__loop0_level_positions__L18_L6" = true := by
  decide +kernel

theorem lp_checks_11 : lpEntryOk 19 7 "__loop0_level_positions__L19_L7" = true := by
  decide +kernel

theorem lp_checks_12 : lpEntryOk 20 2 "__loop0_level_positions__L20_L2" = true := by
  decide +kernel

theorem lp_checks_13 : lpEntryOk 21 3 "__loop0_level_positions__L21_L3" = true := by
  decide +kernel

theorem lp_checks_14 : lpEntryOk 22 4 "__loop0_level_positions__L22_L4" = true := by
  decide +kernel

theorem lp_checks_15 : lpEntryOk 20 8 "__loop0_level_positions__L20_L8" = true := by
  decide +kernel

theorem lp_checks_16 : lpEntryOk 23 5 "__loop0_level_positions__L23_L5" = true := by
  decide +kernel

theorem lp_checks_17 : lpEntryOk 24 6 "__loop0_level_positions__L24_L6" = true := by
  decide +kernel

theorem lp_checks_18 : lpEntryOk 25 7 "__loop0_level_positions__L25_L7" = true := by
  decide +kernel

theorem lp_checks_19 : lpEntryOk 26 2 "__loop0_level_positions__L26_L2" = true := by
  decide +kernel

theorem lp_checks_20 : lpEntryOk 27 3 "__loop0_level_positions__L27_L3" = true := by
  decide +kernel

theorem lp_checks_21 : lpEntryOk 28 4 "__loop0_level_positions__L28_L4" = true := by
  decide +kernel

/-- **Every `lpTable` entry's facts.** -/
theorem lp_checks : ∀ e ∈ lpTable, lpEntryOk e.2.2.1 e.2.2.2 e.2.1 = true :=
  List.forall_mem_cons.2 ⟨lp_checks_0,
  List.forall_mem_cons.2 ⟨lp_checks_1,
  List.forall_mem_cons.2 ⟨lp_checks_2,
  List.forall_mem_cons.2 ⟨lp_checks_3,
  List.forall_mem_cons.2 ⟨lp_checks_4,
  List.forall_mem_cons.2 ⟨lp_checks_5,
  List.forall_mem_cons.2 ⟨lp_checks_6,
  List.forall_mem_cons.2 ⟨lp_checks_7,
  List.forall_mem_cons.2 ⟨lp_checks_8,
  List.forall_mem_cons.2 ⟨lp_checks_9,
  List.forall_mem_cons.2 ⟨lp_checks_10,
  List.forall_mem_cons.2 ⟨lp_checks_11,
  List.forall_mem_cons.2 ⟨lp_checks_12,
  List.forall_mem_cons.2 ⟨lp_checks_13,
  List.forall_mem_cons.2 ⟨lp_checks_14,
  List.forall_mem_cons.2 ⟨lp_checks_15,
  List.forall_mem_cons.2 ⟨lp_checks_16,
  List.forall_mem_cons.2 ⟨lp_checks_17,
  List.forall_mem_cons.2 ⟨lp_checks_18,
  List.forall_mem_cons.2 ⟨lp_checks_19,
  List.forall_mem_cons.2 ⟨lp_checks_20,
  List.forall_mem_cons.2 ⟨lp_checks_21,
  List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end
end LeanVM.Guest.B1.VsC
