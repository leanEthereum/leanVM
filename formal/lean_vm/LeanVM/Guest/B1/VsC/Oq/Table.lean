/-
  LeanVM.Guest.B1.VsC.Oq.Table

  Every specialization of `opening_queries` completes placed (`OqA`), by the kernel's check that
  its hints are pinned (`ExactFreeG`) and its functions' templates.
-/

module

public import LeanVM.Guest.B1.VsC.Oq.MainA

/-!
# `opening_queries`, every specialization

`oq_exactFree_k`: entry `k` of `openingQueriesLoops` passes `exactFree` (one `decide +kernel` an
entry); `oq_loop_flag`: its loop helper is one; `oqA_all`: every entry is `OqA`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete

@[expose] public section

/-- **A loop helper with `opening_queries`' template is one.** -/
theorem oq_loop_flag {loop : String} {fl : Fn} (hfl : coreProgram.find? loop = some fl) {s : Oq}
    (hbl : fl.body = oqLoopT s loop) : coreProgram.loop loop = true := by
  have hn : fl.name = loop := by simpa using List.find?_some hfl
  have hbody : ∃ A g args, fl.body = A ++ [.callIf g loop args, .ret []] := by
    rw [hbl]; unfold oqLoopT
    split
    · exact ⟨oqLoop0A s, _, _, by rw [oqLoop0T, oqNextT_eq]⟩
    · exact ⟨oqLoop1A s, _, _, by rw [oqLoop1T, oqNextT_eq]⟩
  obtain ⟨A, g, args, hb⟩ := hbody
  rw [Program.loop_of_find? hfl, Fn.loop, hb]
  simp [List.reverse_append, hn]

theorem oq_exactFree_0 : ExactFreeG (openingQueriesLoops.getD 0 oqNone).1 :=
  exactFreeG_of (by decide +kernel : exactFree "opening_queries__L1_L6_L32_L6_L0_L0_L0_L0_L0" idx% «opening_queries__L1_L6_L32_L6_L0_L0_L0_L0_L0» = true)

theorem oq_exactFree_1 : ExactFreeG (openingQueriesLoops.getD 1 oqNone).1 :=
  exactFreeG_of (by decide +kernel : exactFree "opening_queries__L1_L6_L32_L12_L0_L0_L0_L0_L0" idx% «opening_queries__L1_L6_L32_L12_L0_L0_L0_L0_L0» = true)

theorem oq_exactFree_2 : ExactFreeG (openingQueriesLoops.getD 2 oqNone).1 :=
  exactFreeG_of (by decide +kernel : exactFree "opening_queries__L0_L4_L16_L6_L0_L0_L0_L0_L0" idx% «opening_queries__L0_L4_L16_L6_L0_L0_L0_L0_L0» = true)

theorem oq_exactFree_3 : ExactFreeG (openingQueriesLoops.getD 3 oqNone).1 :=
  exactFreeG_of (by decide +kernel : exactFree "opening_queries__L0_L4_L16_L6_L2_L3_L8_L3_L1" idx% «opening_queries__L0_L4_L16_L6_L2_L3_L8_L3_L1» = true)

theorem oq_exactFree_4 : ExactFreeG (openingQueriesLoops.getD 4 oqNone).1 :=
  exactFreeG_of (by decide +kernel : exactFree "opening_queries__L0_L4_L16_L12_L0_L0_L0_L0_L0" idx% «opening_queries__L0_L4_L16_L12_L0_L0_L0_L0_L0» = true)

theorem oq_exactFree_5 : ExactFreeG (openingQueriesLoops.getD 5 oqNone).1 :=
  exactFreeG_of (by decide +kernel : exactFree "opening_queries__L0_L4_L16_L6_L3_L6_L12_L4_L1" idx% «opening_queries__L0_L4_L16_L6_L3_L6_L12_L4_L1» = true)

theorem oq_exactFree_6 : ExactFreeG (openingQueriesLoops.getD 6 oqNone).1 :=
  exactFreeG_of (by decide +kernel : exactFree "opening_queries__L0_L4_L16_L6_L4_L10_L20_L5_L1" idx% «opening_queries__L0_L4_L16_L6_L4_L10_L20_L5_L1» = true)

theorem oq_exactFree_7 : ExactFreeG (openingQueriesLoops.getD 7 oqNone).1 :=
  exactFreeG_of (by decide +kernel : exactFree "opening_queries__L0_L4_L16_L12_L4_L10_L20_L5_L1" idx% «opening_queries__L0_L4_L16_L12_L4_L10_L20_L5_L1» = true)

theorem oq_exactFree_8 : ExactFreeG (openingQueriesLoops.getD 8 oqNone).1 :=
  exactFreeG_of (by decide +kernel : exactFree "opening_queries__L0_L4_L16_L6_L5_L15_L36_L6_L1" idx% «opening_queries__L0_L4_L16_L6_L5_L15_L36_L6_L1» = true)

theorem oq_exactFree_9 : ExactFreeG (openingQueriesLoops.getD 9 oqNone).1 :=
  exactFreeG_of (by decide +kernel : exactFree "opening_queries__L0_L4_L16_L12_L5_L15_L36_L6_L1" idx% «opening_queries__L0_L4_L16_L12_L5_L15_L36_L6_L1» = true)

theorem oq_exactFree_10 : ExactFreeG (openingQueriesLoops.getD 10 oqNone).1 :=
  exactFreeG_of (by decide +kernel : exactFree "opening_queries__L0_L4_L16_L12_L2_L3_L8_L3_L1" idx% «opening_queries__L0_L4_L16_L12_L2_L3_L8_L3_L1» = true)

theorem oq_exactFree_11 : ExactFreeG (openingQueriesLoops.getD 11 oqNone).1 :=
  exactFreeG_of (by decide +kernel : exactFree "opening_queries__L0_L4_L16_L12_L3_L6_L12_L4_L1" idx% «opening_queries__L0_L4_L16_L12_L3_L6_L12_L4_L1» = true)

theorem oq_exactFree_12 : ExactFreeG (openingQueriesLoops.getD 12 oqNone).1 :=
  exactFreeG_of (by decide +kernel : exactFree "opening_queries__L1_L6_L32_L18_L0_L0_L0_L0_L0" idx% «opening_queries__L1_L6_L32_L18_L0_L0_L0_L0_L0» = true)

theorem oq_exactFree_13 : ExactFreeG (openingQueriesLoops.getD 13 oqNone).1 :=
  exactFreeG_of (by decide +kernel : exactFree "opening_queries__L0_L4_L16_L18_L0_L0_L0_L0_L0" idx% «opening_queries__L0_L4_L16_L18_L0_L0_L0_L0_L0» = true)

theorem oq_exactFree_14 : ExactFreeG (openingQueriesLoops.getD 14 oqNone).1 :=
  exactFreeG_of (by decide +kernel : exactFree "opening_queries__L0_L4_L16_L18_L4_L10_L20_L5_L1" idx% «opening_queries__L0_L4_L16_L18_L4_L10_L20_L5_L1» = true)

theorem oq_exactFree_15 : ExactFreeG (openingQueriesLoops.getD 15 oqNone).1 :=
  exactFreeG_of (by decide +kernel : exactFree "opening_queries__L0_L4_L16_L18_L5_L15_L36_L6_L1" idx% «opening_queries__L0_L4_L16_L18_L5_L15_L36_L6_L1» = true)

theorem oq_exactFree_16 : ExactFreeG (openingQueriesLoops.getD 16 oqNone).1 :=
  exactFreeG_of (by decide +kernel : exactFree "opening_queries__L1_L6_L32_L24_L0_L0_L0_L0_L0" idx% «opening_queries__L1_L6_L32_L24_L0_L0_L0_L0_L0» = true)

theorem oq_exactFree_17 : ExactFreeG (openingQueriesLoops.getD 17 oqNone).1 :=
  exactFreeG_of (by decide +kernel : exactFree "opening_queries__L0_L4_L16_L18_L2_L3_L8_L3_L1" idx% «opening_queries__L0_L4_L16_L18_L2_L3_L8_L3_L1» = true)

theorem oq_exactFree_18 : ExactFreeG (openingQueriesLoops.getD 18 oqNone).1 :=
  exactFreeG_of (by decide +kernel : exactFree "opening_queries__L0_L4_L16_L24_L0_L0_L0_L0_L0" idx% «opening_queries__L0_L4_L16_L24_L0_L0_L0_L0_L0» = true)

theorem oq_exactFree_19 : ExactFreeG (openingQueriesLoops.getD 19 oqNone).1 :=
  exactFreeG_of (by decide +kernel : exactFree "opening_queries__L0_L4_L16_L18_L3_L6_L12_L4_L1" idx% «opening_queries__L0_L4_L16_L18_L3_L6_L12_L4_L1» = true)

/-- **Every entry's function passes the check.** -/
theorem oq_exactFree_all : ∀ p ∈ openingQueriesLoops, ExactFreeG p.1 := by
  intro p hp
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hp
  rw [List.getElem_eq_getD oqNone]
  have hi' : i < 20 := hi
  interval_cases i
  exacts [oq_exactFree_0, oq_exactFree_1, oq_exactFree_2, oq_exactFree_3, oq_exactFree_4, oq_exactFree_5, oq_exactFree_6, oq_exactFree_7, oq_exactFree_8, oq_exactFree_9, oq_exactFree_10, oq_exactFree_11, oq_exactFree_12, oq_exactFree_13, oq_exactFree_14, oq_exactFree_15, oq_exactFree_16, oq_exactFree_17, oq_exactFree_18, oq_exactFree_19]

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

/-- **Every `opening_queries__L…` completes placed, its end bounded.** -/
theorem oqAE_all (kd : ℕ) : ∀ p ∈ openingQueriesLoops, OqAE fs al cert kd p.1 p.2.1 p.2.2.oq := by
  intro p hp
  obtain ⟨fm, fl, hfm, hpm, hbm, hfl, hpl, hbl⟩ := oqFns_all p hp
  obtain ⟨-, -, hside⟩ := oqSide_all p hp
  exact oqA_complete' hfm hpm hbm hfl hpl hbl (oq_loop_flag hfl hbl) hside (oq_exactFree_all p hp)

/-- **Every `opening_queries__L…` completes placed.** -/
theorem oqA_all (kd : ℕ) : ∀ p ∈ openingQueriesLoops, OqA fs al cert kd p.1 p.2.2.oq :=
  fun p hp => (oqAE_all kd p hp).toA

end
end LeanVM.Guest.B1.VsC
