/-
  LeanVM.Guest.WalkGkr

  The cut obligations (`CutsKnown`) of `verify_bus_gkr` (function `10`) and its radix-four layer
  loop `__loop6` (function `91`): the parity words the loop dispatches on (`GkrPar`), from B1's
  facts on their bodies (`B1.Gkr.Parity`), read through the certificates' cells.
-/

module

public import LeanVM.Guest.Sound
public import LeanVM.Guest.B1.Gkr.Parity

/-!
# The layer loop's parity obligations (REC-GUEST-IFACE 'tool: gkr obligations')

`__loop6`'s certificate takes `GkrPar` (tag `tagGkr`) on its arguments' cells
`[layers, x, start_g, k_mod_next] = [5, 2, 4, 11]` (values `3, 0, 2, 9`) and hands on, at its two
cuts, the parity word's bound (`knownIf = [(20, 12, 4)]`, cell `20` the slot `σ 17`:
`ly_par_parity`) and, before the tail call, `GkrPar` at `x·g` (cell `298`, value `238`:
`ly_par_tail`). `verify_bus_gkr` hands on, before its loop call, `GkrPar` at `x = 1`, conditional
on the cell of `x` holding `1` (`impTag tagGkr 1 1` on `[25, 38, 396, 87]`, values
`16, 380, 375, 64`: `vbg_par`).

`gkrLoop_cutsKnown : CutsKnown (fn_idx% «verify_bus_gkr_loop0»)`, `gkrBus_cutsKnown : CutsKnown (fn_idx% «verify_bus_gkr»)`, for `WalkKnown`
(`walkKnown_of_gkr gkrBus_cutsKnown gkrLoop_cutsKnown`).
-/

namespace LeanVM.Guest.End

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Check
open LeanVM.Guest.B1 LeanVM.Guest.B1.Tables

@[expose] public section

/-! ## The tag (`tagGkr_lt`, `Sound`) -/

theorem semRel0_gkr (rd : Reader) (ws : List E) :
    SemRel0 glob tagGkr rd ws ↔
      GkrPar rd (ws.getD 0 0) (ws.getD 1 0) (ws.getD 2 0) (ws.getD 3 0) := by
  unfold SemRel0
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by unfold tagNe tagGkr; norm_num))]
  exact Iff.rfl

theorem semRel_gkr (rd : Reader) (ws : List E) :
    SemRel glob tagGkr rd ws ↔
      GkrPar rd (ws.getD 0 0) (ws.getD 1 0) (ws.getD 2 0) (ws.getD 3 0) := by
  unfold SemRel
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by have := tagGkr_lt; omega)),
    ite_eq_right_of_eq_false _ _ (eq_false (by unfold tagGkr; norm_num)), semRel0_gkr]

/-- `GkrPar` conditional on the immediate `1` at position `1` (the loop call's `x`). -/
theorem semRel_gkrImp (rd : Reader) (ws : List E) :
    SemRel glob (impTag tagGkr 1 1) rd ws ↔
      (ws.getD 1 0 = 1 →
        GkrPar rd (ws.getD 0 0) (ws.getD 1 0) (ws.getD 2 0) (ws.getD 3 0)) := by
  have ht := tagGkr_lt
  have e1 : impPos (impTag tagGkr 1 1) = 1 := by
    unfold impPos impTag
    rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt ht]
  have e2 : impImm (impTag tagGkr 1 1) = 1 := by
    unfold impImm impTag
    rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt ht]
  have e3 : impBase (impTag tagGkr 1 1) = tagGkr := by
    unfold impBase impTag
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht]
  have hone : OffsetInstruction.immediateWord 1 0 = 1 := (Exec.imm_of_ofBits rfl).trans Exec.ofK_one
  unfold SemRel
  rw [ite_eq_left_of_eq_true _ _ (eq_true (by unfold impTag; omega)), e1, e2, e3, hone, semRel0_gkr]

/-- A value's word, at its certificate cell. -/
theorem valG_of_loc {κ : ℕ} {L : MemoryImage κ} {fp : K} {C : Cert} {v c : ℕ}
    (h : C.locs.getD v 0 = c) : valG L fp C (.n v) = wd L fp c := by
  rw [← h]; rfl

/-! ## `__loop6` (function `91`) -/

theorem coreOf_91 : (coreOf (fn_idx% «verify_bus_gkr_loop0»)).body = lyBody := by
  obtain ⟨fn, hf, -, hb⟩ := lyFound
  have hc := coreOf_find (j := fn_idx% «verify_bus_gkr_loop0») (by norm_num) (by unfold nFns; norm_num)
  rw [show (coreOf (fn_idx% «verify_bus_gkr_loop0»)).name = name% «verify_bus_gkr_loop0» from rfl, hf] at hc
  rw [← Option.some.inj hc, hb]

/-- `__loop6`'s certificate: `GkrPar` on its arguments, two cuts (before the dispatch, before the
tail call). -/
theorem gkr91_cert : (certOf (fn_idx% «verify_bus_gkr_loop0»)).sem = [(tagGkr, [5, 2, 4, 11])] ∧ (certOf (fn_idx% «verify_bus_gkr_loop0»)).cuts.length = 2 ∧
    ((certOf (fn_idx% «verify_bus_gkr_loop0»)).cutAt 1).start = 49 ∧ ((certOf (fn_idx% «verify_bus_gkr_loop0»)).cutAt 1).known = [] ∧
    ((certOf (fn_idx% «verify_bus_gkr_loop0»)).cutAt 1).knownIf = [(20, 12, 4)] ∧ ((certOf (fn_idx% «verify_bus_gkr_loop0»)).cutAt 1).sems = [] ∧
    ((certOf (fn_idx% «verify_bus_gkr_loop0»)).cutAt 2).start = 191 ∧ ((certOf (fn_idx% «verify_bus_gkr_loop0»)).cutAt 2).known = [] ∧
    ((certOf (fn_idx% «verify_bus_gkr_loop0»)).cutAt 2).knownIf = [(20, 12, 4)] ∧
    ((certOf (fn_idx% «verify_bus_gkr_loop0»)).cutAt 2).sems = [(tagGkr, [5, 298, 4, 11])] := by decide +kernel

/-- `__loop6`'s cells: values `0, 2, 3, 9, 17, 238` in cells `2, 4, 5, 11, 20, 298`. -/
theorem gkr91_locs : (certOf (fn_idx% «verify_bus_gkr_loop0»)).locs.getD 0 0 = 2 ∧ (certOf (fn_idx% «verify_bus_gkr_loop0»)).locs.getD 2 0 = 4 ∧
    (certOf (fn_idx% «verify_bus_gkr_loop0»)).locs.getD 3 0 = 5 ∧ (certOf (fn_idx% «verify_bus_gkr_loop0»)).locs.getD 9 0 = 11 ∧
    (certOf (fn_idx% «verify_bus_gkr_loop0»)).locs.getD 17 0 = 20 ∧ (certOf (fn_idx% «verify_bus_gkr_loop0»)).locs.getD 238 0 = 298 := by decide +kernel

/-- **`__loop6`'s cut obligations**: the parity word's bound at both cuts, `GkrPar` at `x·g`
before the tail call. -/
theorem gkrLoop_cutsKnown : CutsKnown (fn_idx% «verify_bus_gkr_loop0») := by
  intro κ L _ _ fp _ hsem i hi h0 hl
  obtain ⟨hs, hlen, s1, k1, i1, m1, s2, k2, i2, m2⟩ := gkr91_cert
  obtain ⟨l0, l2, l3, l9, l17, l238⟩ := gkr91_locs
  rw [hs] at hsem
  have hp := (semRel_gkr _ _).mp (hsem _ (List.mem_singleton_self _))
  simp only [List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ] at hp
  rw [← valG_of_loc l3, ← valG_of_loc l0, ← valG_of_loc l2, ← valG_of_loc l9] at hp
  rw [coreOf_91] at hl
  have hif : ∀ {n}, Stmt.noRetList (lyBody.take n) = true →
      tbStmtsEqb lySlotT (((lyBody.take n).drop 0).take lySlotT.length) = true →
      Stmt.HoldsList (coreProgram.Rel L.read) L.read (valG L fp (certOf (fn_idx% «verify_bus_gkr_loop0»))) (lyBody.take n) True
        (fun _ ↦ True) → MemIf L fp [(20, 12, 4)] := by
    intro n hnr heq hl m hm v hv
    rw [List.mem_singleton] at hm
    subst hm
    rw [← valG_of_loc l17] at hv
    exact ly_par_parity hnr hl heq hp v hv
  rw [hlen] at hi
  obtain rfl | rfl : i = 1 ∨ i = 2 := by omega
  · rw [s1] at hl
    rw [k1, i1, m1]
    exact ⟨fun _ h ↦ by simp at h, hif lyBody_take49_noRet (by decide +kernel) hl,
      fun _ h ↦ by simp at h⟩
  · rw [s2] at hl
    rw [k2, i2, m2]
    refine ⟨fun _ h ↦ by simp at h, hif lyBody_take191_noRet (by decide +kernel) hl, fun t ht ↦ ?_⟩
    rw [List.mem_singleton] at ht
    subst ht
    rw [semRel_gkr]
    simp only [List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ]
    rw [← valG_of_loc l3, ← valG_of_loc l238, ← valG_of_loc l2, ← valG_of_loc l9]
    exact ly_par_tail hl hp

/-! ## `verify_bus_gkr` (function `10`) -/

theorem coreOf_10 : (coreOf (fn_idx% «verify_bus_gkr»)).body = vbgPre ++ [.ret vbgRets] := by
  obtain ⟨fn, hf, -, hb⟩ := vbgFound
  have hc := coreOf_find (j := fn_idx% «verify_bus_gkr») (by norm_num) (by unfold nFns; norm_num)
  rw [show (coreOf (fn_idx% «verify_bus_gkr»)).name = name% «verify_bus_gkr» from rfl, hf] at hc
  rw [← Option.some.inj hc, hb]

/-- `verify_bus_gkr`'s certificate: one cut, before its loop call, `GkrPar` at `x = 1`. -/
theorem gkr10_cert : (certOf (fn_idx% «verify_bus_gkr»)).cuts.length = 1 ∧ ((certOf (fn_idx% «verify_bus_gkr»)).cutAt 1).start = 206 ∧
    ((certOf (fn_idx% «verify_bus_gkr»)).cutAt 1).known = [] ∧ ((certOf (fn_idx% «verify_bus_gkr»)).cutAt 1).knownIf = [] ∧
    ((certOf (fn_idx% «verify_bus_gkr»)).cutAt 1).sems = [(impTag tagGkr 1 1, [25, 38, 396, 87])] := by decide +kernel

/-- `verify_bus_gkr`'s cells: values `16, 375, 64` in cells `25, 396, 87`. -/
theorem gkr10_locs : (certOf (fn_idx% «verify_bus_gkr»)).locs.getD 16 0 = 25 ∧ (certOf (fn_idx% «verify_bus_gkr»)).locs.getD 375 0 = 396 ∧
    (certOf (fn_idx% «verify_bus_gkr»)).locs.getD 64 0 = 87 := by decide +kernel

/-- **`verify_bus_gkr`'s cut obligation**: `GkrPar` at `x = 1` before its loop call. -/
theorem gkrBus_cutsKnown : CutsKnown (fn_idx% «verify_bus_gkr») := by
  intro κ L _ hκ fp _ _ i hi h0 hl
  obtain ⟨hlen, s1, k1, i1, m1⟩ := gkr10_cert
  obtain ⟨l16, l375, l64⟩ := gkr10_locs
  rw [hlen] at hi
  obtain rfl : i = 1 := by omega
  rw [s1, coreOf_10, List.take_append_of_le_length (by decide +kernel)] at hl
  rw [k1, i1, m1]
  refine ⟨fun _ h ↦ by simp at h, fun _ h ↦ by simp at h, fun t ht ↦ ?_⟩
  rw [List.mem_singleton] at ht
  subst ht
  rw [semRel_gkrImp]
  simp only [List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ]
  intro hx
  rw [hx, ← valG_of_loc l16, ← valG_of_loc l375, ← valG_of_loc l64]
  exact vbg_par (hκ.trans (by decide)) L hl

end
end LeanVM.Guest.End
