/-
  LeanVM.Guest.B1.Whir.RootsN

  The subspace roots of `ml ≤ 22` coordinates are the certified ones; the vanishing tables
  checked against them.
-/

module

public import LeanVM.Guest.B1.Whir.RootsCert

/-!
# The roots of every message log

`kRoots_cert`: `kRoots ml` is `1` then the first `ml` certified roots (`kRootsAux_prefix`: the
roots of fewer coordinates are a prefix). `vanishOkC vo ml` checks a level's tables against the
certified roots (one multiplication an entry, for the inverses) and gives `vanishOk`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters

@[expose] public section

/-- The roots of fewer coordinates are a prefix. -/
theorem kRootsAux_prefix : ∀ (n N : ℕ) (last : K) (layer : List K), n ≤ N → N ≤ layer.length →
    kRootsAux n last (layer.take n) = (kRootsAux N last layer).take n
  | 0, _, _, _, _, _ => by simp [kRootsAux]
  | n + 1, N + 1, last, a :: layer, h1, h2 => by
    simp only [List.take_succ_cons, kRootsAux, List.map_cons]
    congr 1
    rw [List.map_take]
    exact kRootsAux_prefix n N _ _ (by omega) (by simp at h2 ⊢; omega)
  | n + 1, 0, _, _, h1, _ => absurd h1 (by omega)
  | n + 1, N + 1, _, [], _, h2 => absurd h2 (by simp)

/-- The certified layers compute the certified roots. -/
theorem kRootsAux_cert : ∀ (n k : ℕ), k + n ≤ 22 →
    kRootsAux n (lastOf k) (layerK k) = (rootK.drop k).take n
  | 0, _, _ => by simp [kRootsAux]
  | n + 1, k, h => by
    have hs : stepOk k = true := step_all k (by omega)
    simp only [stepOk, beq_iff_eq] at hs
    rw [kRootsAux, hs]
    simp only
    have hl : lastOf (k + 1) = rootK.getD k 0 := by simp [lastOf]
    rw [← hl, kRootsAux_cert n (k + 1) (by omega)]
    have hlt : k < rootK.length := by rw [rootK_length]; omega
    rw [hl, List.getD_eq_getElem _ _ hlt, List.drop_eq_getElem_cons hlt, List.take_succ_cons]

theorem kRoots_cert {ml : ℕ} (h : ml ≤ 22) : kRoots ml = (1 :: rootK).take (ml + 1) := by
  have e : (List.range ml).map (fun i ↦ K.ofBits (2 ^ (i + 1))) = (layerK 0).take ml := by
    rw [layerK_zero, ← List.map_take, List.take_range, min_eq_left h]
  rw [kRoots, e, kRootsAux_prefix ml 22 _ _ h (by rw [layerK_zero]; simp),
    show (1 : K) = lastOf 0 from rfl, kRootsAux_cert 22 0 (by omega), List.drop_zero,
    List.take_take, min_eq_left h, List.take_succ_cons]

/-- A level's vanishing tables, checked against the certified roots and inverses. -/
def vanishOkC (vo ml : ℕ) : Bool :=
  decide (ml ≤ 22) && decide (vo + ml ≤ Data.arr_LIG_VANISH_VALS.length) &&
  decide (vo + ml ≤ Data.arr_LIG_VANISH_INVS.length) &&
  ((Data.arr_LIG_VANISH_VALS.drop vo).take ml).map (fun e ↦ K.ofBits e.1) ==
    (1 :: rootK).take ml &&
  ((Data.arr_LIG_VANISH_INVS.drop vo).take ml).map (fun e ↦ K.ofBits e.1) ==
    (1 :: invK).take ml

/-- A run of a table, read entry by entry (`lig`) or at once. -/
theorem lig_run (a : List (ℕ × ℕ × ℕ)) {vo ml : ℕ} (h : vo + ml ≤ a.length) :
    ((List.range ml).map fun t ↦ K.ofBits (lig a (vo + t))) =
      ((a.drop vo).take ml).map (fun e ↦ K.ofBits e.1) := by
  apply List.ext_getElem (by simp; omega)
  intro t h1 h2
  simp only [List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop, lig,
    List.getD_eq_getElem _ _ (show vo + t < a.length by simp at h1; omega)]

theorem getD_range_map {f : ℕ → K} {n t : ℕ} (h : t < n) :
    ((List.range n).map f).getD t 0 = f t := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_take_lt {l : List K} {n t : ℕ} (h : t < n) : (l.take n).getD t 0 = l.getD t 0 := by
  simp [List.getD_eq_getElem?_getD, h]

theorem vanishOk_of_C {vo ml : ℕ} (h : vanishOkC vo ml = true) : vanishOk vo ml = true := by
  simp only [vanishOkC, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hml, hv⟩, hi⟩, h1⟩, h2⟩ := h
  rw [← show _ = _ from lig_run _ hv] at h1
  rw [← show _ = _ from lig_run _ hi] at h2
  simp only [vanishOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range]
  refine ⟨by rw [kRoots_cert hml, List.take_take, min_eq_left (by omega)]; exact h1, fun t ht ↦ ?_⟩
  have e1 := congrArg (fun l ↦ List.getD l t 0) h1
  have e2 := congrArg (fun l ↦ List.getD l t 0) h2
  simp only [getD_range_map ht, getD_take_lt ht] at e1 e2
  rw [vanishVal, vanishInv, e1, e2]
  rcases t with _ | s
  · simp
  · simp only [List.getD_cons_succ]
    have := inv_all s (by omega)
    simpa [invOk] using this

end
end LeanVM.Guest.B1.Whir
