/-
  LeanVM.Guest.B1.Whir.Vanish

  The vanishing tables `LIG_VANISH_VALS`, `LIG_VANISH_INVS` are the subspace roots and their
  inverses, at every level of every candidate.
-/

module

public import LeanVM.Guest.B1.Whir.VanishCert

/-!
# The vanishing tables

A level of message log `μ` reads `μ + 1` entries of each table from its offset `vanish`
(`open_stacked`, `residual_query`, `opening_query`): `LIG_VANISH_VALS[vanish + i]` is root `i` of
`subspaceRoots μ` (the normalizers `W_i(β_i)`, `whir.rs:95-107`) and `LIG_VANISH_INVS` its
inverse.

* `subspaceRoots_cert`: `subspaceRoots μ` is `1` then the first `μ` certified roots
  (`subspaceRootsAux_prefix`: the roots of fewer coordinates are a prefix);
* `vanishOk vo n`: the `n` entries from `vo` of both tables are the certified roots and inverses;
* `vanish_val`, `vanish_inv`: what `vanishOk vo (μ + 1)` gives about `subspaceRoots μ`;
* `vanish_all`: `vanishOk` at every level of every candidate, decided by the kernel.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Protocol.Verifier

@[expose] public section

/-- The roots of fewer coordinates are a prefix. -/
theorem subspaceRootsAux_prefix : ∀ (n N : ℕ) (last : K) (layer : List K), n ≤ N →
    N ≤ layer.length → subspaceRootsAux n last (layer.take n) = (subspaceRootsAux N last layer).take n
  | 0, _, _, _, _, _ => by simp [subspaceRootsAux]
  | n + 1, N + 1, last, a :: layer, h1, h2 => by
    simp only [List.take_succ_cons, subspaceRootsAux, List.map_cons]
    congr 1
    rw [List.map_take]
    exact subspaceRootsAux_prefix n N _ _ (by omega) (by simp at h2 ⊢; omega)
  | n + 1, 0, _, _, h1, _ => absurd h1 (by omega)
  | n + 1, N + 1, _, [], _, h2 => absurd h2 (by simp)

/-- The certified layers compute the certified roots. -/
theorem subspaceRootsAux_cert : ∀ (n k : ℕ), k + n ≤ 22 →
    subspaceRootsAux n (lastOf k) (layerK k) = (rootK.drop k).take n
  | 0, _, _ => by simp [subspaceRootsAux]
  | n + 1, k, h => by
    have hs : stepOk k = true := step_all k (by omega)
    simp only [stepOk, beq_iff_eq] at hs
    rw [subspaceRootsAux, hs]
    simp only
    have hl : lastOf (k + 1) = rootK.getD k 0 := by simp [lastOf]
    rw [← hl, subspaceRootsAux_cert n (k + 1) (by omega)]
    have hlt : k < rootK.length := by rw [rootK_length]; omega
    rw [hl, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some,
      List.drop_eq_getElem_cons hlt, List.take_succ_cons]

/-- **The subspace roots of `μ ≤ 22` coordinates are the certified ones.** -/
theorem subspaceRoots_cert {μ : ℕ} (h : μ ≤ 22) : subspaceRoots μ = (1 :: rootK).take (μ + 1) := by
  have e : (List.range μ).map (fun i ↦ K.ofBits (2 ^ (i + 1))) = (layerK 0).take μ := by
    rw [layerK_zero, ← List.map_take, List.take_range, min_eq_left h]
  rw [subspaceRoots, e, subspaceRootsAux_prefix μ 22 _ _ h (by rw [layerK_zero]; simp),
    show (1 : K) = lastOf 0 from rfl, subspaceRootsAux_cert 22 0 (by omega), List.drop_zero,
    List.take_take, min_eq_left h, List.take_succ_cons]

/-- A level's vanishing tables: the `n` entries from `vo` of each are the certified roots (`1`
first) and their inverses. -/
def vanishOk (vo n : ℕ) : Bool :=
  decide (n ≤ 23) && decide (vo + n ≤ Data.arr_LIG_VANISH_VALS.length) &&
  decide (vo + n ≤ Data.arr_LIG_VANISH_INVS.length) &&
  ((Data.arr_LIG_VANISH_VALS.drop vo).take n).map (fun e ↦ K.ofBits e.1) == (1 :: rootK).take n &&
  ((Data.arr_LIG_VANISH_INVS.drop vo).take n).map (fun e ↦ K.ofBits e.1) == (1 :: invK).take n

/-- A run of a table, read entry by entry (`lig`) or at once. -/
theorem lig_run (a : List (ℕ × ℕ)) {vo n : ℕ} (h : vo + n ≤ a.length) :
    ((List.range n).map fun t ↦ K.ofBits (lig a (vo + t))) =
      ((a.drop vo).take n).map (fun e ↦ K.ofBits e.1) := by
  apply List.ext_getElem (by simp; omega)
  intro t h1 h2
  simp only [List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop, lig,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show vo + t < a.length by simp at h1; omega),
    Option.getD_some]

theorem getD_range_map {f : ℕ → K} {n t : ℕ} (h : t < n) :
    ((List.range n).map f).getD t 0 = f t := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_take_lt {l : List K} {n t : ℕ} (h : t < n) : (l.take n).getD t 0 = l.getD t 0 := by
  simp [List.getD_eq_getElem?_getD, h]

/-- **The values are the roots**: entry `vo + t`, `t ≤ μ`, is root `t` of `subspaceRoots μ`. -/
theorem vanish_val {vo μ : ℕ} (h : vanishOk vo (μ + 1) = true) :
    ∀ t ≤ μ, K.ofBits (vanishVal (vo + t)) = (subspaceRoots μ).getD t 0 := by
  intro t ht
  simp only [vanishOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hn, hv⟩, -⟩, h1⟩, -⟩ := h
  rw [← lig_run _ hv] at h1
  have e1 := congrArg (fun l ↦ List.getD l t 0) h1
  simp only [getD_range_map (show t < μ + 1 by omega), getD_take_lt (show t < μ + 1 by omega)] at e1
  rw [vanishVal, e1, subspaceRoots_cert (by omega), getD_take_lt (by omega)]

/-- **The inverses are the roots' inverses.** -/
theorem vanish_inv {vo μ : ℕ} (h : vanishOk vo (μ + 1) = true) :
    ∀ t ≤ μ, K.ofBits (vanishInv (vo + t)) = ((subspaceRoots μ).getD t 0)⁻¹ := by
  intro t ht
  simp only [vanishOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hn, -⟩, hi⟩, -⟩, h2⟩ := h
  rw [← lig_run _ hi] at h2
  have e2 := congrArg (fun l ↦ List.getD l t 0) h2
  simp only [getD_range_map (show t < μ + 1 by omega), getD_take_lt (show t < μ + 1 by omega)] at e2
  rw [vanishInv, e2, subspaceRoots_cert (by omega), getD_take_lt (by omega)]
  rcases t with _ | s
  · simp
  · simp only [List.getD_cons_succ]
    have hs : invK.getD s 0 * rootK.getD s 0 = 1 := by
      have := inv_all s (by omega)
      simpa [invOk] using this
    exact eq_inv_of_mul_eq_one_left hs

/-- **Every level's vanishing tables**, `μ + 1` entries from its offset. -/
theorem vanish_all : ∀ m < 28, ∀ l < osNLevels m,
    vanishOk (osLv m l).vanish ((osLv m l).logCols + 1) = true := by
  decide +kernel

end
end LeanVM.Guest.B1.Whir
