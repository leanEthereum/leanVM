/-
  Rv64mc.Model.Extra.Keccak

  `Model.KeccakGkr`'s `linear_transpose` in the forms its compiled loops compute it: the weight position `p` of θ's
  output carries, read from `w` at `gIdx p` (`transposeG_getD_eq`); the column sums after the first `n` positions
  (`colsUpTo`), one entry added per position, `n % 320` (`colsUpTo_succ`), all of them `transposeColumns`'s
  (`colsUpTo_full`).
-/

import Rv64mc.Model.KeccakGkr

namespace Rv64mc.Model

open LeanVM.Parameters

/-- The index of `w` the position `p` of θ's output reads: `64 PI[lane] + (z + RHO[lane]) % 64`. -/
def gIdx (p : ℕ) : ℕ := 64 * keccakPiRust.getD (p / 64) 0 + (p % 64 + keccakRhoRust.getD (p / 64) 0) % 64

theorem set_getD_eq (l : List E) (i p : ℕ) (x : E) :
    (l.set i x).getD p 0 = if i = p ∧ i < l.length then x else l.getD p 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h1 : i = p
  · subst h1
    by_cases h2 : i < l.length <;> simp [h2]
  · simp [h1]

private theorem transposeG_inner (W : ℕ → E) (lane : ℕ) (g : List E) :
    ∀ Z, ((List.range Z).foldl (fun g z ↦ g.set (64 * lane + z) (W z)) g).length = g.length ∧
      ∀ p, ((List.range Z).foldl (fun g z ↦ g.set (64 * lane + z) (W z)) g).getD p 0 =
        if 64 * lane ≤ p ∧ p < 64 * lane + Z ∧ p < g.length then W (p - 64 * lane) else g.getD p 0
  | 0 => ⟨rfl, fun p ↦ by simp; omega⟩
  | Z + 1 => by
    obtain ⟨hs, hg⟩ := transposeG_inner W lane g Z
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine ⟨by rw [List.length_set, hs], fun p ↦ ?_⟩
    rw [set_getD_eq, hg p, hs]
    split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; omega)

private theorem transposeG_outer (w : List E) : ∀ L, L ≤ 25 →
    ((List.range L).foldl (fun g lane ↦ (List.range 64).foldl (fun g z ↦
      g.set (64 * lane + z)
        (w.getD (64 * keccakPiRust.getD lane 0 + (z + keccakRhoRust.getD lane 0) % 64) 0)) g)
      (List.replicate 1600 0)).length = 1600 ∧
    ∀ p, ((List.range L).foldl (fun g lane ↦ (List.range 64).foldl (fun g z ↦
      g.set (64 * lane + z)
        (w.getD (64 * keccakPiRust.getD lane 0 + (z + keccakRhoRust.getD lane 0) % 64) 0)) g)
      (List.replicate 1600 0)).getD p 0 = if p < 64 * L then w.getD (gIdx p) 0 else 0
  | 0, _ => ⟨by rw [List.range_zero, List.foldl_nil, List.length_replicate], fun p ↦ by
      rw [List.range_zero, List.foldl_nil, List.getD_eq_getElem?_getD, List.getElem?_replicate]
      split_ifs <;> simp_all⟩
  | L + 1, hL => by
    obtain ⟨hs, hg⟩ := transposeG_outer w L (by omega)
    rw [List.range_succ (n := L), List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨hs', hg'⟩ := transposeG_inner
      (fun z ↦ w.getD (64 * keccakPiRust.getD L 0 + (z + keccakRhoRust.getD L 0) % 64) 0) L
      ((List.range L).foldl (fun g lane ↦ (List.range 64).foldl (fun g z ↦
        g.set (64 * lane + z)
          (w.getD (64 * keccakPiRust.getD lane 0 + (z + keccakRhoRust.getD lane 0) % 64) 0)) g)
        (List.replicate 1600 0)) 64
    refine ⟨hs'.trans hs, fun p ↦ ?_⟩
    rw [hg' p, hg p, hs]
    by_cases h1 : 64 * L ≤ p ∧ p < 64 * L + 64 ∧ p < 1600
    · rw [ite_eq_left h1, ite_eq_left (by omega), gIdx]
      have e1 : p / 64 = L := by omega
      have e2 : p % 64 = p - 64 * L := by omega
      rw [e1, e2]
    · rw [ite_eq_right h1]
      by_cases h2 : p < 64 * L
      · rw [ite_eq_left h2, ite_eq_left (by omega)]
      · rw [ite_eq_right h2, ite_eq_right (by omega)]

theorem transposeG_length_eq (w : List E) : (transposeG w).length = 1600 :=
  (transposeG_outer w 25 le_rfl).1

/-- **Position `p` of `g`** is `w`'s entry at `gIdx p`. -/
theorem transposeG_getD_eq (w : List E) {p : ℕ} (hp : p < 1600) : (transposeG w).getD p 0 = w.getD (gIdx p) 0 := by
  rw [transposeG, (transposeG_outer w 25 le_rfl).2 p, ite_eq_left (by omega)]

/-- One position of the column sums' loop: `columns[64 (j / 64 % 5) + j % 64] += weight`. -/
def colStep (columns : List E) (wj : E × ℕ) : List E :=
  columns.set (64 * (wj.2 / 64 % 5) + wj.2 % 64) (columns.getD (64 * (wj.2 / 64 % 5) + wj.2 % 64) 0 + wj.1)

/-- The column sums after the first `n` positions of `g`. -/
def colsUpTo (g : List E) (n : ℕ) : List E := (g.zipIdx.take n).foldl colStep (List.replicate (5 * 64) 0)

theorem colsUpTo_length (g : List E) (n : ℕ) : (colsUpTo g n).length = 320 := by
  unfold colsUpTo
  induction (g.zipIdx.take n) using List.reverseRecOn with
  | nil => rw [List.foldl_nil, List.length_replicate]
  | append_singleton l x ih => rw [List.foldl_append, List.foldl_cons, List.foldl_nil, colStep, List.length_set, ih]

theorem colsUpTo_zero (g : List E) (c : ℕ) : (colsUpTo g 0).getD c 0 = 0 := by
  rw [colsUpTo, List.take_zero, List.foldl_nil, List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split_ifs <;> rfl

/-- **One more position**: entry `n % 320` gains `g[n]`. -/
theorem colsUpTo_succ (g : List E) {n : ℕ} (hn : n < g.length) :
    colsUpTo g (n + 1) = (colsUpTo g n).set (n % 320) ((colsUpTo g n).getD (n % 320) 0 + g[n]) := by
  have hz : n < g.zipIdx.length := by simpa using hn
  rw [colsUpTo, List.take_add_one, List.foldl_append, List.getElem?_eq_getElem hz]
  simp only [Option.toList_some, List.foldl_cons, List.foldl_nil, colStep, List.getElem_zipIdx, zero_add]
  rw [show 64 * (n / 64 % 5) + n % 64 = n % 320 by omega]
  rfl

theorem colsUpTo_full (g : List E) : colsUpTo g g.length = transposeColumns g := by
  rw [colsUpTo, List.take_of_length_le (by simp)]
  rfl

/-- `linear_transpose` on `1600` weights, per position. -/
theorem linearTransposeRust_some {w : List E} (hw : w.length = 1600) :
    linearTransposeRust w = some ((List.range 1600).map fun j ↦
      (transposeG w).getD j 0 + (transposeColumns (transposeG w)).getD (64 * ((j / 64 % 5 + 1) % 5) + j % 64) 0 +
        (transposeColumns (transposeG w)).getD (64 * ((j / 64 % 5 + 4) % 5) + (j % 64 + 1) % 64) 0) := by
  rw [linearTransposeRust, ite_eq_left hw]

end Rv64mc.Model
