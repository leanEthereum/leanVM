/-
  LeanVM.Guest.B1.Tables.VtC.ABuf

  Buffers of fixed-stride blocks, and the shared selector tables' honest words.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.SAll

/-!
# Strided buffers

`getD_flatMap_const`: a flattening of blocks of `S` words holds block `i` at `S·i`.

`vtShEqW`, `vtShGW`: table `t`'s shared selector tables' buffers (`shared_eq[t]`, `shared_g[t]`):
nibble `j`'s eq levels (stride `32`) and `g`-power table (stride `16`) of the run of `|point| − τ_t`
coordinates above `τ_t`. `vt_runTables`, `vt_runPads`: they give `RunTables`, `RunPads`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The shared selector tables -/

/-- Table `t`'s `shared_eq` words: nibble `j`'s eq levels at `32 j`, zeros past them, `8(n + 1)` words for
its run of `n = |point| - τ_t` coordinates. -/
def vtShEqW (point : List E) (τ : ℕ → ℕ) (t : ℕ) : List E :=
  (List.range (8 * (point.length - τ t + 1))).map fun k ↦
    if k / 32 < (point.length - τ t + 3) / 4 then
      (eqLevels (nib (point.drop (τ t)) (k / 32)) (nib ((point.map (1 + ·)).drop (τ t)) (k / 32))).getD
        (k % 32) 0
    else 0

/-- Table `t`'s `shared_g` words: nibble `j`'s `g`-power table at `16 j`, zeros past them, `4(n + 1)`
words. -/
def vtShGW (point : List E) (τ : ℕ → ℕ) (t : ℕ) : List E :=
  (List.range (4 * (point.length - τ t + 1))).map fun k ↦
    if k / 16 < (point.length - τ t + 3) / 4 then
      (gTable (nib ((gSquaresList.drop (τ t)).take (point.length - τ t)) (k / 16))).getD (k % 16) 0
    else 0

theorem vtShEqW_length (point : List E) (τ : ℕ → ℕ) (t : ℕ) :
    (vtShEqW point τ t).length = 8 * (point.length - τ t + 1) := by
  simp [vtShEqW]

theorem vtShGW_length (point : List E) (τ : ℕ → ℕ) (t : ℕ) :
    (vtShGW point τ t).length = 4 * (point.length - τ t + 1) := by
  simp [vtShGW]

/-- A nibble of a run of `n` words: at most `4` wide, inside the run. -/
theorem nib_width {l : List E} {n j : ℕ} (hl : l.length = n) (hj : j < (n + 3) / 4) :
    (nib l j).length ≤ 4 ∧ 4 * j + (nib l j).length ≤ n ∧ 0 < (nib l j).length := by
  simp only [nib, List.length_take, List.length_drop, hl]; omega

theorem two_pow_succ_sub_two_le {w : ℕ} (hw : w ≤ 4) :
    2 ^ (w + 1) - 2 ≤ 8 * w ∧ 2 ^ w ≤ 4 * w + 1 ∧ 2 ^ w ≤ 16 ∧ 2 ^ (w + 1) - 2 ≤ 30 := by
  interval_cases w <;> simp

/-- **Table `t`'s buffers give `RunTables`.** -/
theorem vt_runTables {rd : Reader} {pe pg : E} {point : List E} {τ : ℕ → ℕ} {t : ℕ}
    (hμ : point.length < 33) (he : ReadsAt rd pe (vtShEqW point τ t))
    (hg : ReadsAt rd pg (vtShGW point τ t)) :
    RunTables rd pe pg (point.length - τ t) (point.drop (τ t)) ((point.map (1 + ·)).drop (τ t))
      ((gSquaresList.drop (τ t)).take (point.length - τ t)) := by
  intro j hj
  have hsql : gSquaresList.length = 34 := by simp [gSquaresList]
  obtain ⟨hw4, hwn, -⟩ := nib_width (l := point.drop (τ t)) (by simp) hj
  have hw1 : (nib ((point.map (1 + ·)).drop (τ t)) j).length = (nib (point.drop (τ t)) j).length := by
    simp [nib]
  have hgw : (nib ((gSquaresList.drop (τ t)).take (point.length - τ t)) j).length =
      (nib (point.drop (τ t)) j).length := by
    simp [nib, hsql]; omega
  obtain ⟨b1, b2, b3, b4⟩ := two_pow_succ_sub_two_le hw4
  constructor
  · rw [tbReadsAt_gen_pow_mul]
    intro k hk
    rw [eqLevels_length rfl hw1] at hk
    have hlt : 32 * j + k < (vtShEqW point τ t).length := by rw [vtShEqW_length]; omega
    have := he (32 * j + k) hlt
    simp only [vtShEqW, List.getElem_map, List.getElem_range] at this
    rwa [show (32 * j + k) / 32 = j by omega, show (32 * j + k) % 32 = k by omega, ite_pos' hj,
      List.getD_eq_getElem _ _ (by rw [eqLevels_length rfl hw1]; exact hk)] at this
  · rw [tbReadsAt_gen_pow_mul]
    intro k hk
    rw [gTable_length rfl, hgw] at hk
    have hk16 : k < 16 := by omega
    have hlt : 16 * j + k < (vtShGW point τ t).length := by rw [vtShGW_length]; omega
    have := hg (16 * j + k) hlt
    simp only [vtShGW, List.getElem_map, List.getElem_range] at this
    rwa [show (16 * j + k) / 16 = j by omega, show (16 * j + k) % 16 = k by omega, ite_pos' hj,
      List.getD_eq_getElem _ _ (by rw [gTable_length rfl, hgw]; exact hk)] at this

/-- **Table `t`'s buffers give `RunPads`**: past each nibble's tables, zeros. -/
theorem vt_runPads {rd : Reader} {pe pg : E} {point : List E} {τ : ℕ → ℕ} {t : ℕ}
    (hμ : point.length < 33) (he : ReadsAt rd pe (vtShEqW point τ t))
    (hg : ReadsAt rd pg (vtShGW point τ t)) :
    RunPads rd pe pg (point.length - τ t) (point.drop (τ t)) := by
  intro j hj
  have hsql : gSquaresList.length = 34 := by simp [gSquaresList]
  obtain ⟨hw4, hwn, -⟩ := nib_width (l := point.drop (τ t)) (by simp) hj
  have hw1 : (nib ((point.map (1 + ·)).drop (τ t)) j).length = (nib (point.drop (τ t)) j).length := by
    simp [nib]
  have hgw : (nib ((gSquaresList.drop (τ t)).take (point.length - τ t)) j).length =
      (nib (point.drop (τ t)) j).length := by
    simp [nib, hsql]; omega
  constructor
  · intro e he1 he2
    rw [loadHolds_mul_gen_pow]
    have hlt : 32 * j + e < (vtShEqW point τ t).length := by rw [vtShEqW_length]; omega
    have := he (32 * j + e) hlt
    simp only [vtShEqW, List.getElem_map, List.getElem_range] at this
    rwa [show (32 * j + e) / 32 = j by omega, show (32 * j + e) % 32 = e by omega, ite_pos' hj,
      List.getD_eq_default _ _ (by rw [eqLevels_length rfl hw1]; exact he1)]
      at this
  · intro u hu1 hu2
    rw [loadHolds_mul_gen_pow]
    have hlt : 16 * j + u < (vtShGW point τ t).length := by rw [vtShGW_length]; omega
    have := hg (16 * j + u) hlt
    simp only [vtShGW, List.getElem_map, List.getElem_range] at this
    rwa [show (16 * j + u) / 16 = j by omega, show (16 * j + u) % 16 = u by omega, ite_pos' hj,
      List.getD_eq_default _ _ (by rw [gTable_length rfl, hgw]; exact hu1)] at this

end
end LeanVM.Guest.B1.Tables
