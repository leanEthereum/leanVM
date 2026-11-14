/-
  LeanVM.Guest.B1.Tables.Vt.Sels

  `verify_tables`' block selectors: every push and count block's selector is the specification's
  `blockSel` of its side's log-sizes, and the running sums of the selectors.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.Fw
public import LeanVM.Guest.B1.Tables.Vt.PushPad
public import LeanVM.Guest.B1.Tables.Vt.CountTotal
public import LeanVM.Guest.B1.Tables.Vt.SelBlocks
public import LeanVM.Guest.B1.Tables.Vt.Sort
public import LeanVM.Protocol.EndToEnd.Complete.BusSide

/-!
# The block selectors

Block `b`'s log-size is `kappa_base[BLOCK_KAPPA_SRC[b]]·g^BLOCK_KAPPA_ADJ[b]` in the exponent,
`vtKap lm τ b` (`Sort`), the side's sizes `vtSizesP` (push: the framework's `0, log_mem, 19`, then each
table block at its table's height) and `vtSizesC` (count). `vt_sels`: every push block's selector
(`block_eq_hi[b]`'s copy) is `blockSel (vtSizesP lm τ) |point| b point`, every count block's
`blockSel (vtSizesC τ) |point| b point`, and the running sums are their sums.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Complete (blockSel blockOffset eqAbove_aligned)

@[expose] public section

/-! ## The sizes -/

/-- The push side's log-sizes: the framework's, then the table blocks'. -/
def vtSizesP (lm : ℕ) (τ : ℕ → ℕ) : List ℕ := [0, lm, 19] ++ vtPushPadData.map fun x ↦ τ x.2.1

/-- The count side's log-sizes. -/
def vtSizesC (τ : ℕ → ℕ) : List ℕ := vtCountPadData.map fun x ↦ τ x.2.1

theorem vt_srcP : ∀ i < 51, blockKappaSrc.getD (3 + i) 0 = (vtPushPadData.getD i default).2.1 + 2 ∧
    blockKappaAdj (3 + i) = 0 ∧ (vtPushPadData.getD i default).2.1 < 6 := by decide

theorem vt_srcC : ∀ i < 45, blockKappaSrc.getD (108 + i) 0 = (vtCountPadData.getD i default).2.1 + 2 ∧
    blockKappaAdj (108 + i) = 0 ∧ (vtCountPadData.getD i default).2.1 < 6 := by decide

theorem vt_tau_getD (lm : ℕ) (τ : ℕ → ℕ) {t : ℕ} (ht : t < 6) :
    ([0, lm] ++ vtTauList τ).getD (t + 2) 0 = τ t := by
  simp only [List.cons_append, List.nil_append, List.getD_cons_succ]
  rw [List.getD_eq_getElem _ _ (by simp [vtTauList]; omega)]
  simp [vtTauList]

theorem vtPushPadData_length : vtPushPadData.length = 51 := rfl

theorem vtCountPadData_length : vtCountPadData.length = 45 := rfl

/-- The push side's cells hold its sizes. -/
theorem vt_kapP (lm : ℕ) (τ : ℕ → ℕ) {c : ℕ} (hc : c < 54) :
    vtKap lm τ c = (vtSizesP lm τ).getD c 0 := by
  rcases Nat.lt_or_ge c 3 with h3 | h3
  · interval_cases c <;> simp [vtKap, vtSizesP, blockKappaSrc, blockKappaAdj]
  · obtain ⟨i, rfl⟩ : ∃ i, c = 3 + i := ⟨c - 3, by omega⟩
    obtain ⟨e1, e2, e3⟩ := vt_srcP i (by omega)
    have hi : i < vtPushPadData.length := by rw [vtPushPadData_length]; omega
    rw [vtKap, e1, e2, vt_tau_getD lm τ e3, vtSizesP, List.getD_append_right _ _ _ _ (by simp),
      show 3 + i - [0, lm, 19].length = i by simp]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi,
      Option.map_some, Option.getD_some, Nat.add_zero]

/-- The count side's cells hold its sizes. -/
theorem vt_kapC (lm : ℕ) (τ : ℕ → ℕ) {c : ℕ} (hc : c < 45) :
    vtKap lm τ (108 + c) = (vtSizesC τ).getD c 0 := by
  obtain ⟨e1, e2, e3⟩ := vt_srcC c hc
  have hi : c < vtCountPadData.length := by rw [vtCountPadData_length]; omega
  rw [vtKap, e1, e2, vt_tau_getD lm τ e3, vtSizesC]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi,
    Option.map_some, Option.getD_some, Nat.add_zero]

/-- `stackOffsets`' offsets of at most `64` blocks of at most `2^34` are below `2^62`. -/
theorem vt_stackOffsets_lt (sizes : List ℕ) (hl : sizes.length ≤ 64)
    (hs : ∀ b, sizes.getD b 0 ≤ 34) (b : ℕ) : (stackOffsets sizes).1.getD b 0 < 2 ^ 62 := by
  rcases Nat.lt_or_ge b sizes.length with hb | hb
  · set ord := (List.range sizes.length).mergeSort (stackLe (sizes.getD · 0))
    have hperm : ord.Perm (List.range sizes.length) := List.mergeSort_perm _ _
    have hmem : b ∈ ord := hperm.mem_iff.mpr (List.mem_range.mpr hb)
    obtain ⟨r, hr, hrb⟩ := List.getElem_of_mem hmem
    have hlen : ord.length = sizes.length := by rw [hperm.length_eq, List.length_range]
    have e := tb_stackOffsets_fst sizes r (by omega)
    rw [show ord.getD r 0 = b by rw [List.getD_eq_getElem _ _ hr, hrb]] at e
    rw [e, tbPrefixSize]
    have hle : ((ord.take r).map fun i ↦ 2 ^ sizes.getD i 0).sum ≤
        ((ord.take r).map fun i ↦ 2 ^ sizes.getD i 0).length * 2 ^ 34 := by
      apply List.sum_le_length_nsmul
      intro x hx
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
      exact Nat.pow_le_pow_right (by norm_num) (hs i)
    simp only [List.length_map, List.length_take] at hle
    calc _ ≤ min r ord.length * 2 ^ 34 := hle
      _ ≤ 64 * 2 ^ 34 := Nat.mul_le_mul_right _ (by omega)
      _ < 2 ^ 62 := by norm_num
  · rw [List.getD_eq_default _ _ (by rw [tb_stackOffsets_length]; exact hb)]
    norm_num

/-- An aligned block's `eqAbove` is its `blockSel`. -/
theorem vt_eqAbove_blockSel (sizes : List ℕ) (b : ℕ) (point : List E) :
    Placement.eqAbove ⟨sizes.getD b 0, (stackOffsets sizes).1.getD b 0⟩ point =
      blockSel sizes point.length b point := by
  rw [eqAbove_aligned]
  rfl

end
end LeanVM.Guest.B1.Tables
