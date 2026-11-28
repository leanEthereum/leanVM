module

public import NativeVm.Math.Tables.Rows

/-!
# The tables' column claims
-/

@[expose] public section

namespace NativeVm.Math.Tables

open NativeVm.Model LeanVM.Parameters

/-- A table's claims: its evaluations `vals` on the columns from `base`, at its point `pt`. -/
abbrev tableClaimsOf (base : Nat) (pt vals : Array EW) : Array ColumnClaimW :=
  vals.zipIdx.map fun (value, column) ↦ ⟨base + column, pt, value⟩

theorem tableClaimsOf_getElem {base : Nat} {pt vals : Array EW} {c : Nat} (h : c < (tableClaimsOf base pt vals).size) :
    (tableClaimsOf base pt vals)[c] = ⟨base + c, pt, vals[c]'(by simpa using h)⟩ := by
  simp [Array.getElem_zipIdx]

theorem tableClaimsOf_size (base : Nat) (pt vals : Array EW) : (tableClaimsOf base pt vals).size = vals.size := by
  simp

/-- The first `t` tables' column claims. -/
def claimsPrefix (ev : Array (Array EW × Array EW)) (t : Nat) : Array ColumnClaimW :=
  ((globalColumnBasesW.zip ev).extract 0 t).flatMap fun (base, point, values) ↦
    values.zipIdx.map fun (value, column) ↦ ⟨base + column, point, value⟩

theorem globalColumnBasesW_eq : globalColumnBasesW = #[5, 18, 31, 38, 52, 66] := by decide

theorem claimsPrefix_six {ev : Array (Array EW × Array EW)} (hev : ev.size = 6) :
    claimsPrefix ev 6 = tableColumnClaims ev := by
  rw [claimsPrefix, Array.extract_eq_self_of_le (by rw [Array.size_zip, hev, globalColumnBasesW_eq]; decide)]
  rfl

theorem claimsPrefix_zero (ev : Array (Array EW × Array EW)) : claimsPrefix ev 0 = #[] := by
  simp [claimsPrefix]

theorem claimsPrefix_succ {ev : Array (Array EW × Array EW)} (hev : ev.size = 6) {t : Nat} (ht : t < 6) :
    claimsPrefix ev (t + 1) = claimsPrefix ev t ++ tableClaimsOf (globalColumnBasesW[t]'(by rw [globalColumnBasesW_eq]; exact ht))
      (ev.getD t (#[], #[])).1 (ev.getD t (#[], #[])).2 := by
  rw [claimsPrefix, Array.extract_succ_right (by omega) (by rw [Array.size_zip, hev, globalColumnBasesW_eq]; exact ht),
    Array.flatMap_push, Array.getElem_zip]
  simp [claimsPrefix, Array.getD_eq_getD_getElem?, hev, ht]

theorem claimsPrefix_size {ev : Array (Array EW × Array EW)} (hev : ev.size = 6)
    (hwid : ∀ t < 6, (ev.getD t (#[], #[])).2.size = widths.getD t 0) :
    ∀ t ≤ 6, (claimsPrefix ev t).size = (widths.take t).sum := by
  intro t ht
  induction t with
  | zero => simp [claimsPrefix_zero]
  | succ t ih =>
    rw [claimsPrefix_succ hev (by omega), Array.size_append, ih (by omega), tableClaimsOf_size, hwid t (by omega)]
    have : ∀ t < 6, (widths.take (t + 1)).sum = (widths.take t).sum + widths.getD t 0 := by decide
    rw [this t (by omega)]

theorem globalColumnBasesW_get {t : Nat} (ht : t < 6) :
    globalColumnBasesW[t]'(by rw [globalColumnBasesW_eq]; exact ht) = 5 + (widths.take t).sum := by
  simp only [globalColumnBasesW_eq]
  interval_cases t <;> rfl

theorem widths_prefix_le {t : Nat} (ht : t ≤ 6) : (widths.take t).sum ≤ 153 := by
  interval_cases t <;> decide

theorem widths_prefix_six : (widths.take 6).sum = 153 := by decide

theorem widths_prefix_succ {t : Nat} (ht : t < 6) :
    (widths.take (t + 1)).sum = (widths.take t).sum + widths.getD t 0 := by
  interval_cases t <;> decide

/-- `tableColumnClaims` of evaluations `widths` long: one claim per table column. -/
theorem tableColumnClaims_size {ev : Array (Array EW × Array EW)} (hev : ev.size = 6)
    (hwid : ∀ t < 6, (ev.getD t (#[], #[])).2.size = widths.getD t 0) :
    (tableColumnClaims ev).size = 153 := by
  rw [← claimsPrefix_six hev, claimsPrefix_size hev hwid 6 le_rfl, widths_prefix_six]

end NativeVm.Math.Tables
