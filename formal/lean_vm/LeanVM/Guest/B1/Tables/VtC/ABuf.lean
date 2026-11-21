/-
  LeanVM.Guest.B1.Tables.VtC.ABuf

  A table's shared selector tables' honest words, as `verify_tables` allocates them.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.SAll
public import LeanVM.Guest.B1.Selectors.SharedHonest

/-!
# A table's shared selector tables

`vtShEqW point τ`, `vtShGW point τ`: the two buffers `verify_tables` allocates for a table of height
`τ` (`ssEqW n`, `ssGW n` words, `n = |point| − τ`), holding the run's honest tables (`ssEqTab`,
`ssGTab`, `Selectors/SharedHonest`) padded with zeros. `vt_runTables`: they give `RunTables`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- The eq table's buffer of a table of height `τ`. -/
def vtShEqW (point : List E) (τ : ℕ) : List E :=
  padTo (ssEqW (point.length - τ))
    (ssEqTab (point.drop τ) ((point.map (1 + ·)).drop τ) (point.length - τ))

/-- The `g` table's buffer. -/
def vtShGW (point : List E) (τ : ℕ) : List E :=
  padTo (ssGW (point.length - τ))
    (ssGTab ((gSquaresList.drop τ).take (point.length - τ)) (point.length - τ))

theorem vt_ssEqTab_le (point : List E) (τ : ℕ) :
    (ssEqTab (point.drop τ) ((point.map (1 + ·)).drop τ) (point.length - τ)).length ≤
      ssEqW (point.length - τ) :=
  ssEqTab_le (by simp) (by simp)

theorem vt_ssGTab_le (gs : List E) (n : ℕ) : (ssGTab gs n).length ≤ ssGW n := by
  have hb : ∀ j, (gTable (nib gs j)).length ≤ 16 := fun j ↦ by
    rw [gTable_length rfl]
    have h4 : (nib gs j).length ≤ 4 := by simp [nib]
    have : 2 ^ (nib gs j).length ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) h4
    simpa using this
  rw [ssGTab, length_flatMap_padTo _ hb, ssGW]; omega

theorem vtShEqW_length (point : List E) (τ : ℕ) :
    (vtShEqW point τ).length = ssEqW (point.length - τ) :=
  padTo_length (vt_ssEqTab_le point τ)

theorem vtShGW_length (point : List E) (τ : ℕ) :
    (vtShGW point τ).length = ssGW (point.length - τ) :=
  padTo_length (vt_ssGTab_le _ _)

/-- A padded buffer holds its prefix. -/
theorem tbReadsAt_padTo {rd : Reader} {p : E} {S : ℕ} {l : List E}
    (h : TbReadsAt rd p (padTo S l)) : TbReadsAt rd p l := by
  have := tbReadsAt_take h l.length
  rwa [padTo, List.take_left' rfl] at this

/-- **A table's buffers give `RunTables`.** -/
theorem vt_runTables {rd : Reader} {pe pg : E} {point : List E} {τ : ℕ}
    (hμ : point.length ≤ 34) (he : TbReadsAt rd pe (vtShEqW point τ))
    (hg : TbReadsAt rd pg (vtShGW point τ)) :
    RunTables rd pe pg (point.length - τ) (point.drop τ) ((point.map (1 + ·)).drop τ)
      ((gSquaresList.drop τ).take (point.length - τ)) :=
  runTables_of (by simp) (by simp) (by simp [gSquaresList]; omega) (tbReadsAt_padTo he)
    (tbReadsAt_padTo hg)

end
end LeanVM.Guest.B1.Tables
