/-
  LeanVM.Guest.B1.VerifySub.Export

  `verify_sub`'s last section: the fresh claim's cells copied to `defer_out`.
-/

module

public import LeanVM.Guest.B1.VerifySub.Flat
import LeanVM.Guest.GuestConst
import LeanVM.Guest.Data.Consts

/-!
# The export

`phExport`: a run returns nothing and copies `r_pt`'s first `19` words, then `splitv`'s `36`, to
`defer_out`: the fresh claim's cells (`FreshClaim.cells`, `vsFresh`). The section is the template
`vsExportT`, checked against the body by the kernel.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- `d = p[off]`. -/
def vsLd (d p off : ℕ) : Stmt := .atom (.load (.n d) (.n p) off)

/-- The export: `defer_out[k] = r_pt[k]` (`k < 19`), then `defer_out[19 + j] = splitv[j]`. -/
def vsExportT : List Stmt :=
  ((List.range 19).flatMap fun k ↦ [vsLd (4015 + k) 12 k, vsLd (4015 + k) 5 k]) ++
    (List.range 36).flatMap fun j ↦ [vsLd (4034 + j) 14 j, vsLd (4034 + j) 5 (19 + j)]

theorem vsExportT_eq : (vsPre.drop 4112).take 110 = vsExportT := stmtsEqb_sound (by decide +kernel)

/-- **The export**: nothing returned, the fresh claim's cells at `defer_out`. -/
theorem phExport : PhExport := by
  intro bytecode κ L C V σ rets R
  have ld : ∀ {d p off : ℕ}, vsLd d p off ∈ vsExportT → LoadHolds L.read (σ (.n p)) off (σ (.n d)) :=
    fun hm ↦ R.atom_in vsExportT_eq hm
  have m1 : ∀ k < 19, vsLd (4015 + k) 12 k ∈ vsExportT ∧ vsLd (4015 + k) 5 k ∈ vsExportT :=
    fun k hk ↦ ⟨List.mem_append_left _ (List.mem_flatMap.2 ⟨k, List.mem_range.2 hk, by simp⟩),
      List.mem_append_left _ (List.mem_flatMap.2 ⟨k, List.mem_range.2 hk, by simp⟩)⟩
  have m2 : ∀ j < 36, vsLd (4034 + j) 14 j ∈ vsExportT ∧ vsLd (4034 + j) 5 (19 + j) ∈ vsExportT :=
    fun j hj ↦ ⟨List.mem_append_right _ (List.mem_flatMap.2 ⟨j, List.mem_range.2 hj, by simp⟩),
      List.mem_append_right _ (List.mem_flatMap.2 ⟨j, List.mem_range.2 hj, by simp⟩)⟩
  refine ⟨R.flat.1, ?_⟩
  intro k hk
  have hlen : (vsFresh L.read σ).cells.length = 19 + 36 := by
    simp only [FreshClaim.cells, vsFresh, List.length_append, wordsAt_length]
  rw [hlen] at hk
  have hp : (vsFresh L.read σ).point.length = 19 := wordsAt_length _ _ _
  simp only [FreshClaim.cells]
  by_cases hk19 : k < 19
  · have l1 := ld (m1 k hk19).1
    have l2 := ld (m1 k hk19).2
    rw [List.getElem_append_left (by rw [hp]; exact hk19)]
    simp only [vsFresh, wordsAt, List.getElem_map, List.getElem_range]
    rw [l1.2]
    exact l2
  · have hj : k - 19 < 36 := by omega
    have l1 := ld (m2 (k - 19) hj).1
    have l2 := ld (m2 (k - 19) hj).2
    rw [List.getElem_append_right (by rw [hp]; omega)]
    simp only [vsFresh, wordsAt, List.getElem_map, List.getElem_range, List.length_map,
      List.length_range]
    have hk' : k - Main.bytecodeLog = k - 19 := rfl
    rw [hk', l1.2]
    rw [show 19 + (k - 19) = k by omega] at l2
    exact l2

end
end LeanVM.Guest.B1.VerifySub
