/-
  LeanVM.Guest.B1.VerifySub.H.Lanes

  The output lanes of `verify_tables`' honest claims: `claim_pool`'s words `112 .. 136`, on the
  `KECCAK` output columns, at `chi` cut to the `KECCAK` table's height.
-/

module

public import LeanVM.Guest.B1.VerifySub.H.Claims
public import LeanVM.Guest.B1.VerifySub.SoundLib

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier

@[expose] public section

theorem vsEvTab_lanes : ∀ i < 25, Tables.vsEvTab (107 + i) = 5 := by decide +kernel

/-- **The honest output lanes.** -/
theorem vtH_lanes {H : Tables.VtHonest} (h : H.Ok) (hr : H.rows.length = 6)
    (hbc : H.bc.length = 2 ^ 23) :
    (lanesOf H.claims).map (·.value) = (H.poolW.drop 112).take 25 ∧
      (lanesOf H.claims).length = 25 ∧
      (lanesOf H.claims).map (·.column) = keccakOutputColumns ∧
      ∀ c ∈ lanesOf H.claims, c.point = H.chiW.take (Tables.vtHt H.rows 5) := by
  have hcol := Tables.VtHonest.vtH_columns h hr
  have hl : H.claims.length = 167 := by
    rw [← List.length_map (f := (·.column)), hcol]; exact claimColumns_length
  rw [(lanes_eq hcol).1]
  refine ⟨?_, by simp [hl], ?_, fun c hc ↦ ?_⟩
  · rw [List.map_take, List.map_drop, Tables.VtHonest.vtH_values h hr]
  · rw [List.map_take, List.map_drop, hcol, claimColumns_lanes_eq]
  · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
    simp only [List.length_take, List.length_drop, hl] at hj
    have hj25 : j < 25 := by omega
    simp only [List.getElem_take, List.getElem_drop]
    have hp := Tables.VtHonest.vtH_points h hr hbc
    have e := congrArg (fun l ↦ l[112 + j]?) hp
    simp only [List.getElem?_map, List.getElem?_eq_getElem (show 112 + j < H.claims.length by omega),
      Option.map_some] at e
    rw [List.append_assoc, List.append_assoc, List.getElem?_append_right (by simp; omega),
      List.getElem?_append_right (by simp; omega), List.getElem?_append_left (by simp; omega)] at e
    simp only [List.length_replicate, List.length_cons, List.length_nil, List.getElem?_map,
      List.getElem?_range (show 112 + j - 4 - 1 < 159 by omega), Option.map_some,
      Option.some.injEq] at e
    rw [e, show 112 + j - 4 - 1 = 107 + j by omega, vsEvTab_lanes j hj25]

end
end LeanVM.Guest.B1.VerifySub
