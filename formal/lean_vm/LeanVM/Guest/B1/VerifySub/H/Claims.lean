/-
  LeanVM.Guest.B1.VerifySub.H.Claims

  `verify_tables`' honest claims (`VtHonest`): their columns are `claimColumns`, their values the
  framework words, the tables' evaluations and the public input's, their points the bus point's
  prefixes, the table sumcheck's point's prefixes (`chi`) and the public input's point.
-/

module

public import LeanVM.Guest.B1.VerifySub.H.Vt

/-!
# The honest claims

`termsPure_snd`: the table loop's claims, table by table. For an accepted honest run
(`VtHonest.Ok`, six row counts): `claims_split` (the bus's four, the tables' `153`, the public
input's two), `vtH_columns` (`claimColumns`), `vtH_values` (the framework words, the evaluations,
`pcW`), `vtH_points` (by position: the bus point cut to `logMemory` three times and to
`logBytecode` once, then evaluation `k`'s table's height of `chiW`, then the public input's
point).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Complete (termsPure)

@[expose] public section

/-- A table's claims: its evaluations at `point` cut to its height. -/
def rowClaims (point : List E) (q : (Table × ℕ × List Form × E) × List E) : List ColumnClaim :=
  q.2.zipIdx.map fun vc ↦ ⟨globalColumnBases.getD q.1.1.opcode 0 + vc.2, point.take q.1.2.1, vc.1⟩

theorem termsPure_snd (cp fp point : List E) :
    ∀ (pairs : List ((Table × ℕ × List Form × E) × List E)) (cursor : ℕ) (final : E)
      (claims : List ColumnClaim),
      (termsPure cp fp point pairs cursor final claims).2 = claims ++ pairs.flatMap (rowClaims point)
  | [], _, _, claims => by simp [termsPure]
  | ((table, height, forms, weight), ev) :: rest, cursor, final, claims => by
    rw [termsPure, termsPure_snd cp fp point rest, List.flatMap_cons, List.append_assoc]
    rfl

theorem rowClaims_values (point : List E) (q : (Table × ℕ × List Form × E) × List E) :
    (rowClaims point q).map (·.value) = q.2 := by
  simp only [rowClaims, List.map_map]
  exact List.zipIdx_map_fst 0 q.2

theorem rowClaims_points (point : List E) (q : (Table × ℕ × List Form × E) × List E) :
    (rowClaims point q).map (·.point) = List.replicate q.2.length (point.take q.1.2.1) := by
  simp only [rowClaims, List.map_map]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

theorem rowClaims_columns (point : List E) (q : (Table × ℕ × List Form × E) × List E) :
    (rowClaims point q).map (·.column) =
      (List.range q.2.length).map (globalColumnBases.getD q.1.1.opcode 0 + ·) := by
  simp only [rowClaims, List.map_map]
  have h := List.zipIdx_map_snd 0 q.2
  rw [← List.range_eq_range'] at h
  rw [← h, List.map_map]
  rfl

/-- The rows of the tables, with evaluations of the tables' widths, by table. -/
theorem flatMap_rows {Y : Type} (F : Table → ℕ → List E → List Y) (G : Table → ℕ → List Y)
    (hFG : ∀ t h ev, ev.length = t.width → F t h ev = G t h) :
    ∀ (ts : List Table) (rows : List (Table × ℕ × List Form × E)) (evs : List (List E)),
      rows.map (·.1) = ts → evs.map List.length = ts.map (·.width) →
      (List.zip rows evs).flatMap (fun q ↦ F q.1.1 q.1.2.1 q.2) =
        (List.zip ts (rows.map (·.2.1))).flatMap (fun p ↦ G p.1 p.2)
  | [], [], [], _, _ => rfl
  | t :: ts, r :: rows, ev :: evs, h1, h2 => by
    simp only [List.map_cons, List.cons.injEq] at h1 h2
    simp only [List.zip_cons_cons, List.flatMap_cons, List.map_cons]
    rw [hFG _ _ _ (by rw [h2.1, h1.1]), h1.1,
      flatMap_rows F G hFG ts rows evs h1.2 h2.2]
  | [], _ :: _, _, h1, _ => by simp at h1
  | _ :: _, [], _, h1, _ => by simp at h1
  | [], [], _ :: _, _, h2 => by simp at h2
  | _ :: _, _ :: _, [], _, h2 => by simp at h2

/-- Evaluation `k`'s table, by the tables' widths. -/
def vsEvTab (k : ℕ) : ℕ :=
  (List.replicate 13 0 ++ List.replicate 13 1 ++ List.replicate 7 2 ++ List.replicate 14 3 ++
    List.replicate 14 4 ++ List.replicate 92 5).getD k 0

theorem vsEvTab_blocks : (List.range 153).map vsEvTab =
    List.replicate 13 0 ++ List.replicate 13 1 ++ List.replicate 7 2 ++ List.replicate 14 3 ++
      List.replicate 14 4 ++ List.replicate 92 5 := by decide +kernel

theorem tables_widths_list : tables.map (·.width) = vtW6 := by decide +kernel

theorem flatMap_zip_fst {Y : Type} (g : Table → List Y) :
    ∀ (ts : List Table) (hs : List ℕ), ts.length ≤ hs.length →
      (List.zip ts hs).flatMap (fun p ↦ g p.1) = ts.flatMap g
  | [], _, _ => rfl
  | _ :: _, [], h => by simp at h
  | t :: ts, h :: hs, hl => by
    simp only [List.zip_cons_cons, List.flatMap_cons]
    rw [flatMap_zip_fst g ts hs (by simp at hl; omega)]

theorem flatMap_zip_width {Y : Type} (g : ℕ → Y) :
    ∀ (ts : List Table) (hs : List ℕ),
      (List.zip ts hs).flatMap (fun p ↦ List.replicate p.1.width (g p.2)) =
        (List.zip (ts.map (·.width)) hs).flatMap (fun p ↦ List.replicate p.1 (g p.2))
  | [], _ => rfl
  | _ :: _, [] => rfl
  | t :: ts, h :: hs => by
    simp only [List.zip_cons_cons, List.flatMap_cons, List.map_cons]
    rw [flatMap_zip_width g ts hs]

theorem xs4_two {xs4 : List E} (h : xs4.length = 4) : (xs4.take 2).length = 2 := by simp [h]

namespace VtHonest

variable {H : VtHonest}

theorem evsT_lengths (h : H.Ok) (hr : H.rows.length = 6) : H.evsT.map List.length = vtW6 := by
  have hl : H.evsT.length = 6 := by rw [h.hevl, vtH_rowsT_length hr]
  apply List.ext_getElem (by simp [hl]; rfl)
  intro i h1 h2
  simp only [List.length_map] at h1
  have hz : (H.rowsT[i]'(by rw [vtH_rowsT_length hr]; omega), H.evsT[i]) ∈
      List.zip H.rowsT H.evsT := by
    rw [List.mem_iff_getElem]
    exact ⟨i, by simp [vtH_rowsT_length hr, hl]; omega, by simp⟩
  have hw := h.hevw _ hz
  simp only at hw
  have ht1 : (H.rowsT[i]'(by rw [vtH_rowsT_length hr]; omega)).1 = tables.getD i default := by
    have := congrArg (·[i]?) (rowsT_fst H hr)
    simp only [List.getElem?_map] at this
    rw [List.getElem?_eq_getElem (by rw [vtH_rowsT_length hr]; omega),
      List.getElem?_eq_getElem (show i < tables.length by show i < 6; omega)] at this
    simp only [Option.map_some, Option.some.injEq] at this
    rw [this, List.getD_eq_getElem]
  rw [List.getElem_map, hw, ht1, vt_tables_widths i (by omega), List.getD_eq_getElem _ 0 h2]

theorem rowsT_heights (hr : H.rows.length = 6) :
    H.rowsT.map (·.2.1) = tableHeightsOf H.rows := by
  have hh : H.L.tableLogHeights.length = 6 := vt_tableHeights_length hr
  simp only [VtHonest.rowsT, vtRows]
  rw [show (fun x : Table × ℕ × List Form × E ↦ x.2.1) =
      (fun x : ℕ × List Form × E ↦ x.1) ∘ (fun x ↦ x.2) from rfl, ← List.map_map,
    List.map_snd_zip (by
      simp only [List.length_zip, hh, busH_forms_length hr,
        LeanVM.Protocol.EndToEnd.Complete.length_tableWeights]
      decide),
    List.map_fst_zip (by
      simp only [List.length_zip, hh, busH_forms_length hr,
        LeanVM.Protocol.EndToEnd.Complete.length_tableWeights]
      omega)]
  rfl

/-- The honest claims, in three parts. -/
theorem claims_split (h : H.Ok) :
    H.claims = H.busH.claims ++ (List.zip H.rowsT H.evsT).flatMap (rowClaims H.pts.reverse) ++
      H.pclaims := by
  rw [(vt_spec h).2.2.2.1, VtHonest.terms, termsPure_snd]
  rfl

theorem busH_claims_values (h : H.Ok) : H.busH.claims.map (·.value) = H.xs4 := by
  have hx := vt_xs4_split h.hx4
  have h2 := xs4_two h.hx4
  simp only [VtHonest.busH, vtBus, vtBusClaims, List.map_append, List.map_cons, List.map_nil]
  generalize hm : H.xs4.take 2 = m at h2
  match m, h2 with
  | [a, b], _ =>
    rw [hx, hm]
    rfl

/-- **The honest claims' values**: the framework words, the evaluations, the public input's. -/
theorem vtH_values (h : H.Ok) :
    H.claims.map (·.value) = H.xs4 ++ H.evsT.flatten ++ H.pcW := by
  have h6 : H.rowsT.length = H.evsT.length := by rw [h.hevl]
  rw [claims_split h, List.map_append, List.map_append, busH_claims_values h, List.map_flatMap]
  simp only [rowClaims_values]
  rw [vt_flatMap_snd, List.map_snd_zip (by omega)]
  rfl

theorem pclaims_columns : H.pclaims.map (·.column) = [memory0, memory1] := rfl

theorem pclaims_points :
    H.pclaims.map (·.point) =
      List.replicate 2 (H.rm :: List.replicate ((H.L.placement memory0).variableCount - 1) 0) := rfl

/-- **The honest claims' columns.** -/
theorem vtH_columns (h : H.Ok) (hr : H.rows.length = 6) : H.claims.map (·.column) = claimColumns := by
  rw [claims_split h, List.map_append, List.map_append, pclaims_columns, List.map_flatMap]
  simp only [rowClaims_columns]
  rw [flatMap_rows (fun t _ ev ↦ (List.range ev.length).map (globalColumnBases.getD t.opcode 0 + ·))
    (fun t _ ↦ (List.range t.width).map (globalColumnBases.getD t.opcode 0 + ·))
    (fun t _ ev hl ↦ by rw [hl]) tables H.rowsT H.evsT (rowsT_fst H hr)
    (by rw [evsT_lengths h hr, tables_widths_list])]
  rw [flatMap_zip_fst (fun t ↦ (List.range t.width).map (globalColumnBases.getD t.opcode 0 + ·))
    tables _ (by simp [vtH_rowsT_length hr]; decide)]
  have h2 := xs4_two h.hx4
  simp only [VtHonest.busH, vtBus, vtBusClaims, List.map_append, List.map_cons, List.map_nil]
  generalize H.xs4.take 2 = m at h2
  match m, h2 with
  | [a, b], _ => rfl

/-- **The honest claims' points**, by position. -/
theorem vtH_points (h : H.Ok) (hr : H.rows.length = 6) (hbc : H.bc.length = 2 ^ 23) :
    H.claims.map (·.point) = List.replicate 3 (H.point.take H.lm) ++ [H.point.take 19] ++
      (List.range 153).map (fun k ↦ H.chiW.take (vtHt H.rows (vsEvTab k))) ++
      List.replicate 2 (H.rm :: List.replicate ((H.L.placement memory0).variableCount - 1) 0) := by
  have hlb : H.L.logBytecode = 19 := by
    show Nat.log2 H.bc.length - busBits = 19
    rw [hbc, Nat.log2_two_pow]; rfl
  rw [claims_split h, List.map_append, List.map_append, pclaims_points, List.map_flatMap]
  simp only [rowClaims_points]
  rw [flatMap_rows (fun _ hh ev ↦ List.replicate ev.length (H.pts.reverse.take hh))
    (fun t hh ↦ List.replicate t.width (H.pts.reverse.take hh))
    (fun t _ ev hl ↦ by rw [hl]) tables H.rowsT H.evsT (rowsT_fst H hr)
    (by rw [evsT_lengths h hr, tables_widths_list])]
  rw [flatMap_zip_width (fun hh ↦ H.pts.reverse.take hh), tables_widths_list, rowsT_heights hr]
  have hsl : (tableHeightsOf H.rows).length = 6 := vt_tableHeights_length hr
  have h2 := xs4_two h.hx4
  have hchi : H.chiW = H.pts.reverse := rfl
  have hlm : H.L.logMemory = H.lm := rfl
  rw [hchi]
  simp only [VtHonest.busH, vtBus, vtBusClaims, List.map_append, List.map_cons, List.map_nil, hlb,
    hlm]
  have e : (List.range 153).map (fun k ↦ H.pts.reverse.take (vtHt H.rows (vsEvTab k))) =
      ((List.range 153).map vsEvTab).map (fun t ↦ H.pts.reverse.take (vtHt H.rows t)) := by
    rw [List.map_map]; rfl
  rw [e, vsEvTab_blocks]
  generalize H.xs4.take 2 = m at h2
  match hhs : tableHeightsOf H.rows, hsl, m, h2 with
  | [h0, h1, h2, h3', h4, h5], _, [a, b], _ =>
    simp [vtW6, vtHt, hhs, List.replicate_succ]

end VtHonest

end
end LeanVM.Guest.B1.Tables
