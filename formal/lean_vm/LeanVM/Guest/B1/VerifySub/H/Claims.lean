/-
  LeanVM.Guest.B1.VerifySub.H.Claims

  `verify_tables`' honest claims (B1-c's `VtHonest`): their values are `claim_pool`'s words,
  their columns `claimColumns`, their points the bus point's prefixes, the table sumcheck's point's
  prefixes (`chi`), and the public input's point.
-/

module

public import LeanVM.Guest.B1.VerifySub.H.Vt

/-!
# The honest claims

`termsPure_snd`: the table loop's claims, table by table. For an accepted honest run
(`VtHonest.Ok`, six row counts): `vtH_values` (the values are `poolW`), `vtH_columns`
(`claimColumns`), `vtH_points` (by position: the bus point cut to `logMemory` four times and to
`logBytecode` once, then evaluation `k`'s table's height of `chiW`, then the public input's point).
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
  (List.replicate 15 0 ++ List.replicate 15 1 ++ List.replicate 8 2 ++ List.replicate 15 3 ++
    List.replicate 14 4 ++ List.replicate 92 5).getD k 0

theorem vsEvTab_blocks : (List.range 159).map vsEvTab =
    List.replicate 15 0 ++ List.replicate 15 1 ++ List.replicate 8 2 ++ List.replicate 15 3 ++
      List.replicate 14 4 ++ List.replicate 92 5 := by decide +kernel

theorem tables_widths_list : tables.map (·.width) = vtW6 := by decide +kernel

namespace VtHonest

variable {H : VtHonest}

theorem evsT_lengths (h : H.Ok) (hr : H.rows.length = 6) : H.evsT.map List.length = vtW6 := by
  obtain ⟨h6, hw⟩ := vtH_evsT_shape h hr
  apply List.ext_getElem (by simp [h6]; rfl)
  intro i h1 h2
  simp only [List.length_map] at h1
  rw [List.getElem_map, ← List.getD_eq_getElem _ [] h1, hw i (by omega),
    List.getD_eq_getElem _ 0 h2]

theorem rowsT_heights (hr : H.rows.length = 6) :
    H.rowsT.map (·.2.1) = tableHeightsOf H.rows := by
  have hf : H.busH.forms.length = 6 :=
    (vt_forms3_shape H.bc H.lm hr H.alphas H.beta H.point (H.xs5.take 3) (H.xs5.getD 3 0)
      (H.xs5.getD 4 0) H.bv (H.values.getD 0 0) (H.values.getD 1 0) (H.values.getD 2 0)).1
  have hh : H.L.tableLogHeights.length = 6 := vt_tableHeights_length hr
  simp only [VtHonest.rowsT, vtRows]
  rw [show (fun x : Table × ℕ × List Form × E ↦ x.2.1) =
      (fun x : ℕ × List Form × E ↦ x.1) ∘ (fun x ↦ x.2) from rfl, ← List.map_map,
    List.map_snd_zip (by
      simp only [List.length_zip, hh, hf, LeanVM.Protocol.EndToEnd.Complete.length_tableWeights]
      decide),
    List.map_fst_zip (by
      simp only [List.length_zip, hh, hf, LeanVM.Protocol.EndToEnd.Complete.length_tableWeights]
      omega)]
  rfl

/-- The honest claims, in three parts. -/
theorem claims_split (h : H.Ok) :
    H.claims = H.busH.claims ++ (List.zip H.rowsT H.evsT).flatMap (rowClaims H.pts.reverse) ++
      H.pclaims := by
  rw [(vt_spec h).2.2.1, VtHonest.terms, termsPure_snd]
  rfl

/-- **The honest claims' values are `claim_pool`'s words.** -/
theorem vtH_values (h : H.Ok) (hr : H.rows.length = 6) : H.claims.map (·.value) = H.poolW := by
  rw [claims_split h, List.map_append, List.map_append, VtHonest.poolW]
  have h6 : H.rowsT.length = H.evsT.length := by rw [vtH_rowsT_length hr, (vtH_evsT_shape h hr).1]
  congr 1
  congr 1
  · simp only [VtHonest.busH, vtBus, vtBusClaims, List.map_append, List.map_cons, List.map_nil]
    have hx := vt_xs5_split h.hx5
    have h3 : (H.xs5.take 3).length = 3 := by simp [h.hx5]
    match hm : H.xs5.take 3, h3 with
    | [a, b, c], _ =>
      rw [hx, hm]; rfl
  · rw [List.map_flatMap]
    simp only [rowClaims_values]
    rw [vt_flatMap_snd, List.map_snd_zip (by omega)]

end VtHonest

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

namespace VtHonest

variable {H : VtHonest}

theorem pclaims_columns : H.pclaims.map (·.column) = [memory0, memory1, memory2] := rfl

theorem pclaims_points :
    H.pclaims.map (·.point) =
      List.replicate 3 (H.rm :: List.replicate ((H.L.placement memory0).variableCount - 1) 0) := rfl

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
  have hx := vt_xs5_split h.hx5
  have h3 : (H.xs5.take 3).length = 3 := by simp [h.hx5]
  simp only [VtHonest.busH, vtBus, vtBusClaims, List.map_append, List.map_cons, List.map_nil]
  match H.xs5.take 3, h3 with
  | [a, b, c], _ => rfl

set_option maxRecDepth 2048 in
/-- **The honest claims' points**, by position. -/
theorem vtH_points (h : H.Ok) (hr : H.rows.length = 6) (hbc : H.bc.length = 2 ^ 23) :
    H.claims.map (·.point) = List.replicate 4 (H.point.take H.lm) ++ [H.point.take 19] ++
      (List.range 159).map (fun k ↦ H.chiW.take (vtHt H.rows (vsEvTab k))) ++
      List.replicate 3 (H.rm :: List.replicate ((H.L.placement memory0).variableCount - 1) 0) := by
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
  have hx := vt_xs5_split h.hx5
  have h3 : (H.xs5.take 3).length = 3 := by simp [h.hx5]
  have hchi : H.chiW = H.pts.reverse := rfl
  have hlm : H.L.logMemory = H.lm := rfl
  rw [hchi]
  simp only [VtHonest.busH, vtBus, vtBusClaims, List.map_append, List.map_cons, List.map_nil, hlb,
    hlm]
  have e : (List.range 159).map (fun k ↦ H.pts.reverse.take (vtHt H.rows (vsEvTab k))) =
      ((List.range 159).map vsEvTab).map (fun t ↦ H.pts.reverse.take (vtHt H.rows t)) := by
    rw [List.map_map]; rfl
  rw [e, vsEvTab_blocks]
  match hhs : tableHeightsOf H.rows, hsl, H.xs5.take 3, h3 with
  | [h0, h1, h2, h3', h4, h5], _, [a, b, c], _ =>
    simp [vtW6, vtHt, hhs, List.replicate_succ, VtHonest.L]

end VtHonest

end
end LeanVM.Guest.B1.Tables
