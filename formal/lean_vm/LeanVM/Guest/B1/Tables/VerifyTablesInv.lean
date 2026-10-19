/-
  LeanVM.Guest.B1.Tables.VerifyTablesInv

  `tablesSeg`'s run, inverted: the claims it returns, their columns and their points.
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTables
public import LeanVM.Guest.B1.Tables.GkrInv
public import LeanVM.Guest.B1.VerifySub.Layout

/-!
# The claims of a run of `tablesSeg`

`RunsTo.tablesSeg_inv`: any run of `tablesSeg` returns the bus's five claims, the tables'
claims on their columns at prefixes of the reversed sumcheck challenges, and the public input's
three claims (`piClaims`). `tablesSeg_claimsOk`: on the deployed layout these are the claims
`verify_sub`'s inversion needs (the shape of g6's `TablesClaimsOk`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem RunsTo.tableTerms_inv (cp fp pt : List E) :
    ∀ (rows : List (Table × ℕ × List Form × E)) (cursor : ℕ) (final : E) (claims : List ColumnClaim)
      (cv cv' : Digest) (xs : List E) (r : E × List ColumnClaim),
      RunsTo (tableTerms cp fp pt rows cursor final claims) cv xs r cv' →
      ∃ evss : List (List E), evss.length = rows.length ∧
        (∀ i (h1 : i < evss.length) (h2 : i < rows.length), evss[i].length = rows[i].1.width) ∧
        r.2 = claims ++ (List.zip rows evss).flatMap (rowClaims pt)
  | [], cursor, final, claims, cv, cv', xs, r, h => by
    have h' : RunsTo (pure (final, claims) : Prog (E × List ColumnClaim)) cv xs r cv' := h
    obtain ⟨-, rfl, -⟩ := RunsTo.ret_inv h'
    exact ⟨[], rfl, fun i h1 => absurd h1 (by simp), by simp⟩
  | (table, height, forms, weight) :: rest, cursor, final, claims, cv, cv', xs, r, h => by
    unfold tableTerms at h
    obtain ⟨x1, x2, evs, cv1, -, h1, h2⟩ := RunsTo.bind_inv' h
    obtain ⟨hl, rfl, -⟩ := RunsTo.readN_inv h1
    obtain ⟨evss, hl', hw, hr⟩ := RunsTo.tableTerms_inv cp fp pt rest _ _ _ _ _ _ _ h2
    refine ⟨evs :: evss, by simp [hl'], fun i h1 h2 => ?_, ?_⟩
    · match i with
      | 0 => simpa using hl
      | i + 1 => simpa using hw i (by simpa using h1) (by simpa using h2)
    · rw [hr]
      simp [rowClaims, List.append_assoc]

/-- **The table sumcheck's run, inverted**: its challenges `chs` (one per round), the tables'
evaluations, and the claims at the reversed challenges. -/
theorem RunsTo.tableSumcheck_inv {heights : List ℕ} {busForms : List (List Form)}
    {cps fps eqp : List E} {target : E} {cv cv' : Digest} {xs : List E} {claims : List ColumnClaim}
    (h : RunsTo (tableSumcheck heights busForms cps fps eqp target) cv xs claims cv') :
    ∃ (chs : List E) (evss : List (List E)), chs.length = heights.foldl max 0 ∧
      evss.length = (List.zip tables (List.zip heights (List.zip busForms
        (tableWeights heights eqp chs.reverse)))).length ∧
      (∀ i (h1 : i < evss.length) (h2 : i < (List.zip tables (List.zip heights (List.zip busForms
        (tableWeights heights eqp chs.reverse)))).length),
        evss[i].length = (List.zip tables (List.zip heights (List.zip busForms
          (tableWeights heights eqp chs.reverse))))[i].1.width) ∧
      claims = (List.zip (List.zip tables (List.zip heights (List.zip busForms
        (tableWeights heights eqp chs.reverse)))) evss).flatMap (rowClaims chs.reverse) := by
  unfold tableSumcheck at h
  obtain ⟨x1, x2, ⟨chs, cl⟩, cv1, -, h1, h⟩ := RunsTo.bind_inv' h
  obtain ⟨cl', cvr, wsr, ch, -, -, -, -, hpt, -, -⟩ := RunsTo.sumcheck_inv _ _ _ _ _ _ _ h1
  obtain ⟨x3, x4, ⟨final, tc⟩, cv3, -, h3, h⟩ := RunsTo.bind_inv' h
  obtain ⟨evss, hl, hw, hr⟩ := RunsTo.tableTerms_inv _ _ _ _ _ _ _ _ _ _ _ h3
  obtain ⟨x5, x6, u, cv5, -, h5, h⟩ := RunsTo.bind_inv' h
  obtain ⟨-, -, -⟩ := RunsTo.require_inv h5
  obtain ⟨-, rfl, -⟩ := RunsTo.ret_inv h
  refine ⟨chs, evss, by simp [hpt], hl, hw, ?_⟩
  simpa using hr

/-- **The table phase's run, inverted.** -/
theorem RunsTo.tablePhase_inv {layout : Layout} {bus : BusResult} {cv cv' : Digest} {xs : List E}
    {claims : List ColumnClaim} (h : RunsTo (tablePhase layout bus) cv xs claims cv') :
    ∃ (chs : List E) (evss : List (List E)) (ws : List E) ,
      chs.length = layout.tableLogHeights.foldl max 0 ∧
      ws = tableWeights layout.tableLogHeights bus.point chs.reverse ∧
      evss.length = (List.zip tables (List.zip layout.tableLogHeights (List.zip bus.forms ws))).length ∧
      (∀ i (h1 : i < evss.length) (h2 : i < (List.zip tables (List.zip layout.tableLogHeights
        (List.zip bus.forms ws))).length),
        evss[i].length = (List.zip tables (List.zip layout.tableLogHeights (List.zip bus.forms ws)))[i].1.width) ∧
      claims = bus.claims ++ (List.zip (List.zip tables (List.zip layout.tableLogHeights
        (List.zip bus.forms ws))) evss).flatMap (rowClaims chs.reverse) := by
  unfold tablePhase at h
  obtain ⟨x1, x2, xi, cv1, -, h1, h⟩ := RunsTo.bind_inv' h
  obtain ⟨x3, x4, tc, cv3, -, h3, h⟩ := RunsTo.bind_inv' h
  obtain ⟨chs, evss, hl, hel, hw, hc⟩ := RunsTo.tableSumcheck_inv h3
  obtain ⟨-, rfl, -⟩ := RunsTo.ret_inv h
  exact ⟨chs, evss, _, hl, rfl, hel, hw, by rw [hc]⟩

/-- **The public input's run, inverted.** -/
theorem RunsTo.publicInputPhase_inv {layout : Layout} {pi : Digest} {cv cv' : Digest} {xs : List E}
    {claims : List ColumnClaim} (h : RunsTo (publicInputPhase layout pi) cv xs claims cv') :
    claims = piClaims layout pi (challengeOf (sqCv cv)) := by
  unfold publicInputPhase at h
  obtain ⟨x1, x2, rm, cv1, -, h1, h⟩ := RunsTo.bind_inv' h
  obtain ⟨-, rfl, -⟩ := RunsTo.sampleE_inv h1
  obtain ⟨-, rfl, -⟩ := RunsTo.ret_inv h
  rfl

/-- **The bus's run, inverted**: three memory words, two final counters, and the bytecode's value
from `ev`. -/
theorem RunsTo.busRest_inv {ev : Evaluations} {layout : Layout} {alphas : List E} {beta : E}
    {point tv : List E} {cv cv' : Digest} {xs : List E} {bus : BusResult}
    (h : RunsTo (busRest ev layout alphas beta point tv) cv xs bus cv') :
    ∃ (memory : List E) (mF bF bv : E), memory.length = 3 ∧
      bus = busVal layout alphas beta point tv memory mF bF bv := by
  unfold busRest at h
  obtain ⟨x1, x2, memory, cv1, -, h1, h⟩ := RunsTo.bind_inv' h
  obtain ⟨hl, rfl, -⟩ := RunsTo.readN_inv h1
  obtain ⟨x3, x4, mF, cv3, -, h3, h⟩ := RunsTo.bind_inv' h
  obtain ⟨x5, x6, bF, cv5, -, h5, h⟩ := RunsTo.bind_inv' h
  obtain ⟨x7, x8, bv, cv7, -, h7, h⟩ := RunsTo.bind_inv' h
  have h' : RunsTo (pure (busVal layout alphas beta point tv memory mF bF bv) : Prog BusResult) cv7 x8 bus cv' := h
  obtain ⟨-, rfl, -⟩ := RunsTo.ret_inv h'
  exact ⟨memory, mF, bF, bv, hl, rfl⟩

/-- **`tablesSeg`'s run, inverted.** -/
theorem RunsTo.tablesSeg_inv {ev : Evaluations} {layout : Layout} {pi : Digest} {alphas : List E}
    {beta : E} {point tv : List E} {cv cv' : Digest} {xs : List E} {bus : BusResult}
    {claims : List ColumnClaim}
    (h : RunsTo (tablesSeg ev layout pi alphas beta point tv) cv xs (bus, claims) cv') :
    ∃ (memory : List E) (mF bF bv : E) (chs : List E) (evss : List (List E)) (ws : List E) (rm : E),
      memory.length = 3 ∧ bus = busVal layout alphas beta point tv memory mF bF bv ∧
      chs.length = layout.tableLogHeights.foldl max 0 ∧
      ws = tableWeights layout.tableLogHeights bus.point chs.reverse ∧
      evss.length = (List.zip tables (List.zip layout.tableLogHeights (List.zip bus.forms ws))).length ∧
      (∀ i (h1 : i < evss.length) (h2 : i < (List.zip tables (List.zip layout.tableLogHeights
        (List.zip bus.forms ws))).length),
        evss[i].length = (List.zip tables (List.zip layout.tableLogHeights (List.zip bus.forms ws)))[i].1.width) ∧
      claims = bus.claims ++ (List.zip (List.zip tables (List.zip layout.tableLogHeights
        (List.zip bus.forms ws))) evss).flatMap (rowClaims chs.reverse) ++ piClaims layout pi rm := by
  unfold tablesSeg at h
  obtain ⟨x1, x2, bus1, cv1, -, h1, h⟩ := RunsTo.bind_inv' h
  obtain ⟨memory, mF, bF, bv, hl, rfl⟩ := RunsTo.busRest_inv h1
  obtain ⟨x3, x4, tc, cv3, -, h3, h⟩ := RunsTo.bind_inv' h
  obtain ⟨chs, evss, ws, hc, hws, hel, hw, htc⟩ := RunsTo.tablePhase_inv h3
  obtain ⟨x5, x6, pc, cv5, -, h5, h⟩ := RunsTo.bind_inv' h
  have hpc := RunsTo.publicInputPhase_inv h5
  obtain ⟨-, he, -⟩ := RunsTo.ret_inv h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨memory, mF, bF, bv, chs, evss, ws, _, hl, rfl, hc, hws, hel, hw, by rw [htc, hpc]⟩

/-! ## The claims' shape on the deployed layout -/

theorem vt_le_sum_of_mem : ∀ {l : List ℕ} {x : ℕ}, x ∈ l → x ≤ l.sum
  | _ :: l, _, List.Mem.head _ => by simp
  | y :: l, x, List.Mem.tail _ h => by have := vt_le_sum_of_mem h; simp; omega

theorem le_log2Ceil_of_mem {l : List ℕ} {x : ℕ} (h : x ∈ l) : x ≤ log2Ceil ((l.map (2 ^ ·)).sum) := by
  have h1 : 2 ^ x ≤ (l.map (2 ^ ·)).sum := vt_le_sum_of_mem (List.mem_map_of_mem h)
  have h2 := le_two_pow_log2Ceil ((l.map (2 ^ ·)).sum)
  exact (Nat.pow_le_pow_iff_right (by decide)).mp (le_trans h1 h2)

theorem foldl_max_le {l : List ℕ} {B : ℕ} (h : ∀ x ∈ l, x ≤ B) : ∀ a ≤ B, l.foldl max a ≤ B := by
  induction l with
  | nil => intro a ha; exact ha
  | cons y l ih =>
    intro a ha
    exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) _ (max_le ha (h y (List.mem_cons_self ..)))

theorem formsShaped_fold {side : ℕ} {w : List E} {β : E} {point : List E} :
    ∀ (l : List (E × BusBlock)) (acc : List (List Form) × E), FormsShaped acc.1 →
      FormsShaped (l.foldl (accStep side w β point) acc).1
  | [], _, h => h
  | _ :: l, _, h => formsShaped_fold l _ (formsShaped_step h)

theorem busVal_forms_shaped (layout : Layout) (alphas : List E) (beta : E) (point tv memory : List E)
    (mF bF bv : E) : FormsShaped (busVal layout alphas beta point tv memory mF bF bv).forms := by
  rw [busVal_eq]
  simp only [accumulateSide_eq]
  exact formsShaped_fold _ _ (formsShaped_fold _ _ (formsShaped_fold _ _ forms0_shaped))

theorem tableWeights_length (heights : List ℕ) (eqp pt : List E) :
    (tableWeights heights eqp pt).length = heights.length := by
  unfold tableWeights
  suffices ∀ (l : List (E × ℕ)) (ws : List E), ws.length = heights.length →
      (l.foldl (fun weights (challenge, coord) ↦ List.zipWith (fun weight height ↦ weight *
        if coord < height then 1 + eqp.getD coord 0 + challenge else challenge) weights heights) ws).length =
        heights.length from this _ _ (by simp)
  intro l
  induction l with
  | nil => intro ws h; exact h
  | cons q l ih => intro ws h; exact ih _ (by simp [List.length_zipWith, h])

theorem columnKappas_table (m lb : ℕ) (hs : List ℕ) {t k : ℕ} (ht : t < 6)
    (hk : k < (tables.getD t default).width) :
    (columnKappas m lb hs).getD (globalColumnBases.getD t 0 + k) 0 = hs.getD t 0 := by
  have hb : globalColumnBases.getD t 0 = 6 + ((tables.take t).map fun x => (List.replicate x.width
      (hs.getD x.opcode 0)).length).sum := by
    rw [globalColumnBases, List.getD_eq_getElem _ _ (by simp [tables_length']; omega), List.getElem_map,
      List.getElem_range, tableWidths, ← List.map_take]
    simp [numGlobalColumns, Table.width]; rfl
  rw [hb, columnKappas, List.getD_eq_getElem?_getD, Nat.add_assoc, List.getElem?_append_right (by simp),
    show 6 + (((tables.take t).map fun x => (List.replicate x.width (hs.getD x.opcode 0)).length).sum + k) -
      [m, m, m, m, lb, hs.getD opBlake2s 0 + qflockSlotBits].length =
      ((tables.take t).map fun x => (List.replicate x.width (hs.getD x.opcode 0)).length).sum + k by simp,
    ← List.getD_eq_getElem?_getD, vt_flatMap_getD _ _ tables t k (by simp [tables_length']; omega)
      (by simpa using hk)]
  rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_replicate]
  have := (vt_widths t ht).2
  rw [this]

theorem placementsOf_vars (kappas : List ℕ) {col : ℕ} (hc : col < kappas.length) :
    ((placementsOf kappas).1.getD col default).vars = kappas.getD col 0 := by
  unfold placementsOf
  simp only
  rw [List.getD_eq_getElem _ _ (by simpa using hc), List.getElem_map, List.getElem_zipIdx,
    List.getD_eq_getElem _ _ hc, Nat.zero_add]
  split <;> rfl

/-- The tables' claims of a run, on their columns. -/
theorem tc_columns (pt : List E) (X : List (ℕ × List Form × E)) (hX : X.length = 6)
    (evss : List (List E)) (he : evss.length = 6)
    (hw : ∀ t < 6, (evss.getD t []).length = (tables.getD t default).width) :
    ((List.zip (List.zip tables X) evss).flatMap (rowClaims pt)).map (·.column) =
      tables.flatMap (fun t ↦ (List.range t.width).map (globalColumnBases.getD t.opcode 0 + ·)) := by
  rw [List.map_flatMap, vt_rows_flatMap X hX _ he, tables_flatMap_fin]
  simp only [rowClaims_column]
  rw [List.flatMap_def, List.flatMap_def, show List.range 6 = (List.finRange 6).map (·.val) by
    decide, List.map_map]
  refine congrArg List.flatten (List.map_congr_left fun t _ => ?_)
  simp only [Function.comp_apply, hw t t.2]

/-- A table's claim of a run: on a column of the table, at the prefix of its height. -/
theorem tc_mem (pt : List E) (X : List (ℕ × List Form × E)) (hX : X.length = 6)
    (evss : List (List E)) (he : evss.length = 6)
    (hw : ∀ t < 6, (evss.getD t []).length = (tables.getD t default).width) {c : ColumnClaim}
    (hc : c ∈ (List.zip (List.zip tables X) evss).flatMap (rowClaims pt)) :
    ∃ t < 6, ∃ k < (tables.getD t default).width,
      c.column = globalColumnBases.getD t 0 + k ∧ c.point = pt.take (X.getD t default).1 := by
  rw [vt_rows_flatMap X hX _ he] at hc
  obtain ⟨t, ht, hc⟩ := List.mem_flatMap.mp hc
  have ht' := List.mem_range.mp ht
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hc
  refine ⟨t, ht', q.2, ?_, ?_, rfl⟩
  · have := List.snd_lt_of_mem_zipIdx hq
    rw [← hw t ht']; simpa using this
  · simp only [(vt_widths t ht').2]

theorem tc_length (pt : List E) (X : List (ℕ × List Form × E)) (hX : X.length = 6)
    (evss : List (List E)) (he : evss.length = 6)
    (hw : ∀ t < 6, (evss.getD t []).length = (tables.getD t default).width) :
    ((List.zip (List.zip tables X) evss).flatMap (rowClaims pt)).length = 104 := by
  have := congrArg List.length (tc_columns pt X hX evss he hw)
  simp only [List.length_map] at this
  rw [this]
  decide +kernel

/-- **The claims' shape** (g6's `TablesClaimsOk`): on the deployed layout, a run of `tablesSeg`
returns the claims on `claimColumns`, the bus's at prefixes of the point, the tables' at prefixes
of the reversed sumcheck challenges `chis`, the public input's at `rm, 0, …`, each claim's point
of its column's placement's size. -/
theorem tablesSeg_claimsOk {bytecode : List K} (hb : bytecode.length = 2 ^ 22) {logMem : ℕ}
    (hm16 : 16 ≤ logMem) {rows : List ℕ} (hr : rows.length = 6) {ev : Evaluations} {pi : Digest}
    {alphas : List E} {beta : E} {point values : List E} {cv cv' : Digest} {xs : List E}
    {bus : BusResult} {claims : List ColumnClaim}
    (hpt : point.length = pushDepth (layoutOf bytecode logMem rows))
    (h : RunsTo (tablesSeg ev (layoutOf bytecode logMem rows) pi alphas beta point values) cv xs
      (bus, claims) cv') :
    ∃ (chis : List E) (rm : E), chis.length ≤ point.length ∧ claims.map (·.column) = claimColumns ∧
      (∀ j (p : List E), (claims.map (·.point))[j]? = some p →
        (j < 5 → p = point.take p.length) ∧ (5 ≤ j → j < nPooled → p = chis.take p.length) ∧
          (nPooled ≤ j → p = rm :: List.replicate
            (((layoutOf bytecode logMem rows).placements.getD memory0 default).vars - 1) 0)) ∧
      ∀ c ∈ claims, c.point.length =
        ((layoutOf bytecode logMem rows).placements.getD c.column default).vars := by
  obtain ⟨memory, mF, bF, bv, chs, evss, ws, rm, hl, rfl, hc, hws, hel, hw, rfl⟩ := RunsTo.tablesSeg_inv h
  obtain ⟨m0, m1, m2, rfl⟩ : ∃ a b c, memory = [a, b, c] := by
    match memory, hl with
    | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
  obtain ⟨hlb, hth, -⟩ := layoutOf_blocks bytecode hb logMem rows hr
  set L := layoutOf bytecode logMem rows with hLd
  set bus := busVal L alphas beta point values [m0, m1, m2] mF bF bv with hbus
  have hfs : FormsShaped bus.forms := busVal_forms_shaped L alphas beta point values [m0, m1, m2] mF bF bv
  have hbl : bus.claims.length = 5 := rfl
  obtain ⟨h0, h1, h2, h3, h4, h5, hhs⟩ : ∃ h0 h1 h2 h3 h4 h5, rows.map log2Ceil = [h0, h1, h2, h3, h4, h5] := by
    match rows.map log2Ceil, (by simp [hr] : (rows.map log2Ceil).length = 6) with
    | [a, b, c, d, e, f], _ => exact ⟨a, b, c, d, e, f, rfl⟩
  have hmem : ∀ x ∈ pushKappas logMem (rows.map log2Ceil), x ≤ point.length := fun x hx => by
    rw [hpt, pushDepth_eq hb logMem rows hr]; exact le_log2Ceil_of_mem hx
  rw [hhs] at hmem
  have hm_le : logMem ≤ point.length := hmem _ (by simp [pushKappas])
  have h18 : 18 ≤ point.length := hmem _ (by simp [pushKappas])
  have hh : ∀ x ∈ L.tableLogHeights, x ≤ point.length := fun x hx => by
    rw [hth, hhs] at hx
    apply hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [pushKappas]
  have hn : chs.length ≤ point.length := by
    rw [hc]; exact foldl_max_le hh 0 (Nat.zero_le _)
  have hhn : ∀ x ∈ L.tableLogHeights, x ≤ chs.length := fun x hx => by
    rw [hc]; exact vt_le_foldl_max _ 0 x (Or.inl hx)
  have hthl : L.tableLogHeights.length = 6 := by rw [hth, hhs]; rfl
  set X := List.zip L.tableLogHeights (List.zip bus.forms ws) with hXd
  have hX : X.length = 6 := by
    simp [hXd, hthl, hfs.1, hws, tableWeights_length]
  have he6 : evss.length = 6 := by rw [hel]; simp [hX, tables_length']
  have hw' : ∀ t < 6, (evss.getD t []).length = (tables.getD t default).width := fun t ht => by
    have := hw t (by omega) (by simp [hX, tables_length']; omega)
    rw [List.getD_eq_getElem _ _ (by omega), this, List.getElem_zip,
      List.getD_eq_getElem _ _ (by simp [tables_length']; omega)]
  have hmap : X.map (·.1) = L.tableLogHeights := by
    rw [hXd]; exact List.map_fst_zip (by simp [hthl, hfs.1, hws, tableWeights_length])
  have hXg : ∀ t < 6, (X.getD t default).1 = L.tableLogHeights.getD t 0 := fun t ht => by
    have : (X.map (·.1)).getD t 0 = (X.getD t default).1 := by
      rw [List.getD_eq_getElem _ _ (by simp [hX]; omega), List.getElem_map,
        List.getD_eq_getElem _ _ (by omega)]
    rw [← this, hmap]
  have hpl : L.placements = (placementsOf (columnKappas logMem 18 L.tableLogHeights)).1 := by
    rw [← hlb]; rfl
  have hkl : (columnKappas logMem 18 L.tableLogHeights).length = 110 := by
    rw [columnKappas_length]; decide +kernel
  have hv0 : (L.placements.getD memory0 default).vars = logMem := by
    rw [hpl, placementsOf_vars _ (by rw [hkl]; decide)]; rfl
  have htl := tc_length chs.reverse X hX evss he6 hw'
  refine ⟨chs.reverse, rm, by rw [List.length_reverse]; exact hn, ?_, ?_, ?_⟩
  · rw [List.map_append, List.map_append, tc_columns chs.reverse X hX evss he6 hw']
    rfl
  · intro j p hp
    rw [List.map_append, List.map_append] at hp
    have hnp : nPooled = 109 := rfl
    rw [hnp]
    rcases lt_or_ge j 5 with hj | hj
    · rw [List.getElem?_append_left (by simp [htl, hbl]; omega), List.getElem?_append_left (by simp [hbl]; omega)] at hp
      refine ⟨fun _ => ?_, fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
      have hb5 : bus.claims.map (·.point) = [point.take L.logMemory, point.take L.logMemory,
          point.take L.logMemory, point.take L.logMemory, point.take L.logBytecode] := rfl
      rw [hb5] at hp
      interval_cases j <;> simp only [List.getElem?_cons_zero, List.getElem?_cons_succ,
        Option.some.injEq] at hp <;> subst hp <;> exact take_eq_take_length _ _
    rcases lt_or_ge j 109 with hj' | hj'
    · rw [List.getElem?_append_left (by simp [htl, hbl]; omega), List.getElem?_append_right (by simp [hbl]; omega)] at hp
      refine ⟨fun h => absurd h (by omega), fun _ _ => ?_, fun h => absurd h (by omega)⟩
      have hm := List.mem_of_getElem? hp
      obtain ⟨c, hc', rfl⟩ := List.mem_map.mp hm
      obtain ⟨t, -, k, -, -, hpt'⟩ := tc_mem chs.reverse X hX evss he6 hw' hc'
      rw [hpt']; exact take_eq_take_length _ _
    · rw [List.getElem?_append_right (by simp [htl, hbl]; omega)] at hp
      refine ⟨fun h => absurd h (by omega), fun h h' => absurd h' (by omega), fun _ => ?_⟩
      have hm := List.mem_of_getElem? hp
      simp only [piClaims, List.zipWith_cons_cons, List.zipWith_nil_left, List.map_cons, List.map_nil,
        List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl <;> rfl
  · intro c hcm
    rw [List.mem_append, List.mem_append] at hcm
    rcases hcm with (hcm | hcm) | hcm
    · simp only [hbus, busVal, List.zipWith_cons_cons, List.zipWith_nil_left, List.cons_append,
        List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hcm
      rcases hcm with rfl | rfl | rfl | rfl | rfl <;>
        (rw [hpl, placementsOf_vars _ (by rw [hkl]; simp [memory0, memory1, memory2,
           memoryFinalCounters, bytecodeFinalCounters])]
         simp [columnKappas, memory0, memory1, memory2, memoryFinalCounters, bytecodeFinalCounters,
          hlb, show L.logMemory = logMem from rfl, hm_le, h18])
    · obtain ⟨t, ht, k, hk, hcol, hpt'⟩ := tc_mem chs.reverse X hX evss he6 hw' hcm
      have hbw : ∀ t < 6, globalColumnBases.getD t 0 + (tables.getD t default).width ≤ 110 := by
        decide +kernel
      have := hbw t ht
      rw [hcol, hpt', hpl, placementsOf_vars _ (by rw [hkl]; omega),
        columnKappas_table _ _ _ ht hk, hXg t ht, List.length_take, List.length_reverse]
      have : L.tableLogHeights.getD t 0 ≤ chs.length :=
        hhn _ (by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)
      omega
    · simp only [piClaims, List.map_cons, List.map_nil, List.zipWith_cons_cons, List.zipWith_nil_left,
        List.mem_cons, List.not_mem_nil, or_false] at hcm
      rcases hcm with rfl | rfl | rfl <;>
        (simp only [List.length_cons, List.length_replicate]
         rw [hv0]
         first
           | omega
           | (rw [hpl, placementsOf_vars _ (by rw [hkl]; simp [memory1, memory2])]
              simp [columnKappas, memory1, memory2]
              omega))

end
end LeanVM.Guest.B1.VerifySub
