/-
  LeanVM.Guest.B1.Tables.VerifyTablesBusSpec

  The bus result `busRest` leaves, at the guest's values: its three totals the guest's
  `bus_table_total`, and each table's forms its blocks' forms weighted by their `eq_hi`.
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTablesBus
public import LeanVM.Guest.B1.Tables.VerifyTablesCopies
public import LeanVM.Guest.B1.Tables.VerifyTablesSegs
public import LeanVM.Guest.B1.Tables.VerifyTablesRun

/-!
# The bus result at the guest's values

`PushTotalEval`, `PullTotalEval` and `CountTotalEval` are the statements of the totals' values
(pieces (4) to (6) of `VT-SPEC-PIECES.md`), taken as hypotheses until they land. From them,
`vt_bus_spec`: `busVal`'s totals are the guest's three totals, and its forms, table by table and
side by side, the sums `ceEx`'s value (piece (2)) is written in.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd.Complete

@[expose] public section

/-! ## The pieces taken as hypotheses -/

/-- Piece (4): the push total's value. -/
def PushTotalEval : Prop :=
  ∀ {ρ χ : ℕ → E} {forms : List (List Form)}, FormsShaped forms →
    ∀ {blocks : List BusBlock} {sl : BusLayout} {fps w : List E} {beta tv : E} {point : List E},
    sl.framework.length = 3 → sl.tables.length = 34 → blocks.length = 34 →
    (∀ i < 37, ρ (selVal.getD i 0 + 23) =
      ((sl.framework ++ sl.tables).getD i default).eqAbove point) →
    (∀ j < 34, (blocks.getD j default).owner = pushOwners.getD j 0) →
    (∀ j < 34, (blocks.getD j default).coordinates = (pushCoordsC.getD j []).map FormC.toForm) →
    (∀ j < 34, ρ (1739 + 14 * pushOwners.getD j 0) =
      paddingWeight (point.take (blocks.getD j default).logRows) (blocks.getD j default).rows) →
    w.length = 16 → (∀ i < 16, w.getD i 0 = χ i) → ρ 12 = beta → ρ 21 = tv →
    fps = [χ 0 * 1 + χ 1 * 1 + χ 2 * 1,
      χ 0 * gen + χ 1 * ρ 1931 + χ 2 * 1 + χ 3 * ρ 1937 + χ 4 * ρ 1955 + χ 5 * ρ 1973,
      χ 0 * gen ^ 2 + χ 1 * ρ 2035 + χ 2 * 1 + ρ 1732] →
    pushTotalEx.eval ρ χ = (accumulateSide forms 0 blocks sl fps w beta point tv).2

/-- Piece (5): the pull total's value. -/
def PullTotalEval : Prop :=
  ∀ {ρ χ : ℕ → E} {forms : List (List Form)}, FormsShaped forms →
    ∀ {blocks : List BusBlock} {sl : BusLayout} {fps w : List E} {beta tv : E} {point : List E},
    sl.framework.length = 3 → sl.tables.length = 34 → blocks.length = 34 →
    (∀ i < 37, ρ (selVal.getD i 0 + 23) =
      ((sl.framework ++ sl.tables).getD i default).eqAbove point) →
    (∀ j < 34, (blocks.getD j default).owner = pushOwners.getD j 0) →
    (∀ j < 34, (blocks.getD j default).coordinates = (pullCoordsC.getD j []).map FormC.toForm) →
    (∀ j < 34, ρ (1739 + 14 * pushOwners.getD j 0) =
      paddingWeight (point.take (blocks.getD j default).logRows) (blocks.getD j default).rows) →
    w.length = 16 → (∀ i < 16, w.getD i 0 = χ i) → ρ 12 = beta → ρ 22 = tv →
    fps = [χ 0 * 1 + χ 1 * ofK (gpowK (2 ^ 18 - 1)) + χ 2 * 1,
      χ 0 * gen + χ 1 * ρ 1931 + χ 2 * ρ 3359 + χ 3 * ρ 1937 + χ 4 * ρ 1955 + χ 5 * ρ 1973,
      χ 0 * gen ^ 2 + χ 1 * ρ 2035 + χ 2 * ρ 3409 + ρ 1732] →
    pullTotalEx.eval ρ χ = (accumulateSide forms 1 blocks sl fps w beta point tv).2

/-- Piece (6): the count total's value. -/
def CountTotalEval : Prop :=
  ∀ {ρ χ : ℕ → E} {forms : List (List Form)}, FormsShaped forms →
    ∀ {blocks : List BusBlock} {sl : BusLayout} {point : List E} {tv : E},
    sl.framework = [] → sl.tables.length = 28 → blocks.length = 28 →
    (∀ j < 28, ρ (selVal.getD (37 + j) 0 + 23) = (sl.tables.getD j default).eqAbove point) →
    (∀ j < 28, (blocks.getD j default).owner = countOwners.getD j 0) →
    (∀ j < 28, (blocks.getD j default).coordinates = [Form.col (vtCountCols.flatten.getD j 0)]) →
    (∀ j < 28, ρ (1739 + 14 * countOwners.getD j 0) =
      paddingWeight (point.take (blocks.getD j default).logRows) (blocks.getD j default).rows) →
    ρ 23 = tv →
    countTotalEx.eval ρ χ = (accumulateSide forms 2 blocks sl [] [1] 0 point tv).2

/-! ## `busVal` side by side -/

theorem busVal_eq (layout : Layout) (alphas : List E) (beta : E) (point treeValues : List E)
    (memory : List E) (memoryFinal bytecodeFinal bytecodeValue : E) :
    busVal layout alphas beta point treeValues memory memoryFinal bytecodeFinal bytecodeValue =
      let fp := fingerprints (eqKernel alphas) memory (point.take layout.logMemory)
        (point.take layout.logBytecode) bytecodeValue
      let a1 := accumulateSide (tables.map fun _ ↦ [{}, {}, {}]) 0 layout.push
        (busLayout [0, layout.logMemory, layout.logBytecode] layout.push) (fp (Verifier.gpow 0) 1 1)
        (eqKernel alphas) beta point (treeValues.getD 0 0)
      let a2 := accumulateSide a1.1 1 layout.pull
        (busLayout [0, layout.logMemory, layout.logBytecode] layout.pull)
        (fp (Verifier.gpow (2 ^ layout.logBytecode - 1)) memoryFinal bytecodeFinal)
        (eqKernel alphas) beta point (treeValues.getD 1 0)
      let a3 := accumulateSide a2.1 2 layout.count (busLayout [] layout.count) [] [1] 0 point
        (treeValues.getD 2 0)
      ⟨(List.zipWith (fun column value ↦ ⟨column, point.take layout.logMemory, value⟩)
        [memory0, memory1, memory2] memory) ++
        [⟨memoryFinalCounters, point.take layout.logMemory, memoryFinal⟩,
          ⟨bytecodeFinalCounters, point.take layout.logBytecode, bytecodeFinal⟩],
        point, a3.1, [a1.2, a2.2, a3.2]⟩ := rfl

/-- A side's forms: each table's form on side `s` gains its blocks' forms, weighted. -/
theorem accSide_forms {side : ℕ} (hs : side < 3) (t s : ℕ) (column : ℕ → E)
    {forms : List (List Form)} (hsh : FormsShaped forms) {blocks : List BusBlock}
    (hown : ∀ b ∈ blocks, b.owner < 6) (sl : BusLayout) (fps w : List E) (beta : E)
    (point : List E) (tv : E) :
    (formAt (accumulateSide forms side blocks sl fps w beta point tv).1 t s).evaluate column =
      (formAt forms t s).evaluate column + sumE ((List.zip (sl.tables.map (·.eqAbove point))
        blocks).map fun p ↦ if p.2.owner = t ∧ side = s then
          p.1 * (blockForm p.2 w beta).evaluate column else 0) ∧
      FormsShaped (accumulateSide forms side blocks sl fps w beta point tv).1 := by
  rw [accumulateSide_eq]
  exact accStep_fold_forms hs t s column _ _ hsh fun p hp => hown _ (List.of_mem_zip hp).2

theorem forms0_shaped : FormsShaped (tables.map fun _ ↦ ([{}, {}, {}] : List Form)) :=
  ⟨by simp [tables_length'], fun t ht => by
    rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact ht), List.getElem_map]; rfl⟩

theorem formAt_forms0 (t s : ℕ) (column : ℕ → E) :
    (formAt (tables.map fun _ ↦ ([{}, {}, {}] : List Form)) t s).evaluate column = 0 := by
  unfold formAt
  rcases Nat.lt_or_ge t tables.length with ht | ht
  · rw [List.getD_eq_getElem (tables.map fun _ ↦ ([{}, {}, {}] : List Form)) default
      (by rw [List.length_map]; exact ht), List.getElem_map]
    match s with
    | 0 | 1 | 2 => rfl
    | s + 3 => rfl
  · rw [List.getD_eq_default (tables.map fun _ ↦ ([{}, {}, {}] : List Form)) default
      (by rw [List.length_map]; exact ht)]
    match s with
    | 0 | 1 | 2 => rfl
    | s + 3 => rfl

/-! ## The coordinates -/

theorem tables_flatMap_fin {α : Type} (g : Table → List α) :
    tables.flatMap g = (List.finRange 6).flatMap fun t : Fin 6 => g (tables.getD (t : ℕ) default) :=
  rfl

theorem push_coords : tables.flatMap (·.flushes.push) = pushCoordsC.map (·.map FormC.toForm) := by
  rw [tables_flatMap_fin, pushCoordsC, List.map_flatMap]
  exact congrArg (fun f => List.flatMap f (List.finRange 6)) (funext fun t => pySide_eq t .push)

theorem pull_coords : tables.flatMap (·.flushes.pull) = pullCoordsC.map (·.map FormC.toForm) := by
  rw [tables_flatMap_fin, pullCoordsC, List.map_flatMap]
  exact congrArg (fun f => List.flatMap f (List.finRange 6)) (funext fun t => pySide_eq t .pull)

/-! ## The totals -/

theorem busLayout_lengths (fw : List ℕ) (blocks : List BusBlock) :
    (busLayout fw blocks).framework.length = fw.length ∧
      (busLayout fw blocks).tables.length = blocks.length := by
  unfold busLayout
  simp [List.length_zipWith, stackOffsets_length]

theorem eqKernel_four {alphas : List E} {χ : ℕ → E} (hal : alphas.length = 4)
    (hχ : ∀ i < 16, (eqKernel alphas).getD i 0 = χ i) : eqKernel alphas = (List.range 16).map χ := by
  have hl : (eqKernel alphas).length = 16 := by rw [length_eqKernel, hal]; rfl
  apply List.ext_getElem (by simp [hl])
  intro i h1 h2
  rw [List.getElem_map, List.getElem_range, ← hχ i (by omega), List.getD_eq_getElem _ _ h1]

/-- The facts of a side's blocks, read off its mapped lists. -/
theorem blocks_getD {blocks : List BusBlock} {α : Type} (f : BusBlock → α) {l : List α} {d : α}
    (h : blocks.map f = l) {j : ℕ} (hj : j < blocks.length) : f (blocks.getD j default) = l.getD j d := by
  rw [← h, List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map]

/-- **The bus totals** at the guest's values: `busVal`'s three totals are the guest's. -/
theorem vt_bus_totals (hP4 : PushTotalEval) (hP5 : PullTotalEval) (hP6 : CountTotalEval)
    {bytecode : List K} (hb : bytecode.length = 2 ^ 22) {logMem : ℕ} {rows : List ℕ}
    (hr : rows.length = 6) {ρ χ : ℕ → E} {alphas point : List E} (hal : alphas.length = 4)
    (hχ : ∀ i < 16, (eqKernel alphas).getD i 0 = χ i)
    (hsel : ∀ i < 37, ρ (selVal.getD i 0 + 23) =
      (((busLayout [0, logMem, 18] (layoutOf bytecode logMem rows).push).framework ++
        (busLayout [0, logMem, 18] (layoutOf bytecode logMem rows).push).tables).getD i
          default).eqAbove point)
    (hselc : ∀ j < 28, ρ (selVal.getD (37 + j) 0 + 23) =
      ((busLayout [] (layoutOf bytecode logMem rows).count).tables.getD j default).eqAbove point)
    (hpw : ∀ t < 6, ρ (1739 + 14 * t) =
      paddingWeight (point.take (log2Ceil (rows.getD t 0))) (rows.getD t 0))
    (hidx1 : ρ 1931 = indexMle (point.take logMem)) (hidx2 : ρ 2035 = indexMle (point.take 18)) :
    (busVal (layoutOf bytecode logMem rows) alphas (ρ 12) point [ρ 21, ρ 22, ρ 23]
      [ρ 1937, ρ 1955, ρ 1973] (ρ 3359) (ρ 3409) (ρ 1732)).totals =
      [pushTotalEx.eval ρ χ, pullTotalEx.eval ρ χ, countTotalEx.eval ρ χ] := by
  obtain ⟨hlb, -, hpo, hco, hpl, hpr, hcl, hcr, hpc, hlc, hcc, hpp⟩ :=
    layoutOf_blocks bytecode hb logMem rows hr
  set L := layoutOf bytecode logMem rows with hLd
  have hlm : L.logMemory = logMem := rfl
  have hwk := eqKernel_four hal hχ
  have hlpo : layoutPushOwners.length = 34 := rfl
  have hlco : layoutCountOwners.length = 28 := rfl
  have hpcl : pushCoordsC.length = 34 := by decide +kernel
  have hlcl : pullCoordsC.length = 34 := by decide +kernel
  have hpl34 : L.push.length = 34 := by
    have := congrArg List.length hpo; simp only [List.length_map] at this; rw [this, hlpo]
  have hll34 : L.pull.length = 34 := by
    have := congrArg List.length hpp; simp only [List.length_map] at this; rw [this, hpl34]
  have hcl28 : L.count.length = 28 := by
    have := congrArg List.length hco; simp only [List.length_map] at this; rw [this, hlco]
  have hlo : L.pull.map (·.owner) = layoutPushOwners := by
    have := congrArg (List.map fun x : ℕ × ℕ × ℕ => x.1) hpp
    simp only [List.map_map] at this; rw [← hpo]; exact this
  have hllr : L.pull.map (·.logRows) = layoutPushOwners.map (fun t => log2Ceil (rows.getD t 0)) := by
    have := congrArg (List.map fun x : ℕ × ℕ × ℕ => x.2.1) hpp
    simp only [List.map_map] at this; rw [← hpl]; exact this
  have hlrr : L.pull.map (·.rows) = layoutPushOwners.map (fun t => rows.getD t 0) := by
    have := congrArg (List.map fun x : ℕ × ℕ × ℕ => x.2.2) hpp
    simp only [List.map_map] at this; rw [← hpr]; exact this
  have hpull := busLayout_pull_push bytecode hb logMem rows hr
  have own6 : ∀ j < 34, layoutPushOwners.getD j 0 < 6 := by decide +kernel
  have cown6 : ∀ j < 28, layoutCountOwners.getD j 0 < 6 := by decide +kernel
  have hpwp : ∀ (O : List ℕ) (n : ℕ), O.length = n → (∀ j < n, O.getD j 0 < 6) →
      ∀ (blocks : List BusBlock), blocks.length = n →
      blocks.map (·.logRows) = O.map (fun t => log2Ceil (rows.getD t 0)) →
      blocks.map (·.rows) = O.map (fun t => rows.getD t 0) →
      ∀ j < n, ρ (1739 + 14 * O.getD j 0) =
        paddingWeight (point.take (blocks.getD j default).logRows) (blocks.getD j default).rows := by
    intro O n hO hO6 blocks hl hlr hrr j hj
    have e : ∀ f : ℕ → ℕ, (O.map f).getD j 0 = f (O.getD j 0) :=
      fun f => by
        rw [List.getD_eq_getElem _ _ (by rw [List.length_map, hO]; omega), List.getElem_map,
          List.getD_eq_getElem _ _ (by rw [hO]; omega)]
    rw [blocks_getD (·.logRows) hlr (by omega) (d := 0), blocks_getD (·.rows) hrr (by omega) (d := 0),
      e, e]
    exact hpw _ (hO6 j hj)
  have fsh1 := (accSide_forms (side := 0) (by omega) 0 0 (fun _ => 0) forms0_shaped (blocks := L.push)
    (fun b hb => by
      have := List.mem_map_of_mem (f := (·.owner)) hb; rw [hpo] at this
      exact vt_owners_lt.1 _ this) (busLayout [0, L.logMemory, L.logBytecode] L.push)
    (fingerprints (eqKernel alphas) [ρ 1937, ρ 1955, ρ 1973] (point.take L.logMemory)
      (point.take L.logBytecode) (ρ 1732) (Verifier.gpow 0) 1 1) (eqKernel alphas) (ρ 12) point
    (ρ 21)).2
  have fsh2 := (accSide_forms (side := 1) (by omega) 0 0 (fun _ => 0) fsh1 (blocks := L.pull)
    (fun b hb => by
      have := List.mem_map_of_mem (f := (·.owner)) hb; rw [hlo] at this
      exact vt_owners_lt.1 _ this) (busLayout [0, L.logMemory, L.logBytecode] L.pull)
    (fingerprints (eqKernel alphas) [ρ 1937, ρ 1955, ρ 1973] (point.take L.logMemory)
      (point.take L.logBytecode) (ρ 1732) (Verifier.gpow (2 ^ L.logBytecode - 1)) (ρ 3359)
      (ρ 3409)) (eqKernel alphas) (ρ 12) point (ρ 22)).2
  rw [busVal_eq]
  simp only [List.getD_cons_zero, List.getD_cons_succ]
  rw [hlb, hlm] at fsh1 fsh2 ⊢
  obtain ⟨hfw, htl⟩ := busLayout_lengths [0, logMem, 18] L.push
  obtain ⟨-, hctl⟩ := busLayout_lengths [] L.count
  refine congrArg₂ List.cons ?_ (congrArg₂ List.cons ?_ (congrArg₂ List.cons ?_ rfl))
  · refine (hP4 forms0_shaped hfw (by rw [htl, hpl34]) hpl34 hsel
      (fun j hj => blocks_getD (·.owner) hpo (by omega))
      (fun j hj => by rw [blocks_getD (·.coordinates) hpc (by omega) (d := []), push_coords,
        List.getD_eq_getElem _ _ (by rw [List.length_map, hpcl]; omega),
        List.getD_eq_getElem _ _ (by rw [hpcl]; omega), List.getElem_map])
      (hpwp _ _ hlpo own6 _ hpl34 hpl hpr) (by rw [length_eqKernel, hal]; rfl) hχ rfl rfl ?_).symm
    have t3 : ((List.range 16).map χ).take 3 = [χ 0, χ 1, χ 2] := rfl
    have t6 : ((List.range 16).map χ).take 6 = [χ 0, χ 1, χ 2, χ 3, χ 4, χ 5] := rfl
    rw [hwk]
    simp only [fingerprints, dot, sepState, sepMem, sepBytecode, Verifier.gpow, hidx1, hidx2, t3, t6,
      List.zipWith_cons_cons, List.zipWith_nil_left, List.foldl_cons, List.foldl_nil,
      List.cons_append, List.nil_append, List.cons.injEq, pow_zero, and_true]
    refine ⟨by ring, by ring, by ring⟩
  · refine (hP5 fsh1 (by rw [hpull]; exact hfw) (by rw [hpull, htl, hpl34]) hll34
      (by rw [hpull]; exact hsel) (fun j hj => blocks_getD (·.owner) hlo (by omega))
      (fun j hj => by rw [blocks_getD (·.coordinates) hlc (by omega) (d := []), pull_coords,
        List.getD_eq_getElem _ _ (by rw [List.length_map, hlcl]; omega),
        List.getD_eq_getElem _ _ (by rw [hlcl]; omega), List.getElem_map])
      (hpwp _ _ hlpo own6 _ hll34 hllr hlrr) (by rw [length_eqKernel, hal]; rfl) hχ rfl rfl ?_).symm
    have t3 : ((List.range 16).map χ).take 3 = [χ 0, χ 1, χ 2] := rfl
    have t6 : ((List.range 16).map χ).take 6 = [χ 0, χ 1, χ 2, χ 3, χ 4, χ 5] := rfl
    have hfin : Verifier.gpow (2 ^ 18 - 1) = ofK (gpowK (2 ^ 18 - 1)) := by
      rw [Verifier.gpow, gen_pow_eq_ofK, gpowK_eq (by decide)]
    rw [hwk, hfin]
    simp only [fingerprints, dot, sepState, sepMem, sepBytecode, Verifier.gpow, hidx1, hidx2, t3, t6,
      List.zipWith_cons_cons, List.zipWith_nil_left, List.foldl_cons, List.foldl_nil,
      List.cons_append, List.nil_append, List.cons.injEq, pow_zero, and_true]
    refine ⟨by ring, by ring, by ring⟩
  · have hcc' : tables.flatMap (fun t => t.countColumns.map fun l => [Form.col l]) =
        vtCountCols.flatten.map fun l => [Form.col l] := by
      have h1 : tables.map (·.countColumns) = vtCountCols := by
        have := congrArg (List.map Prod.fst) tables_counts
        rw [List.map_map] at this
        exact this
      rw [List.flatMap_def, List.map_flatten, ← h1, List.map_map]
      rfl
    have hvl : vtCountCols.flatten.length = 28 := by decide +kernel
    refine (hP6 fsh2 (by simp [busLayout]) (by rw [hctl, hcl28]) hcl28 hselc
      (fun j hj => blocks_getD (·.owner) hco (by omega))
      (fun j hj => by rw [blocks_getD (·.coordinates) hcc (by omega) (d := []), hcc',
        List.getD_eq_getElem _ _ (by rw [List.length_map, hvl]; omega), List.getElem_map,
        List.getD_eq_getElem _ _ (by rw [hvl]; omega)])
      (hpwp _ _ hlco cown6 _ hcl28 hcl hcr) rfl).symm

/-! ## The forms -/

theorem push_runs : ∀ t < 6, ∀ j < 34, (layoutPushOwners.getD j 0 = t ↔ pushStart.getD t 0 ≤ j ∧
    j < pushStart.getD t 0 + ((tables.getD t default).flushes.push).length) := by decide +kernel
theorem pull_runs : ∀ t < 6, ∀ j < 34, (layoutPushOwners.getD j 0 = t ↔ pushStart.getD t 0 ≤ j ∧
    j < pushStart.getD t 0 + ((tables.getD t default).flushes.pull).length) := by decide +kernel
theorem push_starts : ∀ t < 6, pushStart.getD t 0 =
    ((tables.take t).map fun x => x.flushes.push.length).sum ∧
    pushStart.getD t 0 + ((tables.getD t default).flushes.push).length ≤ 34 ∧
    ((vtEqhiVars.getD t []).getD 0 []).length = ((tables.getD t default).flushes.push).length := by
  decide +kernel
theorem pull_starts : ∀ t < 6, pushStart.getD t 0 =
    ((tables.take t).map fun x => x.flushes.pull.length).sum ∧
    pushStart.getD t 0 + ((tables.getD t default).flushes.pull).length ≤ 34 ∧
    ((vtEqhiVars.getD t []).getD 1 []).length = ((tables.getD t default).flushes.pull).length := by
  decide +kernel
theorem count_runs : ∀ t < 6, ∀ j < 28, (layoutCountOwners.getD j 0 = t ↔ countStart.getD t 0 ≤ j ∧
    j < countStart.getD t 0 + (vtCountCols.getD t []).length) := by decide +kernel
theorem count_starts : ∀ t < 6, countStart.getD t 0 =
    ((vtCountCols.take t).map List.length).sum ∧
    countStart.getD t 0 + (vtCountCols.getD t []).length ≤ 28 ∧
    ((vtEqhiVars.getD t []).getD 2 []).length = (vtCountCols.getD t []).length := by
  decide +kernel

theorem tables_countColumns : tables.map (·.countColumns) = vtCountCols := by
  have := congrArg (List.map Prod.fst) tables_counts
  rw [List.map_map] at this
  exact this

theorem countColumns_getD {t : ℕ} (ht : t < 6) :
    (tables.getD t default).countColumns = vtCountCols.getD t [] := by
  rw [← tables_countColumns, List.getD_eq_getElem _ _ (by simpa [tables_length'] using ht),
    List.getD_eq_getElem _ _ (by simpa [tables_length'] using ht), List.getElem_map]

theorem evaluate_col (l : ℕ) (column : ℕ → E) : (Form.col l).evaluate column = column l := by
  simp [Form.col, evaluate_eq, termVal, vt_sumE_cons, vt_sumE_nil, Verifier.gpow]

theorem sumE_ite_false {α : Type} (l : List α) (P : α → Prop) [DecidablePred P] (f : α → E) :
    sumE (l.map fun p => if P p ∧ False then f p else 0) = 0 := by
  simp only [and_false, ↓reduceIte]
  exact vt_sumE_zero l

/-- The selectors of a side's table blocks, from those of the whole side. -/
theorem sels_getD {fw : List Placement} {tb : List Placement} {point : List E} {ρ : ℕ → E} {m n : ℕ}
    (hfw : fw.length = m) (htb : tb.length = n)
    (hsel : ∀ i < m + n, ρ (selVal.getD i 0 + 23) = ((fw ++ tb).getD i default).eqAbove point)
    {j : ℕ} (hj : j < n) :
    ρ (selVal.getD (m + j) 0 + 23) = (tb.map (·.eqAbove point)).getD j 0 := by
  rw [hsel _ (by omega), List.getD_eq_getElem _ _ (by simp [hfw, htb]; omega),
    List.getElem_append_right (by omega), List.getD_eq_getElem _ _ (by simp [htb]; omega),
    List.getElem_map]
  congr 2
  omega

/-- **The bus forms** at the guest's values: table `t`'s form on each side is its blocks' forms
(its count columns, on the count side) weighted by its `eq_hi`. -/
theorem vt_bus_forms {bytecode : List K} (hb : bytecode.length = 2 ^ 22) {logMem : ℕ}
    {rows : List ℕ} (hr : rows.length = 6) {ρ χ : ℕ → E} {alphas point : List E}
    (hal : alphas.length = 4) (hχ : ∀ i < 16, (eqKernel alphas).getD i 0 = χ i)
    (hsel : ∀ i < 37, ρ (selVal.getD i 0 + 23) =
      (((busLayout [0, logMem, 18] (layoutOf bytecode logMem rows).push).framework ++
        (busLayout [0, logMem, 18] (layoutOf bytecode logMem rows).push).tables).getD i
          default).eqAbove point)
    (hselc : ∀ j < 28, ρ (selVal.getD (37 + j) 0 + 23) =
      ((busLayout [] (layoutOf bytecode logMem rows).count).tables.getD j default).eqAbove point)
    (heqhi : ∀ t < 6, ∀ s < 3, ∀ k < ((vtEqhiVars.getD t []).getD s []).length,
      ρ (((vtEqhiVars.getD t []).getD s []).getD k 0) = ρ (selVal.getD (eqhiSel t s k) 0 + 23))
    (treeValues memory : List E) (mF bF bv : E) {t : ℕ} (ht : t < 6) (ev : ℕ → E) :
    let bus := busVal (layoutOf bytecode logMem rows) alphas (ρ 12) point treeValues memory mF bF bv
    (formAt bus.forms t 0).evaluate ev =
        sumE ((List.zip ((vtEqhiVars.getD t []).getD 0 []) (tables.getD t default).flushes.push).map
          fun p => ρ p.1 * (blockForm ⟨0, 0, p.2, t⟩ ((List.range 16).map χ) (ρ 12)).evaluate ev) ∧
      (formAt bus.forms t 1).evaluate ev =
        sumE ((List.zip ((vtEqhiVars.getD t []).getD 1 []) (tables.getD t default).flushes.pull).map
          fun p => ρ p.1 * (blockForm ⟨0, 0, p.2, t⟩ ((List.range 16).map χ) (ρ 12)).evaluate ev) ∧
      (formAt bus.forms t 2).evaluate ev =
        sumE ((List.zip ((vtEqhiVars.getD t []).getD 2 []) (vtCountCols.getD t [])).map
          fun p => ρ p.1 * ev p.2) ∧
      FormsShaped bus.forms := by
  obtain ⟨hlb, -, hpo, hco, -, -, -, -, hpc, hlc, hcc, hpp⟩ :=
    layoutOf_blocks bytecode hb logMem rows hr
  set L := layoutOf bytecode logMem rows with hLd
  have hlm : L.logMemory = logMem := rfl
  have hwk := eqKernel_four hal hχ
  have hlpo : layoutPushOwners.length = 34 := rfl
  have hlco : layoutCountOwners.length = 28 := rfl
  have hpl34 : L.push.length = 34 := by
    have := congrArg List.length hpo; simp only [List.length_map] at this; rw [this, hlpo]
  have hll34 : L.pull.length = 34 := by
    have := congrArg List.length hpp; simp only [List.length_map] at this; rw [this, hpl34]
  have hcl28 : L.count.length = 28 := by
    have := congrArg List.length hco; simp only [List.length_map] at this; rw [this, hlco]
  have hlo : L.pull.map (·.owner) = layoutPushOwners := by
    have := congrArg (List.map fun x : ℕ × ℕ × ℕ => x.1) hpp
    simp only [List.map_map] at this; rw [← hpo]; exact this
  have hpull := busLayout_pull_push bytecode hb logMem rows hr
  have po6 : ∀ b ∈ L.push, b.owner < 6 := fun b hb => by
    have := List.mem_map_of_mem (f := (·.owner)) hb; rw [hpo] at this
    exact vt_owners_lt.1 _ this
  have lo6 : ∀ b ∈ L.pull, b.owner < 6 := fun b hb => by
    have := List.mem_map_of_mem (f := (·.owner)) hb; rw [hlo] at this
    exact vt_owners_lt.1 _ this
  have co6 : ∀ b ∈ L.count, b.owner < 6 := fun b hb => by
    have := List.mem_map_of_mem (f := (·.owner)) hb; rw [hco] at this
    exact vt_owners_lt.2 _ this
  obtain ⟨hfw, htl⟩ := busLayout_lengths [0, logMem, 18] L.push
  obtain ⟨-, hctl⟩ := busLayout_lengths [] L.count
  rw [hpl34] at htl
  rw [hcl28] at hctl
  simp only [busVal_eq, hlb, hlm]
  set fp1 := fingerprints (eqKernel alphas) memory (point.take logMem) (point.take 18) bv
    (Verifier.gpow 0) 1 1
  set fp2 := fingerprints (eqKernel alphas) memory (point.take logMem) (point.take 18) bv
    (Verifier.gpow (2 ^ 18 - 1)) mF bF
  set A1 := accumulateSide (tables.map fun _ ↦ [{}, {}, {}]) 0 L.push
    (busLayout [0, logMem, 18] L.push) fp1 (eqKernel alphas) (ρ 12) point (treeValues.getD 0 0)
  set A2 := accumulateSide A1.1 1 L.pull (busLayout [0, logMem, 18] L.pull) fp2 (eqKernel alphas)
    (ρ 12) point (treeValues.getD 1 0)
  set A3 := accumulateSide A2.1 2 L.count (busLayout [] L.count) [] [1] 0 point
    (treeValues.getD 2 0)
  have F1 := fun s => accSide_forms (side := 0) (by omega) t s ev forms0_shaped po6
    (busLayout [0, logMem, 18] L.push) fp1 (eqKernel alphas) (ρ 12) point (treeValues.getD 0 0)
  have sh1 := (F1 0).2
  have F2 := fun s => accSide_forms (side := 1) (by omega) t s ev sh1 lo6
    (busLayout [0, logMem, 18] L.pull) fp2 (eqKernel alphas) (ρ 12) point (treeValues.getD 1 0)
  have sh2 := (F2 0).2
  have F3 := fun s => accSide_forms (side := 2) (by omega) t s ev sh2 co6
    (busLayout [] L.count) [] [1] 0 point (treeValues.getD 2 0)
  have hsp : ∀ k < 34, ρ (selVal.getD (3 + k) 0 + 23) =
      ((busLayout [0, logMem, 18] L.push).tables.map (·.eqAbove point)).getD k 0 :=
    fun k hk => sels_getD hfw htl hsel hk
  have hsc : ∀ k < 28, ρ (selVal.getD (37 + k) 0 + 23) =
      ((busLayout [] L.count).tables.map (·.eqAbove point)).getD k 0 := fun k hk => by
    rw [hselc k hk, List.getD_eq_getElem _ _ (by simp [hctl]; omega),
      List.getD_eq_getElem _ _ (by simp [hctl]; omega), List.getElem_map]
  have hselLen : ((busLayout [0, logMem, 18] L.push).tables.map (·.eqAbove point)).length = 34 := by
    simp [htl]
  have hcLen : ((busLayout [] L.count).tables.map (·.eqAbove point)).length = 28 := by
    simp [hctl]
  refine ⟨?_, ?_, ?_, (F3 0).2⟩
  · rw [(F3 0).1, (F2 0).1, (F1 0).1, formAt_forms0]
    simp only [show ¬ ((1 : ℕ) = 0) from by decide, show ¬ ((2 : ℕ) = 0) from by decide, and_false,
      and_true, ↓reduceIte, vt_sumE_zero, add_zero, zero_add, hwk]
    obtain ⟨hst, hn, hel⟩ := push_starts t ht
    refine Eq.trans ?_ (vt_side_sum layoutPushOwners pushStart (·.flushes.push) push_runs
      (fun t ht => (push_starts t ht).1) (fun t ht => (push_starts t ht).2.1) hpl34 hselLen hpo hpc
      (fun cs => (blockForm ⟨0, 0, cs, t⟩ ((List.range 16).map χ) (ρ 12)).evaluate ev) ρ ht hel
      fun k hk => ?_)
    · rfl
    rw [heqhi t ht 0 (by omega) k hk, eqhiSel, ite_neg' (by omega), Nat.add_assoc, hsp _ (by omega)]
  · rw [(F3 1).1, (F2 1).1, (F1 1).1, formAt_forms0]
    simp only [show ¬ ((0 : ℕ) = 1) from by decide, show ¬ ((2 : ℕ) = 1) from by decide, and_false,
      and_true, ↓reduceIte, vt_sumE_zero, add_zero, zero_add, hwk]
    rw [hpull]
    obtain ⟨hst, hn, hel⟩ := pull_starts t ht
    refine Eq.trans ?_ (vt_side_sum layoutPushOwners pushStart (·.flushes.pull) pull_runs
      (fun t ht => (pull_starts t ht).1) (fun t ht => (pull_starts t ht).2.1) hll34 hselLen hlo hlc
      (fun cs => (blockForm ⟨0, 0, cs, t⟩ ((List.range 16).map χ) (ρ 12)).evaluate ev) ρ ht hel
      fun k hk => ?_)
    · rfl
    rw [heqhi t ht 1 (by omega) k hk, eqhiSel, ite_neg' (by omega), Nat.add_assoc, hsp _ (by omega)]
  · rw [(F3 2).1, (F2 2).1, (F1 2).1, formAt_forms0]
    simp only [show ¬ ((0 : ℕ) = 2) from by decide, show ¬ ((1 : ℕ) = 2) from by decide, and_false,
      and_true, ↓reduceIte, vt_sumE_zero, add_zero, zero_add]
    obtain ⟨hst, hn, hel⟩ := count_starts t ht
    have hfl : ∀ t < 6, ((tables.getD t default).countColumns.map fun l => [Form.col l]).length =
        (vtCountCols.getD t []).length := fun t ht => by rw [List.length_map, countColumns_getD ht]
    have hcst : ∀ t < 6, countStart.getD t 0 =
        ((tables.take t).map fun x => (x.countColumns.map fun l => [Form.col l]).length).sum :=
      fun t ht => by
        rw [(count_starts t ht).1, ← tables_countColumns, ← List.map_take, List.map_map]
        exact congrArg List.sum (List.map_congr_left fun x _ => (List.length_map _).symm)
    refine Eq.trans (vt_side_sum layoutCountOwners countStart
      (fun x => x.countColumns.map fun l => [Form.col l])
      (fun t ht j hj => by rw [hfl t ht]; exact count_runs t ht j hj) hcst
      (fun t ht => by rw [hfl t ht]; exact (count_starts t ht).2.1) hcl28 hcLen hco hcc
      (fun cs => (blockForm ⟨0, 0, cs, t⟩ [1] 0).evaluate ev) ρ ht
      (eqh := (vtEqhiVars.getD t []).getD 2 []) (by rw [hfl t ht]; exact hel)
      fun k hk => ?_) ?_
    · rw [heqhi t ht 2 (by omega) k hk, eqhiSel, ite_pos' rfl, Nat.add_assoc, hsc _ (by omega)]
    · rw [countColumns_getD ht, List.zip_map_right, List.map_map]
      refine congrArg sumE (List.map_congr_left fun p hp => ?_)
      simp only [Function.comp_apply, Prod.map, id, evaluate_blockForm, List.zipIdx_cons,
        List.zipIdx_nil, List.map_cons, List.map_nil, vt_sumE_cons, vt_sumE_nil, List.getD_cons_zero,
        evaluate_col, one_mul, add_zero, zero_add]

end
end LeanVM.Guest.B1.VerifySub
