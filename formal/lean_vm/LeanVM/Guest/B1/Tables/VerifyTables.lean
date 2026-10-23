/-
  LeanVM.Guest.B1.Tables.VerifyTables

  `verify_tables` is sound (`SoundTables`), from the specification pieces (2), (4), (5), (6) of
  `VT-SPEC-PIECES.md` taken as hypotheses until they land.
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTablesFinal
public import LeanVM.Guest.B1.Tables.VerifyTablesVals
public import LeanVM.Guest.B1.Tables.VerifyTablesTail
public import LeanVM.Guest.B1.Tables.VerifyTablesFront
public import LeanVM.Guest.B1.Tables.VerifyTablesPad
public import LeanVM.Guest.B1.Tables.VerifyTablesSort
public import LeanVM.Guest.B1.Tables.Terminal
public import LeanVM.Guest.B1.Tables.Gkr

/-!
# `verify_tables` is sound

The guest's facts (the heights and row counts, the block selectors, the bus totals, the table
sumcheck, the evaluations, `air_acc`, the public input) give the specification's run of
`tablesSeg` (`runsTo_tablesSeg`), the claims in the pool and `TCtx`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem sum_two_pow_le : ∀ (l : List ℕ), (∀ x ∈ l, x ≤ 33) → (l.map (2 ^ ·)).sum ≤ l.length * 2 ^ 33
  | [], _ => by simp
  | x :: l, h => by
    have ih := sum_two_pow_le l fun y hy => h y (List.mem_cons_of_mem _ hy)
    have : 2 ^ x ≤ 2 ^ 33 := Nat.pow_le_pow_right (by decide) (h x (List.mem_cons_self ..))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith

theorem stackOffsets_lt {l : List ℕ} (hl : l.length ≤ 37) (hx : ∀ x ∈ l, x ≤ 33) {i : ℕ}
    (hi : i < l.length) : (stackOffsets l).1.getD i 0 < 2 ^ 62 := by
  have h1 := stackOffsets_bound l hi
  have h2 := sum_two_pow_le l hx
  have h3 : l.length * 2 ^ 33 ≤ 37 * 2 ^ 33 := Nat.mul_le_mul_right _ hl
  have : 0 < 2 ^ l.getD i 0 := Nat.two_pow_pos _
  have : (37 : ℕ) * 2 ^ 33 < 2 ^ 62 := by norm_num
  omega

theorem busLayout_all_getD (fw : List ℕ) (blocks : List BusBlock) {i : ℕ}
    (hi : i < fw.length + blocks.length) :
    ((busLayout fw blocks).framework ++ (busLayout fw blocks).tables).getD i default =
      { vars := (fw ++ blocks.map (·.logRows)).getD i 0,
        index := (stackOffsets (fw ++ blocks.map (·.logRows))).1.getD i 0 } := by
  have hl := stackOffsets_length (fw ++ blocks.map (·.logRows))
  simp only [busLayout]
  rcases hso : stackOffsets (fw ++ blocks.map (·.logRows)) with ⟨o, d⟩
  rw [hso] at hl
  simp only [List.length_append, List.length_map] at hl
  simp only [List.take_append_drop]
  rw [List.getD_eq_getElem _ _ (by rw [List.length_zipWith, hl]; simp; omega), List.getElem_zipWith,
    List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by rw [hl]; omega)]

theorem busLayout_tables_getD (blocks : List BusBlock) {j : ℕ} (hj : j < blocks.length) :
    (busLayout [] blocks).tables.getD j default =
      { vars := (blocks.map (·.logRows)).getD j 0,
        index := (stackOffsets (blocks.map (·.logRows))).1.getD j 0 } := by
  have h := busLayout_all_getD [] blocks (i := j) (by simpa using hj)
  have hfw : (busLayout [] blocks).framework = [] := by simp [busLayout]
  rw [hfw, List.nil_append] at h
  simpa using h


theorem vt_evss_flatten (σ : Val) :
    (vtEvalVars.map (·.map fun k => σ (.n k))).flatten = evWords σ := by
  rw [← List.map_flatten, vt_evalVars_flatten, evWords]
  have hl : evVal.length = 104 := rfl
  apply List.ext_getElem (by simp [hl])
  intro j h1 h2
  rw [List.getElem_map, List.getElem_map, List.getElem_range,
    List.getD_eq_getElem evVal 0 (by rw [hl]; simpa using h2)]


theorem take_eq_take_length (l : List E) (m : ℕ) : l.take m = l.take (l.take m).length := by
  rw [List.length_take]
  rcases le_total m l.length with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, List.take_of_length_le h, List.take_length]

theorem vt_evTau_tables : ∀ j < 104, evTau.getD j 0 = airTau.getD (vtTableOf.getD j 0) 0 ∧
    vtTableOf.getD j 0 < 6 := by decide +kernel

theorem vt_tableOf_length : vtTableOf.length = 104 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- **`verify_tables` is sound**, from the pieces (2), (4), (5) and (6). -/
theorem verify_tables_sound_of (hP2 : CeExEval) (hP4 : PushTotalEval) (hP5 : PullTotalEval)
    (hP6 : CountTotalEval) {κ : ℕ} (hκ : κ ≤ 32) (Lm : MemImage κ) {bytecode : List K}
    (hb : bytecode.length = 2 ^ 22) : SoundTables bytecode TCtx Lm.read := by
  intro lp pi logMem alphas point values args rets hpre hrel
  obtain ⟨σ, hargs, hv, hrets⟩ := verify_tables_holds hrel
  subst hargs hrets
  obtain ⟨hpi, hz, hmu, hml, hlm16, hlm32, ⟨ds, hdsl, hdims, hbk⟩, hexp, hal, hfpw, hvals⟩ := hpre
  -- the tables' heights and row counts
  have hp := vt_pads hκ Lm hv hz
  have hp' : ∀ t, ∃ τ nrow : ℕ, t < 6 → τ < 29 ∧ nrow ≤ 2 ^ τ ∧ log2Ceil nrow = τ ∧
      σ (.n (1733 + 14 * t)) = gen ^ τ ∧ LoadHolds Lm.read (σ (.n 7)) (t + 1) (gen ^ τ) ∧
      LoadHolds Lm.read (σ (.n 8)) t (eOfNat nrow) ∧
      (τ ≤ point.length → σ (.n (1739 + 14 * t)) = paddingWeight (point.take τ) nrow) := fun t =>
    if ht : t < 6 then by obtain ⟨a, b, h⟩ := hp t ht; exact ⟨a, b, fun _ => h⟩
    else ⟨0, 0, fun h => absurd h ht⟩
  choose τ nr hP using hp'
  have hτ29 : ∀ t < 6, τ t < 29 := fun t ht => (hP t ht).1
  have hdim : ∀ t < 6, LoadHolds Lm.read (σ (.n 7)) (t + 1) (gen ^ τ t) :=
    fun t ht => (hP t ht).2.2.2.2.1
  have hds : ds = (List.range 6).map fun t => gen ^ τ t := by
    apply List.ext_getElem (by simp [hdsl])
    intro t h1 h2
    have := hdims (t + 1) (by simp; omega)
    simp only [List.getElem_cons_succ] at this
    rw [List.getElem_map, List.getElem_range]
    exact loadHolds_unique this (hdim t (by simpa using h2))
  rw [hds] at hbk hdims
  have hks := vt_kappas hbk
  have hks34 := vtKs_lt hlm32 hτ29
  have hsq : ∀ j < 34, LoadHolds Lm.read (σ (.n 10)) j (gen ^ 2 ^ j) := fun j hj => (hexp j hj).2
  obtain ⟨hoffP, hoffC⟩ := vt_offsets hκ Lm hv (vtKs logMem τ) hks34 hks hsq
  have hselBlk : (∀ i < 37, selBlk.getD i 0 = i) ∧ ∀ j < 28, selBlk.getD (37 + j) 0 = 74 + j := by
    decide +kernel
  have selP := fun i (hi : i < 37) => vt_sel hκ Lm hv (i := i) (by omega) (hks34 i (by omega))
    (by rw [hselBlk.1 i hi]; exact hks i (by omega)) (by rw [hselBlk.1 i hi]; exact hoffP i hi)
    (stackOffsets_lt (by simp) (fun x hx => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
      have := hks34 b (by simp at hb; omega); omega) (by simpa using hi)) hz hmu hml hsq
  have selC := fun j (hj : j < 28) => vt_sel hκ Lm hv (i := 37 + j) (by omega)
    (hks34 (74 + j) (by omega))
    (by rw [hselBlk.2 j hj]; exact hks (74 + j) (by omega)) (by rw [hselBlk.2 j hj]; exact hoffC j hj)
    (stackOffsets_lt (by simp) (fun x hx => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
      have := hks34 (74 + b) (by simp at hb; omega); omega) (by simpa using hj)) hz hmu hml hsq
  -- the state at entry, the framework claims, the table sumcheck, the evaluations
  obtain ⟨cv, hcv⟩ : ∃ cv, (σ (.n 0), σ (.n 1)) = digestScalars cv := by
    have c19 := hv.atom 0 (.copy (.n 19) (.n 0)) (by decide +kernel)
    have c20 := hv.atom 1 (.copy (.n 20) (.n 1)) (by decide +kernel)
    obtain ⟨-, cv, h, -⟩ := hv.fsNext 1664 (.n 19) (.n 20) (.n 2) 0 1937 (by decide +kernel)
    simp only [Atom.Holds] at c19 c20
    exact ⟨cv, by rw [← c19, ← c20]; exact h⟩
  obtain ⟨hfr, hcvB, hfp, hfl⟩ := vt_fresh hv hcv
  obtain ⟨n, ws, rs, cl, cvS, hn, hnp, hgn, hx0, hx1, hx2, hx3, hx4, hx5, hwsl, hws, hrsl, hsc,
    hchi, hcp, hpq, hcvS, hcur, hcl⟩ := vt_zc hκ Lm hv τ hτ29 hdim hz hmu hml hcvB
  obtain ⟨hev, hcvR, hevp⟩ := vt_evals hv hcvS
  obtain ⟨hpi1, hpi2, hpi3, hc3, hc4, hpool109, hpool110, hpool111, hr1, hr2, hr3, hr4, hr5,
    hr6⟩ := vt_pi hv hcvR
  obtain ⟨c21, c22, c23⟩ := vt_tree_copies hv
  set xi := challengeOf (sqCv (obsAll cv (freshWords σ))) with hxid
  have hτn : ∀ t < 6, τ t ≤ n := fun t ht => by
    rw [hn]; exact vt_le_foldl_max _ 0 _ (Or.inl (List.mem_map.mpr ⟨t, List.mem_range.mpr ht, rfl⟩))
  -- the framework blocks
  have hk1 : vtKs logMem τ 1 = logMem := by simp [vtKs, blockKappaSrc, blockKappaAdj]
  have hk2 : vtKs logMem τ 2 = 18 := by simp [vtKs, blockKappaSrc, blockKappaAdj]
  have hlmp : logMem ≤ point.length := by have := (selP 1 (by omega)).1; rw [hk1] at this; exact this
  have h18p : 18 ≤ point.length := by have := (selP 2 (by omega)).1; rw [hk2] at this; exact this
  have l1893 := hv.atom 1616 (.load (.n 1893) (.n 9) 1) (by decide +kernel)
  have l1997 := hv.atom 1724 (.load (.n 1997) (.n 9) 2) (by decide +kernel)
  simp only [Atom.Holds] at l1893 l1997
  have g1893 : σ (.n 1893) = gen ^ logMem := by
    rw [loadHolds_unique l1893 (hks 1 (by omega)), hk1]
  have g1997 : σ (.n 1997) = gen ^ 18 := by
    rw [loadHolds_unique l1997 (hks 2 (by omega)), hk2]
  obtain ⟨hidx1, hidx1l⟩ := vt_idx_gen hv idx_ok.1 vt_idx_blocks.1 g1893 (by omega) hz hlmp
  obtain ⟨hidx2, hidx2l⟩ := vt_idx_gen hv idx_ok.2 vt_idx_blocks.2 g1997 (by omega) hz h18p
  have hm3 : ReadsAt Lm.read (σ (.n 13)) [σ (.n 1937), σ (.n 1955), σ (.n 1973)] := fun k hk => by
    simp only [List.length_cons, List.length_nil] at hk
    have := hfp k (by simp [freshWords]; omega)
    interval_cases k <;> exact this
  have hwl : (eqKernel alphas).length = 16 := by rw [length_eqKernel, hal]; rfl
  obtain ⟨vPush, vPull, vCount, vCe, vTarget⟩ := vt_vals hv (by omega) hfpw hidx1l hidx2l hm3
  -- the layout
  set rowsN := (List.range 6).map nr with hrowsN
  have hrl : rowsN.length = 6 := by simp [rowsN]
  have hrg : ∀ t < 6, rowsN.getD t 0 = nr t := fun t ht => by
    simp [rowsN, List.getElem?_range ht]
  have hlg : ∀ t < 6, log2Ceil (rowsN.getD t 0) = τ t := fun t ht => by
    rw [hrg t ht]; exact (hP t ht).2.2.1
  obtain ⟨hlb, hth, hpo, hco, hpl, hpr, hcl', hcr, hpc, hlc, hcc, hpp⟩ :=
    layoutOf_blocks bytecode hb logMem rowsN hrl
  set L := layoutOf bytecode logMem rowsN with hLd
  have hpl34 : L.push.length = 34 := by
    have := congrArg List.length hpo; simp only [List.length_map] at this; rw [this]; rfl
  have hcl28 : L.count.length = 28 := by
    have := congrArg List.length hco; simp only [List.length_map] at this; rw [this]; rfl
  have hszP : [0, logMem, 18] ++ L.push.map (·.logRows) = (List.range 37).map (vtKs logMem τ) := by
    rw [vtKs_push, hpl]
    exact congrArg _ (List.map_congr_left fun t ht => hlg t (vt_owners_lt.1 t ht))
  have hszC : L.count.map (·.logRows) = (List.range 28).map (fun i => vtKs logMem τ (74 + i)) := by
    rw [vtKs_count, hcl']
    exact List.map_congr_left fun t ht => hlg t (vt_owners_lt.2 t ht)
  have hsel : ∀ i < 37, (fun k => σ (.n k)) (selVal.getD i 0 + 23) =
      (((busLayout [0, logMem, 18] L.push).framework ++
        (busLayout [0, logMem, 18] L.push).tables).getD i default).eqAbove point := fun i hi => by
    rw [busLayout_all_getD _ _ (by simp [hpl34]; omega), hszP,
      List.getD_eq_getElem ((List.range 37).map (vtKs logMem τ)) 0 (by simp; omega),
      List.getElem_map, List.getElem_range]
    exact (selP i hi).2.2.2
  have hselc : ∀ j < 28, (fun k => σ (.n k)) (selVal.getD (37 + j) 0 + 23) =
      ((busLayout [] L.count).tables.getD j default).eqAbove point := fun j hj => by
    rw [busLayout_tables_getD _ (by omega), hszC,
      List.getD_eq_getElem ((List.range 28).map fun i => vtKs logMem τ (74 + i)) 0 (by simp; omega),
      List.getElem_map, List.getElem_range]
    exact (selC j hj).2.2.2
  have hpw : ∀ t < 6, (fun k => σ (.n k)) (1739 + 14 * t) =
      paddingWeight (point.take (log2Ceil (rowsN.getD t 0))) (rowsN.getD t 0) := fun t ht => by
    rw [hlg t ht, hrg t ht]
    exact (hP t ht).2.2.2.2.2.2 (le_trans (hτn t ht) hnp)
  have hχ : ∀ i < 16, (eqKernel alphas).getD i 0 = (fun i => (eqKernel alphas).getD i 0) i :=
    fun _ _ => rfl
  have htot := vt_bus_totals (ρ := fun k => σ (.n k)) (χ := fun i => (eqKernel alphas).getD i 0)
    (point := point) hP4 hP5 hP6 hb hrl hal hχ hsel hselc hpw hidx1 hidx2
  have heqhi : ∀ t < 6, ∀ s < 3, ∀ k < ((vtEqhiVars.getD t []).getD s []).length,
      (fun k => σ (.n k)) (((vtEqhiVars.getD t []).getD s []).getD k 0) =
        (fun k => σ (.n k)) (selVal.getD (eqhiSel t s k) 0 + 23) :=
    fun t ht s hs k hk => vt_eqhi hv ht hs hk
  have hforms := fun t (ht : t < 6) ev => vt_bus_forms (ρ := fun k => σ (.n k))
    (χ := fun i => (eqKernel alphas).getD i 0) (point := point) hb hrl hal hχ hsel hselc heqhi
    [σ (.n 16), σ (.n 17), σ (.n 18)] [σ (.n 1937), σ (.n 1955), σ (.n 1973)] (σ (.n 3359))
    (σ (.n 3409)) (σ (.n 1732)) ht ev
  simp only [c21, c22, c23] at htot
  -- the table sumcheck
  set bus := busVal L alphas (σ (.n 12)) point [σ (.n 16), σ (.n 17), σ (.n 18)]
    [σ (.n 1937), σ (.n 1955), σ (.n 1973)] (σ (.n 3359)) (σ (.n 3409)) (σ (.n 1732)) with hbus
  have hnc : (tables.map Table.nConstraints).sum = 2 := rfl
  have hp5 := powers_five xi
  have htarget : σ (.n 4631) = dot ((powers xi ((tables.map Table.nConstraints).sum + 3)).drop
      (tables.map Table.nConstraints).sum) bus.totals := by
    rw [htot, hnc, hp5, vTarget, ← vPush, ← vPull, ← vCount, hx3, hx4, hx5]
    simp only [dot, List.drop, List.zipWith_cons_cons, List.zipWith_nil_left, List.foldl_cons,
      List.foldl_nil]
    ring
  have hheights : L.tableLogHeights = (List.range 6).map τ := by
    rw [hth, hrowsN, List.map_map]
    exact List.map_congr_left fun t ht => (hP t (List.mem_range.mp ht)).2.2.1
  have hsc' : RunsTo (sumcheck (dot ((powers xi ((tables.map Table.nConstraints).sum + 3)).drop
      (tables.map Table.nConstraints).sum) bus.totals) 4
      (List.replicate (L.tableLogHeights.foldl max 0) none)) (sqCv (obsAll cv (freshWords σ))) ws
      (rs, cl) cvS := by
    rw [hheights, ← hn, ← htarget]; exact hsc
  have hbp : bus.point = point := rfl
  have hws6 := tableWeights_eq L.tableLogHeights bus.point rs
    (fun h hh => by
      rw [hheights] at hh; obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hh
      rw [hrsl]; exact hτn t (List.mem_range.mp ht))
    (fun h hh => by
      rw [hheights] at hh; obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hh
      exact le_trans (hτn t (List.mem_range.mp ht)) hnp)
  have hfsh := (hforms 0 (by omega) (fun _ => 0)).2.2.2
  have hbfl : bus.forms.length = 6 := hfsh.1
  have htau : ∀ t < 6, σ (.n (airTau.getD t 0)) = gen ^ τ t := fun t ht => by
    have := hv.atom _ _ (air_blocks t ht).2.2
    simp only [Atom.Holds] at this
    exact loadHolds_unique this (hdim t ht)
  have hair := vt_air hv τ hτn hgn htau hcp hpq 5 (by omega)
  have hxi' : ∀ k < 5, (fun k => σ (.n k)) (vtXiVars.getD k 0) = xi ^ k := fun k hk => by
    interval_cases k
    · rw [pow_zero]; exact hx1
    · rw [pow_one]; exact hx2
    · exact hx3
    · exact hx4
    · exact hx5
  have hfin := vt_final hP2 hxi' vCe rs.reverse L.tableLogHeights (by rw [hheights]; simp)
    bus.forms hbfl hfsh.2 (fun t => ⟨(hforms t t.2 (vtCol (fun k => σ (.n k)) t)).1,
      (hforms t t.2 (vtCol (fun k => σ (.n k)) t)).2.1,
      (hforms t t.2 (vtCol (fun k => σ (.n k)) t)).2.2.1⟩)
    (tableWeights L.tableLogHeights bus.point rs.reverse) (by rw [hws6, hheights]; simp)
  have hfin' : (ttVal ((powers xi ((tables.map Table.nConstraints).sum + 3)).take
      (tables.map Table.nConstraints).sum) ((powers xi ((tables.map Table.nConstraints).sum + 3)).drop
      (tables.map Table.nConstraints).sum) rs.reverse (List.zip tables (List.zip L.tableLogHeights
      (List.zip bus.forms (tableWeights L.tableLogHeights bus.point rs.reverse))))
      (vtEvalVars.map (·.map fun k => σ (.n k))) 0 0 []).1 = cl := by
    rw [hnc, hp5]
    refine hfin.trans ?_
    rw [← hcl, ← hpi1, show (8139 : ℕ) = airAcc 5 from rfl, hair, hws6, hheights]
    refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
    have ht' := List.mem_range.mp ht
    rw [List.map_map, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map,
      List.getElem_range, hrsl]
    rfl
  -- the run
  subst hvals
  set X := List.zip L.tableLogHeights (List.zip bus.forms
    (tableWeights L.tableLogHeights bus.point rs.reverse)) with hXd
  have hX : X.length = 6 := by rw [hXd, hws6, hheights]; simp [hbfl]
  have hl6 : (vtEvalVars.map (·.map fun k => σ (.n k))).length = (List.zip tables X).length := by
    simp [hX, tables_length', vt_evalVars_length]
  have hw6 : ∀ i (hi : i < (List.zip tables X).length)
      (he : i < (vtEvalVars.map (fun l : List ℕ => l.map fun k => σ (.n k))).length),
      (vtEvalVars.map (fun l : List ℕ => l.map fun k => σ (.n k)))[i].length =
        ((List.zip tables X)[i]).1.width := by
    intro i hi he
    have hi6 : i < 6 := by simpa [vt_evalVars_length] using he
    have := (vt_widths i hi6).1
    rw [List.getD_eq_getElem _ _ (by simp [vt_evalVars_length]; omega),
      List.getD_eq_getElem _ _ (by simp [tables_length']; omega)] at this
    simp only [List.getElem_map, List.length_map, List.getElem_zip]
    exact this
  have hrunT := runsTo_tableSumcheck hsc' hl6 hw6 hfin'
  have htc : (ttVal ((powers xi ((tables.map Table.nConstraints).sum + 3)).take
      (tables.map Table.nConstraints).sum) ((powers xi ((tables.map Table.nConstraints).sum + 3)).drop
      (tables.map Table.nConstraints).sum) rs.reverse (List.zip tables X)
      (vtEvalVars.map (·.map fun k => σ (.n k))) 0 0 []).2 = vtTc rs.reverse X (fun k => σ (.n k)) := by
    rw [ttVal_snd _ _ _ _ _ _ _ _ hl6, List.nil_append]; rfl
  rw [htc] at hrunT
  set cvR := obsAll cvS (evWords σ) with hcvRd
  set rm := challengeOf (sqCv cvR) with hrmd
  have hrun : ∀ ev, BytecodeAt ev bytecode (point.take L.logBytecode ++ alphas) (σ (.n 1732)) →
      RunsTo (tablesSeg ev L pi alphas (σ (.n 12)) point [σ (.n 16), σ (.n 17), σ (.n 18)]) cv
        (freshWords σ ++ (ws ++ evWords σ))
        (bus, bus.claims ++ vtTc rs.reverse X (fun k => σ (.n k)) ++ piClaims L pi rm) (sqCv cvR) :=
    fun ev hbv => (runsTo_tablesSeg (publicInput := pi)
      (runsTo_busRest (ev := ev) (layout := L) (alphas := alphas) (beta := σ (.n 12)) (point := point)
        (treeValues := [σ (.n 16), σ (.n 17), σ (.n 18)]) (cv := cv)
        (memory := [σ (.n 1937), σ (.n 1955), σ (.n 1973)]) (memoryFinal := σ (.n 3359))
        (bytecodeFinal := σ (.n 3409)) rfl hbv)
      (runsTo_tablePhase (layout := L) (bus := bus) (cv := obsAll cv (freshWords σ)) hrunT)).of_eq
      (by rw [vt_evss_flatten]; rfl) (by rw [vt_evss_flatten]) (by rw [vt_evss_flatten])
  -- the claims
  obtain ⟨tcCol, tcVal, tcPt⟩ := vt_tc rs.reverse X hX (fun k => σ (.n k))
  have hlenTc : (vtTc rs.reverse X (fun k => σ (.n k))).length = 104 := by
    have := congrArg List.length tcCol; simp only [List.length_map] at this; rw [this]
    decide +kernel
  have hbusVal : bus.claims.map (·.value) = freshWords σ := rfl
  have hbusPt : bus.claims.map (·.point) = [point.take logMem, point.take logMem, point.take logMem,
      point.take logMem, point.take 18] := by
    show [point.take L.logMemory, point.take L.logMemory, point.take L.logMemory,
      point.take L.logMemory, point.take L.logBytecode] = _
    rw [hlb]; rfl
  have hrm : rm = σ (.n 8153) := hpi3.symm
  have hpiVal : (piClaims L pi rm).map (·.value) = [ofK ((σ (.n 3)).limb 0) + σ (.n 8153) *
      (ofK ((σ (.n 3)).limb 0) + ofK ((σ (.n 4)).limb 0)), ofK ((σ (.n 3)).limb 1) + σ (.n 8153) *
      (ofK ((σ (.n 3)).limb 1) + ofK ((σ (.n 4)).limb 1)), 0] := by
    simp only [piClaims, ← hpi, List.map_cons, List.map_nil, List.zipWith_cons_cons,
      List.zipWith_nil_left, multilinearEval_two, hrm, List.cons.injEq, and_true]
    have h3 : (σ (.n 3)).limb 2 = 0 := hc3
    have h4 : (σ (.n 4)).limb 2 = 0 := hc4
    refine ⟨by ring, by ring, ?_⟩
    rw [h3, h4]; simp
  have hpiPt : (piClaims L pi rm).map (·.point) =
      List.replicate 3 (rm :: List.replicate ((L.placements.getD memory0 default).vars - 1) 0) := rfl
  refine ⟨cv, freshWords σ ++ (ws ++ evWords σ), sqCv cvR, rowsN, bus,
    bus.claims ++ vtTc rs.reverse X (fun k => σ (.n k)) ++ piClaims L pi rm, hcv, hrl, ?_, ?_, ?_, ?_,
    fun ev hbv => hrun ev (by rw [hr5] at hbv; exact hbv), ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    simp only [List.length_map] at hk
    rw [List.getElem_map]
    have := (hP k (by omega)).2.2.2.2.2.1
    rw [show rowsN[k] = nr k by simp [rowsN]]
    exact this
  · have : rowsN.map (fun n => gen ^ log2Ceil n) = (List.range 6).map fun t => gen ^ τ t := by
      rw [hrowsN, List.map_map]
      exact List.map_congr_left fun t ht => by
        simp only [Function.comp_apply, (hP t (List.mem_range.mp ht)).2.2.1]
    rw [this]; exact hdims
  · intro m hm
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hm
    rw [(hP t (List.mem_range.mp ht)).2.2.1]
    exact hτ29 t (List.mem_range.mp ht)
  · refine readsAt_append_pow hfr (readsAt_append_pow ?_ ?_)
    · exact hws
    · show ReadsAt _ (σ (.n 2) * gen ^ 5 * gen ^ ws.length) _
      rw [hwsl, ← hcur]; exact hev
  · simp only [List.length_append, hlenTc]; rfl
  · rw [List.map_append, List.map_append, hbusVal, tcVal, hpiVal]
    refine readsAt_append_pow (readsAt_append_pow hfp ?_) ?_
    · intro k hk
      simp only [List.length_map] at hk
      rw [loadHolds_mul_gen_pow, List.getElem_map]
      have := (hevp k (by have : evVal.length = 104 := rfl; omega)).1
      rw [List.getD_eq_getElem _ _ hk] at this
      exact this
    · intro k hk
      simp only [List.length_cons, List.length_nil] at hk
      rw [List.length_append, List.length_map, loadHolds_mul_gen_pow]
      interval_cases k
      · exact hpool109
      · exact hpool110
      · exact hpool111
  · have hlen : (bus.claims ++ vtTc rs.reverse X (fun k => σ (.n k)) ++ piClaims L pi rm).length =
        nClaims := by simp only [List.length_append, hlenTc]; rfl
    refine ⟨rs.reverse, hz, hmu, hchi, by rw [hr4, hgn, List.length_reverse, hrsl],
      by rw [List.length_reverse, hrsl]; exact hnp, hlen, ?_, ?_⟩
    · rw [List.map_append, List.map_append, tcCol]; rfl
    · intro j p hp
      have hnp109 : nPooled = 109 := rfl
      rw [hnp109]
      rw [List.map_append, List.map_append, hbusPt, tcPt, hpiPt] at hp
      have hmap : X.map (·.1) = (List.range 6).map τ := by
        rw [hXd, List.map_fst_zip (by rw [hws6, hheights]; simp [hbfl]), hheights]
      have hXg : ∀ t < 6, (X.getD t default).1 = τ t := fun t ht => by
        have : (X.map (·.1)).getD t 0 = ((List.range 6).map τ).getD t 0 := by rw [hmap]
        rw [List.getD_eq_getElem _ _ (by simp [hX]; omega), List.getElem_map,
          List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, List.getElem_range] at this
        rw [List.getD_eq_getElem _ _ (by rw [hX]; omega)]
        exact this
      rcases lt_or_ge j 5 with hj | hj
      · rw [List.getElem?_append_left (by simp [vt_tableOf_length]; omega),
          List.getElem?_append_left (by simp; omega)] at hp
        have l3345 := hv.atom 3108 (.load (.n 3345) (.n 9) 38) (by decide +kernel)
        have l3395 := hv.atom 3156 (.load (.n 3395) (.n 9) 39) (by decide +kernel)
        simp only [Atom.Holds] at l3345 l3395
        have k38 : vtKs logMem τ 38 = logMem := by simp [vtKs, blockKappaSrc, blockKappaAdj]
        have k39 : vtKs logMem τ 39 = 18 := by simp [vtKs, blockKappaSrc, blockKappaAdj]
        have g3345 : σ (.n 3345) = gen ^ logMem := by
          rw [loadHolds_unique l3345 (hks 38 (by omega)), k38]
        have g3395 : σ (.n 3395) = gen ^ 18 := by
          rw [loadHolds_unique l3395 (hks 39 (by omega)), k39]
        have hm : (point.take logMem).length = logMem := by rw [List.length_take, min_eq_left hlmp]
        have h18 : (point.take 18).length = 18 := by rw [List.length_take, min_eq_left h18p]
        interval_cases j <;> simp only [List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.some.injEq] at hp <;> subst hp <;>
          refine ⟨fun _ => ?_, fun _ => take_eq_take_length _ _, fun h => absurd h (by omega),
            fun h => absurd h (by omega)⟩
        · rw [hm, ← g1893]; exact hfl 0 (by simp)
        · rw [hm, ← g1893]; exact hfl 1 (by simp)
        · rw [hm, ← g1893]; exact hfl 2 (by simp)
        · rw [hm, ← g3345]; exact hfl 3 (by simp)
        · rw [h18, ← g3395]; exact hfl 4 (by simp)
      rcases lt_or_ge j 109 with hj' | hj'
      · rw [List.getElem?_append_left (by simp [vt_tableOf_length]; omega),
          List.getElem?_append_right (by simp; omega)] at hp
        simp only [List.length_cons, List.length_nil, List.getElem?_map] at hp
        rw [List.getElem?_eq_getElem (by rw [vt_tableOf_length]; omega)] at hp
        simp only [Option.map_some, Option.some.injEq] at hp
        subst hp
        obtain ⟨htt, ht6⟩ := vt_evTau_tables (j - 5) (by omega)
        rw [List.getD_eq_getElem vtTableOf 0 (by rw [vt_tableOf_length]; omega)] at htt ht6
        refine ⟨fun _ => ?_, fun h => absurd h (by omega), fun _ _ => take_eq_take_length _ _,
          fun h => absurd h (by omega)⟩
        rw [hXg _ ht6, List.length_take, List.length_reverse, hrsl, min_eq_left (hτn _ ht6),
          ← htau _ ht6, ← htt]
        have := (hevp (j - 5) (by omega)).2.1
        rw [show 5 + (j - 5) = j by omega] at this
        exact this
      · rw [List.getElem?_append_right (by simp [vt_tableOf_length]; omega)] at hp
        simp only [List.length_append, List.length_cons, List.length_nil, List.length_map,
          vt_tableOf_length, List.getElem?_replicate] at hp
        split_ifs at hp
        simp only [Option.some.injEq] at hp
        refine ⟨fun h => absurd h (by omega), fun h => absurd h (by omega), fun _ h => absurd h (by omega),
          fun _ => ?_⟩
        rw [← hp, hrm, hr6]
  · rw [hr1, hr2]; exact hpi2
  · rw [hr3, hcur]
    simp only [List.length_append, hwsl, freshWords, evWords, List.length_cons, List.length_nil,
      List.length_map, List.length_range, ← pow_add, mul_assoc]
    ring_nf

end
end LeanVM.Guest.B1.VerifySub
