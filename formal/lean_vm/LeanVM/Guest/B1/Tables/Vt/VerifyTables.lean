/-
  LeanVM.Guest.B1.Tables.Vt.VerifyTables

  **`verify_tables` is sound** (TRIAGE G #52): under what `verify_sub` establishes, the relation
  gives `TablesOut`.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.AsmFinal
public import LeanVM.Guest.B1.Tables.Vt.AsmClaims
public import LeanVM.Guest.B1.Tables.Vt.BcShare

/-!
# `verify_tables_holds`

For a bytecode of `2^23` words and a memory image of at most `2^32` words: the row counts are the
ones `table_rows` holds, their heights the ones `dims_g` holds; `bc_point` holds the slot
sumcheck's four challenges; from the carried capacity, the four framework words, the bytecode
share's eleven, the table sumcheck's `3n` and the `153` evaluations at the cursor run `tablesSeg`
to `vtBus` and the `159` column claims, for every check of the bytecode's value it returns; the
bus's and the public input's values are in `claim_pool`, the tables' read in place
(`col_eval_words`); `TCtx` holds of them; and the function returns the sponge's capacity after the
public input's challenge, the cursor past the words, `g^n`, the bytecode's value, the challenge
and `col_eval_words`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Complete (termsPure)

@[expose] public section

section
variable {μ : ℕ} (hμ : μ ≤ 32) (Lm : MemoryImage μ)
include hμ

/-- **`verify_tables` is sound** (TRIAGE #52), for a bytecode of `2^23` words. -/
theorem verify_tables_holds (bc : List K) (hbc : bc.length = 2 ^ 23) :
    verify_tables_Spec bc Lm.read := by
  intro pi lm weights point values args rets hpre hrel
  obtain ⟨σ, hargs, h, hrets⟩ := vt_unfold hrel
  subst hargs hrets
  rw [show (List.range 20).map (fun k ↦ σ (.n k)) = [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3),
    σ (.n 4), σ (.n 5), σ (.n 6), σ (.n 7), σ (.n 8), σ (.n 9), σ (.n 10), σ (.n 11), σ (.n 12),
    σ (.n 13), σ (.n 14), σ (.n 15), σ (.n 16), σ (.n 17), σ (.n 18), σ (.n 19)] from rfl] at hpre ⊢
  rw [show vtRets.map σ = [σ (.n 5978), σ (.n 5979), σ (.n 5980), σ (.n 5981), σ (.n 5982),
    σ (.n 5985), σ (.n 5986), σ (.n 5987), σ (.n 5988), σ (.n 5989)] from rfl]
  obtain ⟨hpi, hz, hmu, hml, hlm1, hlm, ⟨ds, hdsl, hdims⟩, hE, -, hwl, hW, hvl, hvals⟩ := hpre
  -- the tables' heights and row counts
  have hpads := vt_pads hμ Lm σ h
  obtain ⟨tf, htf⟩ := tb_exists_fun_of_forall (α := ℕ × ℕ) (n := 6)
    (P := fun t p ↦ ∃ zs : List E, p.1 < 31 ∧ LoadHolds Lm.read (σ (.n 10)) (t + 1) (gen ^ p.1) ∧
      LoadHolds Lm.read (σ (.n 11)) t (eOfNat p.2) ∧ p.2 ≤ 2 ^ p.1 ∧ zs.length = p.1 ∧
      TbReadsAt Lm.read (σ (.n 8)) zs ∧ σ (.n (vtPadV t)) = paddingWeight zs p.2 ∧
      p.1 = max (log2Ceil p.2) (tableLogFloors.getD t 0))
    (fun t ht ↦ by
      obtain ⟨τ, n, zs, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hpads t ht
      exact ⟨(τ, n), zs, h1, h2, h3, h4, h5, h6, h7, h8⟩)
  set rows : List ℕ := (List.range 6).map fun t ↦ (tf t).2 with hrows
  have hr : rows.length = 6 := by simp [hrows]
  have hRw : ∀ t < 6, vtRw rows t = (tf t).2 := fun t ht ↦ by
    simp [vtRw, hrows, List.getD_eq_getElem?_getD, ht]
  have hHt : ∀ t < 6, vtHt rows t = (tf t).1 := fun t ht ↦ by
    obtain ⟨_, -, -, -, -, -, -, -, he⟩ := htf t ht
    rw [he, vtHt, tableHeightsOf, List.getD_eq_getElem _ _ (by simp [hr, tableLogFloors]; omega)]
    simp only [List.getElem_zipWith]
    rw [← List.getD_eq_getElem _ 0, ← List.getD_eq_getElem _ 0, ← vtRw, hRw t ht]
  have hτ31 : ∀ t < 6, vtHt rows t < 31 := fun t ht ↦ by
    rw [hHt t ht]; exact (htf t ht).choose_spec.1
  have hτ : ∀ t < 6, vtHt rows t < 33 := fun t ht ↦ by have := hτ31 t ht; omega
  have hdim : ∀ t < 6, LoadHolds Lm.read (σ (.n 10)) (t + 1) (gen ^ vtHt rows t) := fun t ht ↦ by
    rw [hHt t ht]; exact (htf t ht).choose_spec.2.1
  -- the dims and kappa_base
  have hds : ds = (vtTauList (vtHt rows)).map (gen ^ ·) := by
    apply List.ext_getElem (by simp [hdsl, vtTauList])
    intro i h1 h2
    have hi : i < 6 := by omega
    have := tb_loadHolds_unique (hdims (i + 1) (by simp; omega)) (hdim i hi)
    simp only [List.getElem_cons_succ] at this
    rw [this]
    simp [vtTauList]
  rw [hds] at hdims
  have hkb : ∀ i < 8, σ (.n (25 + i)) = gen ^ ([0, lm] ++ vtTauList (vtHt rows)).getD i 0 := by
    obtain ⟨k0, kl⟩ := vt_kb h
    intro i hi
    rcases i with _ | i
    · simpa using k0
    · rw [show 25 + (i + 1) = 26 + i by omega,
        tb_loadHolds_unique (kl i (by omega)) (hdims i (by simp [vtTauList]; omega))]
      rcases i with _ | i
      · simp
      · have hi6 : i < 6 := by omega
        simp only [List.getElem_cons_succ, List.getElem_map, List.cons_append, List.nil_append,
          List.getD_cons_succ]
        rw [List.getD_eq_getElem _ _ (by simp [vtTauList]; omega)]
  have hkbt : ∀ t < 6, σ (.n (27 + t)) = gen ^ vtHt rows t := fun t ht => by
    have := hkb (2 + t) (by omega)
    rwa [show 25 + (2 + t) = 27 + t by omega, Nat.add_comm 2 t, vt_tau_getD lm _ ht] at this
  -- the round count and the table sumcheck
  obtain ⟨n, hgn, hτn, hτex, hnm⟩ := vt_zc_n hμ Lm h hτ hkbt hml hmu
  obtain ⟨hT, xs, pts, claimN, hrun, hxs, hxl, hpl, h2647, h2648, hchi, hcprod, hpeq⟩ :=
    vt_zc_run h (n := n) (by omega) hgn
  -- the padding weights
  have hpw : ∀ t < 6, σ (.n (vtPadV t)) =
      paddingWeight (point.take (vtHt rows t)) (vtRw rows t) := fun t ht ↦ by
    obtain ⟨zs, -, -, -, -, hzl, hzr, hpwz, -⟩ := htf t ht
    have hle : (tf t).1 ≤ point.length := by have := hτn t ht; rw [hHt t ht] at this; omega
    rw [hpwz, hHt t ht, hRw t ht, tbReadsAt_unique hzr (tbReadsAt_take hz (tf t).1) (by simp; omega)]
  -- the GKR leaves
  have hv3 : values = [σ (.n 2441), σ (.n 2487), σ (.n 2542)] := by
    have l0 := h.atomAt 2488 (.load (.n 2441) (.n 17) 0) (by decide +kernel)
    have l1 := h.atomAt 2534 (.load (.n 2487) (.n 17) 1) (by decide +kernel)
    have l2 := h.atomAt 2589 (.load (.n 2542) (.n 17) 2) (by decide +kernel)
    simp only [Atom.Holds] at l0 l1 l2
    refine tbReadsAt_unique hvals (fun k hk ↦ ?_) (by simp [hvl, nTrees])
    simp only [List.length_cons, List.length_nil] at hk
    interval_cases k
    · exact l0
    · exact l1
    · exact l2
  -- the totals, the bus words, the bytecode share, xi and the evaluations
  set L := layoutOf bc lm rows with hL
  have hlb : L.logBytecode = 19 := vt_layout_logBytecode bc lm rows hbc
  obtain ⟨T0, T1, T2⟩ := vt_asm_totals hμ Lm h hbc hz hmu hml hE hlm hr hτ hkb hwl hW hpw
  obtain ⟨hfr, -, -, -, -, -⟩ := vt_fresh h
  obtain ⟨ys, hysl, hys, hbcp, h1897, -, -, hsh⟩ := vt_bc h hwl hW (point.take L.logBytecode)
  obtain ⟨hxi, hxi2⟩ := vt_xi h
  obtain ⟨hrm, hcap', h5985, h5986, h5987, h5988, h5989, -, -⟩ := vt_pi h
  set slots := [σ (.n 1867), σ (.n 1883), σ (.n 1891), σ (.n 1899)] with hslots
  set bus := vtBus L weights (σ (.n 14)) point values [σ (.n 812), σ (.n 816)] (σ (.n 1302))
    (σ (.n 1316)) (σ (.n 1840)) slots with hbus
  have hforms : bus.forms = (vtAcc2 L weights (σ (.n 14)) point [σ (.n 812), σ (.n 816)]
      (σ (.n 1302)) (σ (.n 1316)) (σ (.n 1840)) (σ (.n 2441)) (σ (.n 2487)) (σ (.n 2542))).1 := by
    simp only [hbus, vtBus, hv3, List.getD_cons_zero, List.getD_cons_succ]
  set evs : List (List E) := vtEvsT σ with hevs
  have A_len : evs.length = (vtRows (tableHeightsOf rows) bus.forms point pts).length := by
    have hF6 : (vtAcc2 L weights (σ (.n 14)) point [σ (.n 812), σ (.n 816)] (σ (.n 1302))
        (σ (.n 1316)) (σ (.n 1840)) (σ (.n 2441)) (σ (.n 2487)) (σ (.n 2542))).1.length = 6 :=
      (vt_forms3_shape bc lm hr weights _ point _ _ _ _ _ _ _).1
    rw [hforms, vtEvsT_length]
    simp [vtRows, List.length_zip, vt_tableHeights_length hr, hF6,
      LeanVM.Protocol.EndToEnd.Complete.length_tableWeights, tables]
  have A_w : ∀ p ∈ List.zip (vtRows (tableHeightsOf rows) bus.forms point pts) evs,
      p.2.length = p.1.1.width :=
    vt_evsT_widths σ _
  have A_flat : evs.flatten = vtEvs σ := vt_evsT_flatten σ
  have A_fin : (termsPure ((powers (σ (.n 2610)) 5).take 2) ((powers (σ (.n 2610)) 5).drop 2)
      pts.reverse (List.zip (vtRows (tableHeightsOf rows) bus.forms point pts) evs) 0 0 []).1 =
      σ (.n 2648) := by
    rw [hforms]
    exact vt_asm_final hμ Lm h bc hbc hz hmu hml hE hlm hr hτ hkb hwl hW hgn hτn hnm hpl
      hcprod hpeq hchi
  -- the table phase
  set s0 := vtXiFs σ with hs0
  have hξ : s0.squeeze.1 = σ (.n 2610) := hxi.symm
  have htot : bus.totals = [σ (.n 2442), σ (.n 2488), σ (.n 2543)] := by
    simp only [hbus, vtBus, hv3, List.getD_cons_zero, List.getD_cons_succ]
    rw [T0, T1, T2]
  have htarget : dot ((powers s0.squeeze.1 ((tables.map Table.nConstraints).sum + 3)).drop
      (tables.map Table.nConstraints).sum) bus.totals = σ (.n 2620) := by
    rw [vt_nConstraints, hξ, vt_powers5, htot, hT]
    simp only [dot, List.drop_succ_cons, List.drop_zero, List.zipWith_cons_cons,
      List.zipWith_nil_left, List.foldl_cons, List.foldl_nil]
    ring
  have hs1 : (⟨(List.range 5).map fun k ↦ σ (.n (2642 + k)), []⟩ : Fs) = ⟨vtCapV σ 0, []⟩ := rfl
  have hn : L.tableLogHeights.foldl max 0 = n := vt_foldl_max hr hτn hτex
  have hsc : RunsTo (sumcheck (dot ((powers s0.squeeze.1 ((tables.map Table.nConstraints).sum +
      3)).drop (tables.map Table.nConstraints).sum) bus.totals) 4 (List.replicate n none))
      s0.squeeze.2 xs (pts, claimN) ⟨vtCapV σ 0, []⟩ := by
    rw [htarget, hxi2, ← hs1]; exact hrun
  have hfin' : (termsPure ((powers s0.squeeze.1 ((tables.map Table.nConstraints).sum + 3)).take
        (tables.map Table.nConstraints).sum)
      ((powers s0.squeeze.1 ((tables.map Table.nConstraints).sum + 3)).drop
        (tables.map Table.nConstraints).sum) pts.reverse
      (List.zip (vtRows L.tableLogHeights bus.forms bus.point pts) evs) 0 0 []).1 = claimN := by
    rw [vt_nConstraints, hξ, ← h2648]
    exact A_fin
  have hTP := vt_tablePhase_run L bus s0 hn hsc evs A_len A_w hfin'
  rw [A_flat, show (⟨vtCapV σ 0, []⟩ : Fs).absorbAll (vtEvs σ) dsObserve = vtEvalFs σ from rfl]
    at hTP
  have hPI := vt_publicInputPhase_run L pi (vtEvalFs σ)
  set tclaims := (termsPure ((powers s0.squeeze.1 ((tables.map Table.nConstraints).sum + 3)).take
        (tables.map Table.nConstraints).sum)
      ((powers s0.squeeze.1 ((tables.map Table.nConstraints).sum + 3)).drop
        (tables.map Table.nConstraints).sum) pts.reverse
      (List.zip (vtRows L.tableLogHeights bus.forms bus.point pts) evs) 0 0 []).2 with htc
  set pclaims := List.zipWith (fun column value ↦ (⟨column, (vtEvalFs σ).squeeze.1 ::
        List.replicate ((L.placement memory0).variableCount - 1) 0, value⟩ : ColumnClaim))
        [memory0, memory1] (([0, 1] : List (Fin 2)).map fun limb ↦
          multilinearEval [ofK ((digestHalves pi).1.limb limb),
            ofK ((digestHalves pi).2.limb limb)] [(vtEvalFs σ).squeeze.1]) with hpc
  have hAC := vt_asm_claims hμ Lm h hbc hpi hz hmu hml hE hlm hr hτ hkb hgn hnm hτn hpl hchi
    bus rfl ((powers s0.squeeze.1 ((tables.map Table.nConstraints).sum + 3)).take
        (tables.map Table.nConstraints).sum)
      ((powers s0.squeeze.1 ((tables.map Table.nConstraints).sum + 3)).drop
        (tables.map Table.nConstraints).sum) bus.forms
      (by rw [hforms]; exact (vt_forms3_shape bc lm hr weights _ point _ _ _ _ _ _ _).1)
  have hcl : bus.claims ++ tclaims ++ pclaims = vtAllClaims bc lm rows pi point pts
      ((powers s0.squeeze.1 ((tables.map Table.nConstraints).sum + 3)).take
        (tables.map Table.nConstraints).sum)
      ((powers s0.squeeze.1 ((tables.map Table.nConstraints).sum + 3)).drop
        (tables.map Table.nConstraints).sum) bus.forms σ := by
    rw [hpc, htc, ← hrm]
    rfl
  refine ⟨vtFreshWords σ ++ (ys ++ [σ (.n 1905)]) ++ (xs ++ vtEvs σ),
    (vtEvalFs σ).squeeze.2.cap, rows, bus, bus.claims ++ tclaims ++ pclaims, hr, ?rowsRead,
    ?dimsRead, ?h31, ?xsRead, ⟨slots, rfl, hbcp, rfl⟩, ?run, ?len, ?pool, ?cew, ?pipool, ?tctx,
    ?caps, ?cur⟩
  case rowsRead =>
    intro t ht
    have ht6 : t < 6 := by simpa [hr] using ht
    obtain ⟨_, -, -, h3, -⟩ := htf t ht6
    simp only [List.getElem_map]
    rw [← List.getD_eq_getElem _ 0 (by omega), ← vtRw, hRw t ht6]
    exact h3
  case dimsRead => rwa [vt_tableHeights_eq hr]
  case h31 =>
    intro x hx
    rw [vt_tableHeights_eq hr] at hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
    exact hτ31 t (List.mem_range.mp ht)
  case xsRead =>
    refine vt_readsAt_append (vt_readsAt_append hfr ?_) (vt_readsAt_append ?_ ?_)
    · rw [show (vtFreshWords σ).length = 7 from rfl]; exact hys
    · rw [show (vtFreshWords σ ++ (ys ++ [σ (.n 1905)])).length = 14 by simp [hysl, vtFreshWords],
        show (14 : ℕ) = 13 + 1 from rfl, pow_add, ← mul_assoc,
        show σ (.n 5) * gen ^ 13 = σ (.n 1897) by rw [h1897, mul_assoc, ← pow_add]]
      exact fun k hk ↦ by simpa using hxs k hk
    · intro k hk
      simp only [vtEvs, List.length_map, List.length_range] at hk
      simp only [vtEvs, List.getElem_map, List.getElem_range]
      rw [show (vtFreshWords σ ++ (ys ++ [σ (.n 1905)])).length = 14 by simp [hysl, vtFreshWords],
        hxl, show σ (.n 5) * gen ^ 14 * gen ^ (3 * n) = σ (.n 2647) by
          rw [h2647, h1897]; ring]
      exact (vt_eval h hk).1
  case run =>
    intro ev hev
    have hbv : BytecodeAt ev L.bytecode (point.take L.logBytecode ++ slots) (σ (.n 1905)) := by
      rw [← h5987]; exact hev
    have hBR := vt_busRest_run ev L weights (σ (.n 14)) point values [σ (.n 812), σ (.n 816)] rfl
      (σ (.n 1302)) (σ (.n 1316)) (σ (.n 1840)) (σ (.n 1905)) slots
      ([σ (.n 1840), σ (.n 1844), σ (.n 1848)] ++ ys ++ [σ (.n 1905)])
      ⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)], []⟩ s0 hsh hbv
    unfold tablesSeg
    exact RunsTo.of_eq (hBR.bind (hTP.bind (hPI.bind (runsTo_ret _ _)))) rfl
      (by simp [vtFreshWords]) (by simp only [hbus, htc, hpc, List.append_assoc]) rfl
  case len => rw [hcl]; exact hAC.1
  case pool => rw [hcl]; exact hAC.2.1
  case cew => rw [hcl, h5989]; exact hAC.2.2.1
  case pipool => rw [hcl]; exact hAC.2.2.2.1
  case tctx => rw [hcl, h5988, h5986]; exact hAC.2.2.2.2
  case caps => rw [← hcap']; rfl
  case cur =>
    rw [h5985, h2647, h1897]
    simp only [List.length_append, vtEvs, List.length_map, List.length_range, hxl, hysl,
      show (vtFreshWords σ).length = 7 from rfl, List.length_cons, List.length_nil, pow_add]
    ring

end

end
end LeanVM.Guest.B1.Tables
