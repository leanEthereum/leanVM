/-
  LeanVM.Guest.B1.Tables.Vt.VerifyTables

  **`verify_tables` is sound** (TRIAGE G #52): under what `verify_sub` establishes, the relation
  gives `TablesOut`.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.AsmFinal
public import LeanVM.Guest.B1.Tables.Vt.AsmClaims

/-!
# `verify_tables_holds` (G:2109-2535)

For a bytecode of `2^23` words and a memory image of at most `2^32` words: the row counts are
the ones `table_rows` holds, their heights the ones `dims_g` holds; from the carried capacity,
the five framework words, the table sumcheck's `3n` words and the `159` evaluations at the
cursor run `tablesSeg` to `vtBus` and the `165` column claims, the bus's and the public input's
values in `claim_pool`, the tables' read in place (`col_eval_words`); `TCtx` holds of them; and
the function returns the sponge's capacity after the public input's challenge, the cursor past
the words, `g^n`, the bytecode's value, the challenge and `col_eval_words`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Complete (termsPure)

@[expose] public section

section
variable {μ : ℕ} (hμ : μ ≤ 32) (Lm : MemoryImage μ)
include hμ

/-- **`verify_tables` is sound** (G:2153-2579; TRIAGE #52), for a bytecode of `2^23` words. -/
theorem verify_tables_holds (bc : List K) (hbc : bc.length = 2 ^ 23) :
    verify_tables_Spec bc Lm.read := by
  intro pi lm alphas point values args rets hpre hrel
  obtain ⟨σ, hargs, h, hrets⟩ := vt_unfold hrel
  subst hargs hrets
  rw [show (List.range 20).map (fun k ↦ σ (.n k)) = [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3),
    σ (.n 4), σ (.n 5), σ (.n 6), σ (.n 7), σ (.n 8), σ (.n 9), σ (.n 10), σ (.n 11), σ (.n 12),
    σ (.n 13), σ (.n 14), σ (.n 15), σ (.n 16), σ (.n 17), σ (.n 18), σ (.n 19)] from rfl] at hpre ⊢
  rw [show vtRets.map σ = [σ (.n 6961), σ (.n 6962), σ (.n 6963), σ (.n 6964), σ (.n 6965),
    σ (.n 6968), σ (.n 6969), σ (.n 6970), σ (.n 6971), σ (.n 6972)] from rfl]
  obtain ⟨hpi, hz, hmu, hml, hlm16, hlm, ⟨ds, hdsl, hdims⟩, hE, hal, hW, hvals⟩ := hpre
  -- the tables' heights and row counts
  have hpads := vt_pads hμ Lm σ h
  obtain ⟨tf, htf⟩ := tb_exists_fun_of_forall (α := ℕ × ℕ) (n := 6)
    (P := fun t p ↦ ∃ zs : List E, p.1 < 29 ∧ LoadHolds Lm.read (σ (.n 10)) (t + 1) (gen ^ p.1) ∧
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
  have hτ : ∀ t < 6, vtHt rows t < 29 := fun t ht ↦ by
    rw [hHt t ht]; exact (htf t ht).choose_spec.1
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
    · rw [show 28 + (i + 1) = 29 + i by omega,
        tb_loadHolds_unique (kl i (by omega)) (hdims i (by simp [vtTauList]; omega))]
      rcases i with _ | i
      · simp
      · have hi6 : i < 6 := by omega
        simp only [List.getElem_cons_succ, List.getElem_map, List.cons_append, List.nil_append,
          List.getD_cons_succ]
        rw [List.getD_eq_getElem _ _ (by simp [vtTauList]; omega)]
  have hkbt : ∀ t < 6, σ (.n (30 + t)) = gen ^ vtHt rows t := fun t ht => by
    have := hkb (2 + t) (by omega)
    rwa [show 28 + (2 + t) = 30 + t by omega, Nat.add_comm 2 t, vt_tau_getD lm _ ht] at this
  -- the round count and the table sumcheck
  obtain ⟨n, hgn, hτn, hτex, hnm⟩ := vt_zc_n hμ Lm h hτ hkbt hml hmu
  obtain ⟨hT, xs, pts, claimN, hrun, hxs, hxl, hpl, h2609, h2610, hchi, hcprod, hpeq⟩ :=
    vt_zc_run h (n := n) (by omega) hgn
  -- the padding weights
  have hpw : ∀ t < 6, σ (.n (vtPadV t)) =
      paddingWeight (point.take (vtHt rows t)) (vtRw rows t) := fun t ht ↦ by
    obtain ⟨zs, -, -, -, -, hzl, hzr, hpwz, -⟩ := htf t ht
    have hle : (tf t).1 ≤ point.length := by have := hτn t ht; rw [hHt t ht] at this; omega
    rw [hpwz, hHt t ht, hRw t ht, tbReadsAt_unique hzr (tbReadsAt_take hz (tf t).1) (by simp; omega)]
  -- the totals, the bus words, the evaluations and the public input
  obtain ⟨T0, T1, T2⟩ := vt_asm_totals hμ Lm h hbc hz hmu hml hE hlm hr hτ hkb hal hW hpw
  obtain ⟨hfr, -, hxi, hcap⟩ := vt_fresh h
  obtain ⟨hrm, hcap', h6862, h6863, h6864, h6865, h6866, -, -, -, -, -⟩ := vt_pi h
  have c5 := h.atomAt 5 (.copy (.n 25) (.n 17)) (by decide +kernel)
  have c6 := h.atomAt 6 (.copy (.n 26) (.n 18)) (by decide +kernel)
  have c7 := h.atomAt 7 (.copy (.n 27) (.n 19)) (by decide +kernel)
  simp only [Atom.Holds] at c5 c6 c7
  -- the forms
  have hforms : (vtBus (layoutOf bc lm rows) alphas (σ (.n 14)) point values
      [σ (.n 830), σ (.n 843), σ (.n 856)] (σ (.n 1843)) (σ (.n 1898)) (σ (.n 581))).forms =
      (vtAcc2 (layoutOf bc lm rows) alphas (σ (.n 14)) point
        [σ (.n 830), σ (.n 843), σ (.n 856)] (σ (.n 1843)) (σ (.n 1898)) (σ (.n 581))
        (σ (.n 25)) (σ (.n 26)) (σ (.n 27))).1 := by
    simp only [vtBus, hvals, List.getD_cons_zero, List.getD_cons_succ, ← c5, ← c6, ← c7]
  set evs : List (List E) := vtEvsT σ with hevs
  have A_len : evs.length = (vtRows (tableHeightsOf rows) (vtBus (layoutOf bc lm rows) alphas
      (σ (.n 14)) point values [σ (.n 830), σ (.n 843), σ (.n 856)] (σ (.n 1843)) (σ (.n 1898))
      (σ (.n 581))).forms point pts).length := by
    rw [hforms, vtEvsT_length]
    simp [vtRows, List.length_zip, vt_tableHeights_length hr,
      (vt_forms3_shape bc lm hr alphas _ point _ _ _ _ _ _ _).1, LeanVM.Protocol.EndToEnd.Complete.length_tableWeights, tables]
  have A_w : ∀ p ∈ List.zip (vtRows (tableHeightsOf rows) (vtBus (layoutOf bc lm rows) alphas
      (σ (.n 14)) point values [σ (.n 830), σ (.n 843), σ (.n 856)] (σ (.n 1843)) (σ (.n 1898))
      (σ (.n 581))).forms point pts) evs, p.2.length = p.1.1.width :=
    vt_evsT_widths σ _
  have A_flat : evs.flatten = vtEvs σ := vt_evsT_flatten σ
  have A_fin : (termsPure ((powers (σ (.n 2588)) 5).take 2) ((powers (σ (.n 2588)) 5).drop 2)
      pts.reverse (List.zip (vtRows (tableHeightsOf rows) (vtBus (layoutOf bc lm rows) alphas
      (σ (.n 14)) point values [σ (.n 830), σ (.n 843), σ (.n 856)] (σ (.n 1843)) (σ (.n 1898))
      (σ (.n 581))).forms point pts) evs) 0 0 []).1 = σ (.n 2626) := by
    rw [hforms]
    exact vt_asm_final hμ Lm h bc hbc hz hmu hml hE hlm hr hτ hkb hal hW hgn hτn hnm hpl
      hcprod hpeq hchi
  -- the run
  set L := layoutOf bc lm rows with hL
  set bus := vtBus L alphas (σ (.n 14)) point values [σ (.n 830), σ (.n 843), σ (.n 856)]
    (σ (.n 1843)) (σ (.n 1898)) (σ (.n 581)) with hbus
  set s0 := vtFreshFs σ with hs0
  have hξ : s0.squeeze.1 = σ (.n 2588) := hxi.symm
  have htot : bus.totals = [σ (.n 1820), σ (.n 2073), σ (.n 2515)] := by
    simp only [hbus, vtBus, hvals, List.getD_cons_zero, List.getD_cons_succ, ← c5, ← c6, ← c7]
    rw [T0, T1, T2]
  have htarget : dot ((powers s0.squeeze.1 ((tables.map Table.nConstraints).sum + 3)).drop
      (tables.map Table.nConstraints).sum) bus.totals = σ (.n 2598) := by
    rw [vt_nConstraints, hξ, vt_powers5, htot, hT]
    simp only [dot, List.drop_succ_cons, List.drop_zero, List.zipWith_cons_cons,
      List.zipWith_nil_left, List.foldl_cons, List.foldl_nil]
    ring
  have hs0sq : s0.squeeze.2 = ⟨(List.range 5).map fun k ↦ σ (.n (2577 + k)), []⟩ := by
    rw [hcap]; rfl
  have hs1 : (⟨(List.range 5).map fun k ↦ σ (.n (2620 + k)), []⟩ : Fs) = ⟨vtCapV σ 0, []⟩ := rfl
  have hn : L.tableLogHeights.foldl max 0 = n := vt_foldl_max hr hτn hτex
  have hsc : RunsTo (sumcheck (dot ((powers s0.squeeze.1 ((tables.map Table.nConstraints).sum +
      3)).drop (tables.map Table.nConstraints).sum) bus.totals) 4 (List.replicate n none))
      s0.squeeze.2 xs (pts, claimN) ⟨vtCapV σ 0, []⟩ := by
    rw [htarget, hs0sq, ← hs1]; exact hrun
  have hfin' : (termsPure ((powers s0.squeeze.1 ((tables.map Table.nConstraints).sum + 3)).take
        (tables.map Table.nConstraints).sum)
      ((powers s0.squeeze.1 ((tables.map Table.nConstraints).sum + 3)).drop
        (tables.map Table.nConstraints).sum) pts.reverse
      (List.zip (vtRows L.tableLogHeights bus.forms bus.point pts) evs) 0 0 []).1 = claimN := by
    rw [vt_nConstraints, hξ, ← h2610]
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
        [memory0, memory1, memory2] (([0, 1, 2] : List (Fin 3)).map fun limb ↦
          multilinearEval [ofK ((digestHalves pi).1.limb limb),
            ofK ((digestHalves pi).2.limb limb)] [(vtEvalFs σ).squeeze.1]) with hpc
  have hAC := vt_asm_claims hμ Lm h hbc hpi hz hmu hml hE hlm hr hτ hkb hgn hnm hτn hpl hchi
    bus rfl ((powers s0.squeeze.1 ((tables.map Table.nConstraints).sum + 3)).take
        (tables.map Table.nConstraints).sum)
      ((powers s0.squeeze.1 ((tables.map Table.nConstraints).sum + 3)).drop
        (tables.map Table.nConstraints).sum) bus.forms
      (by rw [hbus, hforms]; exact (vt_forms3_shape bc lm hr alphas _ point _ _ _ _ _ _ _).1)
  have hcl : bus.claims ++ tclaims ++ pclaims = vtAllClaims bc lm rows pi point pts
      ((powers s0.squeeze.1 ((tables.map Table.nConstraints).sum + 3)).take
        (tables.map Table.nConstraints).sum)
      ((powers s0.squeeze.1 ((tables.map Table.nConstraints).sum + 3)).drop
        (tables.map Table.nConstraints).sum) bus.forms σ := by
    rw [hpc, htc, ← hrm]
    rfl
  refine ⟨vtFreshWords σ ++ (xs ++ vtEvs σ), (vtEvalFs σ).squeeze.2.cap, rows, bus,
    bus.claims ++ tclaims ++ pclaims, hr, ?rowsRead, ?dimsRead, ?h29, ?xsRead, ?run, ?len, ?pool,
    ?cew, ?pipool, ?tctx, ?caps, ?cur⟩
  case rowsRead =>
    intro t ht
    have ht6 : t < 6 := by simpa [hr] using ht
    obtain ⟨_, -, -, h3, -⟩ := htf t ht6
    simp only [List.getElem_map]
    rw [← List.getD_eq_getElem _ 0 (by omega), ← vtRw, hRw t ht6]
    exact h3
  case dimsRead => rwa [vt_tableHeights_eq hr]
  case h29 =>
    intro x hx
    rw [vt_tableHeights_eq hr] at hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
    exact hτ t (List.mem_range.mp ht)
  case xsRead =>
    refine vt_readsAt_append hfr (vt_readsAt_append ?_ ?_)
    · rw [show (vtFreshWords σ).length = 5 from rfl]; exact hxs
    · intro k hk
      simp only [vtEvs, List.length_map, List.length_range] at hk
      simp only [vtEvs, List.getElem_map, List.getElem_range]
      rw [show (vtFreshWords σ).length = 5 from rfl, hxl, ← h2609]
      exact (vt_eval h hk).1
  case run =>
    intro ev hev
    have hbv : BytecodeAt ev L.bytecode (point.take L.logBytecode ++ alphas) (σ (.n 581)) := by
      rw [← h6864]; exact hev
    have hBR := vt_busRest_run ev L alphas (σ (.n 14)) point values
      [σ (.n 830), σ (.n 843), σ (.n 856)] rfl (σ (.n 1843)) (σ (.n 1898)) (σ (.n 581)) hbv
      ⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)], []⟩
    unfold tablesSeg
    exact RunsTo.of_eq (hBR.bind (hTP.bind (hPI.bind (runsTo_ret _ _)))) rfl
      (by simp [vtFreshWords]) (by simp only [hbus, htc, hpc, List.append_assoc]) rfl
  case len => rw [hcl]; exact hAC.1
  case pool => rw [hcl]; exact hAC.2.1
  case cew => rw [hcl, h6866]; exact hAC.2.2.1
  case pipool => rw [hcl]; exact hAC.2.2.2.1
  case tctx => rw [hcl, h6865, h6863]; exact hAC.2.2.2.2
  case caps => rw [← hcap']; rfl
  case cur =>
    rw [h6862, h2609]
    simp only [List.length_append, vtEvs, List.length_map, List.length_range, hxl,
      show (vtFreshWords σ).length = 5 from rfl, pow_add]
    ring

end

end
end LeanVM.Guest.B1.Tables
