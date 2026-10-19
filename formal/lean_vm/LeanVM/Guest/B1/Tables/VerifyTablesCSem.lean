/-
  LeanVM.Guest.B1.Tables.VerifyTablesCSem

  `verify_tables`' completeness: the bus target and the final check on the body's prefix.
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTables
public import LeanVM.Guest.B1.Tables.VerifyTablesCAt
public import LeanVM.Guest.B1.Tables.VerifyTablesCTrace

/-!
# The bus totals and the terms' sum, on a prefix

The soundness side's derivations (`verify_tables_sound_of`) replayed on `VtHoldsAt`: the three
totals the guest computes by statement `4273` are the bus's (`vt_totals_c`), so the table
sumcheck's target is the run's (`vt_target_dot`); the accumulated terms at `8139` are the
table sumcheck's terms' sum on the guest's evaluations (`vt_final_c`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

section
variable {rd : Reader} {σ : Val}

/-- **The bus totals** are the three values the guest computes by statement `4273`. -/
theorem vt_totals_c (hP4 : PushTotalEval) (hP5 : PullTotalEval) (hP6 : CountTotalEval)
    {bytecode : List K} (hb : bytecode.length = 2 ^ 22) {logMem : ℕ} {rows : List ℕ}
    (hr : rows.length = 6) {alphas point : List E} (hal : alphas.length = 4)
    (h : VtHoldsAt 4273 rd σ) (hfw : ReadsAt rd (σ (.n 11)) (eqKernel alphas))
    (h1 : LoadHolds rd (σ (.n 1852)) 1 (σ (.n 1931))) (h2 : LoadHolds rd (σ (.n 1852)) 2 (σ (.n 2035)))
    (hm : ReadsAt rd (σ (.n 13)) [σ (.n 1937), σ (.n 1955), σ (.n 1973)])
    (hsel : ∀ i < 37, σ (.n (selVal.getD i 0 + 23)) =
      (((busLayout [0, logMem, 18] (layoutOf bytecode logMem rows).push).framework ++
        (busLayout [0, logMem, 18] (layoutOf bytecode logMem rows).push).tables).getD i
          default).eqAbove point)
    (hselc : ∀ j < 28, σ (.n (selVal.getD (37 + j) 0 + 23)) =
      ((busLayout [] (layoutOf bytecode logMem rows).count).tables.getD j default).eqAbove point)
    (hpw : ∀ t < 6, σ (.n (1739 + 14 * t)) =
      paddingWeight (point.take (log2Ceil (rows.getD t 0))) (rows.getD t 0))
    (hidx1 : σ (.n 1931) = indexMle (point.take logMem)) (hidx2 : σ (.n 2035) = indexMle (point.take 18)) :
    (busVal (layoutOf bytecode logMem rows) alphas (σ (.n 12)) point [σ (.n 21), σ (.n 22), σ (.n 23)]
      [σ (.n 1937), σ (.n 1955), σ (.n 1973)] (σ (.n 3359)) (σ (.n 3409)) (σ (.n 1732))).totals =
      [σ (.n 3326), σ (.n 3705), σ (.n 4553)] := by
  have hw : 16 ≤ (eqKernel alphas).length := by rw [length_eqKernel, hal]; decide
  have hL := vt_fpw_sound hw hfw
  have hE : LoadTab.Sound rd σ (fun i => (eqKernel alphas).getD i 0) [] := fun _ hq => absurd hq (by simp)
  rw [vt_bus_totals (ρ := fun k => σ (.n k)) (χ := fun i => (eqKernel alphas).getD i 0) hP4 hP5 hP6 hb
    hr hal (fun _ _ => rfl) hsel hselc hpw hidx1 hidx2,
    window_eval_at h hL 1505 1587 3326 pushTotalEx (by norm_num) vt_push_total,
    window_eval_at h (vt_pullTab_sound hw hfw h1 h2 hm) 1505 1892 3705 pullTotalEx (by norm_num)
      vt_pull_total,
    window_eval_at h hE 3397 876 4553 countTotalEx (by norm_num) vt_count_total]

/-- The table sumcheck's target on the totals. -/
theorem vt_target_dot (xi T0 T1 T2 : E) :
    dot ((powers xi (vtNC + 3)).drop vtNC) [T0, T1, T2] = xi ^ 2 * T0 + xi ^ 3 * T1 + xi ^ 4 * T2 := by
  rw [show vtNC = 2 from rfl, powers_five]
  simp only [dot, List.drop, List.zipWith_cons_cons, List.zipWith_nil_left, List.foldl_cons,
    List.foldl_nil]
  ring

/-- **The accumulated terms are the table sumcheck's terms' sum** on the guest's evaluations: with
`n` the tables' largest log-height, the challenges `rs` (in round order) whose running products
and equality prefix the two buffers at `4639` and `4655` hold, and `ξ`'s powers at
`4622 ..< 4627`. -/
theorem vt_final_c (hP2 : CeExEval) {bytecode : List K} (hb : bytecode.length = 2 ^ 22) {logMem : ℕ}
    {rows : List ℕ} (hr : rows.length = 6) {alphas point : List E} (hal : alphas.length = 4)
    (h : VtHoldsAt 7854 rd σ) (hfw : ReadsAt rd (σ (.n 11)) (eqKernel alphas))
    (h1 : LoadHolds rd (σ (.n 1852)) 1 (σ (.n 1931))) (h2 : LoadHolds rd (σ (.n 1852)) 2 (σ (.n 2035)))
    (hm : ReadsAt rd (σ (.n 13)) [σ (.n 1937), σ (.n 1955), σ (.n 1973)])
    (hsel : ∀ i < 37, σ (.n (selVal.getD i 0 + 23)) =
      (((busLayout [0, logMem, 18] (layoutOf bytecode logMem rows).push).framework ++
        (busLayout [0, logMem, 18] (layoutOf bytecode logMem rows).push).tables).getD i
          default).eqAbove point)
    (hselc : ∀ j < 28, σ (.n (selVal.getD (37 + j) 0 + 23)) =
      ((busLayout [] (layoutOf bytecode logMem rows).count).tables.getD j default).eqAbove point)
    {rs : List E} (hrsl : rs.length = vtN (layoutOf bytecode logMem rows))
    (hnp : vtN (layoutOf bytecode logMem rows) ≤ point.length)
    (hgn : σ (.n 4554) = gen ^ vtN (layoutOf bytecode logMem rows))
    (htau : ∀ t < 6, σ (.n (airTau.getD t 0)) = gen ^ log2Ceil (rows.getD t 0))
    (hcp : ∀ j ≤ vtN (layoutOf bytecode logMem rows), LoadHolds rd (σ (.n 4639)) j (prodE (rs.take j)))
    (hpq : ∀ k ≤ vtN (layoutOf bytecode logMem rows),
      LoadHolds rd (σ (.n 4655)) k (eqEval (point.take k) (rs.reverse.take k)))
    {xi : E} (hxi : ∀ k < 5, σ (.n (4622 + k)) = xi ^ k)
    (tv memory : List E) (mF bF bv : E) :
    σ (.n 8139) = (ttVal ((powers xi (vtNC + 3)).take vtNC) ((powers xi (vtNC + 3)).drop vtNC) rs.reverse
      (vtRows (layoutOf bytecode logMem rows)
        (busVal (layoutOf bytecode logMem rows) alphas (σ (.n 12)) point tv memory mF bF bv) rs.reverse)
      (vtEvalVars.map (·.map fun k => σ (.n k))) 0 0 []).1 := by
  set L := layoutOf bytecode logMem rows with hLd
  set n := vtN L with hn
  set τ : ℕ → ℕ := fun t => log2Ceil (rows.getD t 0) with hτd
  set bus := busVal L alphas (σ (.n 12)) point tv memory mF bF bv with hbus
  have hheights : L.tableLogHeights = (List.range 6).map τ := by
    show rows.map log2Ceil = _
    apply List.ext_getElem (by simp [hr])
    intro t h1 h2
    simp only [List.getElem_map, List.getElem_range, hτd]
    rw [List.getD_eq_getElem _ _ (by simpa [hr] using h1)]
  have hτn : ∀ t < 6, τ t ≤ n := fun t ht => by
    rw [hn, vtN, hheights]
    exact vt_le_foldl_max _ 0 _ (Or.inl (List.mem_map.mpr ⟨t, List.mem_range.mpr ht, rfl⟩))
  have hχ : ∀ i < 16, (eqKernel alphas).getD i 0 = (fun i => (eqKernel alphas).getD i 0) i :=
    fun _ _ => rfl
  have heqhi : ∀ t < 6, ∀ s < 3, ∀ k < ((vtEqhiVars.getD t []).getD s []).length,
      (fun k => σ (.n k)) (((vtEqhiVars.getD t []).getD s []).getD k 0) =
        (fun k => σ (.n k)) (selVal.getD (eqhiSel t s k) 0 + 23) :=
    fun t ht s hs k hk => vt_eqhi_at h (by norm_num) ht hs hk
  have hforms := fun t (ht : t < 6) ev => vt_bus_forms (ρ := fun k => σ (.n k))
    (χ := fun i => (eqKernel alphas).getD i 0) (point := point) hb hr hal hχ hsel hselc heqhi
    tv memory mF bF bv ht ev
  have hws6 := tableWeights_eq L.tableLogHeights bus.point rs
    (fun h hh => by
      rw [hheights] at hh; obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hh
      rw [hrsl]; exact hτn t (List.mem_range.mp ht))
    (fun h hh => by
      rw [hheights] at hh; obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hh
      exact le_trans (hτn t (List.mem_range.mp ht)) hnp)
  have hfsh := (hforms 0 (by omega) (fun _ => 0)).2.2.2
  have hbfl : bus.forms.length = 6 := hfsh.1
  have hair := vt_air_at h τ hτn hgn htau hcp hpq 5 (by omega)
  have hxi' : ∀ k < 5, (fun k => σ (.n k)) (vtXiVars.getD k 0) = xi ^ k := fun k hk => by
    interval_cases k
    · exact hxi 0 (by omega)
    · exact hxi 1 (by omega)
    · exact hxi 2 (by omega)
    · exact hxi 3 (by omega)
    · exact hxi 4 (by omega)
  have hw16 : 16 ≤ (eqKernel alphas).length := by rw [length_eqKernel, hal]; decide
  have vCe := (vt_vals_at h hw16 hfw h1 h2 hm).2.2.2.1
  have hfin := vt_final hP2 hxi' vCe rs.reverse L.tableLogHeights (by rw [hheights]; simp)
    bus.forms hbfl hfsh.2 (fun t => ⟨(hforms t t.2 (vtCol (fun k => σ (.n k)) t)).1,
      (hforms t t.2 (vtCol (fun k => σ (.n k)) t)).2.1,
      (hforms t t.2 (vtCol (fun k => σ (.n k)) t)).2.2.1⟩)
    (tableWeights L.tableLogHeights bus.point rs.reverse) (by rw [hws6, hheights]; simp)
  rw [show vtNC = 2 from rfl, powers_five]
  refine Eq.trans ?_ hfin.symm
  rw [show (8139 : ℕ) = airAcc 5 from rfl, hair, hws6, hheights]
  refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
  have ht' := List.mem_range.mp ht
  simp only [List.map_map, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht',
    Option.map_some, Option.getD_some, Function.comp_apply, hrsl]
  rfl

end

end
end LeanVM.Guest.B1.VerifySub
