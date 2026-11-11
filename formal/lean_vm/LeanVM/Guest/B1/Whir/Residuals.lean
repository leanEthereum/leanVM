/-
  LeanVM.Guest.B1.Whir.Residuals

  A level's residual sum: the residual loop over its query pairs, the odd query inline, the
  running `inner` advanced by the level's scale times the sum.
-/

module

public import LeanVM.Guest.B1.Whir.LevelResidual
public import LeanVM.Guest.B1.Whir.RateCfg

/-!
# The residual sums (G:1721-1744)

`osResidual_sound`: level `lvl`'s block reads `μ` from `level_mus`, its positions `P`, its row's
words `D` in `basis_d`, its scale `L` in `level_scale`, and stores
`inner[lvl + 1] = inner[lvl] + L·h`, `h` the chain `h ← (h + R(P_i))·μ` over its queries from `0`
(`resFold`), `R` the level's `residual_query`: the dispatch on the rate into `level_residual`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader} {σ : Val}

/-- A level's residual at a position. -/
abbrev lvRes (lv : OsLv) (D : ℕ → E) (p : E) : E :=
  residualProd (osVals lv.vanish lv.logCols) p D lv.logCols

/-- `resFold` is the sum of the residuals weighted by powers of `μ`. -/
theorem resFold_eq_sum (D : ℕ → E) (vo ml : ℕ) (mu h : E) (P : ℕ → E) (n : ℕ) :
    resFold D vo ml mu h ((List.range n).map P) =
      h * mu ^ n + ∑ i ∈ Finset.range n, residualProd (osVals vo ml) (P i) D ml * mu ^ (n - i) := by
  induction n with
  | zero => simp [resFold]
  | succ n ih =>
    rw [List.range_succ, List.map_append, resFold_append, ih]
    simp only [List.map_cons, List.map_nil, resFold, List.foldl_cons, List.foldl_nil,
      Finset.sum_range_succ]
    have : ∀ i ∈ Finset.range n, residualProd (osVals vo ml) (P i) D ml * mu ^ (n + 1 - i) =
        residualProd (osVals vo ml) (P i) D ml * mu ^ (n - i) * mu := by
      intro i hi
      rw [Finset.mem_range] at hi
      rw [show n + 1 - i = n - i + 1 by omega, pow_succ, mul_assoc]
    rw [Finset.sum_congr rfl this, ← Finset.sum_mul, pow_succ, show n + 1 - n = 1 by omega]
    ring

/-- **A level's residual sum**: the level's slots of `query_positions` and its row of `basis_d`,
`μ` from `level_mus`, the dispatch on the rate into `level_residual`, the running `inner`
advanced by the scale times the chain. -/
theorem osResidual_sound {C : CallRel} {c : OsCfg} {lvl : ℕ} {lv : OsLv} {ich bd ls : ℕ}
    {mats : List OsMat} {k : ℕ}
    (hLR : ∀ args rets, C (osResidualName lv) args rets →
      MeaningLevelResidual lv.queries lv.logCols rd args rets)
    (hrate : LvRate σ c lvl lv) (hvan : lv.vanish = vanishOff lv.logCols)
    (hpo : lv.posOff < u128Bound) (hlc : lvl * ligColsCap < u128Bound) (hmats : MatsOk σ mats)
    {D P : ℕ → E} {I L mu : E}
    (hD : ∀ s < lv.logCols, LoadHolds rd (σ (.n bd)) (lvl * ligColsCap + s) (D s))
    (hP : ∀ i < lv.queries, LoadHolds rd (σ (.n osQpos)) (lv.posOff + i) (P i))
    (hM : LoadHolds rd (σ (.n osMus)) lvl mu)
    (hI : LoadHolds rd (σ (.n ich)) lvl I) (hL : LoadHolds rd (σ (.n ls)) lvl L)
    (hok : AllOk C rd σ (osResidual c ich bd ls lvl lv mats k).1) :
    LoadHolds rd (σ (.n ich)) (lvl + 1)
      (I + L * resFold D lv.vanish lv.logCols mu 0 ((List.range lv.queries).map P)) ∧
    MatsOk σ (osResidual c ich bd ls lvl lv mats k).2.1 := by
  set P' := c.plan
  set qp := osMatP P' mats osQpos lv.posOff k
  set m1 := osMatsAfter P' mats osQpos lv.posOff k
  set bp := osMatP P' m1 bd (lvl * ligColsCap) qp.2.2
  set j := bp.2.2
  have hst : (osResidual c ich bd ls lvl lv mats k).1 = qp.1 ++ bp.1 ++
      [.atom (.load (.n j) (.n osMus) lvl),
        .dispatch (.n osRate) ((c.lvAt lvl).map osResidualName) [.n qp.2.1, .n bp.2.1, .n j]
          [.n (j + 1)],
        .atom (.load (.n (j + 2)) (.n ich) lvl), .atom (.load (.n (j + 3)) (.n ls) lvl),
        .atom (.mul (.n (j + 4)) (.n (j + 3)) (.n (j + 1))),
        .atom (.add (.n (j + 5)) (.n (j + 2)) (.n (j + 4))),
        .atom (.load (.n (j + 5)) (.n ich) (lvl + 1))] := rfl
  have hm2 : (osResidual c ich bd ls lvl lv mats k).2.1 = osMatsAfter P' m1 bd (lvl * ligColsCap) qp.2.2 :=
    rfl
  rw [hst] at hok
  rw [hm2]
  rw [allOk_append, allOk_append] at hok
  obtain ⟨⟨hqp, hbp⟩, hrest⟩ := hok
  have k1 := osMatsAfter_ok hmats hpo hqp
  have eqp := osMatP_val hmats hpo hqp
  have ebp := osMatP_val k1 hlc hbp
  rw [allOk_cons, allOk_cons] at hrest
  obtain ⟨hm, hdsp, hrest⟩ := hrest
  simp only [StmtOk, Atom.Holds] at hm
  simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds] at hrest
  obtain ⟨l0, l1, m2, a3, s4⟩ := hrest
  have hcall := dispatch_rate hrate osResidualName hdsp
  simp only [List.map_cons, List.map_nil] at hcall
  have hv := hLR _ _ hcall D P (fun s hs ↦ by rw [ebp, loadHolds_mul_gen_pow]; exact hD s hs)
    (fun i hi ↦ by rw [eqp, loadHolds_mul_gen_pow]; exact hP i hi)
  simp only [List.cons.injEq, and_true] at hv
  have hmu : σ (.n j) = mu := loadHolds_unique hm hM
  refine ⟨?_, osMatsAfter_ok k1 hlc hbp⟩
  rw [hv, hmu, ← hvan] at m2
  rw [a3, m2, loadHolds_unique l0 hI, loadHolds_unique l1 hL] at s4
  exact s4

end
end LeanVM.Guest.B1.Whir
