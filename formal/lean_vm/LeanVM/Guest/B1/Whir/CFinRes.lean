/-
  LeanVM.Guest.B1.Whir.CFinRes

  A level's residual sum, honestly.
-/

module

public import LeanVM.Guest.B1.Whir.CFinBases

/-!
# A level's residual sum, honestly

`osResidual_complete`: the level's slots of `query_positions` and its row of `basis_d`
materialized, `μ` read from `level_mus`, the dispatch on the rate into `level_residual` holding
of them and returning the chain `h` (`DispC`, a hypothesis), `inner[lvl + 1] = inner[lvl] +
scale·h` stored. `osResiduals_complete`: every level.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- The values after the level's sum: the inner value, the scale, the scaled sum, the new inner. -/
def resEndVals (I L sum : E) : List E := [I, L, L * sum, I + L * sum]

/-- The end of a level's residual: the inner value and the scale read, the new inner value
stored. -/
theorem resEnd_complete {ich ls e sv lvl : ℕ} (σ : Val) (hich : ich < e) (hls : ls < e)
    (hsv : sv < e) {I L : E} (hI : LoadHolds rd (σ (.n ich)) lvl I)
    (hL : LoadHolds rd (σ (.n ls)) lvl L)
    (hout : LoadHolds rd (σ (.n ich)) (lvl + 1) (I + L * σ (.n sv))) :
    BlkF C rd σ e (e + 4) (fun j ↦ (resEndVals I L (σ (.n sv))).getD (j - e) 0)
      [.atom (.load (.n e) (.n ich) lvl), .atom (.load (.n (e + 1)) (.n ls) lvl),
        .atom (.mul (.n (e + 2)) (.n (e + 1)) (.n sv)), .atom (.add (.n (e + 3)) (.n e) (.n (e + 2))),
        .atom (.load (.n (e + 3)) (.n ich) (lvl + 1))]
      (fun σ' ↦ AgreeBelow e σ σ') := by
  intro σ' ha hr
  have V : ∀ j < 4, σ' (.n (e + j)) = (resEndVals I L (σ (.n sv))).getD j 0 := fun j hj ↦ by
    rw [hr _ (by omega) (by omega)]; simp only [Nat.add_sub_cancel_left]
  have v0 := V 0 (by omega); have v1 := V 1 (by omega); have v2 := V 2 (by omega)
  have v3 := V 3 (by omega)
  simp only [resEndVals, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at v0 v1 v2 v3
  refine ⟨?_, ha⟩
  simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
  refine ⟨by rw [v0, ha _ hich]; exact hI, by rw [v1, ha _ hls]; exact hL,
    by rw [v2, v1, ha _ hsv], by rw [v3, v0, v2], by rw [v3, ha _ hich]; exact hout⟩



/-- The values of a level's residual: the two materializations, `μ`, the chain, the end. -/
def residualF (c : OsCfg) (_ich bd _ls lvl : ℕ) (lv : OsLv) (mats : List OsMat) (k : ℕ) (σ : Val)
    (M h I L : E) : ℕ → E :=
  let P := c.plan
  let qp := osMatP P mats osQpos lv.posOff k
  let m1 := osMatsAfter P mats osQpos lv.posOff k
  let bp := osMatP P m1 bd (lvl * ligColsCap) qp.2.2
  fun i ↦ if i < qp.2.2 then matPVal σ P mats osQpos lv.posOff k i
    else if i < bp.2.2 then matPVal σ P m1 bd (lvl * ligColsCap) qp.2.2 i
    else (([M, h] ++ resEndVals I L h).getD (i - bp.2.2) 0)

theorem osResidual_k (c : OsCfg) (ich bd ls lvl : ℕ) (lv : OsLv) (mats : List OsMat) (k : ℕ) :
    k + 6 ≤ (osResidual c ich bd ls lvl lv mats k).2.2 := by
  have h1 := osMatP_next c.plan mats osQpos lv.posOff k
  have h2 := osMatP_next c.plan (osMatsAfter c.plan mats osQpos lv.posOff k) bd (lvl * ligColsCap)
    (osMatP c.plan mats osQpos lv.posOff k).2.2
  show k + 6 ≤ (osMatP c.plan (osMatsAfter c.plan mats osQpos lv.posOff k) bd (lvl * ligColsCap)
    (osMatP c.plan mats osQpos lv.posOff k).2.2).2.2 + 6
  omega

/-- **A level's residual sum, honestly.** -/
theorem osResidual_complete {c : OsCfg} {lvl : ℕ} {lv : OsLv} {ich bd ls k : ℕ} {mats : List OsMat}
    (σ : Val) {R : E} (hR : σ (.n osRate) = R)
    (hk : 161 ≤ k) (hich : ich < k) (hbd : bd < k) (hls : ls < k)
    (hm : MatsOk σ mats) (hmb : MatsBelow k mats)
    (hpo : lv.posOff < u128Bound) (hlc : lvl * ligColsCap < u128Bound) {M h I L : E}
    (hM : LoadHolds rd (σ (.n osMus)) lvl M)
    (hD : DispC C rd R ((c.lvAt lvl).map osResidualName)
      [σ (.n osQpos) * gen ^ lv.posOff, σ (.n bd) * gen ^ (lvl * ligColsCap), M] [h])
    (hI : LoadHolds rd (σ (.n ich)) lvl I) (hLs : LoadHolds rd (σ (.n ls)) lvl L)
    (hout : LoadHolds rd (σ (.n ich)) (lvl + 1) (I + L * h)) :
    BlkF C rd σ k (osResidual c ich bd ls lvl lv mats k).2.2
      (residualF c ich bd ls lvl lv mats k σ M h I L) (osResidual c ich bd ls lvl lv mats k).1
      (fun σ' ↦ AgreeBelow k σ σ' ∧ MatsOk σ' (osResidual c ich bd ls lvl lv mats k).2.1 ∧
        MatsBelow (osResidual c ich bd ls lvl lv mats k).2.2 (osResidual c ich bd ls lvl lv mats k).2.1) := by
  set P := c.plan
  set qp := osMatP P mats osQpos lv.posOff k with hqp
  set m1 := osMatsAfter P mats osQpos lv.posOff k with hm1
  set bp := osMatP P m1 bd (lvl * ligColsCap) qp.2.2 with hbp
  set j := bp.2.2 with hj
  have o1 : k ≤ qp.2.2 := osMatP_next _ _ _ _ _
  have o2 : qp.2.2 ≤ j := osMatP_next _ _ _ _ _
  have hst : osResidual c ich bd ls lvl lv mats k = (qp.1 ++ bp.1 ++
      [.atom (.load (.n j) (.n osMus) lvl),
        .dispatch (.n osRate) ((c.lvAt lvl).map osResidualName) [.n qp.2.1, .n bp.2.1, .n j]
          [.n (j + 1)],
        .atom (.load (.n (j + 2)) (.n ich) lvl), .atom (.load (.n (j + 3)) (.n ls) lvl),
        .atom (.mul (.n (j + 4)) (.n (j + 3)) (.n (j + 1))),
        .atom (.add (.n (j + 5)) (.n (j + 2)) (.n (j + 4))),
        .atom (.load (.n (j + 5)) (.n ich) (lvl + 1))],
      osMatsAfter P m1 bd (lvl * ligColsCap) qp.2.2, j + 6) := rfl
  rw [hst]
  dsimp only
  have hfv : ∀ i, residualF c ich bd ls lvl lv mats k σ M h I L i =
      if i < qp.2.2 then matPVal σ P mats osQpos lv.posOff k i
      else if i < j then matPVal σ P m1 bd (lvl * ligColsCap) qp.2.2 i
      else (([M, h] ++ resEndVals I L h).getD (i - j) 0) := fun i ↦ rfl
  intro σ' ha hv
  have hm0 : MatsOk σ' mats := matsOk_agree hm hmb ha
  have rQ : RangeVals σ' k qp.2.2 (matPVal σ P mats osQpos lv.posOff k) :=
    rangeVals_sub (k' := j + 6) hv le_rfl (by omega) fun i h1 h2 ↦ by
      rw [hfv]; simp only [show i < qp.2.2 from h2, ↓reduceIte]
  obtain ⟨okQ, vQ⟩ := osMatP_complete (C := C) (rd := rd) hpo hm0
    (ha _ (show osQpos < k by unfold osQpos; omega)) rQ
  have hm1' : MatsOk σ' m1 := osMatsAfter_ok hm0 hpo okQ
  have rB : RangeVals σ' qp.2.2 j (matPVal σ P m1 bd (lvl * ligColsCap) qp.2.2) :=
    rangeVals_sub (k' := j + 6) hv o1 (by omega) fun i h1 h2 ↦ by
      rw [hfv]; simp only [show ¬ i < qp.2.2 by omega, show i < j from h2, ↓reduceIte]
  obtain ⟨okB, vB⟩ := osMatP_complete (C := C) (rd := rd) hlc hm1' (ha _ hbd) rB
  have hm2 : MatsOk σ' (osMatsAfter P m1 bd (lvl * ligColsCap) qp.2.2) := osMatsAfter_ok hm1' hlc okB
  have hB1 : MatsBelow (j + 6) m1 :=
    matsBelow_after hmb (by unfold osQpos; omega) (by omega) (by omega)
  have hB2 : MatsBelow (j + 6) (osMatsAfter P m1 bd (lvl * ligColsCap) qp.2.2) :=
    matsBelow_after hB1 (by omega) le_rfl (by omega)
  have tail : ∀ i < 6, σ' (.n (j + i)) = ([M, h] ++ resEndVals I L h).getD i 0 := fun i hi ↦ by
    rw [hv (j + i) (by omega) (by omega), hfv]
    simp only [show ¬ j + i < qp.2.2 by omega, show ¬ j + i < j by omega, ↓reduceIte,
      Nat.add_sub_cancel_left]
  have v0 := tail 0 (by omega); have v1 := tail 1 (by omega); have v2 := tail 2 (by omega)
  have v3 := tail 3 (by omega); have v4 := tail 4 (by omega); have v5 := tail 5 (by omega)
  simp only [resEndVals, List.cons_append, List.nil_append, List.getD_cons_zero,
    List.getD_cons_succ, Nat.add_zero] at v0 v1 v2 v3 v4 v5
  have eR' : σ' (.n osRate) = R := by rw [ha _ (by unfold osRate; omega), hR]
  refine ⟨?_, ha, hm2, hB2⟩
  simp only [allOk_append]
  refine ⟨⟨okQ, okB⟩, ?_⟩
  simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
  have hd : ([.n qp.2.1, .n bp.2.1, .n j] : List V).map σ' =
      [σ (.n osQpos) * gen ^ lv.posOff, σ (.n bd) * gen ^ (lvl * ligColsCap), M] := by
    simp only [List.map_cons, List.map_nil]; rw [vQ, vB, v0]
  have hr : ([.n (j + 1)] : List V).map σ' = [h] := by simp only [List.map_cons, List.map_nil]; rw [v1]
  refine ⟨by rw [v0, ha _ (show osMus < k by unfold osMus; omega)]; exact hM,
    hD σ' eR' [.n qp.2.1, .n bp.2.1, .n j] [.n (j + 1)] hd hr,
    by rw [v2, ha _ hich]; exact hI, by rw [v3, ha _ hls]; exact hLs, by rw [v4, v3, v1],
    by rw [v5, v2, v4], by rw [v5, ha _ hich]; exact hout⟩

/-- What a level's residual reads and stores, its honest data named: `μ`, the chain `h` the
dispatch returns, the inner sums `I` and the scale `L`. -/
structure ResMem (C : CallRel) (rd : Reader) (σ : Val) (R : E) (c : OsCfg) (ich bd ls lvl : ℕ)
    (lv : OsLv) (M h I L : E) : Prop where
  hpo : lv.posOff < u128Bound
  hlc : lvl * ligColsCap < u128Bound
  hM : LoadHolds rd (σ (.n osMus)) lvl M
  hD : DispC C rd R ((c.lvAt lvl).map osResidualName)
    [σ (.n osQpos) * gen ^ lv.posOff, σ (.n bd) * gen ^ (lvl * ligColsCap), M] [h]
  hI : LoadHolds rd (σ (.n ich)) lvl I
  hLs : LoadHolds rd (σ (.n ls)) lvl L
  hout : LoadHolds rd (σ (.n ich)) (lvl + 1) (I + L * h)

/-- The values of every level's residual. -/
def residualsF (c : OsCfg) (ich bd ls : ℕ) (M h I L : ℕ → E) :
    ℕ → List OsLv → List OsMat → ℕ → Val → ℕ → E
  | lvl, lv :: rest, mats, k, σ =>
    seqF σ k (osResidual c ich bd ls lvl lv mats k).2.2
      (residualF c ich bd ls lvl lv mats k σ (M lvl) (h lvl) (I lvl) (L lvl))
      fun σ1 ↦ residualsF c ich bd ls M h I L (lvl + 1) rest (osResidual c ich bd ls lvl lv mats k).2.1
        (osResidual c ich bd ls lvl lv mats k).2.2 σ1
  | _, [], _, _, _ => fun _ ↦ 0

theorem osResiduals_k (c : OsCfg) (ich bd ls : ℕ) : ∀ (lvl : ℕ) (levels : List OsLv)
    (mats : List OsMat) (k : ℕ), k ≤ (osResiduals c ich bd ls lvl levels mats k).2
  | _, [], _, _ => le_rfl
  | lvl, lv :: rest, mats, k => by
    simp only [osResiduals]
    have := osResidual_k c ich bd ls lvl lv mats k
    have := osResiduals_k c ich bd ls (lvl + 1) rest (osResidual c ich bd ls lvl lv mats k).2.1
      (osResidual c ich bd ls lvl lv mats k).2.2
    omega

/-- **Every level's residual sum, honestly.** -/
theorem osResiduals_complete {c : OsCfg} {ich bd ls : ℕ} {R : E} (M h I L : ℕ → E) :
    ∀ (levels : List OsLv) (lvl : ℕ) (mats : List OsMat) (k : ℕ) (σ : Val), σ (.n osRate) = R →
      161 ≤ k → ich < k → bd < k → ls < k → MatsOk σ mats → MatsBelow k mats →
      (∀ i (hi : i < levels.length), ResMem C rd σ R c ich bd ls (lvl + i) levels[i]
        (M (lvl + i)) (h (lvl + i)) (I (lvl + i)) (L (lvl + i))) →
      BlkF C rd σ k (osResiduals c ich bd ls lvl levels mats k).2
        (residualsF c ich bd ls M h I L lvl levels mats k σ) (osResiduals c ich bd ls lvl levels mats k).1
        (fun σ' ↦ AgreeBelow k σ σ')
  | [], lvl, mats, k, σ, _, _, _, _, _, _, _, _ => by
    simp only [osResiduals]; exact BlkF.nil fun _ h ↦ h
  | lv :: rest, lvl, mats, k, σ, hR, hk, hich, hbd, hls, hm, hmb, hh => by
    have h0 := hh 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    have hA := osResidual_complete (C := C) (rd := rd) (c := c) (lvl := lvl) (lv := lv) (ich := ich)
      (bd := bd) (ls := ls) (k := k) (mats := mats) σ hR hk hich hbd hls hm hmb h0.hpo h0.hlc h0.hM
      h0.hD h0.hI h0.hLs h0.hout
    simp only [osResiduals, residualsF]
    have hk1 := osResidual_k c ich bd ls lvl lv mats k
    have hk2 := osResiduals_k c ich bd ls (lvl + 1) rest (osResidual c ich bd ls lvl lv mats k).2.1
      (osResidual c ich bd ls lvl lv mats k).2.2
    refine BlkF.then (k1 := (osResidual c ich bd ls lvl lv mats k).2.2) (by omega) hk2 hA
      fun σ1 _ ⟨ha1, hm1, hmb1⟩ ↦ ?_
    have e : ∀ v, v < k → σ1 (.n v) = σ (.n v) := ha1
    refine BlkF.mono (osResiduals_complete M h I L rest (lvl + 1) _ _ σ1
      (by rw [e _ (by unfold osRate; omega), hR]) (by omega) (by omega)
      (by omega) (by omega) hm1 hmb1 fun i hi ↦ ?_) fun σ' ha2 i hi ↦ (ha2 i (by omega)).trans (ha1 i hi)
    have := hh (i + 1) (by simp; omega)
    rw [show lvl + (i + 1) = lvl + 1 + i by ring] at this
    have eq : σ1 (.n osQpos) = σ (.n osQpos) := e _ (show osQpos < k by unfold osQpos; omega)
    have em : σ1 (.n osMus) = σ (.n osMus) := e _ (show osMus < k by unfold osMus; omega)
    obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := this
    exact ⟨g1, g2, by rw [em]; exact g3, by rw [eq, e _ hbd]; exact g4,
      by rw [e _ hich]; exact g5, by rw [e _ hls]; exact g6, by rw [e _ hich]; exact g7⟩

end
end LeanVM.Guest.B1.Whir
