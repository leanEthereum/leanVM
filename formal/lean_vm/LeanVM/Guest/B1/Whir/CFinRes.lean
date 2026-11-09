/-
  LeanVM.Guest.B1.Whir.CFinRes

  A level's residual sum, honestly.
-/

module

public import LeanVM.Guest.B1.Whir.CFinResQ
public import LeanVM.Guest.B1.Whir.Residuals

/-!
# A level's residual sum, honestly

`osResidual_complete`: `μ` read from `level_mus`, the chain's buffer allocated at `RC` (its first
word zero, its word `n = queries / 8` the loop's chain `acc`), the loop called (a hypothesis on the
call relation), the remaining `queries % 8` queries inline (`osResSteps_complete`: each
`h ← (h + R(p))·μ`), `inner[lvl + 1] = inner[lvl] + scale·h` stored. `osResiduals_complete`: every
level.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- The values before the remaining queries: `μ`, the buffer, its first word, the loop's call, the
chain after the loop. -/
def resPreVals (n : ℕ) (M RC acc : E) : List E :=
  [M, gw (n + 1), RC, word 0 0 0, word 1 0 0, gw n, word 1 0 0 + gw n, word 1 0 0, gw n, acc]

/-- The part before the remaining queries. -/
def osResPre (c : OsCfg) (bd lvl : ℕ) (lv : OsLv) (k : ℕ) : List Stmt :=
  [.atom (.load (.n k) (.n osMus) lvl)] ++ osHeap (lv.queries / resBatch + 1) (k + 1) ++
    [.atom (.const (.n (k + 3)) (word 0 0 0)), .atom (.load (.n (k + 3)) (.n (k + 2)) 0)] ++
    osLoopCall (c.resLoop lvl) (lv.queries / resBatch) [osQpos, bd, k + 2, k] (k + 4) ++
    [.atom (.load (.n (k + 9)) (.n (k + 2)) (lv.queries / resBatch))]

/-- **The part before the remaining queries, honestly.** -/
theorem osResPre_complete {c : OsCfg} {lvl : ℕ} {lv : OsLv} {bd k : ℕ} (σ : Val) (M RC acc : E)
    (hk : 164 ≤ k) (hbd : bd < k) (hn : lv.queries / resBatch < u128Bound)
    (hM : LoadHolds rd (σ (.n osMus)) lvl M)
    (hL : IsInK (1 + gen ^ (lv.queries / resBatch)) ∧ (1 + gen ^ (lv.queries / resBatch) ≠ 0 →
      C (c.resLoop lvl) [1, gen ^ (lv.queries / resBatch), σ (.n osQpos), σ (.n bd), RC, M] []))
    (h0 : LoadHolds rd RC 0 0) (hacc : LoadHolds rd RC (lv.queries / resBatch) acc) :
    BlkF C rd σ k (k + 10) (fun j ↦ (resPreVals (lv.queries / resBatch) M RC acc).getD (j - k) 0)
      (osResPre c bd lvl lv k)
      (fun σ' ↦ σ' (.n (k + 9)) = acc ∧ σ' (.n k) = M ∧ AgreeBelow k σ σ') := by
  intro σ' ha hr
  have V : ∀ j < 10, σ' (.n (k + j)) = (resPreVals (lv.queries / resBatch) M RC acc).getD j 0 :=
    fun j hj ↦ by rw [hr _ (by omega) (by omega)]; simp only [Nat.add_sub_cancel_left]
  have v0 := V 0 (by omega); have v1 := V 1 (by omega); have v2 := V 2 (by omega)
  have v3 := V 3 (by omega); have v4 := V 4 (by omega); have v5 := V 5 (by omega)
  have v6 := V 6 (by omega); have v7 := V 7 (by omega); have v8 := V 8 (by omega)
  have v9 := V 9 (by omega)
  simp only [resPreVals, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  refine ⟨?_, v9, v0, ha⟩
  have hgn : gw (lv.queries / resBatch) = gen ^ (lv.queries / resBatch) := gw_eq hn
  simp only [osResPre, osHeap, osLoopCall, allOk_append, allOk_cons, allOk_nil, and_true, StmtOk,
    Atom.Holds, List.map_cons, List.map_nil, and_assoc]
  have eq1 : σ' (.n osQpos) = σ (.n osQpos) := ha _ (show osQpos < k by unfold osQpos; omega)
  have eq2 : σ' (.n osMus) = σ (.n osMus) := ha _ (show osMus < k by unfold osMus; omega)
  have eq3 := ha _ hbd
  refine ⟨by rw [v0, eq2]; exact hM, v1, v3, by rw [v3, v2, word_zero]; exact h0, v4, v5,
    by rw [v6, v4, v5], v7, v8, by rw [v6, word_one, hgn]; exact hL.1, fun h ↦ ?_,
    by rw [v9, v2]; exact hacc⟩
  rw [v6, word_one, hgn] at h
  rw [v7, v8, v2, v0, word_one, hgn, eq1, eq3]
  exact hL.2 h

theorem osResQuery_k (pos bd row vo n k : ℕ) :
    k + 2 ≤ (osResQuery pos bd row vo n k).2.2 ∧
      (osResQuery pos bd row vo n k).2.1 < (osResQuery pos bd row vo n k).2.2 := by
  have h := osResQ_k pos bd row vo (n - 1) 1 (k + 1) (k + 2)
  simp only [osResQuery]
  refine ⟨by omega, ?_⟩
  rcases Nat.eq_zero_or_pos (n - 1) with h0 | h0
  · rw [h.2.1 h0]; omega
  · rw [h.2.2 h0]; omega

/-- The values of one residual step from `k`: the position, its `residual_query`, the chain's
sum and product. -/
def resStepF (bd row vo ncols : ℕ) (D : ℕ → E) (M p hv : E) (k : ℕ) (σ : Val) : ℕ → E :=
  let e := (osResQuery k bd row vo ncols (k + 1)).2.2
  let R := residualProd (osVals vo ncols) p D ncols
  seqF σ k (k + 1) (fun _ ↦ p) fun σ1 ↦
  seqF σ1 (k + 1) e (resQueryF vo ncols k (k + 1) σ1 D) fun _ ↦
  fun i ↦ if i = e then hv + R else (hv + R) * M

/-- **One residual step, honestly.** -/
theorem osResStep_complete {pp bd row vo ncols mu j h k : ℕ} {D : ℕ → E} {M p hv PP BD : E}
    (σ : Val) (hn : 1 ≤ ncols) (hk : 6 ≤ k) (hpp : pp < k) (hbd : bd < k) (hh : h < k)
    (hmu : mu < k) (ePP : σ (.n pp) = PP) (eBD : σ (.n bd) = BD) (eh : σ (.n h) = hv)
    (eM : σ (.n mu) = M) (hp : LoadHolds rd PP j p)
    (hD : ∀ s < ncols, LoadHolds rd BD (row + s) (D s)) :
    BlkF C rd σ k (osResStep pp bd row vo ncols mu j h k).2.2 (resStepF bd row vo ncols D M p hv k σ)
      (osResStep pp bd row vo ncols mu j h k).1
      (fun σ' ↦ σ' (.n (osResStep pp bd row vo ncols mu j h k).2.1) =
        (hv + residualProd (osVals vo ncols) p D ncols) * M ∧ AgreeBelow k σ σ') := by
  obtain ⟨he1, he2⟩ := osResQuery_k k bd row vo ncols (k + 1)
  set e := osResQuery k bd row vo ncols (k + 1) with hedef
  set R := residualProd (osVals vo ncols) p D ncols
  have est : (osResStep pp bd row vo ncols mu j h k).1 = [.atom (.load (.n k) (.n pp) j)] ++
      (e.1 ++ [.atom (.add (.n e.2.2) (.n h) (.n e.2.1)), .atom (.mul (.n (e.2.2 + 1)) (.n e.2.2) (.n mu))]) := by
    simp only [osResStep, List.append_assoc]; rfl
  have ek : (osResStep pp bd row vo ncols mu j h k).2 = (e.2.2 + 1, e.2.2 + 2) := rfl
  rw [est, ek]
  unfold resStepF
  have hA : BlkF C rd σ k (k + 1) (fun _ ↦ p) [.atom (.load (.n k) (.n pp) j)]
      (fun σ' ↦ σ' (.n k) = p ∧ AgreeBelow k σ σ') := by
    intro σ' ha hr
    have v := hr k le_rfl (by omega)
    refine ⟨?_, v, ha⟩
    simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
    rw [v, ha _ hpp, ePP]; exact hp
  refine BlkF.then (k1 := k + 1) (by omega) (by omega) hA fun σ1 _ ⟨h1, ha1⟩ ↦ ?_
  have hQ := osResQuery_complete (C := C) (rd := rd) (pos := k) (bd := bd) (row := row) (vo := vo)
    (n := ncols) (k := k + 1) (D := D) σ1 hn (by omega) (by omega) (by omega)
    (fun s hs ↦ by rw [ha1 _ hbd, eBD]; exact hD s hs)
  refine BlkF.then (k1 := e.2.2) (by omega) (by omega) hQ fun σ2 _ ⟨h2, ha2⟩ ↦ ?_
  rw [h1] at h2
  intro σ' ha hr
  have v0 := hr e.2.2 le_rfl (by omega)
  have v1 := hr (e.2.2 + 1) (by omega) (by omega)
  try rw [← hedef] at v0 v1 h2
  beta_reduce at v0 v1
  simp only [show e.2.2 + 1 ≠ e.2.2 by omega, ↓reduceIte] at v0 v1
  have eh' : σ' (.n h) = hv := by rw [ha _ (by omega), ha2 _ (by omega), ha1 _ hh, eh]
  have eM' : σ' (.n mu) = M := by rw [ha _ (by omega), ha2 _ (by omega), ha1 _ hmu, eM]
  have eR : σ' (.n e.2.1) = R := by rw [ha _ he2, h2]
  refine ⟨?_, show σ' (.n (e.2.2 + 1)) = (hv + R) * M from v1,
    fun i hi ↦ (ha i (by omega)).trans ((ha2 i (by omega)).trans (ha1 i hi))⟩
  simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
  exact ⟨by rw [v0, eh', eR], by rw [v1, v0, eM']⟩

/-- The values of the residual steps from `k`, the chain at `hv`. -/
def resStepsF (bd row vo ncols : ℕ) (D : ℕ → E) (M : E) : List E → E → ℕ → Val → ℕ → E
  | [], _, _, _ => fun _ ↦ 0
  | p :: ps, hv, k, σ =>
    let e := (osResQuery k bd row vo ncols (k + 1)).2.2
    seqF σ k (e + 2) (resStepF bd row vo ncols D M p hv k σ) fun σ1 ↦
      resStepsF bd row vo ncols D M ps ((hv + residualProd (osVals vo ncols) p D ncols) * M) (e + 2) σ1

theorem osResSteps_k (pp bd row vo ncols mu : ℕ) : ∀ (js : List ℕ) (h k : ℕ), h < k →
    k ≤ (osResSteps pp bd row vo ncols mu js h k).2.2 ∧
      (osResSteps pp bd row vo ncols mu js h k).2.1 < (osResSteps pp bd row vo ncols mu js h k).2.2
  | [], h, k, hh => ⟨le_rfl, hh⟩
  | j :: js, h, k, _ => by
    have := osResQuery_k k bd row vo ncols (k + 1)
    have ih := osResSteps_k pp bd row vo ncols mu js
      ((osResQuery k bd row vo ncols (k + 1)).2.2 + 1) ((osResQuery k bd row vo ncols (k + 1)).2.2 + 2)
      (by omega)
    show k ≤ (osResSteps pp bd row vo ncols mu js ((osResQuery k bd row vo ncols (k + 1)).2.2 + 1)
      ((osResQuery k bd row vo ncols (k + 1)).2.2 + 2)).2.2 ∧ _
    exact ⟨by omega, ih.2⟩

/-- **The residual steps, honestly.** -/
theorem osResSteps_complete {pp bd row vo ncols mu : ℕ} {D : ℕ → E} {M PP BD : E} (hn : 1 ≤ ncols) :
    ∀ (js : List ℕ) (ps : List E) (h k : ℕ) (hv : E) (σ : Val), 6 ≤ k → pp < k → bd < k → h < k →
      mu < k → σ (.n pp) = PP → σ (.n bd) = BD → σ (.n h) = hv → σ (.n mu) = M →
      List.Forall₂ (fun j p ↦ LoadHolds rd PP j p) js ps →
      (∀ s < ncols, LoadHolds rd BD (row + s) (D s)) →
      BlkF C rd σ k (osResSteps pp bd row vo ncols mu js h k).2.2
        (resStepsF bd row vo ncols D M ps hv k σ) (osResSteps pp bd row vo ncols mu js h k).1
        (fun σ' ↦ σ' (.n (osResSteps pp bd row vo ncols mu js h k).2.1) = resFold D vo ncols M hv ps ∧
          AgreeBelow k σ σ')
  | [], [], h, k, hv, σ, _, _, _, hh, _, _, _, eh, _, _, _ => by
    simp only [osResSteps]
    exact BlkF.nil fun σ' ha ↦ ⟨by rw [ha _ hh, eh]; rfl, ha⟩
  | j :: js, p :: ps, h, k, hv, σ, hk, hpp, hbd, hh, hmu, ePP, eBD, eh, eM, hF, hD => by
    obtain ⟨-, hFs⟩ := List.forall₂_cons.mp hF
    have hp := (List.forall₂_cons.mp hF).1
    have hA := osResStep_complete (C := C) (rd := rd) (pp := pp) (bd := bd) (row := row) (vo := vo)
      (ncols := ncols) (mu := mu) (j := j) (h := h) (k := k) (D := D) σ hn hk hpp hbd hh hmu ePP eBD
      eh eM hp hD
    have hqk := osResQuery_k k bd row vo ncols (k + 1)
    set e := osResQuery k bd row vo ncols (k + 1) with hedef
    have e1 : (osResStep pp bd row vo ncols mu j h k).2 = (e.2.2 + 1, e.2.2 + 2) := rfl
    rw [e1] at hA
    dsimp only at hA
    have hk2 := (osResSteps_k pp bd row vo ncols mu js (e.2.2 + 1) (e.2.2 + 2) (by omega)).1
    have eS : osResSteps pp bd row vo ncols mu (j :: js) h k =
        ((osResStep pp bd row vo ncols mu j h k).1 ++
          (osResSteps pp bd row vo ncols mu js (e.2.2 + 1) (e.2.2 + 2)).1,
          (osResSteps pp bd row vo ncols mu js (e.2.2 + 1) (e.2.2 + 2)).2) := rfl
    have eF : resStepsF bd row vo ncols D M (p :: ps) hv k σ = seqF σ k (e.2.2 + 2)
        (resStepF bd row vo ncols D M p hv k σ) (fun σ1 ↦ resStepsF bd row vo ncols D M ps
          ((hv + residualProd (osVals vo ncols) p D ncols) * M) (e.2.2 + 2) σ1) := rfl
    rw [eS, eF]
    dsimp only
    have hB : ∀ σ1, AgreeBelow k σ σ1 →
        (σ1 (.n (e.2.2 + 1)) = (hv + residualProd (osVals vo ncols) p D ncols) * M ∧
          AgreeBelow k σ σ1) →
        BlkF C rd σ1 (e.2.2 + 2) (osResSteps pp bd row vo ncols mu js (e.2.2 + 1) (e.2.2 + 2)).2.2
          (resStepsF bd row vo ncols D M ps ((hv + residualProd (osVals vo ncols) p D ncols) * M)
            (e.2.2 + 2) σ1)
          (osResSteps pp bd row vo ncols mu js (e.2.2 + 1) (e.2.2 + 2)).1
          (fun σ' ↦ σ' (.n (osResSteps pp bd row vo ncols mu js (e.2.2 + 1) (e.2.2 + 2)).2.1) =
            resFold D vo ncols M ((hv + residualProd (osVals vo ncols) p D ncols) * M) ps ∧
            AgreeBelow k σ σ') := fun σ1 _ ⟨h1, ha1⟩ ↦
      BlkF.mono (osResSteps_complete hn js ps (e.2.2 + 1) (e.2.2 + 2) _ σ1 (by omega) (by omega)
        (by omega) (by omega) (by omega) (by rw [ha1 _ hpp, ePP]) (by rw [ha1 _ hbd, eBD]) h1
        (by rw [ha1 _ hmu, eM]) hFs hD) fun σ' ⟨hv', ha2⟩ ↦
          ⟨hv', fun i hi ↦ (ha2 i (by omega)).trans (ha1 i hi)⟩
    refine BlkF.mono (BlkF.seq (k1 := e.2.2 + 2) (by omega) hk2 hA hB)
      fun σ' ⟨_, hv', ha2⟩ ↦ ⟨?_, ha2⟩
    rw [hv']; simp [resFold, List.foldl_cons]
  | [], _ :: _, _, _, _, _, _, _, _, _, _, _, _, _, _, hF, _ => by cases hF
  | _ :: _, [], _, _, _, _, _, _, _, _, _, _, _, _, _, hF, _ => by cases hF

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


/-- A level's remaining queries' steps. -/
abbrev resTl (lvl : ℕ) (lv : OsLv) (bd k : ℕ) : List Stmt × ℕ × ℕ :=
  osResSteps osQpos bd (lvl * ligColsCap) lv.vanish lv.logCols k (osResTail lv) (k + 9) (k + 10)

theorem osResidual_eq (c : OsCfg) (ich bd ls lvl : ℕ) (lv : OsLv) (k : ℕ) :
    osResidual c ich bd ls lvl lv k =
      (osResPre c bd lvl lv k ++ ((resTl lvl lv bd k).1 ++
        [.atom (.load (.n (resTl lvl lv bd k).2.2) (.n ich) lvl),
          .atom (.load (.n ((resTl lvl lv bd k).2.2 + 1)) (.n ls) lvl),
          .atom (.mul (.n ((resTl lvl lv bd k).2.2 + 2)) (.n ((resTl lvl lv bd k).2.2 + 1))
            (.n (resTl lvl lv bd k).2.1)),
          .atom (.add (.n ((resTl lvl lv bd k).2.2 + 3)) (.n (resTl lvl lv bd k).2.2)
            (.n ((resTl lvl lv bd k).2.2 + 2))),
          .atom (.load (.n ((resTl lvl lv bd k).2.2 + 3)) (.n ich) (lvl + 1))]),
        (resTl lvl lv bd k).2.2 + 4) := by
  simp only [osResidual, osResPre, List.append_assoc]

/-- The values of a level's residual. -/
def residualF (_c : OsCfg) (lvl : ℕ) (lv : OsLv) (bd k : ℕ) (σ : Val) (RC acc M I L : E)
    (P D : ℕ → E) : ℕ → E :=
  seqF σ k (k + 10) (fun j ↦ (resPreVals (lv.queries / resBatch) M RC acc).getD (j - k) 0) fun σ1 ↦
  seqF σ1 (k + 10) (resTl lvl lv bd k).2.2
    (resStepsF bd (lvl * ligColsCap) lv.vanish lv.logCols D M
      ((List.range (lv.queries % resBatch)).map P) acc (k + 10) σ1) fun σ2 ↦
  fun j ↦ (resEndVals I L (σ2 (.n (resTl lvl lv bd k).2.1))).getD (j - (resTl lvl lv bd k).2.2) 0

theorem forall₂_resTail (lv : OsLv) {Q : E} {P : ℕ → E}
    (hP : ∀ i < lv.queries % resBatch,
      LoadHolds rd Q (lv.posOff + (lv.queries - lv.queries % resBatch) + i) (P i)) :
    List.Forall₂ (fun j p ↦ LoadHolds rd Q j p) (osResTail lv)
      ((List.range (lv.queries % resBatch)).map P) := by
  unfold osResTail
  rw [List.forall₂_iff_get]
  refine ⟨by simp, fun i h1 h2 ↦ ?_⟩
  simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range]
  simp only [List.length_map, List.length_range] at h1
  exact hP i h1

/-- **A level's residual sum, honestly.** -/
theorem osResidual_complete {c : OsCfg} {lvl : ℕ} {lv : OsLv} {ich bd ls k : ℕ} (σ : Val)
    (hk : 164 ≤ k) (hich : ich < k) (hbd : bd < k) (hls : ls < k) (hml : 1 ≤ lv.logCols)
    (hn : lv.queries / resBatch < u128Bound) (RC acc M : E)
    (hM : LoadHolds rd (σ (.n osMus)) lvl M)
    (hL : IsInK (1 + gen ^ (lv.queries / resBatch)) ∧ (1 + gen ^ (lv.queries / resBatch) ≠ 0 →
      C (c.resLoop lvl) [1, gen ^ (lv.queries / resBatch), σ (.n osQpos), σ (.n bd), RC, M] []))
    (h0 : LoadHolds rd RC 0 0) (hacc : LoadHolds rd RC (lv.queries / resBatch) acc)
    {P D : ℕ → E}
    (hP : ∀ i < lv.queries % resBatch,
      LoadHolds rd (σ (.n osQpos)) (lv.posOff + (lv.queries - lv.queries % resBatch) + i) (P i))
    (hD : ∀ s < lv.logCols, LoadHolds rd (σ (.n bd)) (lvl * ligColsCap + s) (D s))
    {I L : E} (hI : LoadHolds rd (σ (.n ich)) lvl I) (hLs : LoadHolds rd (σ (.n ls)) lvl L)
    (hout : LoadHolds rd (σ (.n ich)) (lvl + 1)
      (I + L * resFold D lv.vanish lv.logCols M acc ((List.range (lv.queries % resBatch)).map P))) :
    BlkF C rd σ k (osResidual c ich bd ls lvl lv k).2 (residualF c lvl lv bd k σ RC acc M I L P D)
      (osResidual c ich bd ls lvl lv k).1 (fun σ' ↦ AgreeBelow k σ σ') := by
  rw [osResidual_eq]
  dsimp only
  unfold residualF
  have hpre := osResPre_complete (C := C) (rd := rd) (c := c) (lvl := lvl) (lv := lv) (bd := bd)
    (k := k) σ M RC acc hk hbd hn hM hL h0 hacc
  have htk : k + 10 ≤ (resTl lvl lv bd k).2.2 ∧ (resTl lvl lv bd k).2.1 < (resTl lvl lv bd k).2.2 :=
    osResSteps_k osQpos bd (lvl * ligColsCap) lv.vanish lv.logCols k (osResTail lv) (k + 9)
      (k + 10) (by omega)
  refine BlkF.then (k1 := k + 10) (by omega) (by omega) hpre fun σ1 _ ⟨h9, hk0, ha1⟩ ↦ ?_
  have hS := osResSteps_complete (C := C) (rd := rd) (pp := osQpos) (bd := bd) (row := lvl * ligColsCap)
    (vo := lv.vanish) (ncols := lv.logCols) (mu := k) (D := D) (M := M) (PP := σ (.n osQpos))
    (BD := σ (.n bd)) hml (osResTail lv) ((List.range (lv.queries % resBatch)).map P) (k + 9) (k + 10)
    acc σ1 (by omega) (by unfold osQpos; omega) (by omega) (by omega) (by omega)
    (ha1 _ (by unfold osQpos; omega)) (ha1 _ hbd) h9 hk0 (forall₂_resTail lv hP) hD
  refine BlkF.then (k1 := (resTl lvl lv bd k).2.2) htk.1 (by omega) hS fun σ2 _ ⟨hs, ha2⟩ ↦ ?_
  have e2 : ∀ v, v < k → σ2 (.n v) = σ (.n v) := fun v hv ↦ (ha2 v (by omega)).trans (ha1 v hv)
  refine BlkF.mono (resEnd_complete (C := C) (rd := rd) (ich := ich) (ls := ls)
    (e := (resTl lvl lv bd k).2.2) (sv := (resTl lvl lv bd k).2.1) (lvl := lvl) σ2
    (by omega) (by omega) htk.2 (by rw [e2 _ hich]; exact hI) (by rw [e2 _ hls]; exact hLs)
    (by rw [e2 _ hich, hs]; exact hout)) fun σ' ha3 i hi ↦
      (ha3 i (by omega)).trans ((ha2 i (by omega)).trans (ha1 i hi))

/-- What a level's residual reads and stores, its honest data named: the chain's buffer `RC`, the
loop's chain `acc`, `μ`, the remaining queries' positions `P`, the row's words `D`. -/
structure ResMem (C : CallRel) (rd : Reader) (σ : Val) (c : OsCfg) (ich bd ls lvl : ℕ) (lv : OsLv)
    (RC acc M I L : E) (P D : ℕ → E) : Prop where
  hml : 1 ≤ lv.logCols
  hn : lv.queries / resBatch < u128Bound
  hM : LoadHolds rd (σ (.n osMus)) lvl M
  hL : IsInK (1 + gen ^ (lv.queries / resBatch)) ∧ (1 + gen ^ (lv.queries / resBatch) ≠ 0 →
    C (c.resLoop lvl) [1, gen ^ (lv.queries / resBatch), σ (.n osQpos), σ (.n bd), RC, M] [])
  h0 : LoadHolds rd RC 0 0
  hacc : LoadHolds rd RC (lv.queries / resBatch) acc
  hP : ∀ i < lv.queries % resBatch,
    LoadHolds rd (σ (.n osQpos)) (lv.posOff + (lv.queries - lv.queries % resBatch) + i) (P i)
  hD : ∀ s < lv.logCols, LoadHolds rd (σ (.n bd)) (lvl * ligColsCap + s) (D s)
  hI : LoadHolds rd (σ (.n ich)) lvl I
  hLs : LoadHolds rd (σ (.n ls)) lvl L
  hout : LoadHolds rd (σ (.n ich)) (lvl + 1)
    (I + L * resFold D lv.vanish lv.logCols M acc ((List.range (lv.queries % resBatch)).map P))

/-- The values of every level's residual. -/
def residualsF (c : OsCfg) (bd : ℕ) (RC acc M I L : ℕ → E) (P D : ℕ → ℕ → E) :
    ℕ → List OsLv → ℕ → Val → ℕ → E
  | lvl, lv :: rest, k, σ =>
    seqF σ k (osResidual c 0 bd 0 lvl lv k).2
      (residualF c lvl lv bd k σ (RC lvl) (acc lvl) (M lvl) (I lvl) (L lvl) (P lvl) (D lvl))
      fun σ1 ↦ residualsF c bd RC acc M I L P D (lvl + 1) rest (osResidual c 0 bd 0 lvl lv k).2 σ1
  | _, [], _, _ => fun _ ↦ 0

theorem osResidual_k_eq (c : OsCfg) (ich bd ls lvl : ℕ) (lv : OsLv) (k : ℕ) :
    (osResidual c ich bd ls lvl lv k).2 = (osResidual c 0 bd 0 lvl lv k).2 := rfl

theorem osResidual_k (c : OsCfg) (ich bd ls lvl : ℕ) (lv : OsLv) (k : ℕ) :
    k + 14 ≤ (osResidual c ich bd ls lvl lv k).2 := by
  rw [osResidual_eq]
  have : k + 10 ≤ (resTl lvl lv bd k).2.2 :=
    (osResSteps_k osQpos bd (lvl * ligColsCap) lv.vanish lv.logCols k (osResTail lv) (k + 9)
      (k + 10) (by omega)).1
  show k + 14 ≤ (resTl lvl lv bd k).2.2 + 4
  omega

theorem osResiduals_k (c : OsCfg) (ich bd ls : ℕ) : ∀ (lvl : ℕ) (levels : List OsLv) (k : ℕ),
    k ≤ (osResiduals c ich bd ls lvl levels k).2
  | _, [], _ => le_rfl
  | lvl, lv :: rest, k => by
    simp only [osResiduals]
    have := osResidual_k c ich bd ls lvl lv k
    have := osResiduals_k c ich bd ls (lvl + 1) rest (osResidual c ich bd ls lvl lv k).2
    omega

/-- **Every level's residual sum, honestly.** -/
theorem osResiduals_complete {c : OsCfg} {ich bd ls : ℕ} (RC acc M I L : ℕ → E)
    (P D : ℕ → ℕ → E) : ∀ (levels : List OsLv) (lvl k : ℕ) (σ : Val), 164 ≤ k → ich < k → bd < k →
      ls < k → (∀ i (hi : i < levels.length), ResMem C rd σ c ich bd ls (lvl + i) levels[i]
        (RC (lvl + i)) (acc (lvl + i)) (M (lvl + i)) (I (lvl + i)) (L (lvl + i)) (P (lvl + i))
        (D (lvl + i))) →
      BlkF C rd σ k (osResiduals c ich bd ls lvl levels k).2
        (residualsF c bd RC acc M I L P D lvl levels k σ) (osResiduals c ich bd ls lvl levels k).1
        (fun σ' ↦ AgreeBelow k σ σ')
  | [], lvl, k, σ, _, _, _, _, _ => by
    simp only [osResiduals]; exact BlkF.nil fun _ h ↦ h
  | lv :: rest, lvl, k, σ, hk, hich, hbd, hls, h => by
    have h0 := h 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    have hA := osResidual_complete (C := C) (rd := rd) (c := c) (lvl := lvl) (lv := lv) (ich := ich)
      (bd := bd) (ls := ls) (k := k) σ hk hich hbd hls h0.hml h0.hn (RC lvl) (acc lvl) (M lvl) h0.hM
      h0.hL h0.h0 h0.hacc h0.hP h0.hD h0.hI h0.hLs h0.hout
    simp only [osResiduals, residualsF]
    rw [← osResidual_k_eq c ich bd ls lvl lv k]
    have hk1 := osResidual_k c ich bd ls lvl lv k
    have hk2 := osResiduals_k c ich bd ls (lvl + 1) rest (osResidual c ich bd ls lvl lv k).2
    refine BlkF.then (k1 := (osResidual c ich bd ls lvl lv k).2) (by omega) hk2 hA
      fun σ1 _ ha1 ↦ ?_
    refine BlkF.mono (osResiduals_complete RC acc M I L P D rest (lvl + 1) _ σ1 (by omega) (by omega)
      (by omega) (by omega) fun i hi ↦ ?_) fun σ' ha2 i hi ↦ (ha2 i (by omega)).trans (ha1 i hi)
    have := h (i + 1) (by simp; omega)
    rw [show lvl + (i + 1) = lvl + 1 + i by ring] at this
    have e : ∀ v, v < k → σ1 (.n v) = σ (.n v) := ha1
    have eq : σ1 (.n osQpos) = σ (.n osQpos) := e _ (show osQpos < k by unfold osQpos; omega)
    have em : σ1 (.n osMus) = σ (.n osMus) := e _ (show osMus < k by unfold osMus; omega)
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11⟩ := this
    exact ⟨g1, g2, by rw [em]; exact g3, by rw [eq, e _ hbd]; exact g4, g5, g6,
      fun i hi ↦ by rw [eq]; exact g7 i hi, fun s hs ↦ by rw [e _ hbd]; exact g8 s hs,
      by rw [e _ hich]; exact g9, by rw [e _ hls]; exact g10, by rw [e _ hich]; exact g11⟩

end
end LeanVM.Guest.B1.Whir
