/-
  LeanVM.Guest.B1.Whir.CResLoop

  The residual loop helper of a non-final level holds at its honest arguments.
-/

module

public import LeanVM.Guest.B1.Whir.CFinRs
public import LeanVM.Guest.B1.Whir.CLoop
public import LeanVM.Guest.CoreData
public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# The residual loop, honestly

`resLoop_iter`: at `x = g^j`, `j < N`, the loop body's statements before its recursive call hold
at the values they define (`evalV` with the memory `rdMem rd`): the batch's positions read at
`qpos·g^po·x^8`, the chains `chain[2j], chain[2j + 1]` advanced over them into
`chain[2j + 2], chain[2j + 3]` (`rcC`). `resLoop_complete`: the loop holds of `1, g^N` and its
arguments, entered behind its guard (`loop_complete`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

/-- The word a reader holds at `p·g^off` (`0` where it holds none). -/
def rdMem (rd : Reader) (p : E) (off : ℕ) : E := (rd (p.limb 0 * addressOfIndex off)).getD 0

theorem rdMem_of {rd : Reader} {p : E} {off : ℕ} {v : E} (h : LoadHolds rd p off v) :
    rdMem rd p off = v ∧ LoadHolds rd p off (rdMem rd p off) := by
  have e : rdMem rd p off = v := by unfold rdMem; rw [h.2]; rfl
  exact ⟨e, by rw [e]; exact h⟩

theorem readsAt_getDr {rd : Reader} {p : E} {xs : List E} (h : ReadsAt rd p xs) {j : ℕ}
    (hj : j < xs.length) : LoadHolds rd p j (xs.getD j 0) := by
  rw [List.getD_eq_getElem _ _ hj]; exact h j hj

theorem rcAt_succ (lv : OsLv) (D : ℕ → E) (hsv : List E) (Pos : ℕ → E) (mu : E) (j : ℕ) :
    rcAt lv D hsv Pos mu (j + 1) = resFold (resP lv D) (resH lv hsv) mu (rcAt lv D hsv Pos mu j)
      ((List.range resBatch).map fun i ↦ Pos (resBatch * j + i)) := by
  unfold rcAt
  rw [← resFold_append, show resBatch * (j + 1) = resBatch * j + resBatch by ring, List.range_add,
    List.map_append, List.map_map]
  rfl

/-! ## `x^resBatch`, honestly -/

/-- The square-and-multiply steps from `k` write `k, k + 1, …` in order, ending below. -/
theorem osPowSteps_ssaP (x : ℕ) : ∀ (ds : List Bool) (acc k : ℕ), acc < k → x < k →
    SsaP k (osPowSteps x ds acc k).1 (k + (ds.length + (ds.filter id).length)) ∧
      (osPowSteps x ds acc k).2 < k + (ds.length + (ds.filter id).length)
  | [], _, k, hak, _ => ⟨by simpa [osPowSteps] using (SsaP.nil (w := k)), by simpa [osPowSteps] using hak⟩
  | true :: ds, acc, k, hak, hxk => by
    obtain ⟨h1, h2⟩ := osPowSteps_ssaP x ds (k + 1) (k + 2) (by omega) (by omega)
    have e : k + ((true :: ds).length + ((true :: ds).filter id).length) =
        k + 2 + (ds.length + (ds.filter id).length) := by simp; omega
    rw [e]
    simp only [osPowSteps, ↓reduceIte]
    exact ⟨.mul le_rfl hak hak (.mul le_rfl (by omega) (by omega) h1), h2⟩
  | false :: ds, acc, k, hak, hxk => by
    obtain ⟨h1, h2⟩ := osPowSteps_ssaP x ds k (k + 1) (by omega) (by omega)
    have e : k + ((false :: ds).length + ((false :: ds).filter id).length) =
        k + 1 + (ds.length + (ds.filter id).length) := by simp; omega
    rw [e]
    simp only [osPowSteps, Bool.false_eq_true, ↓reduceIte]
    exact ⟨.mul le_rfl hak hak h1, h2⟩

theorem osPowSteps_loads (x : ℕ) : ∀ (ds : List Bool) (acc k : ℕ),
    loadsOf (osPowSteps x ds acc k).1 = []
  | [], _, _ => rfl
  | true :: ds, acc, k => by simpa [osPowSteps, osMul, loadsOf] using osPowSteps_loads x ds (k + 1) (k + 2)
  | false :: ds, acc, k => by simpa [osPowSteps, osMul, loadsOf] using osPowSteps_loads x ds k (k + 1)

theorem osBatchPow_ssaP (k : ℕ) (hk : 0 < k) :
    SsaP k (osBatchPow k).1 (k + batchLen) ∧ (osBatchPow k).2 < k + batchLen :=
  osPowSteps_ssaP 0 _ 0 k hk hk

theorem osBatchPow_loads (k : ℕ) : loadsOf (osBatchPow k).1 = [] := osPowSteps_loads 0 _ 0 k

/-- **One iteration of the residual loop, honestly**, at `x = g^j`. -/
theorem resLoop_iter {lvl : ℕ} {lv : OsLv} {hsv : List E} (hst : ResStatic lv hsv)
    (hpo : lv.posOff < u128Bound) {rd : Reader} {qpos bd hs chain mu N : E} {D Pos : ℕ → E} {j : ℕ}
    (hj : j < lv.queries / resBatch)
    (hpos : ∀ k < lv.queries, LoadHolds rd qpos (lv.posOff + k) (Pos k))
    (hD : ∀ t < lv.logCols, LoadHolds rd bd (lvl * ligColsCap + t) (D t))
    (hhs : ∀ c < lv.folds, LoadHolds rd hs (lvl * hsStride + c) (hsv.getD c 0))
    (hrc : ReadsAt rd chain (rcC lv D hsv Pos mu)) :
    ∃ σ : Val, (osParams 7).map σ = [gen ^ j, N, qpos, bd, hs, chain, mu] ∧
      AllOk (coreProgram.Rel rd) rd σ (resLoopA lvl lv ++ osLoopTailA (resLoopR lvl lv)) ∧
      σ (.n (resLoopR lvl lv + 2)) = gen ^ j * gen + N ∧
      (.n (resLoopR lvl lv + 4) :: (List.range (7 - 1)).map fun i ↦ V.n (i + 1)).map σ =
        gen ^ j * gen :: [N, qpos, bd, hs, chain, mu] := by
  unfold resLoopA resLoopR
  dsimp only
  generalize hjs : List.range resBatch = js
  have hx7 : 7 ≤ (osMat 2 lv.posOff 7).2.2 := osMat_next 2 lv.posOff 7
  have hp2 : (osMat 2 lv.posOff 7).2.1 < (osMat 2 lv.posOff 7).2.2 := osMat_ptr_lt 2 lv.posOff 7 (by omega)
  have hS0 : SsaP 7 (osMat 2 lv.posOff 7).1 (osMat 2 lv.posOff 7).2.2 := by
    unfold osMat; split_ifs
    · exact .nil
    · exact .const le_rfl (.mul (by omega) (by omega) (by omega) .nil)
  have hL0 : loadsOf (osMat 2 lv.posOff 7).1 = [] := by unfold osMat; split_ifs <;> rfl
  have hmv : ∀ (σ : Val) (C : CallRel), AllOk C rd σ (osMat 2 lv.posOff 7).1 →
      σ (.n (osMat 2 lv.posOff 7).2.1) = σ (.n 2) * gen ^ lv.posOff := fun _ _ h ↦ osMat_val hpo h
  generalize hpp : osMat 2 lv.posOff 7 = pp at hx7 hp2 hS0 hL0 hmv ⊢
  generalize hx : pp.2.2 = x at hx7 hp2 hS0 hL0 hmv ⊢
  obtain ⟨hB, hBl⟩ := osBatchPow_ssaP x (by omega)
  generalize hy : x + batchLen = y at hB hBl ⊢
  obtain ⟨t1, t2, t3, t4⟩ := osResSteps_ssa y 3 (lvl * ligColsCap) 4 (lvl * hsStride) lv.vanish
    lv.logCols lv.folds lv.highBits 6 (by have := hst.nhs; omega) (by have := hst.cols; omega)
    js (y + 3) (y + 4) (y + 5) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hval := fun (σ : Val) (C : CallRel)
      (hD' : ∀ s < lv.logCols, LoadHolds rd (σ (.n 3)) (lvl * ligColsCap + s) (D s))
      (hH' : ∀ c < lv.folds, LoadHolds rd (σ (.n 4)) (lvl * hsStride + c) (hsv.getD c 0)) ↦
    osResSteps_val (C := C) (σ := σ) (pp := y) (bd := 3) (ro := lvl * ligColsCap) (hp := 4)
      (ho := lvl * hsStride) (vo := lv.vanish) (mu := 6) hst.cols hst.nhs hst.b3 hst.bn hD' hst.len hH'
      js (y + 3) (y + 4) (y + 5)
  generalize hstd : osResSteps y 3 (lvl * ligColsCap) 4 (lvl * hsStride) lv.vanish lv.logCols
    lv.folds lv.highBits 6 js (y + 3) (y + 4) (y + 5) = st at t1 t2 t3 t4 hval ⊢
  generalize hr : st.2.2.2 = r at t1 t2 t3 ⊢
  -- the statements in order
  have hxy : x ≤ y := by have := hB.le; omega
  have hS1 : SsaP 7 (pp.1 ++ (osBatchPow x).1 ++ [osMul y pp.2.1 (osBatchPow x).2,
      osMul (y + 1) 5 0,
      osMul (y + 2) (y + 1) 0]) (y + 3) :=
    (hS0.append hB).append (.mul le_rfl (by omega) hBl (.mul (by omega) (by omega) (by omega)
      (.mul (by omega) (by omega) (by omega) .nil)))
  have hS2 : SsaP (y + 3) [osLd (y + 3) (y + 2) 0, osLd (y + 4) (y + 2) 1] (y + 5) :=
    .load le_rfl (by omega) (.load (by omega) (by omega) .nil)
  have hS3 : Ssa r [osLd st.2.1 (y + 2) 2, osLd st.2.2.1 (y + 2) 3] r :=
    .cons (.store t2 (by have := t1.le; omega)) (.cons (.store t3 (by have := t1.le; omega)) .nil)
  have hS4 : SsaP r (osLoopTailA r) (r + 5) :=
    .const le_rfl (.mul (by omega) (by omega) (by omega) (.add (by omega) (by omega) (by omega)
      (.const (by omega) (.mul (by omega) (by omega) (by omega) .nil))))
  have hP := (hS1.append hS2).append t1
  have hPS := hP.toSsa.append hS3
  have hS := hPS.append hS4.toSsa
  set A1 : List Stmt := pp.1 ++ (osBatchPow x).1 ++ [osMul y pp.2.1 (osBatchPow x).2,
      osMul (y + 1) 5 0, osMul (y + 2) (y + 1) 0] with hA1
  set P : List Stmt := A1 ++ [osLd (y + 3) (y + 2) 0, osLd (y + 4) (y + 2) 1] ++ st.1 with hPd
  set S3 : List Stmt := [osLd st.2.1 (y + 2) 2, osLd st.2.2.1 (y + 2) 3] with hS3d
  -- the valuation
  set v0 : ℕ → E := fun i ↦ [gen ^ j, N, qpos, bd, hs, chain, mu].getD i 0 with hv0
  set M := rdMem rd with hM
  set σ : Val := fun v ↦ evalV M (fun _ ↦ 0) 7 v0 ((P ++ S3) ++ osLoopTailA r) v.idx with hσ
  have hσP : ∀ i < r, σ (.n i) = evalV M (fun _ ↦ 0) 7 v0 P i := fun i hi ↦ by
    show evalV M (fun _ ↦ 0) 7 v0 ((P ++ S3) ++ osLoopTailA r) i = _
    rw [hPS.evalV_lt hS4.toSsa _ hi, hP.toSsa.evalV_lt hS3 _ hi]
  have hσ0 : ∀ i < 7, σ (.n i) = v0 i := fun i hi ↦ by
    show evalV M (fun _ ↦ 0) 7 v0 ((P ++ S3) ++ osLoopTailA r) i = _
    rw [hS.keep _ i hi]
  -- the first block: the batch's pointer and the chains' row
  have hA1s : SsaP 7 A1 (y + 3) := hS1
  have okA1 : AllOk (coreProgram.Rel rd) rd σ A1 := by
    refine ssa_allOk (M := M) (Pt := fun _ ↦ 0) hA1s.toSsa v0 σ (fun i hi ↦ ?_)
      (hA1s.sidesOk fun p o hpo ↦ ?_)
    · rw [hσP i (by have := t1.le; omega), hPd, (hA1s.append hS2).toSsa.evalV_lt t1.toSsa _ (by omega),
        hA1s.toSsa.evalV_lt hS2.toSsa _ hi]
    · simp only [hA1, loadsOf_append, hL0, osBatchPow_loads, List.nil_append, loadsOf,
        List.not_mem_nil] at hpo
  -- its values
  have okA1' := okA1
  simp only [hA1, allOk_append, allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_mul, osMul]
    at okA1'
  obtain ⟨⟨hpp1, hpw⟩, m3, m4, m5⟩ := okA1'
  have e0 : σ (.n 0) = gen ^ j := hσ0 0 (by omega)
  have e2 : σ (.n 2) = qpos := hσ0 2 (by omega)
  have e3 : σ (.n 3) = bd := hσ0 3 (by omega)
  have e4 : σ (.n 4) = hs := hσ0 4 (by omega)
  have e5 : σ (.n 5) = chain := hσ0 5 (by omega)
  have e6 : σ (.n 6) = mu := hσ0 6 (by omega)
  have hX3 : σ (.n y) = qpos * gen ^ (lv.posOff + resBatch * j) := by
    rw [m3, hmv σ _ hpp1, osBatchPow_val _ hpw, e0, e2, ← pow_mul, pow_add, Nat.mul_comm j]; ring
  have hX5 : σ (.n (y + 2)) = chain * gen ^ (2 * j) := by
    rw [m5, m4, e5, e0]; ring
  -- the memory
  have hnb := hj
  have hrcl : ∀ e < 2 * (lv.queries / resBatch + 1),
      LoadHolds rd chain e ((rcC lv D hsv Pos mu).getD e 0) := fun e he ↦
    readsAt_getDr hrc (by rw [rcC_length]; exact he)
  have hch : ∀ o < 4, ∃ v, LoadHolds rd (σ (.n (y + 2))) o v := fun o ho ↦
    ⟨_, by rw [hX5, loadHolds_mul_gen_pow]; exact hrcl (2 * j + o) (by omega)⟩
  have hQ : resBatch * j + resBatch ≤ lv.queries := by
    have := Nat.div_mul_le_self lv.queries resBatch
    have : (j + 1) * resBatch ≤ lv.queries / resBatch * resBatch := Nat.mul_le_mul_right _ hj
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm j] at this; omega
  have hpq : ∀ i < resBatch, LoadHolds rd (σ (.n y)) i (Pos (resBatch * j + i)) := fun i hi ↦ by
    rw [hX3, loadHolds_mul_gen_pow, Nat.add_assoc]; exact hpos _ (by omega)
  -- the pure part holds
  have okP : AllOk (coreProgram.Rel rd) rd σ P := by
    refine ssa_allOk (M := M) (Pt := fun _ ↦ 0) hP.toSsa v0 σ (fun i hi ↦ hσP i hi)
      (hP.sidesOk fun p o hpo ↦ ?_)
    simp only [hPd, hA1, loadsOf_append, hL0, osBatchPow_loads, List.nil_append, loadsOf,
        List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hpo
    rcases hpo with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | hpo
    · obtain ⟨v, hv⟩ := hch 0 (by omega); exact (rdMem_of hv).2
    · obtain ⟨v, hv⟩ := hch 1 (by omega); exact (rdMem_of hv).2
    · rcases t4 p o hpo with ⟨rfl, ho⟩ | ⟨rfl, s', hs', rfl⟩ | ⟨rfl, c', hc', rfl⟩
      · rw [← hjs, List.mem_range] at ho
        exact (rdMem_of (hpq o ho)).2
      · rw [e3]; exact (rdMem_of (hD s' hs')).2
      · rw [e4]; exact (rdMem_of (hhs c' hc')).2
  have okP' := okP
  simp only [hPd, allOk_append] at okP'
  obtain ⟨⟨-, okL2⟩, okSt⟩ := okP'
  simp only [allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_load, osLd] at okL2
  obtain ⟨l6, l7⟩ := okL2
  obtain ⟨g0, g1⟩ := rcC_get lv D hsv Pos mu (j := j) (by omega)
  obtain ⟨g2, g3⟩ := rcC_get lv D hsv Pos mu (j := j + 1) (by omega)
  have v6 : σ (.n (y + 3)) = (rcAt lv D hsv Pos mu j).1 := by
    have h := hrcl (2 * j) (by omega)
    rw [g0, ← Nat.add_zero (2 * j), ← loadHolds_mul_gen_pow, ← hX5] at h
    exact loadHolds_unique l6 h
  have v7 : σ (.n (y + 4)) = (rcAt lv D hsv Pos mu j).2 := by
    have h := hrcl (2 * j + 1) (by omega)
    rw [g1, ← loadHolds_mul_gen_pow, ← hX5] at h
    exact loadHolds_unique l7 h
  obtain ⟨ps, hF, hres⟩ := hval σ (coreProgram.Rel rd) (by rw [e3]; exact hD) (by rw [e4]; exact hhs) okSt
  rw [← hjs] at hF
  obtain ⟨hpl, hpF⟩ := forall₂_range_to _ _ hF
  have eps : ps = (List.range resBatch).map fun i ↦ Pos (resBatch * j + i) := by
    refine List.ext_getElem (by simp [hpl]) fun i h1 h2 ↦ ?_
    simp only [List.getElem_map, List.getElem_range]
    have := hpF i (by omega)
    rw [List.getD_eq_getElem _ _ h1] at this
    exact loadHolds_unique this (hpq i (by simpa using h2))
  have hst2 : (σ (.n st.2.1), σ (.n st.2.2.1)) = rcAt lv D hsv Pos mu (j + 1) := by
    rw [hres, v6, v7, e6, eps, rcAt_succ]
    rfl
  -- the stores
  have okS3 : AllOk (coreProgram.Rel rd) rd σ S3 := by
    simp only [hS3d, allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_load, osLd]
    refine ⟨?_, ?_⟩
    · have h1 := congrArg Prod.fst hst2
      simp only at h1
      rw [h1, hX5, loadHolds_mul_gen_pow, ← g2]
      exact hrcl _ (by omega)
    · have h1 := congrArg Prod.snd hst2
      simp only at h1
      rw [h1, hX5, loadHolds_mul_gen_pow, show 2 * j + 3 = 2 * (j + 1) + 1 by ring, ← g3]
      exact hrcl _ (by omega)
  -- the tail
  have okT : AllOk (coreProgram.Rel rd) rd σ (osLoopTailA r) := by
    refine ssa_allOk (M := M) (Pt := fun _ ↦ 0) hS4.toSsa (evalV M (fun _ ↦ 0) 7 v0 (P ++ S3)) σ
      (fun i _ ↦ ?_) (hS4.sidesOk fun p o hpo ↦ by simp [osLoopTailA, loadsOf] at hpo)
    show evalV M (fun _ ↦ 0) 7 v0 ((P ++ S3) ++ osLoopTailA r) i = _
    rw [hPS.evalV_append]
  obtain ⟨tr2, tr4⟩ := osLoopTailA_val okT
  refine ⟨σ, ?_, ?_, ?_, ?_⟩
  · simp only [osParams, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
      List.nil_append, List.cons_append]
    rw [hσ0 0 (by omega), hσ0 1 (by omega), hσ0 2 (by omega), hσ0 3 (by omega), hσ0 4 (by omega),
      hσ0 5 (by omega), hσ0 6 (by omega)]
    rfl
  · have h := allOk_append.mpr ⟨allOk_append.mpr ⟨okP, okS3⟩, okT⟩
    convert h using 2
    simp only [hPd, hA1, hS3d, List.append_assoc, List.cons_append, List.nil_append]
  · rw [tr2, e0, hσ0 1 (by omega)]; rfl
  · simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
      List.cons_append, Nat.zero_add, tr4, e0]
    rw [hσ0 1 (by omega), hσ0 2 (by omega), hσ0 3 (by omega), hσ0 4 (by omega), hσ0 5 (by omega),
      hσ0 6 (by omega)]
    rfl

/-- **The residual loop of a non-final level holds at its honest arguments**: entered at `1` with
the bound `g^(Q/resBatch)`, on memory holding the positions at `qpos·g^posOff`, the basis row at
`bd`,
the high part at `hs` and the chains' buffer (`rcC`) at `chain`. -/
theorem resLoop_complete {name : String} {lvl : ℕ} {lv : OsLv} {hsv : List E}
    (hfn : FnIs name (osParams 7) (resLoopBody lvl lv name))
    (hst : ResStatic lv hsv) (hpo : lv.posOff < u128Bound) (hn0 : 0 < lv.queries / resBatch)
    {rd : Reader} {qpos bd hs chain mu : E} {D Pos : ℕ → E}
    (hpos : ∀ k < lv.queries, LoadHolds rd qpos (lv.posOff + k) (Pos k))
    (hD : ∀ t < lv.logCols, LoadHolds rd bd (lvl * ligColsCap + t) (D t))
    (hhs : ∀ c < lv.folds, LoadHolds rd hs (lvl * hsStride + c) (hsv.getD c 0))
    (hrc : ReadsAt rd chain (rcC lv D hsv Pos mu)) :
    1 + gen ^ (lv.queries / resBatch) ≠ 0 →
      coreProgram.Rel rd name [1, gen ^ (lv.queries / resBatch), qpos, bd, hs, chain, mu] [] := by
  obtain ⟨fn, hf, hps, hb⟩ := hfn
  rw [resLoopBody_split] at hb
  have h := loop_complete (rd := rd) hf (resLoopA_flat lvl lv) hb (N := gen ^ (lv.queries / resBatch))
    (rest := [qpos, bd, hs, chain, mu]) hn0 rfl fun j hj ↦ by
      obtain ⟨σ, h1, h2, h3, h4⟩ := resLoop_iter (N := gen ^ (lv.queries / resBatch)) hst hpo hj hpos hD
        hhs hrc
      exact ⟨σ, by rw [hps]; exact h1, h2, h3, h4⟩
  exact h.2

end
end LeanVM.Guest.B1.Whir
