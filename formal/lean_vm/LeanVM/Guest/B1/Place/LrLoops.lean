/-
  LeanVM.Guest.B1.Place.LrLoops

  `level_residual`'s loops hold at their honest arguments.
-/

module

public import LeanVM.Guest.B1.Whir.CResLoop
public import LeanVM.Guest.B1.Whir.LrSound
public import LeanVM.Guest.CoreData
public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# `level_residual`'s loops, honestly

The chains run over the positions as the old residual loop's (`Whir/CResLoop.lean`), at the row
`lrRow q cols nhs hbits`: the batches' loop's buffer holds the chains after `8j` positions
(`rcC`), the rest's after `8·nb + j` (`rsC`).

* `lrLoop1_iter`, `lrLoop1_complete`: the batches' loop (`lrLoop1Body`), entered at `1` with the
  bound `g^(q/resBatch)`, on memory holding the positions, the basis row, the high part and `rcC`.
* `lrLoop2_iter`, `lrLoop2_complete`: the rest's loop (`lrLoop2Body`), entered at `1` with the
  bound `g^r`, on memory holding the rest's positions at `tail`, the basis row, the high part and
  `rsC`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

/-- The row of a level whose residual `level_residual` computes. -/
def lrRow (q cols nhs hbits : ℕ) : OsLv :=
  { (default : OsLv) with
    queries := q
    logCols := cols
    folds := nhs
    highBits := hbits
    vanish := cols * (cols + 1) / 2 }

/-! ## The batches' loop -/

set_option maxHeartbeats 800000 in
/-- **One iteration of the batches' loop, honestly**, at `x = g^j`. -/
theorem lrLoop1_iter {q cols nhs hbits : ℕ} {hsv : List E}
    (hst : ResStatic (lrRow q cols nhs hbits) hsv) {rd : Reader} {P CH BD HS mu N : E}
    {D Pos : ℕ → E} {j : ℕ} (hj : j < q / resBatch)
    (hpos : ∀ k < q, LoadHolds rd P k (Pos k))
    (hD : ∀ t < cols, LoadHolds rd BD t (D t))
    (hhs : ∀ c < nhs, LoadHolds rd HS c (hsv.getD c 0))
    (hrc : ReadsAt rd CH (rcC (lrRow q cols nhs hbits) D hsv Pos mu)) :
    ∃ σ : Val, (osParams 7).map σ = [gen ^ j, N, P, CH, BD, HS, mu] ∧
      AllOk (coreProgram.Rel rd) rd σ (lr1A cols nhs hbits ++ osLoopTailA (lr1St cols nhs hbits).2.2.2) ∧
      σ (.n ((lr1St cols nhs hbits).2.2.2 + 2)) = gen ^ j * gen + N ∧
      (.n ((lr1St cols nhs hbits).2.2.2 + 4) :: (List.range (7 - 1)).map fun i ↦ V.n (i + 1)).map σ =
        gen ^ j * gen :: [N, P, CH, BD, HS, mu] := by
  set lv := lrRow q cols nhs hbits with hlv
  have hc1 : 1 ≤ cols := hst.cols
  have hn1 : 1 ≤ nhs := hst.nhs
  have hb3 : hbits ≤ 3 := hst.b3
  have hbn : hbits ≤ cols + 1 := hst.bn
  have hlen : hsv.length = nhs := hst.len
  unfold lr1A lr1St
  generalize hjs : List.range resBatch = js
  obtain ⟨hB, hBl⟩ := osBatchPow_ssaP 7 (by omega)
  generalize hy : 7 + batchLen = y at hB hBl ⊢
  have hy7 : 7 ≤ y := hB.le
  obtain ⟨t1, t2, t3, t4⟩ := osResSteps_ssa y 4 0 5 0 (lrVo cols) cols nhs hbits 6 (by omega)
    (by omega) js (y + 3) (y + 4) (y + 5) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega)
  have hval := fun (σ : Val) (C : CallRel)
      (hD' : ∀ s < cols, LoadHolds rd (σ (.n 4)) (0 + s) (D s))
      (hH' : ∀ c < nhs, LoadHolds rd (σ (.n 5)) (0 + c) (hsv.getD c 0)) ↦
    osResSteps_val (C := C) (σ := σ) (pp := y) (bd := 4) (ro := 0) (hp := 5) (ho := 0)
      (vo := lrVo cols) (mu := 6) hc1 hn1 hb3 hbn hD' hlen hH' js (y + 3) (y + 4) (y + 5)
  generalize hstd : osResSteps y 4 0 5 0 (lrVo cols) cols nhs hbits 6 js (y + 3) (y + 4) (y + 5) =
      st
    at t1 t2 t3 t4 hval ⊢
  generalize hr : st.2.2.2 = r at t1 t2 t3 ⊢
  have hS1 : SsaP 7 ((osBatchPow 7).1 ++ [osMul y 2 (osBatchPow 7).2, osMul (y + 1) 3 0,
      osMul (y + 2) (y + 1) 0]) (y + 3) :=
    hB.append (.mul le_rfl (by omega) hBl (.mul (by omega) (by omega) (by omega)
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
  set A1 : List Stmt := (osBatchPow 7).1 ++ [osMul y 2 (osBatchPow 7).2, osMul (y + 1) 3 0,
      osMul (y + 2) (y + 1) 0] with hA1
  set P' : List Stmt := A1 ++ [osLd (y + 3) (y + 2) 0, osLd (y + 4) (y + 2) 1] ++ st.1 with hPd
  set S3 : List Stmt := [osLd st.2.1 (y + 2) 2, osLd st.2.2.1 (y + 2) 3] with hS3d
  set v0 : ℕ → E := fun i ↦ [gen ^ j, N, P, CH, BD, HS, mu].getD i 0 with hv0
  set M := rdMem rd with hM
  set σ : Val := fun v ↦ evalV M (fun _ ↦ 0) 7 v0 ((P' ++ S3) ++ osLoopTailA r) v.idx with hσ
  have hσP : ∀ i < r, σ (.n i) = evalV M (fun _ ↦ 0) 7 v0 P' i := fun i hi ↦ by
    show evalV M (fun _ ↦ 0) 7 v0 ((P' ++ S3) ++ osLoopTailA r) i = _
    rw [hPS.evalV_lt hS4.toSsa _ hi, hP.toSsa.evalV_lt hS3 _ hi]
  have hσ0 : ∀ i < 7, σ (.n i) = v0 i := fun i hi ↦ by
    show evalV M (fun _ ↦ 0) 7 v0 ((P' ++ S3) ++ osLoopTailA r) i = _
    rw [hS.keep _ i hi]
  -- the first block: the batch's pointer and the chains' row
  have okA1 : AllOk (coreProgram.Rel rd) rd σ A1 := by
    refine ssa_allOk (M := M) (Pt := fun _ ↦ 0) hS1.toSsa v0 σ (fun i hi ↦ ?_)
      (hS1.sidesOk fun p o hpo ↦ ?_)
    · rw [hσP i (by have := t1.le; omega), hPd, (hS1.append hS2).toSsa.evalV_lt t1.toSsa _ (by omega),
        hS1.toSsa.evalV_lt hS2.toSsa _ hi]
    · simp [hA1, loadsOf_append, osBatchPow_loads, loadsOf] at hpo
  have okA1' := okA1
  simp only [hA1, allOk_append, allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_mul, osMul]
    at okA1'
  obtain ⟨hpw, m3, m4, m5⟩ := okA1'
  have e0 : σ (.n 0) = gen ^ j := hσ0 0 (by omega)
  have e2 : σ (.n 2) = P := hσ0 2 (by omega)
  have e3 : σ (.n 3) = CH := hσ0 3 (by omega)
  have e4 : σ (.n 4) = BD := hσ0 4 (by omega)
  have e5 : σ (.n 5) = HS := hσ0 5 (by omega)
  have e6 : σ (.n 6) = mu := hσ0 6 (by omega)
  have hX10 : σ (.n y) = P * gen ^ (resBatch * j) := by
    rw [m3, osBatchPow_val _ hpw, e0, e2, ← pow_mul, Nat.mul_comm j]
  have hX12 : σ (.n (y + 2)) = CH * gen ^ (2 * j) := by
    rw [m5, m4, e3, e0]; ring
  -- the memory
  have hrcl : ∀ e < 2 * (q / resBatch + 1),
      LoadHolds rd CH e ((rcC lv D hsv Pos mu).getD e 0) := fun e he ↦
    readsAt_getDr hrc (by rw [rcC_length]; exact he)
  have hch : ∀ o < 4, ∃ v, LoadHolds rd (σ (.n (y + 2))) o v := fun o ho ↦
    ⟨_, by rw [hX12, loadHolds_mul_gen_pow]; exact hrcl (2 * j + o) (by omega)⟩
  have hQ : resBatch * j + resBatch ≤ q := by
    have := Nat.div_mul_le_self q resBatch
    have : (j + 1) * resBatch ≤ q / resBatch * resBatch := Nat.mul_le_mul_right _ hj
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm j] at this; omega
  have hpq : ∀ i < resBatch, LoadHolds rd (σ (.n y)) i (Pos (resBatch * j + i)) := fun i hi ↦ by
    rw [hX10, loadHolds_mul_gen_pow]; exact hpos _ (by omega)
  -- the pure part holds
  have okP : AllOk (coreProgram.Rel rd) rd σ P' := by
    refine ssa_allOk (M := M) (Pt := fun _ ↦ 0) hP.toSsa v0 σ (fun i hi ↦ hσP i hi)
      (hP.sidesOk fun p o hpo ↦ ?_)
    simp only [hPd, hA1, loadsOf_append, osBatchPow_loads, loadsOf, List.nil_append,
        List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hpo
    rcases hpo with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | hpo
    · obtain ⟨v, hv⟩ := hch 0 (by omega); exact (rdMem_of hv).2
    · obtain ⟨v, hv⟩ := hch 1 (by omega); exact (rdMem_of hv).2
    · rcases t4 p o hpo with ⟨rfl, ho⟩ | ⟨rfl, s', hs', rfl⟩ | ⟨rfl, c', hc', rfl⟩
      · rw [← hjs, List.mem_range] at ho
        exact (rdMem_of (hpq o ho)).2
      · rw [e4, Nat.zero_add]; exact (rdMem_of (hD s' hs')).2
      · rw [e5, Nat.zero_add]; exact (rdMem_of (hhs c' hc')).2
  have okP' := okP
  simp only [hPd, allOk_append] at okP'
  obtain ⟨⟨-, okL2⟩, okSt⟩ := okP'
  simp only [allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_load, osLd] at okL2
  obtain ⟨l13, l14⟩ := okL2
  obtain ⟨g0, g1⟩ := rcC_get lv D hsv Pos mu (j := j) (by show j ≤ q / resBatch; omega)
  obtain ⟨g2, g3⟩ := rcC_get lv D hsv Pos mu (j := j + 1) (by show j + 1 ≤ q / resBatch; omega)
  have v13 : σ (.n (y + 3)) = (rcAt lv D hsv Pos mu j).1 := by
    have h := hrcl (2 * j) (by omega)
    rw [g0, ← Nat.add_zero (2 * j), ← loadHolds_mul_gen_pow, ← hX12] at h
    exact loadHolds_unique l13 h
  have v14 : σ (.n (y + 4)) = (rcAt lv D hsv Pos mu j).2 := by
    have h := hrcl (2 * j + 1) (by omega)
    rw [g1, ← loadHolds_mul_gen_pow, ← hX12] at h
    exact loadHolds_unique l14 h
  obtain ⟨ps, hF, hres⟩ := hval σ (coreProgram.Rel rd) (by rw [e4]; simpa using hD)
    (by rw [e5]; simpa using hhs) okSt
  rw [← hjs] at hF
  obtain ⟨hpl, hpF⟩ := forall₂_range_to _ _ hF
  have eps : ps = (List.range resBatch).map fun i ↦ Pos (resBatch * j + i) := by
    refine List.ext_getElem (by simp [hpl]) fun i h1 h2 ↦ ?_
    simp only [List.getElem_map, List.getElem_range]
    have := hpF i (by omega)
    rw [List.getD_eq_getElem _ _ h1] at this
    exact loadHolds_unique this (hpq i (by simpa using h2))
  have hst2 : (σ (.n st.2.1), σ (.n st.2.2.1)) = rcAt lv D hsv Pos mu (j + 1) := by
    rw [hres, v13, v14, e6, eps, rcAt_succ]
    rfl
  -- the stores
  have okS3 : AllOk (coreProgram.Rel rd) rd σ S3 := by
    simp only [hS3d, allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_load, osLd]
    refine ⟨?_, ?_⟩
    · have h1 := congrArg Prod.fst hst2
      simp only at h1
      rw [h1, hX12, loadHolds_mul_gen_pow, ← g2]
      exact hrcl _ (by omega)
    · have h1 := congrArg Prod.snd hst2
      simp only at h1
      rw [h1, hX12, loadHolds_mul_gen_pow, show 2 * j + 3 = 2 * (j + 1) + 1 by ring, ← g3]
      exact hrcl _ (by omega)
  -- the tail
  have okT : AllOk (coreProgram.Rel rd) rd σ (osLoopTailA r) := by
    refine ssa_allOk (M := M) (Pt := fun _ ↦ 0) hS4.toSsa (evalV M (fun _ ↦ 0) 7 v0 (P' ++ S3)) σ
      (fun i _ ↦ ?_) (hS4.sidesOk fun p o hpo ↦ by simp [osLoopTailA, loadsOf] at hpo)
    show evalV M (fun _ ↦ 0) 7 v0 ((P' ++ S3) ++ osLoopTailA r) i = _
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

/-- **The batches' loop holds at its honest arguments**: entered at `1` with the bound
`g^(q/resBatch)`. -/
theorem lrLoop1_complete {name : String} {q cols nhs hbits : ℕ}
    (hfn : FnIs name (osParams 7) (lrLoop1Body cols nhs hbits name)) {hsv : List E}
    (hst : ResStatic (lrRow q cols nhs hbits) hsv) (hn0 : 0 < q / resBatch)
    {rd : Reader} {P CH BD HS mu : E} {D Pos : ℕ → E}
    (hpos : ∀ k < q, LoadHolds rd P k (Pos k))
    (hD : ∀ t < cols, LoadHolds rd BD t (D t))
    (hhs : ∀ c < nhs, LoadHolds rd HS c (hsv.getD c 0))
    (hrc : ReadsAt rd CH (rcC (lrRow q cols nhs hbits) D hsv Pos mu)) :
    1 + gen ^ (q / resBatch) ≠ 0 →
      coreProgram.Rel rd name [1, gen ^ (q / resBatch), P, CH, BD, HS, mu] [] := by
  obtain ⟨fn, hf, hps, hb⟩ := hfn
  rw [lrLoop1Body_split] at hb
  have h := loop_complete (rd := rd) hf (lr1A_flat cols nhs hbits) hb (N := gen ^ (q / resBatch))
    (rest := [P, CH, BD, HS, mu]) hn0 rfl fun j hj ↦ by
      obtain ⟨σ, h1, h2, h3, h4⟩ := lrLoop1_iter (N := gen ^ (q / resBatch)) hst hj hpos hD hhs hrc
      exact ⟨σ, by rw [hps]; exact h1, h2, h3, h4⟩
  exact h.2

/-! ## The rest's loop -/

/-- The chains after `8·nb + j` positions. -/
def rsAt (lv : OsLv) (D : ℕ → E) (hsv : List E) (Pos : ℕ → E) (mu : E) (nb j : ℕ) : E × E :=
  resFold (resP lv D) (resH lv hsv) mu (0, 0) ((List.range (resBatch * nb + j)).map Pos)

/-- **The rest's chains' buffer**: entries `2j`, `2j + 1` the chains after `8·nb + j` positions. -/
def rsC (lv : OsLv) (D : ℕ → E) (hsv : List E) (Pos : ℕ → E) (mu : E) (nb r : ℕ) : List E :=
  (List.range (2 * (r + 1))).map fun e ↦
    if e % 2 = 0 then (rsAt lv D hsv Pos mu nb (e / 2)).1 else (rsAt lv D hsv Pos mu nb (e / 2)).2

theorem rsC_length (lv : OsLv) (D : ℕ → E) (hsv : List E) (Pos : ℕ → E) (mu : E) (nb r : ℕ) :
    (rsC lv D hsv Pos mu nb r).length = 2 * (r + 1) := by simp [rsC]

theorem rsC_get (lv : OsLv) (D : ℕ → E) (hsv : List E) (Pos : ℕ → E) (mu : E) (nb r : ℕ) {j : ℕ}
    (hj : j ≤ r) :
    (rsC lv D hsv Pos mu nb r).getD (2 * j) 0 = (rsAt lv D hsv Pos mu nb j).1 ∧
      (rsC lv D hsv Pos mu nb r).getD (2 * j + 1) 0 = (rsAt lv D hsv Pos mu nb j).2 := by
  constructor
  · rw [List.getD_eq_getElem _ _ (by rw [rsC_length]; omega)]
    simp [rsC, show 2 * j / 2 = j by omega]
  · rw [List.getD_eq_getElem _ _ (by rw [rsC_length]; omega)]
    simp [rsC, show (2 * j + 1) / 2 = j by omega, show (2 * j + 1) % 2 = 1 by omega]

theorem rsAt_succ (lv : OsLv) (D : ℕ → E) (hsv : List E) (Pos : ℕ → E) (mu : E) (nb j : ℕ) :
    rsAt lv D hsv Pos mu nb (j + 1) =
      resFold (resP lv D) (resH lv hsv) mu (rsAt lv D hsv Pos mu nb j) [Pos (resBatch * nb + j)] := by
  unfold rsAt
  rw [← resFold_append, ← Nat.add_assoc, List.range_succ, List.map_append]
  rfl

set_option maxHeartbeats 800000 in
/-- **One iteration of the rest's loop, honestly**, at `x = g^j`. -/
theorem lrLoop2_iter {q cols nhs hbits : ℕ} {hsv : List E}
    (hst : ResStatic (lrRow q cols nhs hbits) hsv) {rd : Reader} {RS T BD HS mu N : E}
    {D Pos : ℕ → E} {nb r j : ℕ} (hj : j < r)
    (hpos : ∀ k < r, LoadHolds rd T k (Pos (resBatch * nb + k)))
    (hD : ∀ t < cols, LoadHolds rd BD t (D t))
    (hhs : ∀ c < nhs, LoadHolds rd HS c (hsv.getD c 0))
    (hrs : ReadsAt rd RS (rsC (lrRow q cols nhs hbits) D hsv Pos mu nb r)) :
    ∃ σ : Val, (osParams 7).map σ = [gen ^ j, N, RS, T, BD, HS, mu] ∧
      AllOk (coreProgram.Rel rd) rd σ
        (lr2A cols nhs hbits ++ osLoopTailA ((lr2Q cols nhs hbits).2.2.2 + 6)) ∧
      σ (.n ((lr2Q cols nhs hbits).2.2.2 + 6 + 2)) = gen ^ j * gen + N ∧
      (.n ((lr2Q cols nhs hbits).2.2.2 + 6 + 4) :: (List.range (7 - 1)).map fun i ↦ V.n (i + 1)).map σ =
        gen ^ j * gen :: [N, RS, T, BD, HS, mu] := by
  set lv := lrRow q cols nhs hbits with hlv
  have hc1 : 1 ≤ cols := hst.cols
  have hn1 : 1 ≤ nhs := hst.nhs
  have hb3 : hbits ≤ 3 := hst.b3
  have hbn : hbits ≤ cols + 1 := hst.bn
  have hlen : hsv.length = nhs := hst.len
  obtain ⟨q1, q2, q3, q4⟩ := osResQuery_ssa 10 4 0 5 0 (lrVo cols) cols nhs hbits 11 (by omega) (by omega)
    (by omega) (by omega) (by omega)
  have hqv := fun (σ : Val) (C : CallRel)
      (hD' : ∀ s < cols, LoadHolds rd (σ (.n 4)) (0 + s) (D s))
      (hH' : ∀ c < nhs, LoadHolds rd (σ (.n 5)) (0 + c) (hsv.getD c 0)) ↦
    osResQuery_val (C := C) (σ := σ) (pos := 10) (bd := 4) (ro := 0) (hp := 5) (ho := 0)
      (vo := lrVo cols) (k := 11) hc1 hn1 hb3 hbn hD' hlen hH'
  unfold lr2A
  simp only [lr2Q] at q1 q2 q3 q4 hqv ⊢
  generalize hqd : osResQuery 10 4 0 5 0 (lrVo cols) cols nhs hbits 11 = qq at q1 q2 q3 q4 hqv ⊢
  generalize he : qq.2.2.2 = e at q1 q2 q3 ⊢
  have hq1 := q1.le
  have hS1 : SsaP 7 [osMul 7 2 0, osMul 8 7 0, osMul 9 3 0, osLd 10 9 0] 11 :=
    .mul le_rfl (by omega) (by omega) (.mul (by omega) (by omega) (by omega) (.mul (by omega)
      (by omega) (by omega) (.load (by omega) (by omega) .nil)))
  have hR1 : SsaP e [osLd e 8 0, osAdd (e + 1) e qq.2.1, osMul (e + 2) (e + 1) 6] (e + 3) :=
    .load le_rfl (by omega) (.add (by omega) (by omega) (by omega) (.mul (by omega) (by omega)
      (by omega) .nil))
  have hW1 : Ssa (e + 3) [osLd (e + 2) 8 2] (e + 3) := .cons (.store (by omega) (by omega)) .nil
  have hR2 : SsaP (e + 3) [osLd (e + 3) 8 1, osAdd (e + 4) (e + 3) qq.2.2.1, osMul (e + 5) (e + 4) 6]
      (e + 6) :=
    .load le_rfl (by omega) (.add (by omega) (by omega) (by omega) (.mul (by omega) (by omega)
      (by omega) .nil))
  have hW2 : Ssa (e + 6) [osLd (e + 5) 8 3] (e + 6) := .cons (.store (by omega) (by omega)) .nil
  have hT : SsaP (e + 6) (osLoopTailA (e + 6)) (e + 6 + 5) :=
    .const le_rfl (.mul (by omega) (by omega) (by omega) (.add (by omega) (by omega) (by omega)
      (.const (by omega) (.mul (by omega) (by omega) (by omega) .nil))))
  set A1 : List Stmt := [osMul 7 2 0, osMul 8 7 0, osMul 9 3 0, osLd 10 9 0] with hA1
  set R1 : List Stmt := [osLd e 8 0, osAdd (e + 1) e qq.2.1, osMul (e + 2) (e + 1) 6] with hR1d
  set W1 : List Stmt := [osLd (e + 2) 8 2] with hW1d
  set R2 : List Stmt := [osLd (e + 3) 8 1, osAdd (e + 4) (e + 3) qq.2.2.1, osMul (e + 5) (e + 4) 6]
    with hR2d
  set W2 : List Stmt := [osLd (e + 5) 8 3] with hW2d
  set P' : List Stmt := A1 ++ qq.1 ++ R1 with hPd
  have hP : SsaP 7 P' (e + 3) := (hS1.append q1).append hR1
  have hPW := hP.toSsa.append hW1
  have hPWR := hPW.append hR2.toSsa
  have hPWRW := hPWR.append hW2
  have hL := hPWRW.append hT.toSsa
  set v0 : ℕ → E := fun i ↦ [gen ^ j, N, RS, T, BD, HS, mu].getD i 0 with hv0
  set M := rdMem rd with hM
  set L : List Stmt := (((P' ++ W1) ++ R2) ++ W2) ++ osLoopTailA (e + 6) with hLd
  set σ : Val := fun v ↦ evalV M (fun _ ↦ 0) 7 v0 L v.idx with hσ
  have hσP : ∀ i < e + 3, σ (.n i) = evalV M (fun _ ↦ 0) 7 v0 P' i := fun i hi ↦ by
    show evalV M (fun _ ↦ 0) 7 v0 L i = _
    rw [hLd, hPWRW.evalV_lt hT.toSsa _ (by omega), hPWR.evalV_lt hW2 _ (by omega),
      hPW.evalV_lt hR2.toSsa _ (by omega), hP.toSsa.evalV_lt hW1 _ hi]
  have hσR : ∀ i < e + 6, σ (.n i) = evalV M (fun _ ↦ 0) (e + 3)
      (evalV M (fun _ ↦ 0) 7 v0 (P' ++ W1)) R2 i := fun i hi ↦ by
    show evalV M (fun _ ↦ 0) 7 v0 L i = _
    rw [hLd, hPWRW.evalV_lt hT.toSsa _ (by omega), hPWR.evalV_lt hW2 _ hi, hPW.evalV_append]
  have hσ0 : ∀ i < 7, σ (.n i) = v0 i := fun i hi ↦ by
    show evalV M (fun _ ↦ 0) 7 v0 L i = _
    rw [hL.keep _ i hi]
  have e0 : σ (.n 0) = gen ^ j := hσ0 0 (by omega)
  have e2 : σ (.n 2) = RS := hσ0 2 (by omega)
  have e3 : σ (.n 3) = T := hσ0 3 (by omega)
  have e4 : σ (.n 4) = BD := hσ0 4 (by omega)
  have e5 : σ (.n 5) = HS := hσ0 5 (by omega)
  have e6 : σ (.n 6) = mu := hσ0 6 (by omega)
  -- the pointers
  have hS1' : SsaP 7 [osMul 7 2 0, osMul 8 7 0, osMul 9 3 0] 10 :=
    .mul le_rfl (by omega) (by omega) (.mul (by omega) (by omega) (by omega) (.mul (by omega)
      (by omega) (by omega) .nil))
  have okA0 : AllOk (coreProgram.Rel rd) rd σ [osMul 7 2 0, osMul 8 7 0, osMul 9 3 0] := by
    refine ssa_allOk (M := M) (Pt := fun _ ↦ 0) hS1'.toSsa v0 σ (fun i hi ↦ ?_)
      (hS1'.sidesOk fun p o hpo ↦ by simp [loadsOf] at hpo)
    have hld : SsaP 10 [osLd 10 9 0] 11 := .load le_rfl (by omega) .nil
    rw [hσP i (by omega), hPd, ((hS1.append q1)).toSsa.evalV_lt hR1.toSsa _ (by omega),
      hS1.toSsa.evalV_lt q1.toSsa _ (by omega)]
    show evalV M (fun _ ↦ 0) 7 v0 ([osMul 7 2 0, osMul 8 7 0, osMul 9 3 0] ++ [osLd 10 9 0]) i = _
    rw [hS1'.toSsa.evalV_lt hld.toSsa _ hi]
  simp only [allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_mul, osMul] at okA0
  obtain ⟨m7, m8, m9⟩ := okA0
  have hX8 : σ (.n 8) = RS * gen ^ (2 * j) := by rw [m8, m7, e2, e0]; ring
  have hX9 : σ (.n 9) = T * gen ^ j := by rw [m9, e3, e0]
  -- the memory
  have hrsl : ∀ o < 2 * (r + 1), LoadHolds rd RS o ((rsC lv D hsv Pos mu nb r).getD o 0) := fun o ho ↦
    readsAt_getDr hrs (by rw [rsC_length]; exact ho)
  have hrs8 : ∀ o < 4, LoadHolds rd (σ (.n 8)) o ((rsC lv D hsv Pos mu nb r).getD (2 * j + o) 0) :=
    fun o ho ↦ by rw [hX8, loadHolds_mul_gen_pow]; exact hrsl _ (by omega)
  have hp9 : LoadHolds rd (σ (.n 9)) 0 (Pos (resBatch * nb + j)) := by
    rw [hX9, loadHolds_mul_gen_pow, Nat.add_zero]; exact hpos j hj
  -- the pure part
  have okP : AllOk (coreProgram.Rel rd) rd σ P' := by
    refine ssa_allOk (M := M) (Pt := fun _ ↦ 0) hP.toSsa v0 σ (fun i hi ↦ hσP i hi)
      (hP.sidesOk fun p o hpo ↦ ?_)
    simp only [hPd, hA1, hR1d, loadsOf_append, loadsOf, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hpo
    rcases hpo with (⟨rfl, rfl⟩ | hpo) | ⟨rfl, rfl⟩
    · exact (rdMem_of hp9).2
    · rcases q4 p o hpo with ⟨rfl, s', hs', hne, rfl⟩ | ⟨rfl, c', hc', rfl⟩
      · rw [e4, Nat.zero_add]; exact (rdMem_of (hD s' (by omega))).2
      · rw [e5, Nat.zero_add]; exact (rdMem_of (hhs c' hc')).2
    · exact (rdMem_of (hrs8 0 (by omega))).2
  have okP' := okP
  simp only [hPd, hA1, hR1d, allOk_append, allOk_cons, allOk_nil, and_true, stmtOk_atom,
    holds_load, holds_add, holds_mul, osLd, osAdd, osMul] at okP'
  obtain ⟨⟨⟨-, -, -, l10⟩, hq⟩, le0, a1, u1⟩ := okP'
  obtain ⟨p1, p2⟩ := hqv σ (coreProgram.Rel rd) (by rw [e4]; simpa using hD) (by rw [e5]; simpa using hhs) hq
  have v10 : σ (.n 10) = Pos (resBatch * nb + j) := loadHolds_unique l10 hp9
  obtain ⟨g0, g1⟩ := rsC_get lv D hsv Pos mu nb r (j := j) (by omega)
  obtain ⟨g2, g3⟩ := rsC_get lv D hsv Pos mu nb r (j := j + 1) (by omega)
  have ve : σ (.n e) = (rsAt lv D hsv Pos mu nb j).1 := by
    have h := hrs8 0 (by omega)
    rw [Nat.add_zero, g0] at h
    exact loadHolds_unique le0 h
  have hnext : rsAt lv D hsv Pos mu nb (j + 1) =
      (((rsAt lv D hsv Pos mu nb j).1 + lrP cols D (Pos (resBatch * nb + j))) * mu,
        ((rsAt lv D hsv Pos mu nb j).2 + lrH cols nhs hbits hsv (Pos (resBatch * nb + j))) * mu) := by
    rw [rsAt_succ]; rfl
  have ve2 : σ (.n (e + 2)) = (rsAt lv D hsv Pos mu nb (j + 1)).1 := by
    rw [hnext, u1, a1, ve, e6, p1, v10]; rfl
  have okW1 : AllOk (coreProgram.Rel rd) rd σ W1 := by
    simp only [hW1d, allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_load, osLd]
    rw [ve2, ← g2]
    have h := hrs8 2 (by omega)
    rwa [show 2 * j + 2 = 2 * (j + 1) by ring] at h
  -- the second chain
  have okR2 : AllOk (coreProgram.Rel rd) rd σ R2 := by
    refine ssa_allOk (M := M) (Pt := fun _ ↦ 0) hR2.toSsa (evalV M (fun _ ↦ 0) 7 v0 (P' ++ W1)) σ
      (fun i hi ↦ hσR i hi) (hR2.sidesOk fun p o hpo ↦ ?_)
    simp only [hR2d, loadsOf, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hpo
    obtain ⟨rfl, rfl⟩ := hpo
    exact (rdMem_of (hrs8 1 (by omega))).2
  have okR2' := okR2
  simp only [hR2d, allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_load, holds_add, holds_mul,
    osLd, osAdd, osMul] at okR2'
  obtain ⟨le3, a2, u2⟩ := okR2'
  have ve3 : σ (.n (e + 3)) = (rsAt lv D hsv Pos mu nb j).2 := by
    have h := hrs8 1 (by omega)
    rw [g1] at h
    exact loadHolds_unique le3 h
  have ve5 : σ (.n (e + 5)) = (rsAt lv D hsv Pos mu nb (j + 1)).2 := by
    rw [hnext, u2, a2, ve3, e6, p2, v10]; rfl
  have okW2 : AllOk (coreProgram.Rel rd) rd σ W2 := by
    simp only [hW2d, allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_load, osLd]
    rw [ve5, ← g3]
    have h := hrs8 3 (by omega)
    rwa [show 2 * j + 3 = 2 * (j + 1) + 1 by ring] at h
  -- the tail
  have okT : AllOk (coreProgram.Rel rd) rd σ (osLoopTailA (e + 6)) := by
    refine ssa_allOk (M := M) (Pt := fun _ ↦ 0) hT.toSsa
      (evalV M (fun _ ↦ 0) 7 v0 (((P' ++ W1) ++ R2) ++ W2)) σ (fun i _ ↦ ?_)
      (hT.sidesOk fun p o hpo ↦ by simp [osLoopTailA, loadsOf] at hpo)
    show evalV M (fun _ ↦ 0) 7 v0 L i = _
    rw [hLd, hPWRW.evalV_append]
  obtain ⟨tr2, tr4⟩ := osLoopTailA_val okT
  refine ⟨σ, ?_, ?_, ?_, ?_⟩
  · simp only [osParams, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
      List.nil_append, List.cons_append]
    rw [hσ0 0 (by omega), hσ0 1 (by omega), hσ0 2 (by omega), hσ0 3 (by omega), hσ0 4 (by omega),
      hσ0 5 (by omega), hσ0 6 (by omega)]
    rfl
  · have h := allOk_append.mpr ⟨allOk_append.mpr ⟨allOk_append.mpr ⟨allOk_append.mpr
      ⟨okP, okW1⟩, okR2⟩, okW2⟩, okT⟩
    convert h using 2
    simp only [hPd, hA1, hR1d, hW1d, hR2d, hW2d, List.append_assoc, List.cons_append,
      List.nil_append]
  · rw [tr2, e0, hσ0 1 (by omega)]; rfl
  · simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
      List.cons_append, Nat.zero_add, tr4, e0]
    rw [hσ0 1 (by omega), hσ0 2 (by omega), hσ0 3 (by omega), hσ0 4 (by omega), hσ0 5 (by omega),
      hσ0 6 (by omega)]
    rfl

/-- **The rest's loop holds at its honest arguments**: entered at `1` with the bound `g^r`. -/
theorem lrLoop2_complete {name : String} {q cols nhs hbits : ℕ}
    (hfn : FnIs name (osParams 7) (lrLoop2Body cols nhs hbits name)) {hsv : List E}
    (hst : ResStatic (lrRow q cols nhs hbits) hsv) {nb r : ℕ} (hr0 : 0 < r)
    {rd : Reader} {RS T BD HS mu : E} {D Pos : ℕ → E}
    (hpos : ∀ k < r, LoadHolds rd T k (Pos (resBatch * nb + k)))
    (hD : ∀ t < cols, LoadHolds rd BD t (D t))
    (hhs : ∀ c < nhs, LoadHolds rd HS c (hsv.getD c 0))
    (hrs : ReadsAt rd RS (rsC (lrRow q cols nhs hbits) D hsv Pos mu nb r)) :
    1 + gen ^ r ≠ 0 → coreProgram.Rel rd name [1, gen ^ r, RS, T, BD, HS, mu] [] := by
  obtain ⟨fn, hf, hps, hb⟩ := hfn
  rw [lrLoop2Body_split] at hb
  have h := loop_complete (rd := rd) hf (lr2A_flat cols nhs hbits) hb (N := gen ^ r)
    (rest := [RS, T, BD, HS, mu]) hr0 rfl fun j hj ↦ by
      obtain ⟨σ, h1, h2, h3, h4⟩ := lrLoop2_iter (N := gen ^ r) hst hj hpos hD hhs hrs
      exact ⟨σ, by rw [hps]; exact h1, h2, h3, h4⟩
  exact h.2

end
end LeanVM.Guest.B1.Whir
