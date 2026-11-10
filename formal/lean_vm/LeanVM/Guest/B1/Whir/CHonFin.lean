/-
  LeanVM.Guest.B1.Whir.CHonFin

  The finish of open_stacked's body at the honest data, under `OsH`.
-/

module

public import LeanVM.Guest.B1.Whir.CHonComp
public import LeanVM.Guest.B1.Whir.CHonMemFin
public import LeanVM.Guest.B1.Whir.CHonCall
public import LeanVM.Guest.B1.Whir.CFinCall

/-!
# The finish, at the honest data

`fin_of`: `body_of`'s finish hypothesis. From the finish's static facts (`FinStatic`), each
non-final level's record facts (`RecRun`), the memory under `OsH` holding the honest buffers
(`Whir/CHonMem*`) and `fold_final_msg`'s meaning, `osFinishA_completeC`'s block allocates the
finish's buffers (`bufsAt`), returns the target, the point buffers, the glued weight and the final
lane at the tail challenges, and calls the residual loops at their honest values.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Guest.Memory LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- The finish's start: the tail challenges' value and the claim below its next free value. -/
theorem osFin_k {c : OsCfg} (hsf : (osLvsEnd c).Sf) :
    osFinTch c < (osFinSt c).k ∧ (osFinSt c).claim < (osFinSt c).k ∧ 36 ≤ (osFinSt c).k := by
  set st := osLvsEnd c with hst
  set k := st.k with hk
  set s0 : OsSt := { st with k := k + 2 } with hs0
  have hsf0 : s0.Sf := ⟨hsf.fs, ⟨fun x hx ↦ by have := hsf.below.fs x hx; show x < k + 2; omega,
    by have := hsf.below.cb; show st.cb < k + 2; omega, by have := hsf.below.claim; show st.claim < k + 2; omega,
    fun x hx ↦ by
      obtain ⟨a, b, d⟩ := hsf.below.mats x hx
      exact ⟨show x.out < k + 2 by omega, show x.src < k + 2 by omega, show x.base < k + 2 by omega⟩⟩,
    hsf.co, fun p hp ↦ by have := hsf.padB p hp; show p + 4 < k + 2; omega,
    by have := hsf.k; show 36 ≤ k + 2; omega⟩
  set f := osTailRounds (k + 1) 0 c.yrLog s0 with hf
  have hsf1 : f.2.Sf := osTailRounds_sf (k + 1) c.yrLog 0 s0 hsf0
  have kj : k + 2 ≤ f.2.k := osTailRounds_k (k + 1) c.yrLog 0 s0
  have e1 : osFinTch c = k + 1 := rfl
  have e2 : (osFinSt c).k = f.2.k + (yrLogCap - c.yrLog) := rfl
  have e3 : (osFinSt c).claim = f.2.claim := rfl
  have := hsf1.below.claim
  have := hsf1.k
  rw [e1, e2, e3]
  omega

/-- The finish's block ends past its start. -/
theorem osFinishA_k {c : OsCfg} {st : OsSt} {tch : ℕ} {G T : List E} {recs : List OsRec}
    (hS : FinStatic c G T recs) (htch : tch < st.k) (hk : 36 ≤ st.k) : st.k ≤ finEnd c st tch := by
  have w1 : st.k + 1 + 2 ≤ (osPtBlks c (st.k + 1) (st.k + 1 + 1) tch 0 pointCap (st.k + 1 + 2)).2 :=
    osPtBlks_next c _ _ tch pointCap 0 _
  set P2 := (osPtBlks c (st.k + 1) (st.k + 1 + 1) tch 0 pointCap (st.k + 1 + 2)).2
  set mid := c.levels.take c.yrLevel with hmid
  have w2 : P2 + 6 ≤ (osBases c tch (P2 + 1) (P2 + 3) (P2 + 5) 0 mid (P2 + 6)).2 :=
    osBases_next c tch _ _ _ mid 0 _
  set B := (osBases c tch (P2 + 1) (P2 + 3) (P2 + 5) 0 mid (P2 + 6)).2
  have hrsS : ∀ i (hi : i < mid.length), ResStatic mid[i]
      (hsvOf (finLv c (0 + i)) (recs.getD (0 + i) default)) := fun i hi ↦ by
    have hy : mid.length = c.yrLevel := by rw [hmid, List.length_take]; have := hS.yr; have := hS.n2; omega
    rw [take_getElem hi, Nat.zero_add]; exact hS.rs i (by omega)
  have w3 : B + 3 ≤ (osResiduals c (B + 1) (P2 + 1) (P2 + 3) (P2 + 5) 0 mid (B + 3)).2 :=
    osResiduals_next c _ _ _ _ (fun i ↦ hsvOf (finLv c i) (recs.getD i default)) mid 0 (B + 3)
      (by omega) (by omega) hrsS
  have w4 := (osOodWeights_ssa c tch (c.levels.headD default).logCols 1 c.levels.tail none
    (osResiduals c (B + 1) (P2 + 1) (P2 + 3) (P2 + 5) 0 mid (B + 3)).2 (by omega) (by omega) (by simp)).1.le
  show st.k ≤ (osOodWeights c tch (c.levels.headD default).logCols 1 c.levels.tail none
    (osResiduals c (B + 1) (P2 + 1) (P2 + 3) (P2 + 5) 0 mid (B + 3)).2).2.2 + 6
  omega

/-- What each non-final level's record holds on the run. -/
structure RecRun (h : OsHD) (i : ℕ) : Prop where
  F : ((h.L i).osRec h.logN).F = (osLvAt h.c i).foldsOff + (osLvAt h.c i).folds
  mu : ((h.L i).osRec h.logN).mu = (osLvAt h.c i).logCols
  ql : ((h.L i).osRec h.logN).qs.length = (osLvAt h.c i).queries
  hl : ((h.L i).osRec h.logN).high.length = (osLvAt h.c i).folds
  z0 : ((h.L i).osRec h.logN).z0.length = (osLvAt h.c i).logCols
  z1 : ((h.L i).osRec h.logN).z1.length = (osLvAt h.c i).logCols
  lam : (h.L i).lam h.logN ≠ 0
  Q : (osLvAt h.c i).queries ≤ (osLvAt h.c i).squeezes * sqPer (osLvAt h.c i)
  qs : ∀ k < (osLvAt h.c i).queries, ((h.L i).osRec h.logN).qs.getD k 0 =
    qwPosOf (osLvAt h.c i).depth ((h.L i).word h.logN (k / sqPer (osLvAt h.c i))) (k % sqPer (osLvAt h.c i))

theorem OsHD.recs_getD (h : OsHD) (hL : h.Ls.length = h.c.levels.length) (hyr : h.c.yrLevel + 1 = h.c.levels.length)
    {i : ℕ} (hi : i < h.c.yrLevel) : h.recs.getD i default = (h.L i).osRec h.logN := by
  have hi' : i < h.Ls.length := by omega
  simp only [OsHD.recs, lvsRecs, OsHD.L, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_take,
    hi, ↓reduceIte, List.getElem?_eq_getElem hi', Option.map_some, Option.getD_some]

/-- **The finish's buffers in allocation order.** -/
theorem bufsAt_fin {c : OsCfg} (hHS : HonStatic c) (b : ℕ) :
    bufsAt c b (14 + 2 * c.levels.length) (6 + c.yrLevel) =
      finAllocs c (osPtrF c b (14 + 2 * c.levels.length)) (osPtrF c b (15 + 2 * c.levels.length))
        (osPtrF c b (16 + 2 * c.levels.length)) (osPtrF c b (17 + 2 * c.levels.length))
        (osPtrF c b (18 + 2 * c.levels.length)) (osPtrF c b (19 + 2 * c.levels.length))
        (fun l ↦ osPtrF c b (20 + 2 * c.levels.length + l)) := by
  set n := c.levels.length with hn
  have sz : ∀ k < 6, (osSizesF c).getD (14 + 2 * n + k) 0 =
      [pointCap, pointCap, n * ligColsCap, n, n, 2 * n].getD k 0 := fun k hk ↦ by
    have := hHS.fin (k := k + 1) (by omega)
    rw [show 13 + 2 * n + (k + 1) = 14 + 2 * n + k by omega] at this
    rw [this]
    rcases k with _ | _ | _ | _ | _ | _ | k <;> rfl
  rw [← bufsAt_add, finAllocs]
  congr 1
  · simp only [bufsAt]
    rw [show List.range 6 = [0, 1, 2, 3, 4, 5] from rfl]
    simp only [List.map_cons, List.map_nil]
    rw [sz 0 (by omega), sz 1 (by omega), sz 2 (by omega), sz 3 (by omega), sz 4 (by omega), sz 5 (by omega)]
    rw [Nat.add_zero, show 14 + 2 * n + 1 = 15 + 2 * n by omega, show 14 + 2 * n + 2 = 16 + 2 * n by omega,
      show 14 + 2 * n + 3 = 17 + 2 * n by omega, show 14 + 2 * n + 4 = 18 + 2 * n by omega,
      show 14 + 2 * n + 5 = 19 + 2 * n by omega]
    rfl
  · simp only [bufsAt]
    refine List.map_congr_left fun i hi ↦ ?_
    have hi' := List.mem_range.mp hi
    rw [show 14 + 2 * n + 6 + i = 20 + 2 * n + i by omega, hHS.rc hi']

/-- **`body_of`'s finish hypothesis**, at the honest data. -/
theorem fin_of {h : OsHD} {b : ℕ} {cur tabs : E} {xs : List E} (hHS : HonStatic h.c)
    (hF : FinStatic h.c h.G h.T h.recs) (hL : h.Ls.length = h.c.levels.length)
    (hrun : ∀ i < h.c.yrLevel, RecRun h i) (hylen : 2 ^ h.c.yrLog = h.c.yrLen)
    (hfold : h.c.yrLen ≤ h.Lf.fw.fold.length)
    (hffm : osKindOf ("fold_final_msg__L" ++ natStr h.c.yrLog) = some (.ffm h.c.yrLog))
    (hres : ∀ l < h.c.yrLevel, osKindOf (h.c.resLoop l) = none) (hsf : (osLvsEnd h.c).Sf) :
    ∀ σ, (∀ i < 13, σ (.n (11 + 2 * i)) = osPtrF h.c b i) → σ (.n osTabs) = tabs →
      σ (.n (osFinTch h.c)) = osPtrF h.c b (13 + 2 * h.c.levels.length) →
      σ (.n (osFinSt h.c).claim) = (tailRun h.Lf.fw.pairs (h.capAt h.c.levels.length)
        (h.claimAt h.c.levels.length)).2.1 →
      BlkA (fun C rd ↦ OsH C rd h.c b h.own cur tabs xs) σ (osFinSt h.c).k
        (finEnd h.c (osFinSt h.c) (osFinTch h.c)) (osFinishA h.c (osFinSt h.c) (osFinTch h.c)).1
        (fun σ' ↦ (osFinSt h.c).k ≤ finEnd h.c (osFinSt h.c) (osFinTch h.c) ∧
          AllocsAt σ' (osFinishA h.c (osFinSt h.c) (osFinTch h.c)).1 =
            bufsAt h.c b (14 + 2 * h.c.levels.length) (6 + h.c.yrLevel) ∧
          (osFinishA h.c (osFinSt h.c) (osFinTch h.c)).2.map σ' =
            [h.tr.2.1 + h.T.prod * recsDeficit h.recs h.G, osPtrF h.c b (osIxPT h.c),
              osPtrF h.c b (osIxPT1 h.c),
              (h.recs.flatMap recGlued).foldl (fun w g ↦ w + g.scalar * g.weightAt ((h.G ++ h.T).drop g.foldStart)) 0,
              multilinearEval (h.Lf.fw.fold.take h.c.yrLen) h.T] ∧
          ∀ l < h.c.yrLevel,
            (osResCall h.c l).1.map σ' = some (1 + gen ^ ((osLvAt h.c l).queries / resBatch)) ∧
            (osResCall h.c l).2.2.1.map σ' = [1, gen ^ ((osLvAt h.c l).queries / resBatch),
              osPtrF h.c b 11, osPtrF h.c b (osIxBD h.c), osPtrF h.c b 8, osPtrF h.c b (osIxRC h.c l),
              h.li l]) := by
  intro σ hp ht htch hcl
  set c := h.c with hc
  set n := c.levels.length with hn
  have hyr : c.yrLevel + 1 = n := hHS.yr
  obtain ⟨k1, k2, k3⟩ := osFin_k hsf
  have hcl' : σ (.n (osFinSt c).claim) = h.tr.2.1 := by
    have hnn : ¬ n ≤ h.c.yrLevel := by rw [← hc]; omega
    rw [hcl, OsHD.capAt, OsHD.claimAt]
    simp only [hnn, ↓reduceIte]
    rfl
  have p2 : σ (.n osFmsg) = osPtrF c b 2 := hp 2 (by omega)
  have p4 : σ (.n osFch) = osPtrF c b 4 := hp 4 (by omega)
  have p6 : σ (.n osBetas) = osPtrF c b 6 := hp 6 (by omega)
  have p7 : σ (.n osMus) = osPtrF c b 7 := hp 7 (by omega)
  have p8 : σ (.n osHs) = osPtrF c b 8 := hp 8 (by omega)
  have p9 : σ (.n osOodz) = osPtrF c b 9 := hp 9 (by omega)
  have p10 : σ (.n osOodSc) = osPtrF c b 10 := hp 10 (by omega)
  have p11 : σ (.n osQpos) = osPtrF c b 11 := hp 11 (by omega)
  have hTl : h.T.length ≤ yrLogCap := by rw [hF.Tl]; exact hHS.ylog
  have hB := osFinishA_completeC (H := fun C rd ↦ OsH C rd c b h.own cur tabs xs) (σ := σ) (G := h.G) (T := h.T)
    (recs := h.recs) (li := h.li) (Y := multilinearEval (h.Lf.fw.fold.take c.yrLen) h.T)
    (PT := osPtrF c b (14 + 2 * n)) (PT1 := osPtrF c b (15 + 2 * n)) (BD := osPtrF c b (16 + 2 * n))
    (LS := osPtrF c b (17 + 2 * n)) (LA := osPtrF c b (18 + 2 * n)) (ICH := osPtrF c b (19 + 2 * n))
    (RC := fun l ↦ osPtrF c b (20 + 2 * n + l)) hF k1 k2 k3 fun C rd hH ↦ by
      have hm : OsMemF rd c b h.own := hH.2.2.1
      have i1 : 13 + 2 * n + 1 = 14 + 2 * n := by omega
      have i2 : 13 + 2 * n + 2 = 15 + 2 * n := by omega
      have i3 : 13 + 2 * n + 3 = 16 + 2 * n := by omega
      have i4 : 13 + 2 * n + 4 = 17 + 2 * n := by omega
      have i5 : 13 + 2 * n + 5 = 18 + 2 * n := by omega
      have i6 : 13 + 2 * n + 6 = 19 + 2 * n := by omega
      refine ⟨fun i hi ↦ ?_, fun i hi ↦ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi ↦ ?_, ?_,
        fun i hi _ ↦ osH_special hH (hres i hi) _ _⟩
      · have r := hrun i hi
        rw [h.recs_getD hL hyr hi]
        exact h.recStored_of hHS hm p9 p10 p6 p7 p8 p11 hi r.F r.mu r.ql r.hl r.z0 r.z1 r.lam r.Q r.qs
      · rw [p7]; exact (h.mid_glue hHS hm hi).2.2.2
      · rw [p4]; exact h.fch_all hHS hm hF.Gl
      · rw [htch]; exact h.tail_reads hHS hm hTl
      · have := h.pt_reads hHS hm (by rw [finPtC_length _ hF])
        rwa [i1] at this
      · have := h.pt1_reads hHS hm (by rw [finPt1C_length _ hF])
        rwa [i2] at this
      · have := h.bd_reads hHS hm
        rwa [i3] at this
      · have := h.ls_reads hHS hm
        rwa [i4] at this
      · have := h.la_reads hHS hm
        rwa [i5] at this
      · have := h.ich_reads hHS hm
        rwa [i6, ← hcl'] at this
      · exact h.rc_reads hHS hm hi (by simp only [finRcC, rcC_length]; exact le_rfl)
      · rw [p2, htch]
        have hs2 : (osSizesF c).getD 2 0 = c.yrLen + (c.levels.getD c.yrLevel default).folds := by
          rw [hHS.head (j := 2) (by omega)]; rfl
        have hml : (h.Lf.fw.fold.take c.yrLen).length = 2 ^ c.yrLog := by
          rw [List.length_take, hylen]; omega
        have hrm : ReadsAt rd (osPtrF c b 2) (h.Lf.fw.fold.take c.yrLen) := fun e he ↦ by
          rw [List.length_take] at he
          have := h.load hm (hHS.headLt (j := 2) (by omega)) (by unfold osIxQbp; omega) (e := e)
            (by rw [hs2]; omega)
          rw [OsHD.ownW_fmsg, OsHD.fmsgC, List.getD_eq_getElem _ _ (by omega)] at this
          rwa [List.getElem_take]
        refine osH_named hH hffm (ffm_pre hml hF.Tl hrm (h.tail_reads hHS hm hTl)) fun q hq ↦ ?_
        simp only [OsKind.spec, foldFinalSpec, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · refine fixedAt_buf0 (hHS.headLt (j := 2) (by omega)) (by unfold osIxQbp; omega) ?_
          rw [h.own_getD (hHS.headLt (j := 2) (by omega)), OsHD.ownAt, fitTo_length, hs2, hylen]
          omega
        · refine fixedAt_buf0 (hHS.finLt (k := 0) (by omega)) (by unfold osIxQbp; omega) ?_
          show c.yrLog ≤ (h.own.getD (13 + 2 * n + 0) []).length
          rw [h.own_getD (hHS.finLt (k := 0) (by omega)), OsHD.ownAt, fitTo_length, hHS.fin (k := 0) (by omega)]
          exact hHS.ylog
  refine hB.mono fun σ' ⟨⟨ha, hr⟩, hv⟩ ↦ ⟨osFinishA_k hF k1 k3, ?_, ?_, fun l hl ↦ ?_⟩
  · rw [ha, bufsAt_fin hHS]
  · rw [hr, hcl']; rfl
  · obtain ⟨e1, e2⟩ := osResCall_vals hv l hl
    refine ⟨e1, ?_⟩
    rw [e2, p11, p8]
    rfl

end
end LeanVM.Guest.B1.Whir
