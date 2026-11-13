/-
  LeanVM.Guest.B1.Whir.CHonFin

  The finish of open_stacked's body at the honest data, under `OsHA`.
-/

module

public import LeanVM.Guest.B1.Whir.CHonComp
public import LeanVM.Guest.B1.Whir.CHonMemFin
public import LeanVM.Guest.B1.Whir.CHonCall
public import LeanVM.Guest.B1.Whir.CFinM
public import LeanVM.Guest.B1.Whir.CHonNames

/-!
# The finish, at the honest data

`fin_of`: `body_of`'s finish hypothesis. From the finish's static facts (`FinStatic`), each
non-final level's record facts (`RecRun`), the memory under `OsHA` holding the honest buffers
(`Whir/CHonMem*`) and `fold_final_msg`'s meaning, `osFinishA_completeC`'s block allocates the
finish's buffers (`bufsAt`), returns the target, the point buffers, the glued weight and the final
lane at the tail challenges, and dispatches into `level_residual` at its honest values.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Guest.Memory LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- The finish's start: the tail challenges' value and the claim below its next free value. -/
theorem osFin_k {c : OsCfg} (hsf : (osLvsEnd c).Sf) :
    osFinTch c < (osFinSt c).k ∧ (osFinSt c).claim < (osFinSt c).k ∧ 33 ≤ (osFinSt c).k := by
  set st := osLvsEnd c with hst
  set k := st.k with hk
  set s0 : OsSt := { st with k := k + 2 } with hs0
  have hsf0 : s0.Sf := ⟨hsf.fs, ⟨fun x hx ↦ by have := hsf.below.fs x hx; show x < k + 2; omega,
    by have := hsf.below.cb; show st.cb < k + 2; omega, by have := hsf.below.claim; show st.claim < k + 2; omega,
    fun x hx ↦ by
      obtain ⟨a, b, d⟩ := hsf.below.mats x hx
      exact ⟨show x.out < k + 2 by omega, show x.src < k + 2 by omega, show x.base < k + 2 by omega⟩⟩,
    hsf.co, fun p hp ↦ by have := hsf.padB p hp; show p + 4 < k + 2; omega,
    by have := hsf.k; show 33 ≤ k + 2; omega⟩
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
theorem osFinishA_k {c : OsCfg} {st : OsSt} {tch : ℕ} (htch : tch < st.k) (hk : 33 ≤ st.k) : st.k ≤ finEnd c st tch := by
  have w1 : st.k + 1 + 2 ≤ (osPtBlks c (st.k + 1) (st.k + 1 + 1) tch 0 pointCap (st.k + 1 + 2)).2 :=
    osPtBlks_next c _ _ tch pointCap 0 _
  set P2 := (osPtBlks c (st.k + 1) (st.k + 1 + 1) tch 0 pointCap (st.k + 1 + 2)).2
  set mid := c.levels.take c.yrLevel with hmid
  have w2 : P2 + 6 ≤ (osBases c tch (P2 + 1) (P2 + 3) (P2 + 5) 0 mid (P2 + 6)).2 :=
    osBases_next c tch _ _ _ mid 0 _
  set B := (osBases c tch (P2 + 1) (P2 + 3) (P2 + 5) 0 mid (P2 + 6)).2
  have w3 : B + 3 ≤ (osResiduals c (B + 1) (P2 + 1) (P2 + 3) (P2 + 5) 0 mid st.mats (B + 3)).2 :=
    osResiduals_next c _ _ _ _ mid 0 st.mats (B + 3)
  have w4 := (osOodWeights_ssa c tch (c.levels.headD default).logCols 1 c.levels.tail none
    (osResiduals c (B + 1) (P2 + 1) (P2 + 3) (P2 + 5) 0 mid st.mats (B + 3)).2 (by omega) (by omega) (by simp)).1.le
  show st.k ≤ (osOodWeights c tch (c.levels.headD default).logCols 1 c.levels.tail none
    (osResiduals c (B + 1) (P2 + 1) (P2 + 3) (P2 + 5) 0 mid st.mats (B + 3)).2).2.2 + 6
  omega

/-- What each non-final level's record holds on the run. -/
structure RecRun (h : OsHD) (i : ℕ) : Prop where
  F : ((h.L i).osRec h.logN).F = ((h.c.levels.getD i default)).foldsOff + ((h.c.levels.getD i default)).folds
  mu : ((h.L i).osRec h.logN).mu = ((h.c.levels.getD i default)).logCols
  ql : ((h.L i).osRec h.logN).qs.length = ((h.c.levels.getD i default)).queries
  hl : ((h.L i).osRec h.logN).high.length = ((h.c.levels.getD i default)).folds
  z0 : ((h.L i).osRec h.logN).z0.length = ((h.c.levels.getD i default)).logCols
  lam : (h.L i).lam h.logN ≠ 0
  Q : ((h.c.levels.getD i default)).queries ≤ ((h.c.levels.getD i default)).squeezes * sqPer ((h.c.levels.getD i default))
  qs : ∀ k < ((h.c.levels.getD i default)).queries, ((h.L i).osRec h.logN).qs.getD k 0 =
    qwPosOf ((h.c.levels.getD i default)).depth ((h.L i).word h.logN (k / sqPer ((h.c.levels.getD i default)))) (k % sqPer ((h.c.levels.getD i default)))

theorem OsHD.recs_getD (h : OsHD) (hL : h.Ls.length = h.c.levels.length) (hyr : h.c.yrLevel + 1 = h.c.levels.length)
    {i : ℕ} (hi : i < h.c.yrLevel) : h.recs.getD i default = (h.L i).osRec h.logN := by
  have hi' : i < h.Ls.length := by omega
  simp only [OsHD.recs, lvsRecs, OsHD.L, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_take,
    hi, ↓reduceIte, List.getElem?_eq_getElem hi', Option.map_some, Option.getD_some]

/-- **The finish's buffers in allocation order.** -/
theorem bufsAt_fin {c : OsCfg} (hHS : HonStatic c) (b : ℕ) :
    bufsAt c b (13 + c.yrLevel) 6 =
      finAllocs c (osPtrA c b (13 + c.yrLevel)) (osPtrA c b (14 + c.yrLevel))
        (osPtrA c b (15 + c.yrLevel)) (osPtrA c b (16 + c.yrLevel))
        (osPtrA c b (17 + c.yrLevel)) (osPtrA c b (18 + c.yrLevel)) := by
  set y := c.yrLevel with hy
  set n := c.levels.length with hn
  have sz : ∀ k < 6, (osSizesL c).getD (13 + y + k) 0 =
      [pointCap, pointCap, n * ligColsCap, n, n, 2 * n].getD k 0 := fun k hk ↦ by
    have := hHS.fin (k := k + 1) (by omega)
    rw [show 12 + c.yrLevel + (k + 1) = 13 + y + k by omega] at this
    rw [this]
    rcases k with _ | _ | _ | _ | _ | _ | k <;> rfl
  simp only [bufsAt, finAllocs]
  rw [show List.range 6 = [0, 1, 2, 3, 4, 5] from rfl]
  simp only [List.map_cons, List.map_nil]
  rw [sz 0 (by omega), sz 1 (by omega), sz 2 (by omega), sz 3 (by omega), sz 4 (by omega), sz 5 (by omega)]
  rw [Nat.add_zero, show 13 + y + 1 = 14 + y by omega, show 13 + y + 2 = 15 + y by omega,
    show 13 + y + 3 = 16 + y by omega, show 13 + y + 4 = 17 + y by omega, show 13 + y + 5 = 18 + y by omega]
  rfl

/-- **`body_of`'s finish hypothesis**, at the honest data, the residual chains' returns bridged to
`osLrRetA` at `D`. -/
theorem fin_of {h : OsHD} {b : ℕ} {cur tabs : E} {xs : List E} {D : ℕ → OsLvData} (hHS : HonStatic h.c)
    (hNm : HonNames h.c) (hF : FinStatic h.c h.G h.T h.recs) (hL : h.Ls.length = h.c.levels.length)
    (hrun : ∀ i < h.c.yrLevel, RecRun h i) (hylen : 2 ^ h.c.yrLog = h.c.yrLen)
    (hfold : h.c.yrLen ≤ h.Lf.fw.fold.length)
    (hffm : osKindOf ("fold_final_msg__L" ++ natStr h.c.yrLog) = some (.ffm h.c.yrLog))
    (hD : ∀ l < h.c.yrLevel, (D l).mu = h.li l ∧
      finRes h.c h.G h.T h.recs h.li l = osLrRetA h.c h.own l (D l).mu) :
    ∀ σ, (osLvsEnd h.c).Sf → (osFinSt h.c).Ok σ →
      (∀ l < h.c.levels.length, LvRate σ h.c l (h.c.levels.getD l default)) →
      (∀ i < 11, σ (.n (12 + 2 * i)) = osPtrA h.c b i) → σ (.n osTabs) = tabs →
      σ (.n (osFinTch h.c)) = osPtrA h.c b (12 + h.c.yrLevel) →
      σ (.n (osFinSt h.c).claim) = (tailRun h.Lf.fw.pairs (h.capAt h.c.levels.length)
        (h.claimAt h.c.levels.length)).2.1 →
      BlkA (fun C rd ↦ OsHA C rd h.c b h.own cur tabs xs) σ (osFinSt h.c).k
        (finEnd h.c (osFinSt h.c) (osFinTch h.c)) (osFinishA h.c (osFinSt h.c) (osFinTch h.c)).1
        (fun σ' ↦ (osFinSt h.c).k ≤ finEnd h.c (osFinSt h.c) (osFinTch h.c) ∧
          AllocsAt σ' (osFinishA h.c (osFinSt h.c) (osFinTch h.c)).1 = bufsAt h.c b (13 + h.c.yrLevel) 6 ∧
          (osFinishA h.c (osFinSt h.c) (osFinTch h.c)).2.map σ' =
            [h.tr.2.1 + h.T.prod * recsDeficit h.recs h.G, osPtrA h.c b (osIxPtA h.c),
              osPtrA h.c b (osIxPt1A h.c),
              (h.recs.flatMap recGlued).foldl (fun w g ↦ w + g.scalar * g.weightAt ((h.G ++ h.T).drop g.foldStart)) 0,
              multilinearEval (h.Lf.fw.fold.take h.c.yrLen) h.T] ∧
          ∀ l < h.c.yrLevel,
            ((osLrCalls h.c).getD l ([], [])).1.map σ' =
              [osPtrA h.c b osIxQposA * gen ^ (osLvA h.c l).posOff,
                osPtrA h.c b (osIxBdA h.c) * gen ^ (l * ligColsCap),
                osPtrA h.c b osIxHsA * gen ^ (l * hsStride), (D l).mu] ∧
            ((osLrCalls h.c).getD l ([], [])).2.map σ' =
              [(osLrRetA h.c h.own l (D l).mu).1, (osLrRetA h.c h.own l (D l).mu).2]) := by
  intro σ hsf hok hrt hp ht htch hcl
  set c := h.c with hc
  set n := c.levels.length with hn
  have hyr : c.yrLevel + 1 = n := hHS.yr
  obtain ⟨k1, k2, k3⟩ := osFin_k hsf
  have hcl' : σ (.n (osFinSt c).claim) = h.tr.2.1 := by
    have hnn : ¬ n ≤ h.c.yrLevel := by rw [← hc]; omega
    rw [hcl, OsHD.capAt, OsHD.claimAt]
    simp only [hnn, ↓reduceIte]
    rfl
  have p2 : σ (.n osFmsg) = osPtrA c b 0 := hp 0 (by omega)
  have p4 : σ (.n osFch) = osPtrA c b 2 := hp 2 (by omega)
  have p6 : σ (.n osBetas) = osPtrA c b 4 := hp 4 (by omega)
  have p7 : σ (.n osMus) = osPtrA c b 5 := hp 5 (by omega)
  have p8 : σ (.n osHs) = osPtrA c b 6 := hp 6 (by omega)
  have p9 : σ (.n osOodz) = osPtrA c b 7 := hp 7 (by omega)
  have p10 : σ (.n osOodSc) = osPtrA c b 8 := hp 8 (by omega)
  have p11 : σ (.n osQpos) = osPtrA c b 9 := hp 9 (by omega)
  have hTl : h.T.length ≤ yrLogCap := by rw [hF.Tl]; exact hHS.ylog
  have hB := osFinishA_completeC (H := fun C rd ↦ OsHA C rd c b h.own cur tabs xs) (σ := σ) (G := h.G)
    (T := h.T) (recs := h.recs) (li := h.li) (Y := multilinearEval (h.Lf.fw.fold.take c.yrLen) h.T)
    (PT := osPtrA c b (13 + c.yrLevel)) (PT1 := osPtrA c b (14 + c.yrLevel)) (BD := osPtrA c b (15 + c.yrLevel))
    (LS := osPtrA c b (16 + c.yrLevel)) (LA := osPtrA c b (17 + c.yrLevel)) (ICH := osPtrA c b (18 + c.yrLevel))
    hF k1 k2 k3 hok.sf.below.mats (fun _ _ _ ↦ hok.mats) fun C rd hH ↦ by
      have hm : OsMemA rd c b h.own := hH.2.2.1
      have i1 : 12 + c.yrLevel + 1 = 13 + c.yrLevel := by omega
      have i2 : 12 + c.yrLevel + 2 = 14 + c.yrLevel := by omega
      have i3 : 12 + c.yrLevel + 3 = 15 + c.yrLevel := by omega
      have i4 : 12 + c.yrLevel + 4 = 16 + c.yrLevel := by omega
      have i5 : 12 + c.yrLevel + 5 = 17 + c.yrLevel := by omega
      have i6 : 12 + c.yrLevel + 6 = 18 + c.yrLevel := by omega
      refine ⟨fun i hi ↦ ?_, fun i hi ↦ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi ↦ ?_,
        fun i hi ↦ osH_special hH (hNm.2.2.2.2.2.2.1 i hi).2.2 _ _⟩
      · have r := hrun i hi
        rw [h.recs_getD hL hyr hi]
        exact h.recStored_of hHS hm p9 p10 p6 p7 p8 p11 hi r.F r.mu r.ql r.hl r.z0 r.lam r.Q r.qs
      · rw [p7]; exact (h.mid_glue hHS hm hi).2.2
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
      · rw [p2, htch]
        have hs2 : (osSizesL c).getD 0 0 = c.yrLen + (c.levels.getD c.yrLevel default).folds := by
          rw [hHS.head (j := 0) (by omega)]; rfl
        have hml : (h.Lf.fw.fold.take c.yrLen).length = 2 ^ c.yrLog := by
          rw [List.length_take, hylen]; omega
        have hrm : ReadsAt rd (osPtrA c b 0) (h.Lf.fw.fold.take c.yrLen) := fun e he ↦ by
          rw [List.length_take] at he
          have := h.load hm (hHS.headLt (j := 0) (by omega)) (by unfold osIxQbpA; omega) (e := e)
            (by rw [hs2]; omega)
          rw [OsHD.ownW_fmsg, OsHD.fmsgC, List.getD_eq_getElem _ _ (by omega)] at this
          rwa [List.getElem_take]
        refine osH_named hH hffm (ffm_pre hml hF.Tl hrm (h.tail_reads hHS hm hTl)) fun q hq ↦ ?_
        simp only [OsKind.spec, foldFinalSpec, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · refine fixedAt_buf0 (hHS.headLt (j := 0) (by omega)) (by unfold osIxQbpA; omega) ?_
          rw [h.own_getD (hHS.headLt (j := 0) (by omega)), OsHD.ownAt, fitTo_length, hs2, hylen]
          omega
        · refine fixedAt_buf0 (hHS.finLt (k := 0) (by omega)) (by unfold osIxQbpA; omega) ?_
          show c.yrLog ≤ (h.own.getD (12 + c.yrLevel + 0) []).length
          rw [h.own_getD (hHS.finLt (k := 0) (by omega)), OsHD.ownAt, fitTo_length, hHS.fin (k := 0) (by omega)]
          exact hHS.ylog
      · exact hrt i (by omega)
  refine hB.mono fun σ' ⟨⟨ha, hr⟩, eBD, hv⟩ ↦ ⟨osFinishA_k k1 k3, ?_, ?_, fun l hl ↦ ?_⟩
  · rw [ha, bufsAt_fin hHS]
  · rw [hr, hcl']; rfl
  · obtain ⟨e1, e2⟩ := hv l hl
    obtain ⟨dmu, dres⟩ := hD l hl
    have eL : osLrCalls c = finResCalls c (osFinSt c) (osFinTch c) := rfl
    rw [eL, e1, e2, p11, p8, ← dres, dmu]
    exact ⟨rfl, rfl⟩

end
end LeanVM.Guest.B1.Whir
