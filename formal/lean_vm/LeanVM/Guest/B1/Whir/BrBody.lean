/-
  LeanVM.Guest.B1.Whir.BrBody

  open_stacked's body, honestly, on the Spec's honest run.
-/

module

public import LeanVM.Guest.B1.Whir.BrFin3
public import LeanVM.Guest.B1.Whir.BrHeight

/-!
# The body on the Spec's run

`OsAt`: the pointers of the frame's own buffers (the fixed buffers, the tail challenges, the point
and `point1`, the basis coefficients, scales and inner sums, and each level's squeeze chain, row
weights and residual chain). `OsMem`: memory holds each buffer's honest words there (`BrCont`).
`OsCallsOk`: the calls of `C` the body makes, at their honest arguments and returns.

**`osBodyA_honest`**: on an accepting run of `whirOpen μ r target` from `⟨capOf S, []⟩` with no
zero challenge, at a candidate's facts and sizes, there is an honest trace `tr` (the run's words
`c0 :: c2 :: …`), whose point buffers hold the run's point zero-padded and one plus it one-padded,
such that for every valuation holding the call's arguments, every memory holding the buffers'
honest words and the words at the cursor, and every call relation the body's calls hold in, the
body before its `ret` holds at the values `bodyF` and returns `[w.target, PT, PT1, w.inner,
w.residual]`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

/-- The pointers of the frame's own buffers. -/
structure OsAt where
  P : OsPtrs
  T : E
  PT : E
  PT1 : E
  BD : E
  LS : E
  ICH : E
  sqz : ℕ → E
  wp : ℕ → E
  rc : ℕ → E

/-- **Memory holds the buffers' honest words** (those the body reads). -/
structure OsMem (rd : Reader) (A : OsAt) (c : OsCfg) (tr : OsTr) : Prop where
  fixed : FixedMem rd A.P c tr
  T : ReadsAt rd A.T (tailC tr.Lf tr.xsR)
  PT : ReadsAt rd A.PT (ptC tr (c.levels.headD default).folds)
  PT1 : ReadsAt rd A.PT1 (pt1C tr (c.levels.headD default).folds)
  BD : ReadsAt rd A.BD (bdC c tr)
  LS : ReadsAt rd A.LS (lsC c tr)
  ICH : ReadsAt rd A.ICH (ichC c tr)
  sqz : ∀ i < c.levels.length, ReadsAt rd (A.sqz i) (sqzC c tr i)
  rc : ∀ i < c.levels.length, ReadsAt rd (A.rc i) (rcC c tr i)

/-- **The calls of `C` the body makes**, at their honest arguments and returns. -/
structure OsCallsOk (C : CallRel) (rd : Reader) (A : OsAt) (c : OsCfg) (tr : OsTr) : Prop where
  fold : ∀ args rets, MeaningOpeningFold rd args rets → C "opening_fold" args rets
  lv : ∀ i < c.levels.length, LvCallsOk C rd A.P c i (lvAt c i) (tr.L i) (A.sqz i) (A.wp i)
  res : ∀ i < c.levels.length, ResCallOk C A.P c i A.BD (A.rc i) (finM tr i)
  ffm : C ("fold_final_msg__L" ++ natStr c.yrLog) [A.P.fmsg, A.T] [multilinearEval tr.Lf.ms tr.Tc]

/-- The honest data of the body's levels. -/
def OsTr.Ds (tr : OsTr) (A : OsAt) : List LvDat := spDats tr.Ls 0 A.sqz A.wp

/-- The tail's words. -/
def OsTr.tailWords (c : OsCfg) (tr : OsTr) : List E := tr.xsR.take (2 * (c.yrLog - 1))

/-- **The body's values**, on the honest trace. -/
def osBodyF (c : OsCfg) (tr : OsTr) (σ : Val) (c0 c2 : E) (A : OsAt) : ℕ → E :=
  bodyF c σ A.P c0 c2 (tr.Ds A) A.T (tr.tailWords c) (multilinearEval tr.Lf.ms tr.Tc) A.PT A.PT1
    A.BD A.LS A.ICH (finI c tr c.levels.length)
    (fun j ↦ (ptC tr (c.levels.headD default).folds).getD j 0) (finB c tr)
    (Xof tr.rs tr.Fall tr.Tc) A.rc (finAcc c tr) (finM tr) (finI c tr) (finL c tr) (finPq c tr)
    (finD c tr) (Λof tr.rs) (Zof tr.rs) (Yof tr.rs tr.Fall tr.Tc)

/-- **What the run gives of its trace** beyond the body: each level's query step is one of the
run's (so `CapsAgree` speaks of it), and each level's tree has height `L.D`. -/
structure TrRun (c : OsCfg) (μ r : ℕ) (target : E) (S : KeccakState) (xs : List E) (os : List (List Opening))
    (root : Digest) (tr : OsTr) : Prop where
  qs : ∀ L ∈ tr.Ls, (L.height, L.qs.zip L.os) ∈
    queryStepsOf (whirOpen μ r target) (osStart μ r S xs os root)
  height : ∀ i < tr.Ls.length, (tr.L i).height = (tr.L i).D
  index : ∀ i < tr.Ls.length, (tr.L i).index = i
  width : ∀ i < tr.Ls.length, (tr.L i).width = lvWidth i (lvAt c i)

/-- **open_stacked's body, honestly, on the Spec's run.** -/
theorem osBodyA_honest {c : OsCfg} {μ r : ℕ} {cfg : List Whir.Level} (hF : CandFacts c μ r cfg)
    (hs : OsSizes c) {S : KeccakState} {root : Digest} {target : E} {xs : List E} {os : List (List Opening)}
    {w : WhirEnd} {s' : Fs} {roots' : List (Digest × ℕ × ℕ)}
    (hrun : RunsWith (whirOpen μ r target) ⟨capOf S, []⟩ xs os [(root, stackShape μ r)] w s'
      roots')
    (hnz : NoZeroChallenge μ r target S xs os root) :
    ∃ (c0 c2 : E) (tr : OsTr), TrFit c tr ∧ (tr.point (c.levels.headD default).folds).length = μ ∧
      ptC tr (c.levels.headD default).folds = w.point ++ List.replicate (pointCap - μ) 0 ∧
      pt1C tr (c.levels.headD default).folds =
        w.point.map (1 + ·) ++ List.replicate (pointCap - μ) 1 ∧
      (∀ (C : CallRel) (rd : Reader) (σ : Val) (A : OsAt),
        [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)] = capOf S → σ (.n 5) = target →
        σ (.n 6) = (digestHalves root).1 → σ (.n 7) = (digestHalves root).2 →
        ReadsAt rd (σ (.n 8)) xs → OsMem rd A c tr → OsCallsOk C rd A c tr →
        BlkF C rd σ 9 (osFinEnd c (osTlSt c).2.1 (osTlSt c).2.2) (osBodyF c tr σ c0 c2 A)
          (osBodyA c)
          (fun σ' ↦ (osFinishRet c (osTlSt c).2.1 (osTlSt c).2.2).map σ' =
            [w.target, A.PT, A.PT1, w.inner, w.residual] ∧ AgreeBelow 9 σ σ')) ∧
      TrRun c μ r target S xs os root tr := by
  obtain ⟨c0, c2, xs', Ls, hxs, hlc, hch, hqs⟩ := nz_trace hF hrun hnz
  set lane := (cfg.head?.map (·.fold)).getD 0 with hlane
  obtain ⟨hlane', -⟩ := levelsOk_lane hF.lok
  set tr : OsTr := ⟨Ls, xs'.drop (Ls.map SpLv.words).flatten.length⟩ with htr
  obtain ⟨hfit, hroot0, hE⟩ := trFit_of_run hF hch
  have hn := hF.n2
  -- the run's end is the trace's
  obtain ⟨osR, R, -, hres⟩ := hE.res
  have hw : w = tr.Lf.wend lane tr.xsR := (Prod.mk.inj hres).1
  have hFl := fall_length hF hfit
  have hpl : (tr.point (c.levels.headD default).folds).length = μ := by
    rw [point_length, hFl, hfit.tcLen, hF.mu]
  have hpoint : w.point = tr.point (c.levels.headD default).folds := by
    rw [hw, ← hlane', SpLv.wend]; rfl
  have hheight : ∀ i < tr.Ls.length, (tr.L i).height = (tr.L i).D := by
    intro i hi
    rcases i with _ | i
    · have h0 := chain_height0 hch
      simp only [List.getD_cons_zero, Prod.mk.injEq] at h0
      have hi0 : 0 < c.levels.length := by omega
      have hfit0 := hfit.fit 0 hi0
      have hlvb0 := hfit.lvb 0 hi0
      show (Ls.getD 0 default).height = (Ls.getD 0 default).D
      have h1 : (Ls.getD 0 default).height = (stackShape μ r).1 := congrArg Prod.fst h0.2
      have hml0 : (Ls.getD 0 default).ml = (lvAt c 0).logCols := hfit0.ml
      have hd0 : (lvAt c 0).depth = (lvAt c 0).logCols + (Ls.getD 0 default).level.logInvRate :=
        hlvb0.depth
      have hhd : c.levels.headD default = lvAt c 0 := by
        cases h' : c.levels with
        | nil => simp [h'] at hn
        | cons a b => simp [lvAt, h']
      rw [h1, hF.shape, hhd, SpLv.D, hml0, ← hd0]
    · exact chain_heights _ _ _ _ _ _ _ _ _ hch rfl i (by simpa using hi)
  obtain ⟨-, hat, -, -, -, -⟩ := chain_at _ _ _ _ _ _ _ _ _ hch
  have hindex : ∀ i < tr.Ls.length, (tr.L i).index = i := fun i hi ↦ by
    have := (hat i hi).index
    rw [Nat.zero_add] at this
    exact this
  have hwidth : ∀ i < tr.Ls.length, (tr.L i).width = lvWidth i (lvAt c i) := by
    intro i hi
    rcases i with _ | i
    · have h0 := chain_height0 hch
      simp only [List.getD_cons_zero, Prod.mk.injEq] at h0
      have h1 : (Ls.getD 0 default).width = (stackShape μ r).2 := congrArg Prod.snd h0.2
      have hhd : c.levels.headD default = lvAt c 0 := by
        cases h' : c.levels with
        | nil => simp [h'] at hn
        | cons a b => simp [lvAt, h']
      show (Ls.getD 0 default).width = _
      rw [h1, hF.shape, hhd]
    · have hw := chain_widths _ _ _ _ _ _ _ _ _ hch rfl i (by simpa using hi)
      have hl := (hat (i + 1) (by simpa using hi)).level
      have hlw := levelsOk_width 0 c.levels cfg hF.lok i (by rw [← hfit.len]; simpa using hi)
      show (Ls.getD (i + 1) default).width = _
      rw [hw, hl, hlw, Nat.zero_add]
  refine ⟨c0, c2, tr, hfit, hpl, by rw [ptC, hpoint, hpl], by rw [pt1C, hpoint, hpl], ?_,
    ⟨hqs, hheight, hindex, hwidth⟩⟩
  intro C rd σ A hcap h5 h6 h7 hrd hm hc
  -- the head's words
  rw [hxs] at hrd
  have h0 : LoadHolds rd (σ (.n 8)) 0 c0 := hrd 0 (by simp)
  have h2 : LoadHolds rd (σ (.n 8)) 1 c2 := hrd 1 (by simp)
  have hrd' : ReadsAt rd (σ (.n 8) * gen ^ 2) xs' := readsAt_right (xs := [c0, c2]) hrd
  have hr0 : LoadHolds rd A.P.roots 0 (σ (.n 6)) := by
    have := readsAt_map_range hm.fixed.roots (k := 0) (by omega)
    simp only [Nat.zero_mod, Nat.zero_div, ↓reduceIte, OsTr.L] at this
    rw [h6, ← hroot0]; exact this
  have hr1 : LoadHolds rd A.P.roots 1 (σ (.n 7)) := by
    have := readsAt_map_range hm.fixed.roots (k := 1) (by omega)
    simp only [show (1 : ℕ) % 2 = 1 from rfl, show (1 : ℕ) / 2 = 0 from rfl, one_ne_zero,
      ↓reduceIte, OsTr.L] at this
    rw [h7, ← hroot0]; exact this
  have hcan : AllCanonical [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)] := by
    rw [hcap]; exact capOf_canonical S
  have hsp : headSponge σ c0 c2 = ⟨capOf S, [(c0, dsObserve), (c2, dsObserve)]⟩ := by
    rw [headSponge, hcap]
  -- the levels
  obtain ⟨hlv, hO⟩ := lvsH_sp (C := C) (rd := rd) (P := A.P) A.sqz A.wp c.levels cfg 0
    ⟨target, [c0, target + c2, c2], [], []⟩ _ xs' os _ Ls _ (σ (.n 8) * gen ^ 2) hF.lok hch
    (by simpa using hF.off0.symm) hrd'
    (fun i hi ↦ by simpa [OsTr.L] using lvMemB_cont hF hfit hs hm.fixed hi (hm.sqz i hi))
    (fun i hi ↦ by simpa [OsTr.L] using hc.lv i hi)
  have hlvs : LvsH C rd A.P c 0 c.levels (tr.Ds A) (headSponge σ c0 c2) [c0, σ (.n 5) + c2, c2]
      (σ (.n 5)) (σ (.n 8) * gen ^ 2) := by
    rw [hsp, h5]; exact hlv
  have hBL : bodyLvs c σ c0 c2 (tr.Ds A) = lvsOut c 0 c.levels (spDats Ls 0 A.sqz A.wp)
      ⟨capOf S, [(c0, dsObserve), (c2, dsObserve)]⟩ [c0, target + c2, c2] target
      (σ (.n 8) * gen ^ 2) := by
    rw [bodyLvs, hsp, h5]; rfl
  -- the tail
  have hml : tr.Lf.ml = c.yrLog := by
    rw [hfit.lf, (hfit.fit _ (by omega)).ml]
    have := hF.last
    rwa [getLastD_eq_getD _ (by intro h; rw [h] at hn; simp at hn)] at this
  have hO' : ChainEnd rd lane (bodyLvs c σ c0 c2 (tr.Ds A)) tr.Lf tr.xsR
      (w, ⟨s', [], [], roots'⟩) := by
    rw [hBL]; exact hO
  obtain ⟨hxl, hrdT, hT, hlast, hzero, htgt⟩ := tail_sp hO' hml hF.ylog hs.yr hm.T
  -- the body
  refine BlkF.mono (osBodyA_complete (C := C) (rd := rd) σ A.P (Ds := tr.Ds A)
    (xs := tr.tailWords c) (Y := multilinearEval tr.Lf.ms tr.Tc)
    (by intro h; have := congrArg List.length h; simp at this; omega) h0 h2 hr0 hr1
    (fun i hi ↦ readsAt_map_range hm.fixed.win hi) hcan hlvs hc.fold hxl hrdT hT hlast hzero
    hc.ffm (fin_pt hF hfit hs hm.fixed hm.T hm.PT hm.PT1)
    (fun i hi ↦ fin_bases hF hfit hs hm.fixed hm.T hm.BD hm.LS hi)
    (by have := readsAt_map_range hm.ICH (k := 0) (by omega); simpa [finI] using this)
    (fun i hi ↦ fin_res hF hfit hs hm.fixed hm.BD hm.LS hm.ICH hi (hm.rc i hi) (hc.res i hi))
    (readsAt_map_range hm.ICH (k := c.levels.length) (by omega))
    (fin_ood hF hfit hs hm.fixed hm.T)) fun σ' ⟨hr, ha⟩ ↦ ⟨?_, ha⟩
  rw [hr, OsTr.tailWords, htgt, fin_inner hF hfit, hw]
  rfl

end
end LeanVM.Guest.B1.Whir
