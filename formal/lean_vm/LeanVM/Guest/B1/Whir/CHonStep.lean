/-
  LeanVM.Guest.B1.Whir.CHonStep

  A level of open_stacked's body at the honest data's values: from the start the levels keep
  (`QAt`) to the next, its allocation and its helpers' dispatches (`RAt`).
-/

module

public import LeanVM.Guest.B1.Whir.CHonAlloc
public import LeanVM.Guest.B1.Whir.CHonLvC

/-!
# A level's step

`QAt h b tabs cur xs l st σ`: the state `st` before level `l` (`osStAt`), its invariants, the
head's buffers' pointers at `b`, the window table, the rate's selector at every level, the
carried capacity, the claim and the cursor at the honest data's (`OsHD.capAt`, `claimAt`,
`xsAt`). `RAt h b tabs l batched σ'`: level `l`'s allocation (`bufsAt`) and its dispatches into
`level_positions` and `level_queries` at their honest values, as `OsHelperVals` states them.

`lvMid_step`, `lvFin_step`: a level's block from `QAt l` to `QAt (l + 1)` and `RAt l`, from its
calls and memory (`MidC`, `FinC`) at the honest values and the honest data's equalities, with the
level's calls' values (`cvMid`, `cvFin`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Guest.Memory LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakHash

@[expose] public section

namespace OsHD

variable (h : OsHD)

/-- Level `l`'s capacity entering its positions. -/
def capL (l : ℕ) : List E := capOf ((h.L l).qS h.logN)

/-- Level `l`'s `λ`. -/
def lamAt (l : ℕ) : E := (h.L l).lam h.logN

end OsHD

/-- **The start of level `l`.** -/
structure QAt (h : OsHD) (b : ℕ) (tabs cur : E) (xs : List E) (l : ℕ) (st : OsSt) (σ : Val) :
    Prop where
  eq : st = osStAt h.c l
  ok : st.Ok σ
  ptr : ∀ i < 9, σ (.n (12 + 2 * i)) = osPtrA h.c b i
  qp : σ (.n osQpos) = osPtrA h.c b osIxQposA
  qb : σ (.n osQbp) = osPtrA h.c b osIxQbpA
  tabs : σ (.n osTabs) = tabs
  rate : ∀ l' < h.c.levels.length, LvRate σ h.c l' (h.c.levels.getD l' default)
  fs : st.fsv σ = h.capAt l
  claim : σ (.n st.claim) = h.claimAt l
  cur : st.cur σ = cur * gen ^ (xs.length - (h.xsAt l).length)
  co : st.co ≤ 2
  pad : ∃ p, st.pad = some p
  rtl : st.rts.length = l
  rts : ∀ l' < l, RtVals σ st.rts st.k l' (h.c.levels.getD l' default)

theorem QAt.agree {h : OsHD} {b : ℕ} {tabs cur : E} {xs : List E} {l : ℕ} {st : OsSt} {σ σ' : Val}
    (hq : QAt h b tabs cur xs l st σ) (ha : AgreeBelow st.k σ σ') : QAt h b tabs cur xs l st σ' := by
  have k33 := hq.ok.sf.k
  obtain ⟨e1, -, e3, e4⟩ := OsSt.agree hq.ok.sf.below ha
  refine ⟨hq.eq, hq.ok.agree ha, fun i hi ↦ by rw [ha _ (by omega)]; exact hq.ptr i hi,
    by rw [ha _ (by show 36 < st.k; omega)]; exact hq.qp, by rw [ha _ (by show 37 < st.k; omega)]; exact hq.qb,
    by rw [ha _ (by show 10 < st.k; omega)]; exact hq.tabs, fun l' hl' ↦ ?_, by rw [e1]; exact hq.fs,
    by rw [e3]; exact hq.claim, by rw [e4]; exact hq.cur, hq.co, hq.pad, hq.rtl,
    fun l' hl' ↦ (hq.rts l' hl').agree le_rfl ha⟩
  obtain ⟨ri, hri, hx, hlen, hlv⟩ := hq.rate l' hl'
  exact ⟨ri, hri, by rw [ha _ (show 0 < st.k by omega)]; exact hx, hlen, hlv⟩

/-- **Level `l`'s allocation and its helpers' dispatches' values.** -/
def RAt (h : OsHD) (b : ℕ) (tabs : E) (l : ℕ) (batched : E) (σ' : Val) : Prop :=
  let c := h.c
  let lv := c.levels.getD l default
  AllocsAt σ' (osLevel c l lv (osStAt c l)).1 = bufsAt c b (12 + l) 1 ∧
  (osLpCallOf c l).1.map σ' = h.word l 0 :: h.capL l ++
    [osPtrA c b osIxQposA * gen ^ lv.posOff, osPtrA c b osIxQbpA * gen ^ lv.posOff, tabs,
      gen ^ lv.squeezes] ∧
  (osLpCallOf c l).2.map σ' = ((⟨h.capL l, []⟩ : Fs).squeezeN (lv.squeezes - 1)).2.cap ∧
  (osLqCallOf c l).1.map σ' =
    [if l = c.yrLevel then 0 else h.lamAt l, if l = c.yrLevel then 0 else h.li l,
      osPtrA c b osIxCoefsA * gen ^ (2 * lv.foldsOff), osHsPtrA c b l,
      osPtrA c b osIxQposA * gen ^ lv.posOff, osPtrA c b osIxQbpA * gen ^ lv.posOff] ∧
  (osLqCallOf c l).2.map σ' =
    [(digestHalves (h.root l)).1, (digestHalves (h.root l)).2, batched,
      (if l = c.yrLevel then 0 else h.lamAt l) ^ lv.queries]

/-! ## The states -/

theorem osStFrom_get (c : OsCfg) : ∀ (lvl : ℕ) (lvs : List OsLv) (s : OsSt) (i : ℕ), i < lvs.length →
    osStFrom c lvl lvs s (i + 1) = (osLevel c (lvl + i) (lvs.getD i default) (osStFrom c lvl lvs s i)).2
  | _, [], _, _, h => absurd h (by simp)
  | lvl, lv :: rest, s, 0, _ => by simp [osStFrom, osLevels]
  | lvl, lv :: rest, s, i + 1, h => by
    rw [osStFrom_succ, osStFrom_succ, osStFrom_get c (lvl + 1) rest _ i (by simp at h; omega)]
    simp only [List.getD_cons_succ, show lvl + 1 + i = lvl + (i + 1) by ring]

/-! ## The allocations' values -/

theorem logG_gw {e : ℕ} (he : e < 2 ^ 64 - 1) : logG (gw e) = e := by
  rw [gw_eq (show e < u128Bound by unfold u128Bound; omega), logG_gen_pow he]

theorem allocsAt_one {σ : Val} {ss : List Stmt} {a1 s1 : ℕ}
    (hf : ss.filterMap Stmt.allocSz = [(.n a1, .inr (.n s1))]) :
    AllocsAt σ ss = [(σ (.n a1), logG (σ (.n s1)))] := by
  simp [AllocsAt, hf]

/-! ## A non-final level -/

variable {M : Reader → Prop} {H : CallRel → Reader → Prop}

/-- The next level's start from a level's block: the state's invariants, pointers, rates and
`level_rate` values. -/
theorem QAt.next {h : OsHD} {b : ℕ} {tabs cur : E} {xs : List E} {l : ℕ} {st : OsSt} {σ σ' : Val}
    (hq : QAt h b tabs cur xs l st σ) (hl : l < h.c.levels.length)
    (hstep : OsStep σ σ' st (osLevel h.c l (h.c.levels.getD l default) st).2)
    (hk9 : st.k + 9 ≤ (osLevel h.c l (h.c.levels.getD l default) st).2.k)
    (hpo : (h.c.levels.getD l default).posOff < u128Bound) (hqu : (h.c.levels.getD l default).queries < u128Bound)
    (hrv : ∀ j < 4, σ' (.n (st.k + 1 + 2 * j + 1)) = gw ((osRateVals (h.c.levels.getD l default)).getD j 0))
    (hfs : (osLevel h.c l (h.c.levels.getD l default) st).2.fsv σ' = h.capAt (l + 1))
    (hcl : σ' (.n (osLevel h.c l (h.c.levels.getD l default) st).2.claim) = h.claimAt (l + 1))
    (hcur : (osLevel h.c l (h.c.levels.getD l default) st).2.cur σ' =
      cur * gen ^ (xs.length - (h.xsAt (l + 1)).length)) :
    QAt h b tabs cur xs (l + 1) (osLevel h.c l (h.c.levels.getD l default) st).2 σ' := by
  have k33 := hq.ok.sf.k
  obtain ⟨hco, hpad, hrts⟩ := osLevel_fields h.c l (h.c.levels.getD l default) st hq.pad
  refine ⟨?_, hstep.ok, fun i hi ↦ by rw [hstep.agree _ (by omega)]; exact hq.ptr i hi,
    by rw [hstep.agree _ (by show 36 < st.k; omega)]; exact hq.qp,
    by rw [hstep.agree _ (by show 37 < st.k; omega)]; exact hq.qb,
    by rw [hstep.agree _ (by show 10 < st.k; omega)]; exact hq.tabs, fun l' hl' ↦ ?_, hfs, hcl, hcur, hco, hpad,
    by rw [hrts, List.length_append, hq.rtl]; rfl, fun l' hl' ↦ ?_⟩
  · rw [hq.eq, osStAt, osStAt, osStFrom_get h.c 0 h.c.levels _ l hl, Nat.zero_add]
  · obtain ⟨ri, hri, hx, hlen, hlv'⟩ := hq.rate l' hl'
    exact ⟨ri, hri, by rw [hstep.agree _ (show 0 < st.k by omega)]; exact hx, hlen, hlv'⟩
  · rw [hrts]
    rcases Nat.lt_or_ge l' l with h1 | h1
    · exact ((hq.rts l' h1).agree hstep.le hstep.agree).append _ (by rw [hq.rtl]; exact h1)
    · obtain rfl : l' = l := by omega
      exact rtVals_new hq.rtl hk9 hpo hqu hrv

/-- **A non-final level's step.** -/
theorem lvMid_step {h : OsHD} {b : ℕ} {tabs cur : E} {xs : List E} {l : ℕ} (hS : BodyStatic h.c)
    (hl : l < h.c.yrLevel) {st : OsSt} {σ : Val} (hq : QAt h b tabs cur xs l st σ) (W : MidW)
    (rd0 : Reader) (hl0 : LowDef 11 rd0) (hrwl : W.rw.length = 5 * (h.c.levels.getD l default).folds)
    (hpS : W.pS = osPtrA h.c b (12 + l))
    (hf5 : 5 * (h.c.levels.getD l default).folds + 2 < u128Bound)
    (hoff : (l + 1) * ligColsCap < u128Bound) (hpo : (h.c.levels.getD l default).posOff < u128Bound)
    (hsq : (h.c.levels.getD l default).squeezes < u128Bound)
    (hqu : (h.c.levels.getD l default).queries < u128Bound)
    (h3 : 2 * (h.c.levels.getD l default).foldsOff < u128Bound) (hh8 : l * hsStride < u128Bound)
    (hiz : IsZeroC (HM M H))
    (hC : ∀ C rd, HM M H C rd → MidC C rd σ h.c l (h.c.levels.getD l default) (h.capAt l) (h.claimAt l)
      (cur * gen ^ (xs.length - (h.xsAt l).length)) W)
    (hag0 : ∀ C rd, H C rd → LowAgree rd rd0)
    (hcap' : capOf (W.SL (h.c.levels.getD l default) (h.capAt l) (h.claimAt l)) = h.capAt (l + 1))
    (hcl' : W.claimOut (h.c.levels.getD l default) (h.capAt l) (h.claimAt l) = h.claimAt (l + 1))
    (hcur' : xs.length - (h.xsAt l).length +
        (5 * (h.c.levels.getD l default).folds + (2 + (h.c.levels.getD l default).folds) + 3) =
      xs.length - (h.xsAt (l + 1)).length)
    (hw0 : rdCell (W.S2 (h.c.levels.getD l default) (h.capAt l) (h.claimAt l)) 0 = h.word l 0)
    (hcapL : capOf (W.S2 (h.c.levels.getD l default) (h.capAt l) (h.claimAt l)) = h.capL l)
    (hlamv : W.lam (h.c.levels.getD l default) (h.capAt l) (h.claimAt l) = h.lamAt l)
    (hr0 : W.r0 = (digestHalves (h.root l)).1) (hr1 : W.r1 = (digestHalves (h.root l)).2) :
    BlkA M H σ st.k (osLevel h.c l (h.c.levels.getD l default) st).2.k
      (osLevel h.c l (h.c.levels.getD l default) st).1 (fun σ' ↦
      st.k ≤ (osLevel h.c l (h.c.levels.getD l default) st).2.k ∧
      QAt h b tabs cur xs (l + 1) (osLevel h.c l (h.c.levels.getD l default) st).2 σ' ∧
      RAt h b tabs l W.batched σ' ∧
      cvOf (osLevel h.c l (h.c.levels.getD l default) st).1 σ' = cvMid l (h.c.levels.getD l default)
        (h.capAt l) (h.claimAt l) (cur * gen ^ (xs.length - (h.xsAt l).length)) W (σ' (.n osRate))
        (osPtrA h.c b 7) (osPtrA h.c b 3) (osPtrA h.c b 6) (osPtrA h.c b osIxQposA) (osPtrA h.c b osIxQbpA)
        tabs) := by
  set c := h.c with hc
  set lv := c.levels.getD l default with hlv
  obtain ⟨-, hLv, -, hlen0, hyr0, -, hsent0, -, -, -, -, -, -, -, -, hlt0⟩ := hS
  have hyr : c.yrLevel + 1 = c.levels.length := hyr0
  have hlen : (osSizesL c).length = 20 + c.yrLevel := hlen0
  have hsent : ∀ l < c.yrLevel, (osSizesL c).getD (12 + l) 0 = 2 + (c.levels.getD l default).folds := hsent0
  have hlt : ∀ j < (osSizesL c).length, (osSizesL c).getD j 0 < 2 ^ 64 - 1 := hlt0
  have hst : st = osStAt c l := hq.eq
  have hfs := hq.fs
  have hcl := hq.claim
  have hcu := hq.cur
  have hfin : l ≠ c.yrLevel := by omega
  have hblk := osLevelMid_complete (M := M) (H := H) (c := c) (lvl := l) (lv := lv) (st := st) σ hq.ok.sf
    (fun _ _ _ ↦ hq.ok) hfin W rd0 hl0 hrwl hq.pad (by have := hq.co; omega) hoff hpo hsq h3 hh8 hiz
    (fun _ _ _ ↦ hq.rate l (by show l < c.levels.length; omega))
    (fun C rd hH ↦ by rw [hfs, hcl, hcu]; exact hC C rd hH) hag0
  refine hblk.mono fun σ' ⟨hstep, eF, ecur, ecl, hrv, e1, e2, pa, pr, qa, qr, hk9, hcv⟩ ↦ ?_
  have ht : σ (.n osTabs) = tabs := hq.tabs
  have hptr : ∀ i < 9, σ (.n (12 + 2 * i)) = osPtrA c b i := hq.ptr
  rw [hfs, hcl, hcu] at *
  have hsz := hsent l hl
  have ePos : osLpCallOf c l = osPosCall (osPosStL c l lv st) := by rw [hst]; rfl
  have eQ : osLqCallOf c l = osQCallOf c l lv (osPreQ c l lv st) := by rw [hst]; rfl
  refine ⟨hstep.le, hq.next (by show l < c.levels.length; omega) hstep hk9 hpo hqu hrv ?_ ?_ ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · have := congrArg Fs.cap eF
    simp only [OsSt.F] at this
    rw [← hcap']; exact this
  · rw [ecl, hcl']
  · rw [ecur, ← hcur', MidW.cur1]
    simp only [mul_assoc, ← pow_add]
    ring_nf
  · have hf := hLv l (by omega)
    simp only [lvAllocsV, hfin, ↓reduceIte] at hf
    rw [← hst] at hf
    unfold osRndSt at e1 e2
    rw [show osStAt c l = st from hst.symm, allocsAt_one hf, e1, e2, hpS, bufsAt_one, hsz,
      logG_gw (by have := hlt (12 + l) (by omega); rwa [hsz] at this)]
  · rw [ePos, pa, hw0, hcapL]
    simp only [lpArgsV, ht, hq.qp, hq.qb]
    rfl
  · rw [ePos, pr, MidW.cap3, hcapL]; rfl
  · rw [eQ, qa, hlamv, show σ (.n osCoefs) = osPtrA c b osIxCoefsA from hptr 3 (by norm_num),
      show σ (.n osHs) = osPtrA c b osIxHsA from hptr 6 (by norm_num), hq.qp, hq.qb, ← hc]
    simp only [hfin, ↓reduceIte, OsHD.li, OsHD.lamAt, osHsPtrA, hlv]
  · rw [eQ, qr, hlamv, hr0, hr1, ← hc]
    simp only [hfin, ↓reduceIte, OsHD.lamAt, hlv]
  · rw [hcv, show σ (.n osRate) = σ' (.n osRate) from (hstep.agree _ (by have := hq.ok.sf.k; show 0 < st.k; omega)).symm,
      show σ (.n osOodz) = osPtrA c b 7 from hptr 7 (by norm_num),
      show σ (.n osCoefs) = osPtrA c b 3 from hptr 3 (by norm_num),
      show σ (.n osHs) = osPtrA c b 6 from hptr 6 (by norm_num), hq.qp, hq.qb, ht]

/-! ## The final level -/

/-- **The final level's step.** -/
theorem lvFin_step {h : OsHD} {b : ℕ} {tabs cur : E} {xs : List E} (hS : BodyStatic h.c)
    {st : OsSt} {σ : Val} (hq : QAt h b tabs cur xs h.c.yrLevel st σ) (W : FinWD)
    (rd0 : Reader) (hl0 : LowDef 11 rd0)
    (hrwl : W.rw.length = 5 * (h.c.levels.getD h.c.yrLevel default).folds)
    (hpH : W.pH = osPtrA h.c b (12 + h.c.yrLevel))
    (hf5 : 5 * (h.c.levels.getD h.c.yrLevel default).folds + 2 < u128Bound)
    (hpo : (h.c.levels.getD h.c.yrLevel default).posOff < u128Bound)
    (hsq : (h.c.levels.getD h.c.yrLevel default).squeezes < u128Bound)
    (hqu : (h.c.levels.getD h.c.yrLevel default).queries < u128Bound)
    (h3 : 2 * (h.c.levels.getD h.c.yrLevel default).foldsOff < u128Bound)
    (hh8 : h.c.yrLevel * hsStride < u128Bound)
    (hC : ∀ C rd, HM M H C rd → FinC C rd σ h.c h.c.yrLevel (h.c.levels.getD h.c.yrLevel default)
      (h.capAt h.c.yrLevel) (h.claimAt h.c.yrLevel) (cur * gen ^ (xs.length - (h.xsAt h.c.yrLevel).length)) W)
    (hag0 : ∀ C rd, H C rd → LowAgree rd rd0)
    (hcap' : W.cap3 (h.c.levels.getD h.c.yrLevel default) (h.capAt h.c.yrLevel) (h.claimAt h.c.yrLevel) =
      h.capAt (h.c.yrLevel + 1))
    (hcl' : W.cl1 (h.c.levels.getD h.c.yrLevel default) (h.capAt h.c.yrLevel) (h.claimAt h.c.yrLevel) =
      h.claimAt (h.c.yrLevel + 1))
    (hcur' : xs.length - (h.xsAt h.c.yrLevel).length +
        (5 * (h.c.levels.getD h.c.yrLevel default).folds +
          (h.c.yrLen + (h.c.levels.getD h.c.yrLevel default).folds + 1)) =
      xs.length - (h.xsAt (h.c.yrLevel + 1)).length)
    (hw0 : cellsOfState (W.S2 (h.c.levels.getD h.c.yrLevel default) (h.capAt h.c.yrLevel)
      (h.claimAt h.c.yrLevel)) false 0 = h.word h.c.yrLevel 0)
    (hcapL : capOf (W.S2 (h.c.levels.getD h.c.yrLevel default) (h.capAt h.c.yrLevel)
      (h.claimAt h.c.yrLevel)) = h.capL h.c.yrLevel)
    (hr0 : W.r0 = (digestHalves (h.root h.c.yrLevel)).1)
    (hr1 : W.r1 = (digestHalves (h.root h.c.yrLevel)).2) :
    BlkA M H σ st.k (osLevel h.c h.c.yrLevel (h.c.levels.getD h.c.yrLevel default) st).2.k
      (osLevel h.c h.c.yrLevel (h.c.levels.getD h.c.yrLevel default) st).1 (fun σ' ↦
      st.k ≤ (osLevel h.c h.c.yrLevel (h.c.levels.getD h.c.yrLevel default) st).2.k ∧
      QAt h b tabs cur xs (h.c.yrLevel + 1)
        (osLevel h.c h.c.yrLevel (h.c.levels.getD h.c.yrLevel default) st).2 σ' ∧
      RAt h b tabs h.c.yrLevel W.batched σ' ∧
      cvOf (osLevel h.c h.c.yrLevel (h.c.levels.getD h.c.yrLevel default) st).1 σ' =
        cvFin h.c (h.c.levels.getD h.c.yrLevel default) (h.capAt h.c.yrLevel) (h.claimAt h.c.yrLevel)
          (cur * gen ^ (xs.length - (h.xsAt h.c.yrLevel).length)) W (σ' (.n osRate)) (osPtrA h.c b 0)
          (osPtrA h.c b 3) (osPtrA h.c b osIxQposA) (osPtrA h.c b osIxQbpA) tabs) := by
  set c := h.c with hc
  set l := c.yrLevel with hl
  set lv := c.levels.getD l default with hlv
  obtain ⟨-, hLv, -, hlen0, hyr0, -, -, hlane0, -, -, -, -, -, -, -, hlt0⟩ := hS
  have hyr : c.yrLevel + 1 = c.levels.length := hyr0
  have hlen : (osSizesL c).length = 20 + c.yrLevel := hlen0
  have hlane : (osSizesL c).getD (12 + c.yrLevel) 0 = c.yrLen + (c.levels.getD c.yrLevel default).folds := hlane0
  have hlt : ∀ j < (osSizesL c).length, (osSizesL c).getD j 0 < 2 ^ 64 - 1 := hlt0
  have hst : st = osStAt c l := hq.eq
  have hfs := hq.fs
  have hcl := hq.claim
  have hcu := hq.cur
  have hblk := osLevelFin_complete (M := M) (H := H) (c := c) (lvl := l) (lv := lv) (st := st) σ hq.ok.sf
    (fun _ _ _ ↦ hq.ok) rfl W rd0 hl0 hrwl hq.pad (by have := hq.co; omega) hpo hsq h3 hh8
    (fun _ _ _ ↦ hq.rate l (by show l < c.levels.length; omega))
    (fun C rd hH ↦ by rw [hfs, hcl, hcu]; exact hC C rd hH) hag0
  refine hblk.mono fun σ' ⟨hstep, eF, ecur, ecl, hrv, e3, e4, pa, pr, qa, qr, hk9, hcv⟩ ↦ ?_
  have ht : σ (.n osTabs) = tabs := hq.tabs
  have hptr : ∀ i < 9, σ (.n (12 + 2 * i)) = osPtrA c b i := hq.ptr
  rw [hfs, hcl, hcu] at *
  have ePos : osLpCallOf c l = osPosCall (osPosStL c l lv st) := by rw [hst]; rfl
  have eQ : osLqCallOf c l = osQCallOf c l lv (osPreQ c l lv st) := by rw [hst]; rfl
  have eH : (osPreQ c l lv st).hs = (osPositions c l (osPosStL c l lv st)).2.k + 1 := by
    simp only [osPreQ, osHsFinal, osPosStL, hl, ↓reduceIte]; rfl
  refine ⟨hstep.le, hq.next (by show l < c.levels.length; omega) hstep hk9 hpo hqu hrv ?_ ?_ ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · have := congrArg Fs.cap eF
    simp only [OsSt.F] at this
    rw [← hcap']; exact this
  · rw [ecl, hcl']
  · rw [ecur, ← hcur', MidW.cur1]
    simp only [mul_assoc, ← pow_add]
    ring_nf
  · have hf := hLv l (by omega)
    simp only [lvAllocsV, hl, ↓reduceIte] at hf
    rw [← hst] at hf
    have e3' : σ' (.n (osPositions c l (osQGrind (osFinalMsg c lv (osRounds true lv.foldsOff lv.folds
        (osRates c l st).2).2).2).2).2.k) = gw (c.yrLen + lv.folds) := by
      have : osPosStL c l lv st = (osQGrind (osFinalMsg c lv (osRounds true lv.foldsOff lv.folds
          (osRates c l st).2).2).2).2 := by simp only [osPosStL, hl, ↓reduceIte]; rfl
      rw [← this]; exact e3
    have e4' : σ' (.n ((osPositions c l (osQGrind (osFinalMsg c lv (osRounds true lv.foldsOff lv.folds
        (osRates c l st).2).2).2).2).2.k + 1)) = W.pH := by
      have : osPosStL c l lv st = (osQGrind (osFinalMsg c lv (osRounds true lv.foldsOff lv.folds
          (osRates c l st).2).2).2).2 := by simp only [osPosStL, hl, ↓reduceIte]; rfl
      rw [← this, ← eH]; exact e4
    rw [show osStAt c l = st from hst.symm, allocsAt_one hf, e3', e4', hpH, bufsAt_one, hlane,
      logG_gw (by have := hlt (12 + l) (by omega); rwa [hlane] at this)]
  · rw [ePos, pa, hw0, hcapL]
    simp only [lpArgsV, ht, hq.qp, hq.qb]
    rfl
  · rw [ePos, pr, FinWD.cap3, hcapL]; rfl
  · rw [eQ, qa, show σ (.n osCoefs) = osPtrA c b osIxCoefsA from hptr 3 (by norm_num), hq.qp, hq.qb, hpH,
      ← hc]
    simp only [hl, ↓reduceIte, osHsPtrA, osIxLaneA, hlv]
  · rw [eQ, qr, hr0, hr1, ← hc]
    simp only [hl, ↓reduceIte, hlv]
  · rw [hcv, show σ (.n osRate) = σ' (.n osRate) from (hstep.agree _ (by have := hq.ok.sf.k; show 0 < st.k; omega)).symm,
      show σ (.n osFmsg) = osPtrA c b 0 from hptr 0 (by norm_num),
      show σ (.n osCoefs) = osPtrA c b 3 from hptr 3 (by norm_num), hq.qp, hq.qb, ht]

end
end LeanVM.Guest.B1.Whir
