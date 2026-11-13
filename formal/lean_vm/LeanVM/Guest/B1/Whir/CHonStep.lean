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
calls and memory (`MidC`, `FinC`) at the honest values and the honest data's equalities.
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
  ptr : ∀ i < 11, σ (.n (12 + 2 * i)) = osPtrA h.c b i
  tabs : σ (.n osTabs) = tabs
  rate : ∀ l' < h.c.levels.length, LvRate σ h.c l' (h.c.levels.getD l' default)
  fs : st.fsv σ = h.capAt l
  claim : σ (.n st.claim) = h.claimAt l
  cur : st.cur σ = cur * gen ^ (xs.length - (h.xsAt l).length)

theorem QAt.agree {h : OsHD} {b : ℕ} {tabs cur : E} {xs : List E} {l : ℕ} {st : OsSt} {σ σ' : Val}
    (hq : QAt h b tabs cur xs l st σ) (ha : AgreeBelow st.k σ σ') : QAt h b tabs cur xs l st σ' := by
  have k33 := hq.ok.sf.k
  obtain ⟨e1, -, e3, e4⟩ := OsSt.agree hq.ok.sf.below ha
  refine ⟨hq.eq, hq.ok.agree ha, fun i hi ↦ by rw [ha _ (by omega)]; exact hq.ptr i hi,
    by rw [ha _ (by show 10 < st.k; omega)]; exact hq.tabs, fun l' hl' ↦ ?_, by rw [e1]; exact hq.fs,
    by rw [e3]; exact hq.claim, by rw [e4]; exact hq.cur⟩
  obtain ⟨ri, hri, hx, hlen, hlv⟩ := hq.rate l' hl'
  exact ⟨ri, hri, by rw [ha _ (show 0 < st.k by omega)]; exact hx, hlen, hlv⟩

/-- **Level `l`'s allocation and its helpers' dispatches' values.** -/
def RAt (h : OsHD) (b : ℕ) (tabs : E) (l : ℕ) (batched : E) (σ' : Val) : Prop :=
  let c := h.c
  let lv := c.levels.getD l default
  AllocsAt σ' (osLevel c l lv (osStAt c l)).1 = bufsAt c b (11 + l) 1 ∧
  (osLpCallOf c l).1.map σ' = h.word l 0 :: h.capL l ++
    [osPtrA c b osIxQposA * gen ^ lv.posOff, osPtrA c b osIxQbpA * gen ^ lv.posOff, tabs] ∧
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

variable {H : CallRel → Reader → Prop}

/-- **A non-final level's step.** -/
theorem lvMid_step {h : OsHD} {b : ℕ} {tabs cur : E} {xs : List E} {l : ℕ} (hS : BodyStatic h.c)
    (hl : l < h.c.yrLevel) {st : OsSt} {σ : Val} (hq : QAt h b tabs cur xs l st σ) (W : MidW)
    (hpS : W.pS = osPtrA h.c b (11 + l))
    (hr3 : 2 * ((h.c.levels.getD l default).foldsOff + (h.c.levels.getD l default).folds) < u128Bound)
    (hoff : (l + 1) * ligColsCap < u128Bound) (hpo : (h.c.levels.getD l default).posOff < u128Bound)
    (h3 : 2 * (h.c.levels.getD l default).foldsOff < u128Bound) (hh8 : l * hsStride < u128Bound)
    (hlam : W.lam (h.c.levels.getD l default) (h.capAt l) (h.claimAt l) ≠ 0)
    (hC : ∀ C rd, H C rd → MidC C rd σ h.c l (h.c.levels.getD l default) (h.capAt l) (h.claimAt l)
      (cur * gen ^ (xs.length - (h.xsAt l).length)) W)
    (hcap' : capOf (W.SL (h.c.levels.getD l default) (h.capAt l) (h.claimAt l)) = h.capAt (l + 1))
    (hcl' : W.claimOut (h.c.levels.getD l default) (h.capAt l) (h.claimAt l) = h.claimAt (l + 1))
    (hcur' : xs.length - (h.xsAt l).length +
        (5 * (h.c.levels.getD l default).folds + (2 + (h.c.levels.getD l default).folds) + 3) =
      xs.length - (h.xsAt (l + 1)).length)
    (hw0 : rdCell (W.S2 (h.c.levels.getD l default) (h.capAt l) (h.claimAt l)) 0 = h.word l 0)
    (hcapL : capOf (W.S2 (h.c.levels.getD l default) (h.capAt l) (h.claimAt l)) = h.capL l)
    (hlamv : W.lam (h.c.levels.getD l default) (h.capAt l) (h.claimAt l) = h.lamAt l)
    (hr0 : W.r0 = (digestHalves (h.root l)).1) (hr1 : W.r1 = (digestHalves (h.root l)).2) :
    BlkA H σ st.k (osLevel h.c l (h.c.levels.getD l default) st).2.k
      (osLevel h.c l (h.c.levels.getD l default) st).1 (fun σ' ↦
      st.k ≤ (osLevel h.c l (h.c.levels.getD l default) st).2.k ∧
      QAt h b tabs cur xs (l + 1) (osLevel h.c l (h.c.levels.getD l default) st).2 σ' ∧
      RAt h b tabs l W.batched σ') := by
  set c := h.c with hc
  set lv := c.levels.getD l default with hlv
  obtain ⟨-, hLv, -, hlen0, hyr0, -, hsent0, -, -, -, -, -, -, -, -, hlt0⟩ := hS
  have hyr : c.yrLevel + 1 = c.levels.length := hyr0
  have hlen : (osSizesL c).length = 19 + c.yrLevel := hlen0
  have hsent : ∀ l < c.yrLevel, (osSizesL c).getD (11 + l) 0 = 2 + (c.levels.getD l default).folds := hsent0
  have hlt : ∀ j < (osSizesL c).length, (osSizesL c).getD j 0 < 2 ^ 64 - 1 := hlt0
  have hst : st = osStAt c l := hq.eq
  have hfs := hq.fs
  have hcl := hq.claim
  have hcu := hq.cur
  have hfin : l ≠ c.yrLevel := by omega
  have hblk := osLevelMid_complete (H := H) (c := c) (lvl := l) (lv := lv) (st := st) σ hq.ok.sf
    (fun _ _ _ ↦ hq.ok) hfin W hr3 hoff hpo h3 hh8 (by rw [hfs, hcl]; exact hlam)
    (fun _ _ _ ↦ hq.rate l (by show l < c.levels.length; omega))
    (fun C rd hH ↦ by rw [hfs, hcl, hcu]; exact hC C rd hH)
  refine hblk.mono fun σ' ⟨hstep, eF, ecur, ecl, e1, e2, pa, pr, qa, qr⟩ ↦ ?_
  have k33 := hq.ok.sf.k
  have hp : ∀ i < 11, σ' (.n (12 + 2 * i)) = osPtrA c b i := fun i hi ↦ by
    rw [hstep.agree _ (by omega)]; exact hq.ptr i hi
  have ht : σ (.n osTabs) = tabs := hq.tabs
  have hptr : ∀ i < 11, σ (.n (12 + 2 * i)) = osPtrA c b i := hq.ptr
  rw [hfs, hcl, hcu] at *
  have hsz := hsent l hl
  have ePos : osLpCallOf c l = osPosCall c lv (osCommit c l lv (osRounds c.plan lv.foldsOff lv.folds st).2).2 := by
    rw [hst]; simp only [osLpCallOf, osPosSt, osPosCall, hfin, ↓reduceIte]; rfl
  have eQ : osLqCallOf c l = osQCallOf c l lv (osPreQ c l lv st) := by rw [hst]; rfl
  have q9 : σ (.n osQpos) = osPtrA c b osIxQposA := hptr 9 (by norm_num)
  have q10 : σ (.n osQbp) = osPtrA c b osIxQbpA := hptr 10 (by norm_num)
  refine ⟨hstep.le, ⟨?_, hstep.ok, hp, ?_, fun l' hl' ↦ ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hq.eq, osStAt, osStAt, osStFrom_get c 0 c.levels _ l (by omega), Nat.zero_add]
  · rw [hstep.agree _ (by show 10 < st.k; omega)]; exact ht
  · obtain ⟨ri, hri, hx, hlen, hlv'⟩ := hq.rate l' hl'
    exact ⟨ri, hri, by rw [hstep.agree _ (show 0 < st.k by omega)]; exact hx, hlen, hlv'⟩
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
    rw [show osStAt c l = st from hst.symm, allocsAt_one hf, e1, e2, hpS, bufsAt_one, hsz,
      logG_gw (by have := hlt (11 + l) (by omega); rwa [hsz] at this)]
  · rw [ePos, pa, hw0, hcapL, ht, q9, q10]
  · rw [ePos, pr, MidW.cap3, hcapL]; rfl
  · rw [eQ, qa, hlamv, show σ (.n osCoefs) = osPtrA c b osIxCoefsA from hptr 3 (by norm_num),
      show σ (.n osHs) = osPtrA c b osIxHsA from hptr 6 (by norm_num), q9, q10, ← hc]
    simp only [hfin, ↓reduceIte, OsHD.li, OsHD.lamAt, osHsPtrA, hlv]
  · rw [eQ, qr, hlamv, hr0, hr1, ← hc]
    simp only [hfin, ↓reduceIte, OsHD.lamAt, hlv]

/-! ## The final level -/

/-- **The final level's step.** -/
theorem lvFin_step {h : OsHD} {b : ℕ} {tabs cur : E} {xs : List E} (hS : BodyStatic h.c)
    {st : OsSt} {σ : Val} (hq : QAt h b tabs cur xs h.c.yrLevel st σ) (W : FinWD)
    (hpH : W.pH = osPtrA h.c b (11 + h.c.yrLevel))
    (hr3 : 2 * ((h.c.levels.getD h.c.yrLevel default).foldsOff +
      (h.c.levels.getD h.c.yrLevel default).folds) < u128Bound)
    (hpo : (h.c.levels.getD h.c.yrLevel default).posOff < u128Bound)
    (h3 : 2 * (h.c.levels.getD h.c.yrLevel default).foldsOff < u128Bound)
    (hh8 : h.c.yrLevel * hsStride < u128Bound)
    (hC : ∀ C rd, H C rd → FinC C rd σ h.c h.c.yrLevel (h.c.levels.getD h.c.yrLevel default)
      (h.capAt h.c.yrLevel) (h.claimAt h.c.yrLevel) (cur * gen ^ (xs.length - (h.xsAt h.c.yrLevel).length)) W)
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
    BlkA H σ st.k (osLevel h.c h.c.yrLevel (h.c.levels.getD h.c.yrLevel default) st).2.k
      (osLevel h.c h.c.yrLevel (h.c.levels.getD h.c.yrLevel default) st).1 (fun σ' ↦
      st.k ≤ (osLevel h.c h.c.yrLevel (h.c.levels.getD h.c.yrLevel default) st).2.k ∧
      QAt h b tabs cur xs (h.c.yrLevel + 1)
        (osLevel h.c h.c.yrLevel (h.c.levels.getD h.c.yrLevel default) st).2 σ' ∧
      RAt h b tabs h.c.yrLevel W.batched σ') := by
  set c := h.c with hc
  set l := c.yrLevel with hl
  set lv := c.levels.getD l default with hlv
  obtain ⟨-, hLv, -, hlen0, hyr0, -, -, hlane0, -, -, -, -, -, -, -, hlt0⟩ := hS
  have hyr : c.yrLevel + 1 = c.levels.length := hyr0
  have hlen : (osSizesL c).length = 19 + c.yrLevel := hlen0
  have hlane : (osSizesL c).getD (11 + c.yrLevel) 0 = c.yrLen + (c.levels.getD c.yrLevel default).folds := hlane0
  have hlt : ∀ j < (osSizesL c).length, (osSizesL c).getD j 0 < 2 ^ 64 - 1 := hlt0
  have hst : st = osStAt c l := hq.eq
  have hfs := hq.fs
  have hcl := hq.claim
  have hcu := hq.cur
  have hblk := osLevelFin_complete (H := H) (c := c) (lvl := l) (lv := lv) (st := st) σ hq.ok.sf
    (fun _ _ _ ↦ hq.ok) rfl W hr3 hpo h3 hh8 (fun _ _ _ ↦ hq.rate l (by show l < c.levels.length; omega))
    (fun C rd hH ↦ by rw [hfs, hcl, hcu]; exact hC C rd hH)
  refine hblk.mono fun σ' ⟨hstep, eF, ecur, ecl, e3, e4, pa, pr, qa, qr⟩ ↦ ?_
  have k33 := hq.ok.sf.k
  have hp : ∀ i < 11, σ' (.n (12 + 2 * i)) = osPtrA c b i := fun i hi ↦ by
    rw [hstep.agree _ (by omega)]; exact hq.ptr i hi
  have ht : σ (.n osTabs) = tabs := hq.tabs
  have hptr : ∀ i < 11, σ (.n (12 + 2 * i)) = osPtrA c b i := hq.ptr
  rw [hfs, hcl, hcu] at *
  have ePos : osLpCallOf c l = osPosCall c lv (osFinalMsg c lv (osRounds c.plan lv.foldsOff lv.folds st).2).2 := by
    rw [hst]; simp only [osLpCallOf, osPosSt, osPosCall, hl, ↓reduceIte]; rfl
  have eQ : osLqCallOf c l = osQCallOf c l lv (osPreQ c l lv st) := by rw [hst]; rfl
  have eH : (osPreQ c l lv st).hs =
      (osPositions c l lv (osFinalMsg c lv (osRounds c.plan lv.foldsOff lv.folds st).2).2).2.k + 1 := by
    simp only [osPreQ, osHsFinal, hl, ↓reduceIte]
  have q9 : σ (.n osQpos) = osPtrA c b osIxQposA := hptr 9 (by norm_num)
  have q10 : σ (.n osQbp) = osPtrA c b osIxQbpA := hptr 10 (by norm_num)
  refine ⟨hstep.le, ⟨?_, hstep.ok, hp, ?_, fun l' hl' ↦ ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hq.eq, osStAt, osStAt, osStFrom_get c 0 c.levels _ l (by omega), Nat.zero_add]
  · rw [hstep.agree _ (by show 10 < st.k; omega)]; exact ht
  · obtain ⟨ri, hri, hx, hlen, hlv'⟩ := hq.rate l' hl'
    exact ⟨ri, hri, by rw [hstep.agree _ (show 0 < st.k by omega)]; exact hx, hlen, hlv'⟩
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
    rw [show osStAt c l = st from hst.symm, allocsAt_one hf, e3, ← eH, e4, hpH, bufsAt_one, hlane,
      logG_gw (by have := hlt (11 + l) (by omega); rwa [hlane] at this)]
  · rw [ePos, pa, hw0, hcapL, ht, q9, q10]
  · rw [ePos, pr, FinWD.cap3, hcapL]; rfl
  · rw [eQ, qa, show σ (.n osCoefs) = osPtrA c b osIxCoefsA from hptr 3 (by norm_num), q9, q10, hpH,
      ← hc]
    simp only [hl, ↓reduceIte, osHsPtrA, osIxLaneA, hlv]
  · rw [eQ, qr, hr0, hr1, ← hc]
    simp only [hl, ↓reduceIte, hlv]

end
end LeanVM.Guest.B1.Whir
