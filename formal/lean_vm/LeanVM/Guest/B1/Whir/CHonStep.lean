/-
  LeanVM.Guest.B1.Whir.CHonStep

  A level of open_stacked's body at the honest data's values: from the start the levels keep
  (`QAt`) to the next, its allocations and special calls (`RAt`).
-/

module

public import LeanVM.Guest.B1.Whir.CHonAlloc
public import LeanVM.Guest.B1.Whir.CHonBuf
public import LeanVM.Guest.B1.Whir.CLevel

/-!
# A level's step

`QAt h b tabs cur xs l st σ`: the state `st` before level `l` (`osStAt`), its invariants, the
fixed buffers' pointers at `b`, the window table, the carried capacity, the claim and the cursor
at the honest data's (`OsHD.capAt`, `claimAt`, `curOff`). `RAt h b tabs l σ'`: level `l`'s
allocations (`bufsAt`) and its special calls' values, as `OsSpecVals` states them.

`lvMid_step`, `lvFin_step`: a level's block from `QAt l` to `QAt (l + 1)` and `RAt l`, from its
calls and memory (`MidC`, `FinC`) at the honest values and the honest data's equalities.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Guest.Memory LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

namespace OsHD

variable (h : OsHD)

/-- Sample `j` of level `l`. -/
def word (l j : ℕ) : E := (h.L l).word h.logN j

/-- `λ⁻¹` the queries of level `l` take, `0` at the final level. -/
def lamInv (l : ℕ) : E := if l = h.c.yrLevel then 0 else h.li l

/-- The carried capacity before level `l`, the closing rounds' after the levels. -/
def capAt (l : ℕ) : List E := if l ≤ h.c.yrLevel then (h.L l).cap else (h.Lf.F3 h.logN).cap

/-- The guest's claim before level `l`, after the final level's folds after the levels. -/
def claimAt (l : ℕ) : E := if l ≤ h.c.yrLevel then h.gclAt l else h.cl1F

/-- The words from level `l` on, the closing rounds' after the levels. -/
def xsAt (l : ℕ) : List E := if l ≤ h.c.yrLevel then (h.L l).xs else tailWords h.Lf.fw.pairs

end OsHD

/-- **The start of level `l`.** -/
structure QAt (h : OsHD) (b : ℕ) (tabs cur : E) (xs : List E) (l : ℕ) (st : OsSt) (σ : Val) :
    Prop where
  eq : st = osStFrom h.c 0 h.c.levels (osHead h.c).2 l
  ok : st.Ok σ
  ptr : ∀ i < 13, σ (.n (11 + 2 * i)) = osPtrF h.c b i
  tabs : σ (.n osTabs) = tabs
  fs : st.fsv σ = h.capAt l
  claim : σ (.n st.claim) = h.claimAt l
  cur : st.cur σ = cur * gen ^ (xs.length - (h.xsAt l).length)

theorem QAt.agree {h : OsHD} {b : ℕ} {tabs cur : E} {xs : List E} {l : ℕ} {st : OsSt} {σ σ' : Val}
    (hq : QAt h b tabs cur xs l st σ) (ha : AgreeBelow st.k σ σ') : QAt h b tabs cur xs l st σ' := by
  have k36 := hq.ok.sf.k
  obtain ⟨e1, -, e3, e4⟩ := OsSt.agree hq.ok.sf.below ha
  exact ⟨hq.eq, hq.ok.agree ha, fun i hi ↦ by rw [ha _ (by omega)]; exact hq.ptr i hi,
    by rw [ha _ (by show 9 < st.k; omega)]; exact hq.tabs, by rw [e1]; exact hq.fs,
    by rw [e3]; exact hq.claim, by rw [e4]; exact hq.cur⟩

/-- **Level `l`'s allocations and special calls' values.** -/
def RAt (h : OsHD) (b : ℕ) (tabs : E) (l : ℕ) (σ' : Val) : Prop :=
  let c := h.c
  AllocsAt σ' (osLevel c l (osLvAt c l) (osStAt c l)).1 = bufsAt c b (13 + 2 * l) 2 ∧
  (osDecCall c l).2.2.1.map σ' = [h.word l 0, osPtrF c b 11 * gen ^ (osLvAt c l).posOff,
    osPtrF c b osIxQbp * gen ^ (osLvAt c l).posOff, tabs] ∧
  (osSqCall c l).1.map σ' = some (gen + gen ^ (osLvAt c l).squeezes) ∧
  (osSqCall c l).2.2.1.map σ' = [gen, gen ^ (osLvAt c l).squeezes, osPtrF c b (osIxSqz c l),
    osPtrF c b 11, osPtrF c b osIxQbp, tabs]

/-- **Level `l`'s queries' call values.** -/
def RQ (h : OsHD) (b : ℕ) (l : ℕ) (batched : E) (σ' : Val) : Prop :=
  let c := h.c
  (osQCall c l).2.2.1.map σ' = [osPtrF c b 0 * gen ^ (4 * (osLvAt c l).capOff),
    osPtrF c b 1 * gen ^ (osLvAt c l).capOff, h.lamInv l,
    osPtrF c b 5 * gen ^ (3 * (osLvAt c l).foldsOff), osHsPtr c b l,
    osPtrF c b 11 * gen ^ (osLvAt c l).posOff, osPtrF c b osIxQbp * gen ^ (osLvAt c l).posOff,
    gen ^ oqN c l] ∧
  (osQCall c l).2.2.2.map σ' = [batched]

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

theorem allocsAt_two {σ : Val} {ss : List Stmt} {a1 s1 a2 s2 : ℕ}
    (hf : ss.filterMap Stmt.allocSz = [(.n a1, .inr (.n s1)), (.n a2, .inr (.n s2))]) :
    AllocsAt σ ss = [(σ (.n a1), logG (σ (.n s1))), (σ (.n a2), logG (σ (.n s2)))] := by
  simp [AllocsAt, hf]

/-! ## A non-final level -/

variable {H : CallRel → Reader → Prop}

/-- **A non-final level's step.** -/
theorem lvMid_step {h : OsHD} {b : ℕ} {tabs cur : E} {xs : List E} {l : ℕ} (hS : BodyStatic h.c)
    (hl : l < h.c.yrLevel) {st : OsSt} {σ : Val} (hq : QAt h b tabs cur xs l st σ) (W : MidW)
    (hpS : W.pS = osPtrF h.c b (13 + 2 * l)) (hpZ : W.pZ = osPtrF h.c b (14 + 2 * l))
    (hr3 : 3 * ((osLvAt h.c l).foldsOff + (osLvAt h.c l).folds) < u128Bound)
    (hoff : (oodSamples * (l + 1) + 1) * ligColsCap < u128Bound)
    (hpo : (osLvAt h.c l).posOff < u128Bound) (hS5 : (osLvAt h.c l).squeezes * 5 < u128Bound)
    (hc4 : 4 * (osLvAt h.c l).capOff < u128Bound) (hh8 : l * hsStride < u128Bound)
    (hqu : (osLvAt h.c l).queries < u128Bound)
    (hpw : digitsVal (osPowDigits (osLvAt h.c l).queries) 1 = (osLvAt h.c l).queries)
    (hlam : W.lam (osLvAt h.c l) (h.capAt l) (h.claimAt l) ≠ 0)
    (hC : ∀ C rd, H C rd → MidC C rd σ h.c l (osLvAt h.c l) (h.capAt l) (h.claimAt l)
      (cur * gen ^ (xs.length - (h.xsAt l).length)) W)
    (hcap' : capOf (W.SL (osLvAt h.c l) (h.capAt l) (h.claimAt l)) = h.capAt (l + 1))
    (hcl' : W.claimOut (osLvAt h.c l) (h.capAt l) (h.claimAt l) = h.claimAt (l + 1))
    (hcur' : xs.length - (h.xsAt l).length + (7 * (osLvAt h.c l).folds + (2 + (osLvAt h.c l).folds) + 3 + 1) =
      xs.length - (h.xsAt (l + 1)).length)
    (hw0 : rdCell (W.S2 (osLvAt h.c l) (h.capAt l) (h.claimAt l)) 0 = h.word l 0)
    (hli : (W.lam (osLvAt h.c l) (h.capAt l) (h.claimAt l))⁻¹ = h.lamInv l) :
    BlkA H σ st.k (osLevel h.c l (osLvAt h.c l) st).2.k (osLevel h.c l (osLvAt h.c l) st).1 (fun σ' ↦
      st.k ≤ (osLevel h.c l (osLvAt h.c l) st).2.k ∧
      QAt h b tabs cur xs (l + 1) (osLevel h.c l (osLvAt h.c l) st).2 σ' ∧ RAt h b tabs l σ' ∧
      RQ h b l W.batched σ') := by
  set c := h.c with hc
  set lv := osLvAt c l with hlv
  obtain ⟨-, hLv, -, hlen, hyr, -, hLs, -, -, -, -, -, -, -, -, hlt⟩ := hS
  have hst : st = osStAt c l := hq.eq
  have hfs := hq.fs
  have hcl := hq.claim
  have hcu := hq.cur
  have hblk := osLevelMid_complete (H := H) (c := c) (lvl := l) (lv := lv) (st := st) σ hq.ok.sf
    (fun _ _ _ ↦ hq.ok) (by omega) W hr3 hoff hpo hS5 (by omega) hc4 (by omega) hh8
    (by split_ifs <;> omega) hpw (by rw [hfs, hcl]; exact hlam)
    (fun C rd hH ↦ by rw [hfs, hcl, hcu]; exact hC C rd hH)
  refine hblk.mono fun σ' ⟨hstep, eF, ecur, ecl, e1, e2, e3, e4, d1, s1, s2, q1, q2⟩ ↦ ?_
  have hp : ∀ i < 13, σ' (.n (11 + 2 * i)) = osPtrF c b i := fun i hi ↦ by
    rw [hstep.agree _ (by have := hq.ok.sf.k; omega)]; exact hq.ptr i hi
  have ht : σ (.n osTabs) = tabs := hq.tabs
  have hptr : ∀ i < 13, σ (.n (11 + 2 * i)) = osPtrF c b i := hq.ptr
  rw [hfs, hcl, hcu] at *
  have hsz := hLs l (by omega)
  simp only [show l ≠ c.yrLevel by omega, ↓reduceIte] at hsz
  have hix : osIxSqz c l = 14 + 2 * l := by
    simp only [osIxSqz, show l ≠ c.yrLevel by omega, ↓reduceIte]; ring
  have hhs : osHsPtr c b l = osPtrF c b 8 * gen ^ (l * hsStride) := by
    simp only [osHsPtr, show l ≠ c.yrLevel by omega, ↓reduceIte]
  have hN : gen ^ (if l = 0 then lv.queries / 2 else lv.queries) = gen ^ oqN c l := by
    unfold oqN; split_ifs <;> simp <;> rfl
  refine ⟨hstep.le, ⟨?_, hstep.ok, hp, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [hq.eq, osStFrom_get c 0 c.levels _ l (by omega), Nat.zero_add]
  · rw [hstep.agree _ (by have := hq.ok.sf.k; show 9 < st.k; omega)]; exact ht
  · have := congrArg Fs.cap eF
    simp only [OsSt.F] at this
    rw [← hcap']; exact this
  · rw [ecl, hcl']
  · rw [ecur, ← hcur', MidW.cur1]
    simp only [mul_assoc, ← pow_add]
    ring_nf
  · have hf := hLv l (by omega)
    simp only [lvAllocsV, show l ≠ c.yrLevel by omega, ↓reduceIte] at hf
    rw [← hst] at hf
    rw [show osStAt c l = st from hst.symm, allocsAt_two hf, e1, e2, e3, e4, hpS, hpZ, bufsAt_two,
      show 13 + 2 * l + 1 = 14 + 2 * l by ring, hsz.1, hsz.2]
    rw [logG_gw (by have := hlt (13 + 2 * l) (by omega); rwa [hsz.1] at this),
      logG_gw (by have := hlt (14 + 2 * l) (by omega); rwa [hsz.2] at this)]
  · show (osDecCallAt c lv (lvM c l lv (osStAt c l)).2).2.2.1.map σ' = _
    rw [← hst, d1, hw0, ht, show σ (.n osQpos) = osPtrF c b 11 from hptr 11 (by norm_num),
      show σ (.n osQbp) = osPtrF c b osIxQbp from hptr 12 (by norm_num)]
  · show (osSqCallAt c l lv (lvM c l lv (osStAt c l)).2).1.map σ' = _
    rw [← hst, s1]
  · show (osSqCallAt c l lv (lvM c l lv (osStAt c l)).2).2.2.1.map σ' = _
    rw [← hst, s2, ht, hpZ, show σ (.n osQpos) = osPtrF c b 11 from hptr 11 (by norm_num),
      show σ (.n osQbp) = osPtrF c b osIxQbp from hptr 12 (by norm_num), hix]
  · show (osQCallAt c l lv (lvH c l lv (osStAt c l)).2).2.2.1.map σ' = _
    rw [← hst, q1, hli, show σ (.n osQpos) = osPtrF c b 11 from hptr 11 (by norm_num),
      show σ (.n osQbp) = osPtrF c b osIxQbp from hptr 12 (by norm_num),
      show σ (.n osCaps) = osPtrF c b 0 from hptr 0 (by norm_num),
      show σ (.n osFlags) = osPtrF c b 1 from hptr 1 (by norm_num),
      show σ (.n osCoefs) = osPtrF c b 5 from hptr 5 (by norm_num),
      show σ (.n osHs) = osPtrF c b 8 from hptr 8 (by norm_num), hhs, hN]
  · show (osQCallAt c l lv (lvH c l lv (osStAt c l)).2).2.2.2.map σ' = _
    rw [← hst, q2]

end
end LeanVM.Guest.B1.Whir
