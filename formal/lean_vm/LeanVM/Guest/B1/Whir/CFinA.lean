/-
  LeanVM.Guest.B1.Whir.CFinA

  The body after the closing rounds, honestly: the finish's own buffers and the statements before
  its return at honest values.
-/

module

public import LeanVM.Guest.B1.Whir.CFinPt
public import LeanVM.Guest.B1.Whir.CFinB
public import LeanVM.Guest.B1.Whir.CFinRs
public import LeanVM.Guest.B1.Whir.CFinO
public import LeanVM.Guest.B1.Whir.FinishSound
public import LeanVM.Guest.B1.Whir.RateCfg

/-!
# The finish, honestly

The finish's own buffers' honest words, from all `α`s `G`, the tail challenges `T` and the
non-final levels' records (S1a-3's `OsRec`): the point zero-padded and one plus it one-padded
(`finPtC`, `finPt1C`), each level's basis row (`finBdC`), scale (`finLsC`), product of
coordinates (`finLaC`) and the inner chain (`finIchC`).

`osFinishA_complete`: on memory holding the levels' records (`RecStored`), `λ⁻¹` in `level_lam_invs`,
`G` and `T`, and those buffers at the pointers `PT`, `PT1`, `BD`, `LS`, `LA`, `ICH`, with
`fold_final_msg` returning `Y` and each `level_residual` returning its level's chains, the
statements of `osFinishA` hold at values fixed before the memory and the callees, allocating
exactly those buffers in order (`AllocsAt`). What they return is `osFinish_sound`'s.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

variable {H : CallRel → Reader → Prop}

/-! ## The honest words -/

/-- Level `i` of the configuration. -/
abbrev finLv (c : OsCfg) (i : ℕ) : OsLv := c.levels.getD i default

/-- Non-final level `i`'s coordinates: the terminal point from its folds on. -/
def finX (G T : List E) (recs : List OsRec) (i t : ℕ) : E := (ptFrom G T (recs.getD i default).F).getD t 0

/-- Non-final level `i`'s batching scalar `λ²·λ^Q`. -/
def finBeta (c : OsCfg) (recs : List OsRec) (i : ℕ) : E :=
  (recs.getD i default).lam ^ 2 * (recs.getD i default).lam ^ (finLv c i).queries

/-- Non-final level `i`'s basis row. -/
def finD (c : OsCfg) (G T : List E) (recs : List OsRec) (i : ℕ) : ℕ → E :=
  dOf (finLv c i) (finX G T recs i)

/-- Non-final level `i`'s chains. -/
def finRes (c : OsCfg) (G T : List E) (recs : List OsRec) (li : ℕ → E) (i : ℕ) : E × E :=
  resAll (finLv c i) (finD c G T recs i) (hsvOf (finLv c i) (recs.getD i default))
    (fun k ↦ eOfNat ((recs.getD i default).qs.getD k 0)) (li i)

/-- `point`: the rotated point, zero-padded. -/
def finPtC (c : OsCfg) (G T : List E) : List E :=
  rotPt G T (c.levels.headD default).folds ++ List.replicate (pointCap - (c.nFolds + c.yrLog)) 0

/-- `point1`: one plus each coordinate, one-padded. -/
def finPt1C (c : OsCfg) (G T : List E) : List E :=
  (rotPt G T (c.levels.headD default).folds).map (1 + ·) ++
    List.replicate (pointCap - (c.nFolds + c.yrLog)) 1

/-- `basis_d`: each non-final level's row of `d`s. -/
def finBdC (c : OsCfg) (G T : List E) (recs : List OsRec) : List E :=
  (List.range (c.levels.length * ligColsCap)).map fun e ↦
    if e / ligColsCap < c.yrLevel ∧ e % ligColsCap < (finLv c (e / ligColsCap)).prefixLen + c.yrLog
    then finD c G T recs (e / ligColsCap) (e % ligColsCap) else 0

/-- `level_scale`: `β` times the coefficients. -/
def finLsC (c : OsCfg) (G T : List E) (recs : List OsRec) : List E :=
  (List.range c.levels.length).map fun i ↦
    if i < c.yrLevel then finBeta c recs i *
      ∏ t ∈ Finset.range ((finLv c i).prefixLen + c.yrLog), (finX G T recs i t * invW (finLv c i) t)
    else 0

/-- `level_after`: the product of the coordinates. -/
def finLaC (c : OsCfg) (G T : List E) (recs : List OsRec) : List E :=
  (List.range c.levels.length).map fun i ↦
    if i < c.yrLevel then ∏ t ∈ Finset.range ((finLv c i).prefixLen + c.yrLog), finX G T recs i t
    else 0

/-- The inner chain's sums after `j` levels, from the claim `cl`. -/
def finIch (c : OsCfg) (G T : List E) (recs : List OsRec) (li : ℕ → E) (cl : E) (j : ℕ) : E × E :=
  (∑ i ∈ Finset.range j, (finLsC c G T recs).getD i 0 * (finRes c G T recs li i).1,
    cl + ∑ i ∈ Finset.range j,
      finBeta c recs i * (finLaC c G T recs).getD i 0 * (finRes c G T recs li i).2)

/-- `inner_chain`: entries `2j`, `2j + 1` the sums after `j` levels. -/
def finIchC (c : OsCfg) (G T : List E) (recs : List OsRec) (li : ℕ → E) (cl : E) : List E :=
  (List.range (2 * c.levels.length)).map fun e ↦
    if e % 2 = 0 then (finIch c G T recs li cl (e / 2)).1 else (finIch c G T recs li cl (e / 2)).2

/-! ## What the finish reads and calls -/

/-- **The finish's static facts.** -/
structure FinStatic (c : OsCfg) (G T : List E) (recs : List OsRec) : Prop where
  n2 : 2 ≤ c.levels.length
  n6 : c.levels.length ≤ 6
  yr : c.yrLevel = c.levels.length - 1
  ylog : 1 ≤ c.yrLog
  recl : recs.length = c.yrLevel
  lv : ∀ i < c.yrLevel, LvFin c (finLv c i) (finLv c (i + 1))
  Gl : G.length = c.nFolds
  Tl : T.length = c.yrLog
  lane : (c.levels.headD default).folds ≤ c.nFolds
  mu40 : c.nFolds + c.yrLog ≤ pointCap
  Gnz : ∀ x ∈ G, x ≠ 0
  Tnz : ∀ x ∈ T, x ≠ 0
  recF : ∀ i < c.yrLevel, (recs.getD i default).F = (finLv c i).foldsOff + (finLv c i).folds
  cols : ∀ i < c.yrLevel, (finLv c i).logCols ≤ ligColsCap

/-- **What memory holds and the callees do for the finish**, at the valuation `σ` it starts
from. -/
structure FinMem (C : CallRel) (rd : Reader) (σ : Val) (c : OsCfg) (tch : ℕ) (G T : List E)
    (recs : List OsRec) (li : ℕ → E) (cl Y PT PT1 BD LS LA ICH : E) : Prop where
  stored : ∀ i < c.yrLevel, RecStored rd σ i (finLv c i) (recs.getD i default)
  mus : ∀ i < c.yrLevel, LoadHolds rd (σ (.n osMus)) i (li i)
  fch : ∀ j (h : j < G.length), LoadHolds rd (σ (.n osFch)) j G[j]
  tchs : ReadsAt rd (σ (.n tch)) T
  pt : ReadsAt rd PT (finPtC c G T)
  pt1 : ReadsAt rd PT1 (finPt1C c G T)
  bd : ReadsAt rd BD (finBdC c G T recs)
  ls : ReadsAt rd LS (finLsC c G T recs)
  la : ReadsAt rd LA (finLaC c G T recs)
  ich : ReadsAt rd ICH (finIchC c G T recs li cl)
  ffm : C ("fold_final_msg__L" ++ natStr c.yrLog) [σ (.n osFmsg), σ (.n tch)] [Y]
  rate : ∀ i < c.yrLevel, LvRate σ c i (finLv c i)
  res : ∀ i < c.yrLevel, C (osResidualName (finLv c i))
    [σ (.n osQpos) * gen ^ (finLv c i).posOff, BD * gen ^ (i * ligColsCap),
      σ (.n osHs) * gen ^ (i * hsStride), li i] [(finRes c G T recs li i).1, (finRes c G T recs li i).2]

/-- The finish's buffers and their sizes, in allocation order. -/
def finAllocs (c : OsCfg) (PT PT1 BD LS LA ICH : E) : List (E × ℕ) :=
  [(PT, pointCap), (PT1, pointCap), (BD, c.levels.length * ligColsCap), (LS, c.levels.length),
    (LA, c.levels.length), (ICH, 2 * c.levels.length)]

/-- The finish's last value plus one. -/
def finEnd (c : OsCfg) (st : OsSt) (tch : ℕ) : ℕ :=
  let pts := osPtBlks c (st.k + 1) (st.k + 1 + 1) tch 0 pointCap (st.k + 1 + 2)
  let bs := osBases c tch (pts.2 + 1) (pts.2 + 3) (pts.2 + 5) 0 (c.levels.take c.yrLevel) (pts.2 + 6)
  let rs := osResiduals c (bs.2 + 1) (pts.2 + 1) (pts.2 + 3) (pts.2 + 5) 0 (c.levels.take c.yrLevel)
    st.mats (bs.2 + 3)
  (osOodWeights c tch (c.levels.headD default).logCols 1 c.levels.tail none rs.2).2.2 + 6


/-! ## The honest words, read back -/

theorem readsAt_getD' {rd : Reader} {p : E} {xs : List E} (h : ReadsAt rd p xs) {j : ℕ}
    (hj : j < xs.length) : LoadHolds rd p j (xs.getD j 0) := by
  rw [List.getD_eq_getElem _ _ hj]; exact h j hj

theorem rotPt_length {c : OsCfg} {G T : List E} {recs : List OsRec} (hS : FinStatic c G T recs) :
    (rotPt G T (c.levels.headD default).folds).length = c.nFolds + c.yrLog := by
  simp [rotPt, hS.Gl, hS.Tl]; have := hS.lane; omega

theorem finPtC_getD {c : OsCfg} {G T : List E} {recs : List OsRec} (hS : FinStatic c G T recs) (i : ℕ) :
    (finPtC c G T).getD i 0 = (rotPt G T (c.levels.headD default).folds).getD i 0 := by
  have hl := rotPt_length hS
  have hG := hS.Gl
  have hT := hS.Tl
  have hln := hS.lane
  unfold finPtC
  by_cases h : i < c.nFolds + c.yrLog
  · rw [List.getD_append _ _ _ _ (by omega)]
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_eq_getElem?_getD,
      List.getD_eq_getElem?_getD (l := rotPt _ _ _), List.getElem?_eq_none (l := rotPt _ _ _) (by omega)]
    simp [List.getElem?_replicate]
    split_ifs <;> rfl

theorem finPt1C_getD {c : OsCfg} {G T : List E} {recs : List OsRec} (hS : FinStatic c G T recs) {i : ℕ} (hi : i < pointCap) :
    (finPt1C c G T).getD i 0 = 1 + (rotPt G T (c.levels.headD default).folds).getD i 0 := by
  have hl := rotPt_length hS
  have h40 := hS.mu40
  have hG := hS.Gl
  have hT := hS.Tl
  have hln := hS.lane
  unfold finPt1C
  by_cases h : i < c.nFolds + c.yrLog
  · rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega),
      List.getElem_map, List.getD_eq_getElem _ _ (by omega)]
  · rw [List.getD_append_right _ _ _ _ (by simp; omega), List.getD_eq_getElem?_getD,
      List.getD_eq_getElem?_getD (l := rotPt _ _ _), List.getElem?_eq_none (l := rotPt _ _ _) (by omega)]
    simp only [List.length_map, hl, List.getElem?_replicate, Option.getD_none, add_zero,
      show i - (c.nFolds + c.yrLog) < pointCap - (c.nFolds + c.yrLog) by omega, ↓reduceIte]
    rfl

theorem finPtC_length (c : OsCfg) {G T : List E} {recs : List OsRec} (hS : FinStatic c G T recs) :
    (finPtC c G T).length = pointCap := by
  have := rotPt_length hS; have := hS.mu40; have := hS.Gl; have := hS.Tl; have := hS.lane
  simp [finPtC]; omega

theorem finPt1C_length (c : OsCfg) {G T : List E} {recs : List OsRec} (hS : FinStatic c G T recs) :
    (finPt1C c G T).length = pointCap := by
  have := rotPt_length hS; have := hS.mu40; have := hS.Gl; have := hS.Tl; have := hS.lane
  simp [finPt1C]; omega

/-- Non-final level `i`'s coordinate `t` is the word at its source. -/
theorem finX_src {c : OsCfg} {tch : ℕ} {σ : Val} {rd : Reader} {G T : List E} {recs : List OsRec}
    (hS : FinStatic c G T recs) (hfch : ∀ j (h : j < G.length), LoadHolds rd (σ (.n osFch)) j G[j])
    (htch : ReadsAt rd (σ (.n tch)) T) {i : ℕ} (hi : i < c.yrLevel)
    (hrF : (recs.getD i default).F = (finLv c i).foldsOff + (finLv c i).folds) :
    ∀ t < (finLv c i).prefixLen + c.yrLog,
      LoadHolds rd (σ (.n (coordSrc tch (finLv c i) t).1)) (coordSrc tch (finLv c i) t).2
        (finX G T recs i t) := by
  intro t ht
  have hL := hS.lv i hi
  have hp1 := hL.pre
  have hp2 := hL.cols
  have hp3 := hL.le
  have hG := hS.Gl
  have hT := hS.Tl
  simp only [finX, ptFrom, coordSrc]
  rw [hrF]
  by_cases h1 : t < (finLv c i).prefixLen
  · simp only [h1, ↓reduceIte, hL.rfo]
    rw [List.getD_eq_getElem?_getD, List.getElem?_drop, List.getElem?_append_left (by omega),
      List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact hfch _ (by omega)
  · simp only [h1, ↓reduceIte]
    rw [List.getD_eq_getElem?_getD, List.getElem?_drop, List.getElem?_append_right (by omega),
      List.getElem?_eq_getElem (by omega), Option.getD_some]
    have := htch (t - (finLv c i).prefixLen) (by omega)
    convert this using 2
    omega

/-- Non-final level `i`'s coordinates are not zero, nor their coefficients. -/
theorem finX_ne {c : OsCfg} {G T : List E} {recs : List OsRec} (hS : FinStatic c G T recs) {i : ℕ}
    (hi : i < c.yrLevel) (hrF : (recs.getD i default).F = (finLv c i).foldsOff + (finLv c i).folds) :
    ∀ t < (finLv c i).prefixLen + c.yrLog, finX G T recs i t * invW (finLv c i) t ≠ 0 := by
  intro t ht
  have hL := hS.lv i hi
  have hp1 := hL.pre
  have hp2 := hL.cols
  have hp3 := hL.le
  have hG := hS.Gl
  have hT := hS.Tl
  refine mul_ne_zero ?_ (invW_ne hL.mu64 hL.inv t (by omega))
  simp only [finX, ptFrom]
  rw [hrF, List.getD_eq_getElem _ _ (by simp only [List.length_drop, List.length_append]; omega),
    List.getElem_drop]
  by_cases h : (finLv c i).foldsOff + (finLv c i).folds + t < G.length
  · rw [List.getElem_append_left h]; exact hS.Gnz _ (List.getElem_mem _)
  · rw [List.getElem_append_right (by omega)]; exact hS.Tnz _ (List.getElem_mem _)

theorem finBdC_get {c : OsCfg} {G T : List E} {recs : List OsRec} {i t : ℕ} (hi : i < c.yrLevel)
    (hy : c.yrLevel < c.levels.length) (ht : t < (finLv c i).prefixLen + c.yrLog)
    (h22 : (finLv c i).prefixLen + c.yrLog ≤ ligColsCap) :
    (finBdC c G T recs).length = c.levels.length * ligColsCap ∧
      (finBdC c G T recs).getD (i * ligColsCap + t) 0 = finD c G T recs i t := by
  have hlt : i * ligColsCap + t < c.levels.length * ligColsCap := by
    have : (i + 1) * ligColsCap ≤ c.levels.length * ligColsCap := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, Nat.one_mul] at this; omega
  have hd : (i * ligColsCap + t) / ligColsCap = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by decide), Nat.div_eq_of_lt (by omega), Nat.zero_add]
  have hm : (i * ligColsCap + t) % ligColsCap = t := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  refine ⟨by simp [finBdC], ?_⟩
  rw [List.getD_eq_getElem _ _ (by simp [finBdC]; exact hlt)]
  simp only [finBdC, List.getElem_map, List.getElem_range, hd, hm]
  simp only [show i < c.yrLevel ∧ t < (finLv c i).prefixLen + c.yrLog from ⟨hi, ht⟩, and_self, ↓reduceIte]

theorem finLsC_get {c : OsCfg} {G T : List E} {recs : List OsRec} {i : ℕ} (hi : i < c.yrLevel)
    (hy : c.yrLevel < c.levels.length) :
    (finLsC c G T recs).length = c.levels.length ∧ (finLsC c G T recs).getD i 0 = finBeta c recs i *
      ∏ t ∈ Finset.range ((finLv c i).prefixLen + c.yrLog), (finX G T recs i t * invW (finLv c i) t) := by
  refine ⟨by simp [finLsC], ?_⟩
  rw [List.getD_eq_getElem _ _ (by simp [finLsC]; omega)]
  simp [finLsC, hi]

theorem finLaC_get {c : OsCfg} {G T : List E} {recs : List OsRec} {i : ℕ} (hi : i < c.yrLevel)
    (hy : c.yrLevel < c.levels.length) :
    (finLaC c G T recs).length = c.levels.length ∧ (finLaC c G T recs).getD i 0 =
      ∏ t ∈ Finset.range ((finLv c i).prefixLen + c.yrLog), finX G T recs i t := by
  refine ⟨by simp [finLaC], ?_⟩
  rw [List.getD_eq_getElem _ _ (by simp [finLaC]; omega)]
  simp [finLaC, hi]

theorem finIchC_get {c : OsCfg} {G T : List E} {recs : List OsRec} {li : ℕ → E} {cl : E} {j : ℕ}
    (hj : j < c.levels.length) :
    (finIchC c G T recs li cl).length = 2 * c.levels.length ∧
    (finIchC c G T recs li cl).getD (2 * j) 0 = (finIch c G T recs li cl j).1 ∧
      (finIchC c G T recs li cl).getD (2 * j + 1) 0 = (finIch c G T recs li cl j).2 := by
  refine ⟨by simp [finIchC], ?_, ?_⟩
  · rw [List.getD_eq_getElem _ _ (by simp [finIchC]; omega)]
    simp [finIchC, show 2 * j / 2 = j by omega]
  · rw [List.getD_eq_getElem _ _ (by simp [finIchC]; omega)]
    simp [finIchC, show (2 * j + 1) / 2 = j by omega, show (2 * j + 1) % 2 = 1 by omega]

end
end LeanVM.Guest.B1.Whir
