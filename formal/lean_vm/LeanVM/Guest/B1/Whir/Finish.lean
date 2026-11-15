/-
  LeanVM.Guest.B1.Whir.Finish

  The body after the closing rounds: the final lane at the tail challenges, the point, the basis
  rows, the residual sums, the out-of-domain weights and the returns, against the Spec's
  terminal.
-/

module

public import LeanVM.Guest.B1.Whir.InnerAlg
public import LeanVM.Guest.B1.Whir.FinishSplit
public import LeanVM.Guest.B1.Whir.Point
public import LeanVM.Guest.B1.Eq.MeaningP
public import LeanVM.Guest.B1.Whir.HsScale

/-!
# The finish

`osFinish_sound`: from the levels' records in memory (`RecStored`), every `α` in
`fold_challenges`, the tail challenges at `tch`, the final lane at `final_msg` and the guest's
closing claim, the body after the closing rounds returns the Spec's terminal: the closing claim
plus the deficit times the closing challenges (the high chains, `level_high`), the rotated point
and one plus it, the glued weight (the product chains `level_inner` and the out-of-domain
weights `eqEval_prod`) and the lane's low part at the tail challenges (`fold_final_msg`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## Helpers -/

theorem readsAt_take {p : E} {xs ys : List E} (h1 : ReadsAt rd p xs) (h2 : ReadsAt rd p ys)
    (hl : xs.length ≤ ys.length) : xs = ys.take xs.length := by
  refine List.ext_getElem (by simp; omega) fun i hi _ ↦ ?_
  rw [List.getElem_take]
  exact loadHolds_unique (h1 i hi) (h2 i (by omega))

theorem prod_getD_range (l : List E) : ∏ t ∈ Finset.range l.length, l.getD t 0 = l.prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, Finset.prod_range_succ', List.prod_cons]
    simp only [List.getD_cons_succ, List.getD_cons_zero, ih]
    ring

theorem foldl_add_map {α : Type} (f : α → E) : ∀ (l : List α) (a : E),
    l.foldl (fun w g ↦ w + f g) a = a + (l.map f).sum
  | [], a => by simp
  | x :: l, a => by
    rw [List.foldl_cons, foldl_add_map f l, List.map_cons, List.sum_cons]; ring

theorem readsAt_padded {p : E} {P : List E} {n : ℕ} (f : E → E)
    (h : ∀ i < P.length + n, LoadHolds rd p i (f (P.getD i 0))) :
    ReadsAt rd p (P.map f ++ List.replicate n (f 0)) := by
  intro k hk
  simp only [List.length_append, List.length_map, List.length_replicate] at hk
  by_cases h1 : k < P.length
  · rw [List.getElem_append_left (by simpa using h1), List.getElem_map]
    have := h k hk
    rwa [List.getD_eq_getElem _ _ h1] at this
  · rw [List.getElem_append_right (by simpa using h1), List.getElem_replicate]
    have := h k hk
    rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none] at this

theorem ofK_ne_zero {a : K} (h : a ≠ 0) : ofK a ≠ 0 := by
  intro h0
  exact h ((algebraMap K E).injective (by rw [map_zero]; exact h0))

/-! ## A non-final level's terms -/

/-- A non-final level's static facts the finish reads. -/
structure LvFin (c : OsCfg) (lv lv' : OsLv) : Prop where
  pre : lv.prefixLen + c.yrLog = lv.logCols
  rfo : lv.resFoldOff = lv.foldsOff + lv.folds
  le : lv.foldsOff + lv.folds ≤ c.nFolds
  cols : c.nFolds - (lv.foldsOff + lv.folds) + c.yrLog = lv.logCols
  next : lv'.foldsOff = lv.foldsOff + lv.folds
  ml1 : 1 ≤ lv.logCols
  mu64 : lv.logCols < 64
  nhs : 1 ≤ lv.folds
  b3 : lv.highBits ≤ 3
  bn : lv.highBits ≤ lv.logCols + 1
  hn : lv.folds ≤ 2 ^ lv.highBits
  posOff : lv.posOff < u128Bound
  van : lv.vanish = lv.logCols * (lv.logCols + 1) / 2
  val : ∀ t ≤ lv.logCols, K.ofBits (vanishVal (lv.vanish + t)) = (subspaceRoots lv.logCols).getD t 0
  inv : ∀ t ≤ lv.logCols,
    K.ofBits (vanishInv (lv.vanish + t)) = ((subspaceRoots lv.logCols).getD t 0)⁻¹
  hsm : ∀ c' < lv.folds,
    K.ofBits (hsScale lv.vanish lv.highBits c' (vanishInv (lv.vanish + lv.logCols))) =
      ((subspaceRoots lv.logCols).getD lv.logCols 0)⁻¹ * hsNorm lv.logCols lv.highBits c'

/-- The terminal point from a level's folds on: `(G ++ T).drop F`. -/
abbrev ptFrom (G T : List E) (F : ℕ) : List E := (G ++ T).drop F

/-- A level's stored high part, normalized. -/
def hsvOf (lv : OsLv) (r : OsRec) : List E :=
  (List.range lv.folds).map fun c ↦
    r.high.getD c 0 * word (hsScale lv.vanish lv.highBits c (vanishInv (lv.vanish + lv.logCols))) 0

/-- A level's basis row. -/
def dOf (lv : OsLv) (X : ℕ → E) (t : ℕ) : E := (1 + X t) / (X t * invW lv t)

theorem osVals_ofK {lv : OsLv} (hF : ∀ t ≤ lv.logCols,
    K.ofBits (vanishVal (lv.vanish + t)) = (subspaceRoots lv.logCols).getD t 0) :
    ∀ i < lv.logCols, (osVals lv.vanish lv.logCols).getD i 0 =
      ofK ((subspaceRoots lv.logCols).getD i 0) := by
  intro i hi
  rw [osVals_getD hi, word_eOfNat, eOfNat, hF i (by omega)]

theorem invW_ofK {lv : OsLv} (hF : ∀ t ≤ lv.logCols,
    K.ofBits (vanishInv (lv.vanish + t)) = ((subspaceRoots lv.logCols).getD t 0)⁻¹) :
    ∀ t < lv.logCols, word (vanishInv (lv.vanish + t)) 0 =
      ofK ((subspaceRoots lv.logCols).getD t 0)⁻¹ := by
  intro t ht
  rw [word_eOfNat, eOfNat, hF t (by omega)]

theorem invW_ne {lv : OsLv} (hmu : lv.logCols < 64) (hF : ∀ t ≤ lv.logCols,
    K.ofBits (vanishInv (lv.vanish + t)) = ((subspaceRoots lv.logCols).getD t 0)⁻¹) :
    ∀ t < lv.logCols, invW lv t ≠ 0 := by
  intro t ht
  rw [invW, invW_ofK hF t ht]
  refine ofK_ne_zero (inv_ne_zero ?_)
  rw [subspaceRoots_getD (by omega)]
  exact LeanVM.Protocol.Whir.vanishingAt_basisVec_ne_zero (by omega)

theorem range_map_pos (qs : List ℕ) :
    (List.range qs.length).map (fun k ↦ eOfNat (qs.getD k 0)) = qs.map eOfNat := by
  refine List.ext_getElem (by simp) fun i h1 h2 ↦ ?_
  simp only [List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem _ _ (by simpa using h1)]

/-- **A level's three terms**: the scale times the product chain is `λ³` times its induced
weight, the batching scalar times the product after times the high chain is `λ³·recH` times the
challenges after the level, and the out-of-domain weights are `λ·eqEval`, `λ²·eqEval`. -/
theorem lvl_terms {c : OsCfg} {lv lv' : OsLv} (hF : LvFin c lv lv') {r : OsRec} {G T : List E}
    (hG : G.length = c.nFolds) (hT : T.length = c.yrLog) (hrF : r.F = lv.foldsOff + lv.folds)
    (hrmu : r.mu = lv.logCols) (hql : r.qs.length = lv.queries) (hhl : r.high.length = lv.folds)
    (hz0 : r.z0.length = lv.logCols)
    {li : E} (hli : r.lam * li = 1)
    (hne : ∀ t < lv.logCols, (ptFrom G T r.F).getD t 0 * invW lv t ≠ 0) :
    r.lam ^ 2 * r.lam ^ lv.queries *
        (∏ t ∈ Finset.range lv.logCols, ((ptFrom G T r.F).getD t 0 * invW lv t)) *
        (resAll lv (dOf lv fun t ↦ (ptFrom G T r.F).getD t 0) (hsvOf lv r)
          (fun k ↦ eOfNat (r.qs.getD k 0)) li).1 =
      r.lam * r.lam * inducedWeight r.mu r.qs (powers r.lam r.qs.length) (ptFrom G T r.F) ∧
    r.lam ^ 2 * r.lam ^ lv.queries * (∏ t ∈ Finset.range lv.logCols, (ptFrom G T r.F).getD t 0) *
        (resAll lv (dOf lv fun t ↦ (ptFrom G T r.F).getD t 0) (hsvOf lv r)
          (fun k ↦ eOfNat (r.qs.getD k 0)) li).2 =
      T.prod * (r.lam ^ 2 * recH r * (G.drop r.F).prod) ∧
    r.lam * ∏ t ∈ Finset.range lv.logCols, (1 + r.z0.getD t 0 + (ptFrom G T r.F).getD t 0) =
      r.lam * eqEval r.z0 (ptFrom G T r.F) := by
  have hPl : (ptFrom G T r.F).length = lv.logCols := by
    simp only [ptFrom, List.length_drop, List.length_append, hG, hT, hrF]
    have := hF.cols; have := hF.le; omega
  have hpos : (List.range lv.queries).map (fun k ↦ eOfNat (r.qs.getD k 0)) = r.qs.map eOfNat := by
    rw [← hql]; exact range_map_pos r.qs
  refine ⟨?_, ?_, ?_⟩
  · unfold resAll
    rw [resFold_fst, hpos]
    have h := level_inner hli r.qs (ptFrom G T r.F) hPl (osVals_ofK hF.val) (invW_ofK hF.inv) hne
    rw [hrmu, ← h, hql]
    unfold resP dOf invW
    ring
  · unfold resAll
    rw [resFold_snd, hpos]
    have hhs : ∀ c' < r.high.length, (hsvOf lv r).getD c' 0 =
        r.high.getD c' 0 * ofK ((subspaceRoots lv.logCols).getD lv.logCols 0)⁻¹ *
          ofK (hsNorm lv.logCols lv.highBits c') := by
      intro c' hc
      rw [hhl] at hc
      rw [hsvOf, List.getD_eq_getElem _ _ (by simpa using hc), List.getElem_map, List.getElem_range,
        word_eOfNat, eOfNat, hF.hsm c' hc, ofK_mul', mul_assoc]
    have h := level_high hli r.qs hF.mu64 hF.bn r.high (hsvOf lv r) (by rw [hhl]; exact hF.hn)
      (by simp [hsvOf, hhl]) (osVals_ofK hF.val) hhs
    have hp : ∏ t ∈ Finset.range lv.logCols, (ptFrom G T r.F).getD t 0 = (G.drop r.F).prod * T.prod := by
      rw [← hPl, prod_getD_range, ptFrom, List.drop_append_of_le_length (by rw [hG, hrF]; exact hF.le),
        List.prod_append]
    rw [hp]
    have e : r.lam ^ lv.queries * (r.qs.map eOfNat).foldl (fun a p ↦ (a + resH lv (hsvOf lv r) p) * li) 0 =
        recH r := by
      unfold resH
      have := h
      rw [hhl] at this
      rw [← hql, this, recH, hrmu]
    calc r.lam ^ 2 * r.lam ^ lv.queries * ((G.drop r.F).prod * T.prod) *
          (r.qs.map eOfNat).foldl (fun a p ↦ (a + resH lv (hsvOf lv r) p) * li) 0
        = r.lam ^ 2 * (r.lam ^ lv.queries *
            (r.qs.map eOfNat).foldl (fun a p ↦ (a + resH lv (hsvOf lv r) p) * li) 0) *
            ((G.drop r.F).prod * T.prod) := by ring
      _ = _ := by rw [e]; ring
  · rw [eqEval_prod, hz0, hPl, min_self]

/-! ## The point -/

/-- The rotated point `(G ++ T).drop lane ++ (G ++ T).take lane`. -/
abbrev rotPt (G T : List E) (lane : ℕ) : List E := (G ++ T).drop lane ++ (G ++ T).take lane

/-- **The point's sources**: entry `i` of the rotated point is the fold or tail challenge
`osPtSrc` names, zero past it. -/
theorem ptSrc_ok {c : OsCfg} {tch : ℕ} {G T : List E} (hG : G.length = c.nFolds)
    (hT : T.length = c.yrLog) (hl : (c.levels.headD default).folds ≤ c.nFolds)
    (hfch : ∀ j (h : j < G.length), LoadHolds rd (σ (.n osFch)) j G[j])
    (htch : ReadsAt rd (σ (.n tch)) T) (i : ℕ) :
    PtSrcOk rd σ (osPtSrc c tch i)
      ((rotPt G T (c.levels.headD default).folds).getD i 0) := by
  set lane := (c.levels.headD default).folds with hlane
  have hlen : (G ++ T).length = c.nFolds + c.yrLog := by simp [hG, hT]
  unfold osPtSrc
  simp only [← hlane]
  by_cases h1 : i < c.nFolds - lane
  · simp only [h1, ↓reduceIte, PtSrcOk]
    rw [List.getD_eq_getElem _ _ (by simp [hG, hT]; omega), List.getElem_append_left (by simp [hG, hT]; omega),
      List.getElem_drop, List.getElem_append_left (by omega)]
    exact hfch _ (by omega)
  · by_cases h2 : i < c.nFolds - lane + c.yrLog
    · simp only [h1, h2, ↓reduceIte, PtSrcOk]
      rw [List.getD_eq_getElem _ _ (by simp [hG, hT]; omega), List.getElem_append_left (by simp [hG, hT]; omega),
        List.getElem_drop, List.getElem_append_right (by omega)]
      have := htch (i - (c.nFolds - lane)) (by omega)
      convert this using 2
      omega
    · by_cases h3 : i < c.nFolds + c.yrLog
      · simp only [h1, h2, h3, ↓reduceIte, PtSrcOk]
        rw [List.getD_eq_getElem _ _ (by simp [hG, hT]; omega), List.getElem_append_right (by simp [hG, hT]; omega),
          List.getElem_take, List.getElem_append_left (by simp [hG, hT]; omega)]
        have := hfch (i - (c.nFolds - lane) - c.yrLog) (by omega)
        convert this using 2
        simp [hG, hT]; omega
      · simp only [h1, h2, h3, ↓reduceIte, PtSrcOk]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [hG, hT]; omega),
          Option.getD_none]

end
end LeanVM.Guest.B1.Whir
