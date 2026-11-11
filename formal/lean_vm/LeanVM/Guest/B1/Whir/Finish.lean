/-
  LeanVM.Guest.B1.Whir.Finish

  The body after the tail: the residual's value, the point, the basis rows, the residual sums,
  the out-of-domain weights and the returns.
-/

module

public import LeanVM.Guest.B1.Whir.Residuals
public import LeanVM.Guest.B1.Whir.Bases
public import LeanVM.Guest.B1.Whir.OodW
public import LeanVM.Guest.B1.Whir.Point
public import LeanVM.Guest.B1.Eq.Meaning

/-!
# The finish (G:1667-1757)

`osFinish_sound`: from what the levels and the tail stored (`FinIn`), the returns are the claim,
the two point buffers, the glued weight `Σ_lvl scale_lvl·sum_lvl + Σ_ol ood_ol` (`finInner`) and
the final message folded at the tail challenges.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader} {σ : Val}

/-- `osFinish` before its `ret`. -/
def osFinishA (c : OsCfg) (st : OsSt) (tch : ℕ) : List Stmt :=
  let n := c.levels.length
  let yat := st.k
  let pt := yat + 1
  let pts := osPtBlks c pt (pt + 1) tch 0 pointCap (pt + 2)
  let bd := pts.2 + 1
  let ls := pts.2 + 3
  let bs := osBases c tch bd ls 0 c.levels (pts.2 + 4)
  let ich := bs.2 + 1
  let rs := osResiduals c ich bd ls 0 c.levels st.mats (bs.2 + 3)
  let od := osOodWeights c tch ((c.levels.headD default).logCols) 1 c.levels.tail none rs.2
  let k := od.2.2
  [.call ("fold_final_msg__L" ++ natStr c.yrLog) [.n osFmsg, .n tch] [.n yat],
    .atom (.hint (.alloc (.n pt) pointCap)), .atom (.hint (.alloc (.n (pt + 1)) pointCap))] ++
    pts.1 ++ osHeap (n * ligColsCap) pts.2 ++ osHeap n (pts.2 + 2) ++ bs.1 ++
    osHeap (n + 1) bs.2 ++
    [.atom (.const (.n (bs.2 + 2)) (word 0 0 0)), .atom (.load (.n (bs.2 + 2)) (.n ich) 0)] ++
    rs.1 ++ od.1 ++
    [.atom (.copy (.n k) (.n st.t)), .atom (.copy (.n (k + 1)) (.n pt)),
      .atom (.copy (.n (k + 2)) (.n (pt + 1))), .atom (.load (.n (k + 3)) (.n ich) n),
      .atom (.add (.n (k + 4)) (.n (k + 3)) (.n (od.2.1.getD 0))), .atom (.copy (.n (k + 5)) (.n yat))]

/-- `osFinish`'s returns. -/
def osFinishRet (c : OsCfg) (st : OsSt) (tch : ℕ) : List V :=
  let pts := osPtBlks c (st.k + 1) (st.k + 1 + 1) tch 0 pointCap (st.k + 1 + 2)
  let bs := osBases c tch (pts.2 + 1) (pts.2 + 3) 0 c.levels (pts.2 + 4)
  let rs := osResiduals c (bs.2 + 1) (pts.2 + 1) (pts.2 + 3) 0 c.levels st.mats (bs.2 + 3)
  let k := (osOodWeights c tch ((c.levels.headD default).logCols) 1 c.levels.tail none rs.2).2.2
  [.n k, .n (k + 1), .n (k + 2), .n (k + 4), .n (k + 5)]

theorem osFinish_split (c : OsCfg) (st : OsSt) (tch : ℕ) :
    osFinish c st tch = osFinishA c st tch ++ [.ret (osFinishRet c st tch)] := by
  simp only [osFinish, osFinishA, osFinishRet, List.append_assoc, List.cons_append,
    List.nil_append]

/-! ## The residual sums, every level -/

theorem osResiduals_sound {c : OsCfg} {ich bd ls : ℕ} (G : ℕ → E) (levels : List OsLv) :
    ∀ (lvl : ℕ) (mats : List OsMat) (k : ℕ) (I : E),
      (∀ i (hi : i < levels.length) (mats' : List OsMat) (k' : ℕ) (I' : E), MatsOk σ mats' →
        AllOk (coreProgram.Rel rd) rd σ (osResidual c ich bd ls (lvl + i) levels[i] mats' k').1 →
        LoadHolds rd (σ (.n ich)) (lvl + i) I' →
        LoadHolds rd (σ (.n ich)) (lvl + i + 1) (I' + G (lvl + i)) ∧
          MatsOk σ (osResidual c ich bd ls (lvl + i) levels[i] mats' k').2.1) →
      MatsOk σ mats →
      AllOk (coreProgram.Rel rd) rd σ (osResiduals c ich bd ls lvl levels mats k).1 →
      LoadHolds rd (σ (.n ich)) lvl I →
      LoadHolds rd (σ (.n ich)) (lvl + levels.length)
        (I + ∑ i ∈ Finset.range levels.length, G (lvl + i)) := by
  induction levels with
  | nil => intro lvl _ _ I _ _ _ h; simpa using h
  | cons lv rest ih =>
    intro lvl mats k I hstep hm hok h
    simp only [osResiduals] at hok
    rw [allOk_append] at hok
    have h1 := hstep 0 (by simp) mats k I hm hok.1 (by simpa using h)
    have := ih (lvl + 1) _ _ _ (fun i hi mats' k' I' hm' h1 h2 ↦ by
      have := hstep (i + 1) (by simp; omega) mats' k' I' hm'
        (by rwa [show lvl + (i + 1) = lvl + 1 + i by ring]) (by
          rwa [show lvl + (i + 1) = lvl + 1 + i by ring])
      rwa [show lvl + (i + 1) = lvl + 1 + i by ring] at this) (by simpa using h1.2) hok.2
      (by simpa using h1.1)
    have e : I + ∑ i ∈ Finset.range (lv :: rest).length, G (lvl + i) =
        I + G lvl + ∑ i ∈ Finset.range rest.length, G (lvl + 1 + i) := by
      rw [List.length_cons, Finset.sum_range_succ', Finset.sum_congr rfl
        (fun i _ ↦ by rw [show lvl + (i + 1) = lvl + 1 + i by ring])]
      simp only [Nat.add_zero]
      ring
    rw [e, List.length_cons, show lvl + (rest.length + 1) = lvl + 1 + rest.length by ring]
    exact this

/-! ## The finish -/

/-- Words read at a pointer are determined by their number. -/
theorem readsAt_unique {p : E} {xs ys : List E} (hl : xs.length = ys.length)
    (hx : ReadsAt rd p xs) (hy : ReadsAt rd p ys) : xs = ys :=
  List.ext_getElem hl fun i h1 h2 ↦ loadHolds_unique (hx i h1) (hy i h2)

/-- What a level's residual sum reads: `level_residual`'s meaning at the rate's row, its
positions, `μ = λ⁻¹` in `level_mus`. -/
def ResIn (rd : Reader) (σ : Val) (c : OsCfg) (lvl : ℕ) (lv : OsLv) (P : ℕ → E) (lam : E) :
    Prop :=
  (∀ args rets, coreProgram.Rel rd (osResidualName lv) args rets →
      MeaningLevelResidual lv.queries lv.logCols rd args rets) ∧ LvRate σ c lvl lv ∧
    lv.vanish = vanishOff lv.logCols ∧ lv.posOff < u128Bound ∧ lvl * ligColsCap < u128Bound ∧
    lv.prefixLen + c.yrLog = lv.logCols ∧
    (∀ i < lv.queries, LoadHolds rd (σ (.n osQpos)) (lv.posOff + i) (P i)) ∧ lam ≠ 0 ∧
    LoadHolds rd (σ (.n osMus)) lvl lam⁻¹

/-- **The `μ`-chain times `λ^n` is the `λ`-weighted sum** (`μ = λ⁻¹`). -/
theorem resFold_lam {D : ℕ → E} {vo ml n : ℕ} {lam : E} (h0 : lam ≠ 0) (P : ℕ → E) :
    lam ^ n * resFold D vo ml lam⁻¹ 0 ((List.range n).map P) =
      ∑ j ∈ Finset.range n, lam ^ j * residualProd (osVals vo ml) (P j) D ml := by
  rw [resFold_eq_sum, zero_mul, zero_add, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [Finset.mem_range] at hj
  rw [inv_pow, mul_comm (residualProd _ _ _ _), ← mul_assoc]
  congr 1
  rw [show n = j + (n - j) by omega, pow_add, mul_assoc, show j + (n - j) - j = n - j by omega,
    mul_inv_cancel₀ (pow_ne_zero _ h0), mul_one]

/-- A level's coefficients `d_t`. -/
def dOf (lv : OsLv) (X : ℕ → E) (t : ℕ) : E := (1 + X t) / (X t * invW lv t)

/-- The guest's glued weight: every level's scale times its residual sum, and the out-of-domain
weights. -/
def finInner (c : OsCfg) (β : ℕ → E) (X P W : ℕ → ℕ → E) (Λ : ℕ → E) (Z Y : ℕ → ℕ → E) : E :=
  ∑ i ∈ Finset.range c.levels.length,
    (β i * ∏ t ∈ Finset.range ((c.levels.getD i default).prefixLen + c.yrLog),
        (X i t * invW (c.levels.getD i default) t)) *
      ∑ j ∈ Finset.range (c.levels.getD i default).queries,
        W i j * lvRes (c.levels.getD i default) (dOf (c.levels.getD i default) (X i)) (P i j) +
  oodSum c Λ Z Y (c.levels.headD default).logCols 1 c.levels.tail

/-- **The finish** (G:1518-1608). -/
theorem osFinish_sound {c : OsCfg} {st : OsSt} {tch : ℕ} {ms T Pt : List E} {β Λ Lam : ℕ → E}
    {X P W Z Y : ℕ → ℕ → E} (hW : ∀ i j, W i j = Lam i ^ j)
    (hfm : ∀ args rets, coreProgram.Rel rd ("fold_final_msg__L" ++ natStr c.yrLog) args rets →
      MeaningFoldFinalMsg c.yrLog rd args rets)
    (hms : ms.length = 2 ^ c.yrLog) (hmsr : ReadsAt rd (σ (.n osFmsg)) ms)
    (hT : T.length = c.yrLog) (hTr : ReadsAt rd (σ (.n tch)) T)
    (hpt : ∀ i, PtSrcOk rd σ (osPtSrc c tch i) (Pt.getD i 0))
    (hbasis : ∀ i (hi : i < c.levels.length), BasisIn rd σ c tch i c.levels[i]
      (β i * Lam i ^ c.levels[i].queries) (X i))
    (hres : ∀ i (hi : i < c.levels.length), ResIn rd σ c i c.levels[i] (P i) (Lam i))
    (hood : OodAll rd σ c tch Λ Z Y (c.levels.headD default).logCols 1 c.levels.tail)
    (hn2 : 2 ≤ c.levels.length) (hmats : MatsOk σ st.mats)
    (hok : AllOk (coreProgram.Rel rd) rd σ (osFinishA c st tch)) :
    (osFinishRet c st tch).map σ = [σ (.n st.t), σ (.n (st.k + 1)), σ (.n (st.k + 1 + 1)),
      finInner c β X P W Λ Z Y, multilinearEval ms T] ∧
    (∀ i < pointCap, LoadHolds rd (σ (.n (st.k + 1))) i (Pt.getD i 0) ∧
      LoadHolds rd (σ (.n (st.k + 1 + 1))) i (1 + Pt.getD i 0)) ∧
    ∀ i (hi : i < c.levels.length), ∀ t < c.levels[i].prefixLen + c.yrLog,
      X i t * invW c.levels[i] t ≠ 0 := by
  simp only [osFinishA, osFinishRet] at hok ⊢
  set pts := osPtBlks c (st.k + 1) (st.k + 1 + 1) tch 0 pointCap (st.k + 1 + 2) with hpts
  set bs := osBases c tch (pts.2 + 1) (pts.2 + 3) 0 c.levels (pts.2 + 4) with hbs
  set rs := osResiduals c (bs.2 + 1) (pts.2 + 1) (pts.2 + 3) 0 c.levels st.mats (bs.2 + 3) with hrs
  set od := osOodWeights c tch (c.levels.headD default).logCols 1 c.levels.tail none rs.2 with hod
  simp only [allOk_append] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hA, hP⟩, -⟩, -⟩, hB⟩, -⟩, hZ⟩, hR⟩, hO⟩, hE⟩ := hok
  -- the final message folded at the tail challenges
  simp only [allOk_cons, allOk_nil, and_true, StmtOk, List.map_cons, List.map_nil] at hA
  obtain ⟨m, ps, hml, hpsl, hmr, hpr, hy⟩ := hfm _ _ hA.1
  have em := readsAt_unique (by rw [hml, hms]) hmr hmsr
  have ep := readsAt_unique (by rw [hpsl, hT]) hpr hTr
  simp only [List.cons.injEq, and_true] at hy
  -- the point
  have hpoint := osPtBlks_sound (C := coreProgram.Rel rd) (fun i ↦ Pt.getD i 0) hpt pointCap 0 _ hP
  -- the bases
  have hbo := osBases_sound (C := coreProgram.Rel rd) (bd := pts.2 + 1) (ls := pts.2 + 3)
    (fun i ↦ β i * Lam i ^ (c.levels.getD i default).queries) X
    c.levels 0 _ (fun i hi ↦ by
      simp only [Nat.zero_add, List.getD_eq_getElem _ _ hi]; exact hbasis i hi) hB
  -- the residual sums
  simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds] at hZ
  obtain ⟨z0, s0⟩ := hZ
  rw [z0, word_zero] at s0
  have hich := osResiduals_sound (rd := rd) (σ := σ) (c := c) (ich := bs.2 + 1) (bd := pts.2 + 1)
    (ls := pts.2 + 3) (fun i ↦ (β i * ∏ t ∈ Finset.range ((c.levels.getD i default).prefixLen +
        c.yrLog), (X i t * invW (c.levels.getD i default) t)) *
      ∑ j ∈ Finset.range (c.levels.getD i default).queries,
        W i j * lvRes (c.levels.getD i default) (dOf (c.levels.getD i default) (X i)) (P i j))
    c.levels 0 st.mats _ 0 (fun i hi mats' k' I' hm' h1 h2 ↦ by
      simp only [Nat.zero_add] at h1 h2 ⊢
      obtain ⟨hf, hrate, hvan, hpo, hlc, hlen, hPq, hl0, hM⟩ := hres i hi
      obtain ⟨hD, hL⟩ := hbo i hi
      simp only [Nat.zero_add] at hD hL
      have hgd : c.levels.getD i default = c.levels[i] := by
        rw [List.getD_eq_getElem _ _ hi]
      rw [hgd] at hL ⊢
      obtain ⟨this, hmo⟩ := osResidual_sound hf hrate hvan hpo hlc hm' (D := dOf c.levels[i] (X i))
        (fun s hs ↦ (hD s (by omega)).2) hPq hM h2 hL h1
      refine ⟨?_, hmo⟩
      convert this using 2
      simp only [hW, lvRes]
      rw [← resFold_lam hl0]
      ring) hmats hR (by simpa using s0)
  -- the out-of-domain weights
  obtain ⟨x, hx, hxv⟩ := osOodWeights_sound (C := coreProgram.Rel rd) Λ Z Y c.levels.tail
    (c.levels.headD default).logCols 1 none rs.2 hood hO (Or.inr (by
      intro h
      have := congrArg List.length h
      simp at this
      omega))
  -- the returns
  simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds] at hE
  obtain ⟨e0, e1, e2, l3, a4, e5⟩ := hE
  rw [hx, Option.getD_some, hxv, loadHolds_unique l3 (by simpa using hich)] at a4
  refine ⟨?_, fun i hi ↦ by simpa using hpoint i hi, fun i hi t ht ↦ by
    simpa using ((hbo i hi).1 t ht).1⟩
  simp only [List.map_cons, List.map_nil, e0, e1, e2, a4, e5, hy, em, ep, accVal, zero_add,
    finInner, List.getD_eq_getElem?_getD]

end
end LeanVM.Guest.B1.Whir
