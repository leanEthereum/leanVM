/-
  LeanVM.Guest.B1.Whir.CHonRes

  The residual chains the finish computes are `level_residual`'s over the honest buffers' words.
-/

module

public import LeanVM.Guest.B1.Whir.CHonFinRun
public import LeanVM.Guest.B1.Whir.CHonFields0

/-!
# The residual chains, honestly

`OsHD.own_word`: a word of an honest buffer within its size is its unfitted word.
`OsHD.finRes_eq`: a non-final level's chains (`finRes`, from its basis row, high part and positions)
are `osLrRetA`'s, `level_residual`'s chains over `basis_d`'s, `level_hs`'s and `query_positions`'
words at `μ = λ⁻¹`. `HonRun.fld_resEq`: on a run.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

theorem residualProd_congr' (vals : List E) (x : E) {d d' : ℕ → E} :
    ∀ n, (∀ t < n, d t = d' t) → residualProd vals x d n = residualProd vals x d' n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [residualProd]
    rw [residualProd_congr' vals x n (fun t ht ↦ h t (by omega)), h n (by omega)]

namespace OsHD

variable (h : OsHD)

/-- **A word of an honest buffer** within its size. -/
theorem own_word {j e : ℕ} (hj : j < (osSizesL h.c).length) (he : e < (osSizesL h.c).getD j 0) :
    (osOwnA h.own j).getD e 0 = (h.ownW j).getD e 0 := by
  show (h.own.getD j []).getD e 0 = _
  rw [h.own_getD hj, ownAt, fitTo_getD he]

/-- **A non-final level's chains are `level_residual`'s** over the honest buffers' words. -/
theorem finRes_eq (hHS : HonStatic h.c) (hF : FinStatic h.c h.G h.T h.recs)
    (hL : h.Ls.length = h.c.levels.length) (hrun : ∀ i < h.c.yrLevel, RecRun h i) {l : ℕ}
    (hl : l < h.c.yrLevel) :
    finRes h.c h.G h.T h.recs h.li l = osLrRetA h.c h.own l (h.li l) := by
  have hy := hHS.yr
  have lf := hF.lv l hl
  have hR := hrun l hl
  have hr : h.recs.getD l default = (h.L l).osRec h.logN := h.recs_getD hL hy hl
  have hn6 := hF.n6
  -- the basis row
  have hD : ∀ t < (h.c.levels.getD l default).logCols, finD h.c h.G h.T h.recs l t =
      (osOwnA h.own (osIxBdA h.c)).getD (l * ligColsCap + t) 0 := fun t ht ↦ by
    have ht' : t < (finLv h.c l).prefixLen + h.c.yrLog := by rw [lf.pre]; exact ht
    obtain ⟨hbl, eb⟩ := finBdC_get (G := h.G) (T := h.T) (recs := h.recs) hl (by omega) ht'
      (by rw [lf.pre]; exact hF.cols l hl)
    have hsz := hHS.fin (k := 3) (by omega)
    have hcl : (h.c.levels.getD l default).logCols ≤ ligColsCap := hF.cols l hl
    have hlt : l * ligColsCap + t < h.c.levels.length * ligColsCap := by
      have : (l + 1) * ligColsCap ≤ h.c.levels.length * ligColsCap := Nat.mul_le_mul_right _ (by omega)
      rw [Nat.add_mul, Nat.one_mul] at this
      omega
    rw [show osIxBdA h.c = 12 + h.c.yrLevel + 3 by unfold osIxBdA; omega,
      h.own_word (hHS.finLt (k := 3) (by omega)) (by rw [hsz]; exact hlt), h.ownW_fin (by omega)]
    exact eb.symm
  -- the high part
  have hH : hsvOf (finLv h.c l) (h.recs.getD l default) =
      (List.range (h.c.levels.getD l default).folds).map fun i ↦ (osOwnA h.own osIxHsA).getD (l * hsStride + i) 0 := by
    refine List.map_congr_left fun i hi ↦ ?_
    have hi' := List.mem_range.mp hi
    have hj8 : i < hsStride := lt_of_lt_of_le hi' (hHS.mid hl).2
    have hlt : l * hsStride + i < h.c.levels.length * hsStride := by
      have : (l + 1) * hsStride ≤ h.c.levels.length * hsStride := Nat.mul_le_mul_right _ (by omega)
      rw [Nat.add_mul, Nat.one_mul] at this
      omega
    have h6 := hHS.head (j := 6) (by omega)
    rw [h.own_word (hHS.headLt (j := 6) (by omega)) (by rw [h6]; simpa [headSizes] using hlt),
      ownW_hs, hsC, getD_mapRange _ hlt]
    have e1 : (l * hsStride + i) / hsStride = l := by unfold hsStride at *; omega
    have e2 : (l * hsStride + i) % hsStride = i := by unfold hsStride at *; omega
    simp only [e1, e2, hl, hi', and_self, ↓reduceIte, hr, LvAt.osRec_high]
  -- the positions
  have hP : (List.range (h.c.levels.getD l default).queries).map (fun k ↦ eOfNat ((h.recs.getD l default).qs.getD k 0)) =
      (List.range (h.c.levels.getD l default).queries).map fun k ↦ (osOwnA h.own osIxQposA).getD ((h.c.levels.getD l default).posOff + k) 0 := by
    refine List.map_congr_left fun k hk ↦ ?_
    have hk' := List.mem_range.mp hk
    have hQ : k < (h.c.levels.getD l default).squeezes * sqPer (h.c.levels.getD l default) := lt_of_lt_of_le hk' hR.Q
    obtain ⟨-, htop⟩ := chain_disj hHS.pos
    have := htop l (by omega)
    have h9 := hHS.head (j := 9) (by omega)
    rw [h.own_word (hHS.headLt (j := 9) (by omega)) (by rw [h9]; show _ < h.c.levels.length * ligPosCap; omega),
      ownW_qpos, h.qpos_seg hHS (by omega) hQ, hr, hR.qs k hk']
  -- the chains
  have eP : resP (finLv h.c l) (finD h.c h.G h.T h.recs l) =
      lrP (h.c.levels.getD l default).logCols (fun s ↦ (osOwnA h.own (osIxBdA h.c)).getD (l * ligColsCap + s) 0) := by
    funext x
    unfold resP lrP
    rw [show (finLv h.c l).vanish = lrVo (finLv h.c l).logCols from lf.van]
    exact residualProd_congr' _ x _ fun t ht ↦ hD t ht
  have eH : resH (finLv h.c l) (hsvOf (finLv h.c l) (h.recs.getD l default)) =
      lrH (h.c.levels.getD l default).logCols (h.c.levels.getD l default).folds (h.c.levels.getD l default).highBits
        ((List.range (h.c.levels.getD l default).folds).map fun i ↦ (osOwnA h.own osIxHsA).getD (l * hsStride + i) 0) := by
    funext x
    unfold resH lrH
    rw [show (finLv h.c l).vanish = lrVo (finLv h.c l).logCols from lf.van, hH]
  show resFold (resP (finLv h.c l) (finD h.c h.G h.T h.recs l))
      (resH (finLv h.c l) (hsvOf (finLv h.c l) (h.recs.getD l default))) (h.li l) (0, 0)
      ((List.range (finLv h.c l).queries).map fun k ↦ eOfNat ((h.recs.getD l default).qs.getD k 0)) = _
  rw [eP, eH, hP]
  rfl

end OsHD

namespace HonRun

variable {μ r : ℕ} {target : E} {S : KeccakState} {root : Digest} {xs : List E}
  {os : List (List Opening)} {w : WhirEnd} {cfg : List Whir.Level} {Ls : List LvAt}
  (hR : HonRun μ r target S root xs os w cfg Ls)
include hR

/-- **The chains on a run.** -/
theorem fld_resEq : ∀ l < (hdOf μ r Ls).c.yrLevel,
    finRes (hdOf μ r Ls).c (hdOf μ r Ls).G (hdOf μ r Ls).T (hdOf μ r Ls).recs (hdOf μ r Ls).li l =
      osLrRetA (hdOf μ r Ls).c (hdOf μ r Ls).own l ((hdOf μ r Ls).li l) := fun _ hl ↦
  (hdOf μ r Ls).finRes_eq (honStatic_all _ _ hR.m11 hR.r4) hR.finStatic_run hR.len hR.recRun_run hl

end HonRun

end
end LeanVM.Guest.B1.Whir
