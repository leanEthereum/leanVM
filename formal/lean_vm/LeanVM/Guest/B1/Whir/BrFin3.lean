/-
  LeanVM.Guest.B1.Whir.BrFin3

  The finish's inner sum plus out-of-domain sum is the run's glued weight.
-/

module

public import LeanVM.Guest.B1.Whir.BrFin2

/-!
# The glued weight

`finI_eq`: the inner sum after `m` levels is `Σ scale · chain`, a level's chain the `μ`-chain over
every query. `fin_inner`: the inner sum after
every level plus the out-of-domain weights is the trace's glued weight (by the soundness proof's
`inner_eq`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

variable {c : OsCfg} {tr : OsTr}

theorem finI_eq (c : OsCfg) (tr : OsTr) : ∀ m, finI c tr m = ∑ i ∈ Finset.range m,
    finL c tr i * resFold (finD c tr i) (lvAt c i).vanish (lvAt c i).logCols (finM tr i) 0
      ((List.range (lvAt c i).queries).map (Pof tr.rs i))
  | 0 => by simp [finI]
  | m + 1 => by rw [finI, finI_eq c tr m, Finset.sum_range_succ]; rfl

/-- **The inner sum plus the out-of-domain sum is the trace's glued weight.** -/
theorem fin_inner {μ r : ℕ} {cfg : List Whir.Level} (hF : CandFacts c μ r cfg) (h : TrFit c tr) :
    finI c tr c.levels.length + oodSum c (Λof tr.rs) (Zof tr.rs) (Yof tr.rs tr.Fall tr.Tc)
      ((c.levels.headD default).logCols) 1 c.levels.tail =
    tr.Lf.wsEnd.glued.foldl (fun weight claim ↦
      weight + claim.scalar * claim.weightAt (tr.Fall.drop claim.foldStart ++ tr.Tc)) 0 := by
  have hn := hF.n2
  have hFl := fall_length hF h
  have hlv : ∀ i < c.levels.length, LvFin c tr.rs tr.Fall tr.Tc i := by
    intro i hi
    have hst := hF.lv i hi
    have hfit := h.fit i hi
    have hb := h.lvb i hi
    have hle : (lvAt c i).foldsOff + (lvAt c i).folds ≤ c.nFolds := hst.le
    have hcols : c.nFolds - ((lvAt c i).foldsOff + (lvAt c i).folds) + c.yrLog =
        (lvAt c i).logCols := hst.cols
    have hpre : (lvAt c i).prefixLen + c.yrLog = (lvAt c i).logCols := hst.pre
    refine ⟨by rw [rec_F h hi, hFl]; exact hle, by rw [rec_F h hi, hFl, h.tcLen]; exact hcols,
      by rw [rs_get h hi]; exact hfit.ml, by rw [rs_get h hi]; simp [recOf, SpLv.qs_length, hb.queries],
      hpre, vanish_val hst.vanish, fun t ht ↦ (vanish_inv hst.vanish t ht).1,
      fun t ht ↦ mul_ne_zero (xof_ne hF h hi ht) (vanish_inv hst.vanish t ht).2, fun hf ↦ ?_,
      fun hf ↦ ?_⟩
    · rw [rs_get h hi]; simp [recOf, hfit.fin.mpr hf]
    · have hfin : (tr.L i).fin = false := by
        cases e : (tr.L i).fin
        · rfl
        · exact absurd (hfit.fin.mp e) hf
      refine ⟨oodZ (tr.L i).F1 (tr.L i).ra (tr.L i).rb (tr.L i).ml, by rw [rs_get h hi]; simp [recOf, hfin], ?_⟩
      rw [oodZ_length _ _ _ (by rw [hfit.ml]; exact hst.ml1), hfit.ml]
  have hrs : tr.rs.length = c.levels.length := by simp [OsTr.rs, h.len]
  rw [h.glued, inner_eq hrs (by omega) hF.yr h.tcLen hlv, finI_eq, finInner]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i hi ↦ ?_) rfl
  obtain ⟨R, d, hOk⟩ := h.ok i (Finset.mem_range.mp hi)
  have hl0 : (tr.rs.getD i default).lam ≠ 0 := by
    rw [rs_get h (Finset.mem_range.mp hi)]; exact hOk.lam
  have key := resFold_lam (D := finD c tr i) (vo := (lvAt c i).vanish) (ml := (lvAt c i).logCols)
    (n := (lvAt c i).queries) hl0 (Pof tr.rs i)
  simp only [finL, finB, finM, Wof, finD, lvAt, lvRes] at key ⊢
  rw [← key]
  ring

end
end LeanVM.Guest.B1.Whir
