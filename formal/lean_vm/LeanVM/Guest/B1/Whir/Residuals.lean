/-
  LeanVM.Guest.B1.Whir.Residuals

  A level's residual sum: the residual loop over its query pairs, the odd query inline, the
  running `inner` advanced by the level's scale times the sum.
-/

module

public import LeanVM.Guest.B1.Whir.ResLoop

/-!
# The residual sums (G:1721-1744)

`osResidual_sound`: level `lvl`'s block reads `μ` from `level_mus`, its positions `P`, its row's
words `D` in `basis_d`, its scale `L` in `level_scale`, and stores
`inner[lvl + 1] = inner[lvl] + L·h`, `h` the chain `h ← (h + R(P_i))·μ` over its queries from `0`
(`resFold`), `R` the level's `residual_query`: the loop over the batches of eight, the rest inline.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader} {σ : Val}

/-- A level's residual at a position. -/
abbrev lvRes (lv : OsLv) (D : ℕ → E) (p : E) : E :=
  residualProd (osVals lv.vanish lv.logCols) p D lv.logCols

/-- `resFold` is the sum of the residuals weighted by powers of `μ`. -/
theorem resFold_eq_sum (D : ℕ → E) (vo ml : ℕ) (mu h : E) (P : ℕ → E) (n : ℕ) :
    resFold D vo ml mu h ((List.range n).map P) =
      h * mu ^ n + ∑ i ∈ Finset.range n, residualProd (osVals vo ml) (P i) D ml * mu ^ (n - i) := by
  induction n with
  | zero => simp [resFold]
  | succ n ih =>
    rw [List.range_succ, List.map_append, resFold_append, ih]
    simp only [List.map_cons, List.map_nil, resFold, List.foldl_cons, List.foldl_nil,
      Finset.sum_range_succ]
    have : ∀ i ∈ Finset.range n, residualProd (osVals vo ml) (P i) D ml * mu ^ (n + 1 - i) =
        residualProd (osVals vo ml) (P i) D ml * mu ^ (n - i) * mu := by
      intro i hi
      rw [Finset.mem_range] at hi
      rw [show n + 1 - i = n - i + 1 by omega, pow_succ, mul_assoc]
    rw [Finset.sum_congr rfl this, ← Finset.sum_mul, pow_succ, show n + 1 - n = 1 by omega]
    ring

/-- **A level's residual sum** (G:1721-1744). -/
theorem osResidual_sound {c : OsCfg} {lvl : ℕ} {lv : OsLv} {ich bd ls k : ℕ}
    (hloop : FnIs (c.resLoop lvl) (osParams 6) (resLoopBody lvl lv (c.resLoop lvl)))
    (hml : 1 ≤ lv.logCols) (hpo : lv.posOff < u128Bound)
    (hqo : lv.queries / resBatch < ordG) (hqu : lv.queries / resBatch < u128Bound)
    {D P : ℕ → E} {I L mu : E}
    (hD : ∀ s < lv.logCols, LoadHolds rd (σ (.n bd)) (lvl * ligColsCap + s) (D s))
    (hP : ∀ i < lv.queries, LoadHolds rd (σ (.n osQpos)) (lv.posOff + i) (P i))
    (hM : LoadHolds rd (σ (.n osMus)) lvl mu)
    (hI : LoadHolds rd (σ (.n ich)) lvl I) (hL : LoadHolds rd (σ (.n ls)) lvl L)
    (hok : AllOk (coreProgram.Rel rd) rd σ (osResidual c ich bd ls lvl lv k).1) :
    LoadHolds rd (σ (.n ich)) (lvl + 1)
      (I + L * resFold D lv.vanish lv.logCols mu 0 ((List.range lv.queries).map P)) := by
  obtain ⟨fn, hfind, hps, hbody⟩ := hloop
  set n := lv.queries / resBatch
  simp only [osResidual, allOk_append] at hok
  obtain ⟨⟨⟨⟨⟨⟨hm, -⟩, hz⟩, hc⟩, hl⟩, htl⟩, hrest⟩ := hok
  simp only [osLoopCall, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds, List.map_cons,
    List.map_nil] at hm hz hc hl hrest
  obtain ⟨z3, s3⟩ := hz
  obtain ⟨c4, c5, a6, c7, c8, -, hcall⟩ := hc
  have hmu : σ (.n k) = mu := loadHolds_unique hm hM
  rw [z3, word_zero] at s3
  -- the chain after the loop
  have hchain : σ (.n (k + 9)) = resFold D lv.vanish lv.logCols mu 0
      ((List.range (resBatch * n)).map P) := by
    have hl : LoadHolds rd (σ (.n (k + 2))) n (σ (.n (k + 9))) := hl
    rcases Nat.eq_zero_or_pos n with hn0 | hn0
    · rw [hn0] at hl ⊢
      simpa [resFold] using loadHolds_unique hl s3
    · have hgn : gw n = gen ^ n := gw_eq hqu
      have hit := resLoop_sound hfind lvl lv hps hbody hml hpo (D := D) (n := n) hn0 hqo
        (σ (.n osQpos)) (σ (.n bd)) (σ (.n (k + 2))) (σ (.n k)) hD (by
          rw [a6, c4, c5, c7, c8, hgn, word_one] at hcall
          exact hcall)
      have := resChain (P := P) (fun i hi ↦ hP i (by
        have := Nat.div_mul_le_self lv.queries resBatch; simp only [n] at hi; nlinarith)) s3 hit n le_rfl
      rw [hmu] at this
      exact loadHolds_unique hl this
  -- the remaining queries
  have hq : resBatch * n + lv.queries % resBatch = lv.queries := Nat.div_add_mod _ _
  obtain ⟨ps, hF, hv⟩ := osResSteps_val hml hD _ _ _ htl
  have eps : ps = (List.range (lv.queries % resBatch)).map fun i ↦ P (resBatch * n + i) := by
    have hlen := hF.length_eq
    simp only [osResTail, List.length_map, List.length_range] at hlen
    refine List.ext_getElem (by simp [hlen]) fun i h1 h2 ↦ ?_
    simp only [List.length_map, List.length_range] at h2
    have h3 := (List.forall₂_iff_get.mp hF).2 i (by simp [osResTail]; omega) h1
    simp only [osResTail, List.get_eq_getElem, List.getElem_map, List.getElem_range] at h3 ⊢
    refine loadHolds_unique h3 ?_
    have := hP (resBatch * n + i) (by omega)
    rwa [show lv.posOff + (lv.queries - lv.queries % resBatch) + i = lv.posOff + (resBatch * n + i) by
      omega]
  have hsplit : (List.range lv.queries).map P = (List.range (resBatch * n)).map P ++
      (List.range (lv.queries % resBatch)).map fun i ↦ P (resBatch * n + i) := by
    conv_lhs => rw [← hq]
    rw [List.range_add, List.map_append, List.map_map]
    rfl
  obtain ⟨l0, l1, m2, a3, s4⟩ := hrest
  rw [hv, hchain, hmu, eps, ← resFold_append, ← hsplit] at m2
  rw [a3, m2, loadHolds_unique l0 hI, loadHolds_unique l1 hL] at s4
  exact s4

end
end LeanVM.Guest.B1.Whir
