/-
  LeanVM.Guest.B1.Whir.Residuals

  The non-final levels' residual chains and the inner chain they feed.
-/

module

public import LeanVM.Guest.B1.Whir.ResLoop

/-!
# The residuals (G:1826-1862)

A non-final level's residual (`osResidual`): `μ` read from `level_mus`, the chains' buffer from
`0, 0`, the loop over its batches of eight queries (`resLoop_sound`, `resChain`), the remaining
queries inline (`osResSteps_val`): the chains over all its positions (`osResidual_sound`). The
level's sums go into `inner_chain`: `ich[2l + 2] = ich[2l] + scale_l·h_l` and
`ich[2l + 3] = ich[2l + 1] + β_l·after_l·hh_l`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- What a level's residual reads: its loop helper, its row and high part, its positions, `μ`. -/
structure ResIn (rd : Reader) (σ : Val) (c : OsCfg) (bd lvl : ℕ) (lv : OsLv) (D : ℕ → E)
    (hsv : List E) (Pos : ℕ → E) (mu : E) : Prop where
  fn : FnIs (c.resLoop lvl) (osParams 7) (resLoopBody lvl lv (c.resLoop lvl))
  read : ResRead rd lvl lv (σ (.n bd)) (σ (.n osHs)) D hsv
  posOff : lv.posOff < u128Bound
  nbo : lv.queries / resBatch < ordG
  nbu : lv.queries / resBatch < u128Bound
  pos : ∀ k < lv.queries, LoadHolds rd (σ (.n osQpos)) (lv.posOff + k) (Pos k)
  mus : LoadHolds rd (σ (.n osMus)) lvl mu

/-- The chains over a level's positions. -/
def resAll (lv : OsLv) (D : ℕ → E) (hsv : List E) (Pos : ℕ → E) (mu : E) : E × E :=
  resFold (resP lv D) (resH lv hsv) mu (0, 0) ((List.range lv.queries).map Pos)

theorem gw_zero : gw 0 = 1 := by rw [gw_eq (by decide), pow_zero]

/-- **A level's residual** (G:1826-1862): the inner chain's two sums advanced by its chains. -/
theorem osResidual_sound (hle : CallRel.Le C (coreProgram.Rel rd)) {c : OsCfg}
    {ich bd ls la lvl : ℕ} {lv : OsLv} {D : ℕ → E} {hsv : List E} {Pos : ℕ → E} {mu : E}
    (hin : ResIn rd σ c bd lvl lv D hsv Pos mu) {k : ℕ}
    (hok : AllOk C rd σ (osResidual c ich bd ls la lvl lv k).1) :
    ∃ i0 i1 s b a : E, LoadHolds rd (σ (.n ich)) (2 * lvl) i0 ∧
      LoadHolds rd (σ (.n ich)) (2 * lvl + 1) i1 ∧ LoadHolds rd (σ (.n ls)) lvl s ∧
      LoadHolds rd (σ (.n osBetas)) lvl b ∧ LoadHolds rd (σ (.n la)) lvl a ∧
      LoadHolds rd (σ (.n ich)) (2 * lvl + 2) (i0 + s * (resAll lv D hsv Pos mu).1) ∧
      LoadHolds rd (σ (.n ich)) (2 * lvl + 3) (i1 + b * a * (resAll lv D hsv Pos mu).2) := by
  obtain ⟨fn, hfind, hps, hbody⟩ := hin.fn
  unfold osResidual at hok
  simp only at hok
  set nb := lv.queries / resBatch with hnb
  set tl := osResSteps osQpos bd (lvl * ligColsCap) osHs (lvl * hsStride) lv.vanish lv.logCols
    lv.folds lv.highBits k (osResTail lv) (k + 10) (k + 11) (k + 12) with htl
  simp only [allOk_append] at hok
  obtain ⟨⟨⟨⟨⟨⟨hmu, -⟩, hz⟩, hcall⟩, hld⟩, hst⟩, hfin⟩ := hok
  simp only [allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_load, holds_const, osLd, osCst]
    at hmu hz hld
  obtain ⟨z3, l3, z4, l4⟩ := hz
  rw [z3, word_zero] at l3
  rw [z4, word_zero] at l4
  obtain ⟨l10, l11⟩ := hld
  have emu : σ (.n k) = mu := loadHolds_unique hmu hin.mus
  -- the loop
  have hR := hin.read
  have hloop : ∀ j < nb, ResIter rd (resP lv D) (resH lv hsv) lv.posOff (σ (.n osQpos))
      (σ (.n (k + 2))) mu (gen ^ j) := by
    rcases Nat.eq_zero_or_pos nb with h0 | h0
    · intro j hj; omega
    · refine resLoop_sound (lvl := lvl) (lv := lv) hfind hps hbody hin.posOff h0 hin.nbo _ _ _ _ _ hR ?_
      simp only [osLoopCall, allOk_cons, allOk_nil, and_true, holds_const, holds_add,
        osCst, osAdd, StmtOk, List.map_cons, List.map_nil] at hcall
      obtain ⟨c5, c6, a7, c8, c9, -, hc⟩ := hcall
      intro hne
      have e7 : σ (.n (k + 5 + 2)) = 1 + gen ^ nb := by
        rw [a7, c5, c6, gw_zero, gw_eq hin.nbu]
      have := hc (by rw [e7]; exact hne)
      rw [c8, c9, gw_zero, gw_eq hin.nbu, emu] at this
      exact hle _ _ _ this
  have hch := resChain (Pos := Pos) (n := nb) (fun i hi ↦ hin.pos i (by
      have := Nat.div_mul_le_self lv.queries resBatch
      rw [hnb] at hi; nlinarith)) (by simpa using l3) (by simpa using l4) hloop nb le_rfl
  obtain ⟨c0, c1⟩ := hch
  have e10 := loadHolds_unique l10 c0
  have e11 := loadHolds_unique l11 c1
  -- the remaining queries
  have hR' : ∀ s < lv.logCols, LoadHolds rd (σ (.n bd)) (lvl * ligColsCap + s) (D s) := hR.D
  obtain ⟨ps, hF, hv⟩ := osResSteps_val hR.cols hR.nhs hR.b3 hR.bn hR' hR.len hR.hs (osResTail lv)
    (k + 10) (k + 11) (k + 12) hst
  have hps' : ps = (List.range (lv.queries % resBatch)).map fun i ↦ Pos (resBatch * nb + i) := by
    have hl := hF.length_eq
    refine List.ext_getElem (by simp [← hl, osResTail]) fun i h1 h2 ↦ ?_
    have := List.forall₂_iff_get.mp hF
    have h3 := this.2 i (by rw [hl]; exact h1) h1
    simp only [List.get_eq_getElem, osResTail, List.getElem_map, List.getElem_range] at h3
    simp only [List.getElem_map, List.getElem_range]
    refine loadHolds_unique h3 ?_
    have hq := hin.pos (resBatch * nb + i) (by
      have := Nat.div_add_mod lv.queries resBatch
      simp at h2; rw [hnb]; omega)
    rw [show lv.posOff + (lv.queries - lv.queries % resBatch) + i = lv.posOff + (resBatch * nb + i) by
      have := Nat.div_add_mod lv.queries resBatch; rw [hnb]; omega]
    exact hq
  have hall : (List.range lv.queries).map Pos = (List.range (resBatch * nb)).map Pos ++ ps := by
    have hQ : resBatch * nb + lv.queries % resBatch = lv.queries := by
      rw [hnb]; exact Nat.div_add_mod _ _
    rw [hps', show List.range lv.queries = List.range (resBatch * nb + lv.queries % resBatch) by
      rw [hQ], List.range_add, List.map_append, List.map_map]
    rfl
  have hres : (σ (.n tl.2.1), σ (.n tl.2.2.1)) = resAll lv D hsv Pos mu := by
    rw [hv, e10, e11, emu, resAll, hall, resFold_append]
    rfl
  -- the inner chain
  simp only [allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_load, holds_mul, holds_add, osLd,
    osMul, osAdd] at hfin
  obtain ⟨l0, l1, m2, a3, s3, l4', l5, l6, m7, m8, a9, s9⟩ := hfin
  have r1 := congrArg Prod.fst hres
  have r2 := congrArg Prod.snd hres
  simp only at r1 r2
  refine ⟨_, _, _, _, _, l0, l4', l1, l5, l6, ?_, ?_⟩
  · rw [a3, m2, r1] at s3; exact s3
  · rw [a9, m8, m7, r2] at s9; exact s9

end
end LeanVM.Guest.B1.Whir
