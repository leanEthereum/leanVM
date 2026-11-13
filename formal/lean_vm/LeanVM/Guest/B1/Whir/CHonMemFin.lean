/-
  LeanVM.Guest.B1.Whir.CHonMemFin

  The finish's memory and OsHonest's query reads, from the honest buffers.
-/

module

public import LeanVM.Guest.B1.Whir.CHonMemLv

/-!
# The finish's memory, honestly

On a memory holding the honest buffers at `b`:

* `fch_all`: the fold challenges;
* `recStored_of`: a non-final level's record (`RecStored`, S1a-3's) at a valuation holding the
  head's pointers, the record's lengths given;
* `ood_rows`: its out-of-domain points in `ood_z`;
* `tail_reads`, `pt_reads`, `pt1_reads`, `bd_reads`, `ls_reads`, `la_reads`, `ich_reads`,
  `rc_reads`: the finish's buffers, their words fitting;
* `qMem_at`: OsHonest's `qMem` at level `l`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem LvAt.osRec_lam (L : LvAt) (logN : ℕ) : (L.osRec logN).lam = L.lam logN := by
  rcases hd : L.d with ⟨rw, W⟩ | ⟨rw, W⟩
  · simp [LvAt.osRec, LvAt.lam, hd, NextW.osRec]
  · simp only [LvAt.osRec, LvAt.lam, hd]; rfl

theorem LvAt.osRec_high (L : LvAt) (logN : ℕ) : (L.osRec logN).high = L.nw.high := by
  rcases hd : L.d with ⟨rw, W⟩ | ⟨rw, W⟩
  · simp [LvAt.osRec, LvAt.nw, hd, NextW.osRec]
  · simp only [LvAt.osRec, LvAt.nw, hd]; rfl

namespace OsHD

variable (h : OsHD) {rd : Reader} {b : ℕ}

/-- **A non-final level's out-of-domain point** in `ood_z`. -/
theorem ood_rows (hS : HonStatic h.c) (hm : OsMemA rd h.c b h.own) {i : ℕ} (hi : i < h.c.yrLevel)
    (hz0 : ((h.L i).osRec h.logN).z0.length = ((h.c.levels.getD i default)).logCols) :
    ReadsAt rd (osPtrA h.c b 7 * gen ^ ((i + 1) * ligColsCap)) ((h.L i).osRec h.logN).z0 := by
  have hyr := hS.yr
  have hc := (hS.mid hi).1
  have h7 : (osSizesL h.c).getD 7 0 = h.c.levels.length * 24 := by
    rw [hS.head (j := 7) (by omega)]; rfl
  have hc' : ((h.c.levels.getD i default)).logCols ≤ 24 := hc
  unfold ligColsCap
  have hn : (i + 1) * 24 + 24 ≤ h.c.levels.length * 24 := by
    have : i + 1 + 1 ≤ h.c.levels.length := by omega
    have := Nat.mul_le_mul_right 24 this
    rw [Nat.add_mul] at this; omega
  intro t ht
  rw [← List.getD_eq_getElem _ 0 ht, loadHolds_mul_gen_pow]
  have a := h.load hm (hS.headLt (j := 7) (by omega)) (by unfold osIxQbpA; omega)
    (e := (i + 1) * 24 + t) (by rw [h7]; omega)
  rw [ownW_oodz, oodzC, getD_mapRange _ (by show _ < h.c.levels.length * 24; omega)] at a
  have e1 : ((i + 1) * 24 + t) / 24 = i + 1 := by omega
  have e2 : ((i + 1) * 24 + t) % 24 = t := by omega
  simp only [e1, e2, Nat.add_sub_cancel, show 1 ≤ i + 1 by omega, hi, and_self, ↓reduceIte] at a
  exact a

/-- **A non-final level's record in memory** (`RecStored`), at a valuation holding the head's
pointers. -/
theorem recStored_of (hS : HonStatic h.c) (hm : OsMemA rd h.c b h.own) {σ : Val}
    (h9 : σ (.n osOodz) = osPtrA h.c b 7) (h10 : σ (.n osOodSc) = osPtrA h.c b 8)
    (h6 : σ (.n osBetas) = osPtrA h.c b 4) (h7 : σ (.n osMus) = osPtrA h.c b 5)
    (h8 : σ (.n osHs) = osPtrA h.c b 6) (h11 : σ (.n osQpos) = osPtrA h.c b 9)
    {i : ℕ} (hi : i < h.c.yrLevel)
    (hF : ((h.L i).osRec h.logN).F = ((h.c.levels.getD i default)).foldsOff + ((h.c.levels.getD i default)).folds)
    (hmu : ((h.L i).osRec h.logN).mu = ((h.c.levels.getD i default)).logCols)
    (hql : ((h.L i).osRec h.logN).qs.length = ((h.c.levels.getD i default)).queries)
    (hhl : ((h.L i).osRec h.logN).high.length = ((h.c.levels.getD i default)).folds)
    (hz0 : ((h.L i).osRec h.logN).z0.length = ((h.c.levels.getD i default)).logCols)
    (hlam0 : (h.L i).lam h.logN ≠ 0)
    (hQ : ((h.c.levels.getD i default)).queries ≤ ((h.c.levels.getD i default)).squeezes * sqPer ((h.c.levels.getD i default)))
    (hqs : ∀ k < ((h.c.levels.getD i default)).queries, ((h.L i).osRec h.logN).qs.getD k 0 =
      qwPosOf ((h.c.levels.getD i default)).depth ((h.L i).word h.logN (k / sqPer ((h.c.levels.getD i default)))) (k % sqPer ((h.c.levels.getD i default)))) :
    RecStored rd σ i ((h.c.levels.getD i default)) ((h.L i).osRec h.logN) := by
  have hyr := hS.yr
  obtain ⟨g1, g3, g4⟩ := h.mid_glue hS hm hi
  have z0 := h.ood_rows hS hm hi hz0
  have el := (h.L i).osRec_lam h.logN
  refine ⟨hF, hmu, hql, hhl, ?_, hz0, ?_, ?_, ?_, fun c hc ↦ ?_, fun k hk ↦ ?_⟩
  · rw [h10, el]; exact g1
  · rw [h9]; exact z0
  · have e3 : (h.L i).lam h.logN ^ 2 * (h.L i).lam h.logN ^ ((h.c.levels.getD i default)).queries =
        (h.L i).lam h.logN * (h.L i).lam h.logN * (h.L i).lam h.logN ^ ((h.c.levels.getD i default)).queries := by
      ring
    rw [h6, el, e3]; exact g3
  · refine ⟨((h.L i).lam h.logN)⁻¹, ?_, ?_⟩
    · rw [h7]; exact g4
    · rw [el]
      have e := mul_inv_cancel₀ hlam0
      exact e
  · rw [h8, (h.L i).osRec_high h.logN]
    exact (h.mid_hs hS hm hi hc).2
  · rw [h11, hqs k hk]
    exact h.pos_load hS hm (by omega) (by omega)

/-! ## The finish's buffers -/

/-- Every fold challenge in `fold_challenges`, as `FinMem.fch` reads them. -/
theorem fch_all (hS : HonStatic h.c) (hm : OsMemA rd h.c b h.own) (hG : h.G.length = h.c.nFolds) :
    ∀ j (hj : j < h.G.length), LoadHolds rd (osPtrA h.c b 2) j h.G[j] := fun j hj ↦ by
  have := h.fch_load hS hm (i := j) (by omega)
  rwa [List.getD_eq_getElem _ _ hj] at this

theorem fin_reads (hS : HonStatic h.c) (hm : OsMemA rd h.c b h.own) {k : ℕ} (hk : k < 7)
    (hl : (h.ownW (12 + h.c.yrLevel + k)).length ≤
      [yrLogCap, pointCap, pointCap, h.c.levels.length * ligColsCap, h.c.levels.length, h.c.levels.length,
        2 * h.c.levels.length].getD k 0) :
    ReadsAt rd (osPtrA h.c b (12 + h.c.yrLevel + k)) (h.ownW (12 + h.c.yrLevel + k)) :=
  h.reads hm (hS.finLt hk) (by unfold osIxQbpA; omega) (by rw [hS.fin hk]; exact hl)

theorem tail_reads (hS : HonStatic h.c) (hm : OsMemA rd h.c b h.own) (hl : h.T.length ≤ yrLogCap) :
    ReadsAt rd (osPtrA h.c b (12 + h.c.yrLevel)) h.T := by
  have := h.fin_reads hS hm (k := 0) (by omega) (by rw [ownW_fin _ (by omega)]; exact hl)
  rwa [ownW_fin _ (by omega)] at this

theorem pt_reads (hS : HonStatic h.c) (hm : OsMemA rd h.c b h.own)
    (hl : (finPtC h.c h.G h.T).length ≤ pointCap) :
    ReadsAt rd (osPtrA h.c b (12 + h.c.yrLevel + 1)) (finPtC h.c h.G h.T) := by
  have := h.fin_reads hS hm (k := 1) (by omega) (by rw [ownW_fin _ (by omega)]; exact hl)
  rwa [ownW_fin _ (by omega)] at this

theorem pt1_reads (hS : HonStatic h.c) (hm : OsMemA rd h.c b h.own)
    (hl : (finPt1C h.c h.G h.T).length ≤ pointCap) :
    ReadsAt rd (osPtrA h.c b (12 + h.c.yrLevel + 2)) (finPt1C h.c h.G h.T) := by
  have := h.fin_reads hS hm (k := 2) (by omega) (by rw [ownW_fin _ (by omega)]; exact hl)
  rwa [ownW_fin _ (by omega)] at this

theorem bd_reads (hS : HonStatic h.c) (hm : OsMemA rd h.c b h.own) :
    ReadsAt rd (osPtrA h.c b (12 + h.c.yrLevel + 3)) (finBdC h.c h.G h.T h.recs) := by
  have := h.fin_reads hS hm (k := 3) (by omega) (by rw [ownW_fin _ (by omega)]; simp [finBdC])
  rwa [ownW_fin _ (by omega)] at this

theorem ls_reads (hS : HonStatic h.c) (hm : OsMemA rd h.c b h.own) :
    ReadsAt rd (osPtrA h.c b (12 + h.c.yrLevel + 4)) (finLsC h.c h.G h.T h.recs) := by
  have := h.fin_reads hS hm (k := 4) (by omega) (by rw [ownW_fin _ (by omega)]; simp [finLsC])
  rwa [ownW_fin _ (by omega)] at this

theorem la_reads (hS : HonStatic h.c) (hm : OsMemA rd h.c b h.own) :
    ReadsAt rd (osPtrA h.c b (12 + h.c.yrLevel + 5)) (finLaC h.c h.G h.T h.recs) := by
  have := h.fin_reads hS hm (k := 5) (by omega) (by rw [ownW_fin _ (by omega)]; simp [finLaC])
  rwa [ownW_fin _ (by omega)] at this

theorem ich_reads (hS : HonStatic h.c) (hm : OsMemA rd h.c b h.own) :
    ReadsAt rd (osPtrA h.c b (12 + h.c.yrLevel + 6)) (finIchC h.c h.G h.T h.recs h.li h.tr.2.1) := by
  have := h.fin_reads hS hm (k := 6) (by omega) (by rw [ownW_fin _ (by omega)]; simp [finIchC])
  rwa [ownW_fin _ (by omega)] at this

/-! ## OsHonestA's query reads -/

/-- **OsHonestA's `qMem` at level `l`**: the rounds' coefficients and, at the final level, the
normalized lane. -/
theorem qMem_at (hS : HonStatic h.c) (hm : OsMemA rd h.c b h.own) (hL : h.Ls.length = h.c.levels.length)
    (hrl : ∀ i < h.c.levels.length, (h.L i).rounds.length = (h.c.levels.getD i default).folds) {l : ℕ}
    (hl : l < h.c.levels.length) :
    RoundsAt rd (osPtrA h.c b 3 * gen ^ (2 * (h.c.levels.getD l default).foldsOff)) (h.L l).rounds ∧
    (l = h.c.yrLevel → WordsAt rd (osHsPtrA h.c b l) h.hsFC) := by
  refine ⟨h.roundsAt_of hS hm hL hrl hl, fun hf ↦ ?_⟩
  subst hf
  exact h.hsv_words hS hm

end OsHD

end
end LeanVM.Guest.B1.Whir
