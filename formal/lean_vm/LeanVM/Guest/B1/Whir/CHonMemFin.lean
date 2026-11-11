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
theorem ood_rows (hS : HonStatic h.c) (hm : OsMemF rd h.c b h.own) {i : ℕ} (hi : i < h.c.yrLevel)
    (hz0 : ((h.L i).osRec h.logN).z0.length = (osLvAt h.c i).logCols) :
    ReadsAt rd (osPtrF h.c b 9 * gen ^ ((i + 1) * ligColsCap)) ((h.L i).osRec h.logN).z0 := by
  have hyr := hS.yr
  have hc := (hS.mid hi).1
  have h9 : (osSizesF h.c).getD 9 0 = h.c.levels.length * 22 := by
    rw [hS.head (j := 9) (by omega)]; rfl
  have hc' : (osLvAt h.c i).logCols ≤ 22 := hc
  unfold ligColsCap
  have hn : (i + 1) * 22 + 22 ≤ h.c.levels.length * 22 := by
    have : i + 1 + 1 ≤ h.c.levels.length := by omega
    have := Nat.mul_le_mul_right 22 this
    rw [Nat.add_mul] at this; omega
  intro t ht
  rw [← List.getD_eq_getElem _ 0 ht, loadHolds_mul_gen_pow]
  have a := h.load hm (hS.headLt (j := 9) (by omega)) (by unfold osIxQbp; omega)
    (e := (i + 1) * 22 + t) (by rw [h9]; omega)
  rw [ownW_oodz, oodzC, getD_mapRange _ (by show _ < h.c.levels.length * 22; omega)] at a
  have e1 : ((i + 1) * 22 + t) / 22 = i + 1 := by omega
  have e2 : ((i + 1) * 22 + t) % 22 = t := by omega
  simp only [e1, e2, Nat.add_sub_cancel, show 1 ≤ i + 1 by omega, hi, and_self, ↓reduceIte] at a
  exact a

/-- **A non-final level's record in memory** (`RecStored`), at a valuation holding the head's
pointers. -/
theorem recStored_of (hS : HonStatic h.c) (hm : OsMemF rd h.c b h.own) {σ : Val}
    (h9 : σ (.n osOodz) = osPtrF h.c b 9) (h10 : σ (.n osOodSc) = osPtrF h.c b 10)
    (h6 : σ (.n osBetas) = osPtrF h.c b 6) (h7 : σ (.n osMus) = osPtrF h.c b 7)
    (h8 : σ (.n osHs) = osPtrF h.c b 8) (h11 : σ (.n osQpos) = osPtrF h.c b 11)
    {i : ℕ} (hi : i < h.c.yrLevel)
    (hF : ((h.L i).osRec h.logN).F = (osLvAt h.c i).foldsOff + (osLvAt h.c i).folds)
    (hmu : ((h.L i).osRec h.logN).mu = (osLvAt h.c i).logCols)
    (hql : ((h.L i).osRec h.logN).qs.length = (osLvAt h.c i).queries)
    (hhl : ((h.L i).osRec h.logN).high.length = (osLvAt h.c i).folds)
    (hz0 : ((h.L i).osRec h.logN).z0.length = (osLvAt h.c i).logCols)
    (hlam0 : (h.L i).lam h.logN ≠ 0)
    (hQ : (osLvAt h.c i).queries ≤ (osLvAt h.c i).squeezes * sqPer (osLvAt h.c i))
    (hqs : ∀ k < (osLvAt h.c i).queries, ((h.L i).osRec h.logN).qs.getD k 0 =
      qwPosOf (osLvAt h.c i).depth ((h.L i).word h.logN (k / sqPer (osLvAt h.c i))) (k % sqPer (osLvAt h.c i))) :
    RecStored rd σ i (osLvAt h.c i) ((h.L i).osRec h.logN) := by
  have hyr := hS.yr
  obtain ⟨g1, g3, g4⟩ := h.mid_glue hS hm hi
  have z0 := h.ood_rows hS hm hi hz0
  have el := (h.L i).osRec_lam h.logN
  refine ⟨hF, hmu, hql, hhl, ?_, hz0, ?_, ?_, ?_, fun c hc ↦ ?_, fun k hk ↦ ?_⟩
  · rw [h10, el]; exact g1
  · rw [h9]; exact z0
  · have e3 : (h.L i).lam h.logN ^ 2 * (h.L i).lam h.logN ^ (osLvAt h.c i).queries =
        (h.L i).lam h.logN * (h.L i).lam h.logN * (h.L i).lam h.logN ^ (osLvAt h.c i).queries := by
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
theorem fch_all (hS : HonStatic h.c) (hm : OsMemF rd h.c b h.own) (hG : h.G.length = h.c.nFolds) :
    ∀ j (hj : j < h.G.length), LoadHolds rd (osPtrF h.c b 4) j h.G[j] := fun j hj ↦ by
  have := h.fch_load hS hm (i := j) (by omega)
  rwa [List.getD_eq_getElem _ _ hj] at this

theorem fin_reads (hS : HonStatic h.c) (hm : OsMemF rd h.c b h.own) {k : ℕ} (hk : k < 7)
    (hl : (h.ownW (13 + 2 * h.c.levels.length + k)).length ≤
      [yrLogCap, pointCap, pointCap, h.c.levels.length * ligColsCap, h.c.levels.length, h.c.levels.length,
        2 * h.c.levels.length].getD k 0) :
    ReadsAt rd (osPtrF h.c b (13 + 2 * h.c.levels.length + k)) (h.ownW (13 + 2 * h.c.levels.length + k)) :=
  h.reads hm (hS.finLt hk) (by unfold osIxQbp; omega) (by rw [hS.fin hk]; exact hl)

theorem tail_reads (hS : HonStatic h.c) (hm : OsMemF rd h.c b h.own) (hl : h.T.length ≤ yrLogCap) :
    ReadsAt rd (osPtrF h.c b (13 + 2 * h.c.levels.length)) h.T := by
  have := h.fin_reads hS hm (k := 0) (by omega) (by rw [ownW_fin _ (by omega)]; exact hl)
  rwa [ownW_fin _ (by omega)] at this

theorem pt_reads (hS : HonStatic h.c) (hm : OsMemF rd h.c b h.own)
    (hl : (finPtC h.c h.G h.T).length ≤ pointCap) :
    ReadsAt rd (osPtrF h.c b (13 + 2 * h.c.levels.length + 1)) (finPtC h.c h.G h.T) := by
  have := h.fin_reads hS hm (k := 1) (by omega) (by rw [ownW_fin _ (by omega)]; exact hl)
  rwa [ownW_fin _ (by omega)] at this

theorem pt1_reads (hS : HonStatic h.c) (hm : OsMemF rd h.c b h.own)
    (hl : (finPt1C h.c h.G h.T).length ≤ pointCap) :
    ReadsAt rd (osPtrF h.c b (13 + 2 * h.c.levels.length + 2)) (finPt1C h.c h.G h.T) := by
  have := h.fin_reads hS hm (k := 2) (by omega) (by rw [ownW_fin _ (by omega)]; exact hl)
  rwa [ownW_fin _ (by omega)] at this

theorem bd_reads (hS : HonStatic h.c) (hm : OsMemF rd h.c b h.own) :
    ReadsAt rd (osPtrF h.c b (13 + 2 * h.c.levels.length + 3)) (finBdC h.c h.G h.T h.recs) := by
  have := h.fin_reads hS hm (k := 3) (by omega) (by rw [ownW_fin _ (by omega)]; simp [finBdC])
  rwa [ownW_fin _ (by omega)] at this

theorem ls_reads (hS : HonStatic h.c) (hm : OsMemF rd h.c b h.own) :
    ReadsAt rd (osPtrF h.c b (13 + 2 * h.c.levels.length + 4)) (finLsC h.c h.G h.T h.recs) := by
  have := h.fin_reads hS hm (k := 4) (by omega) (by rw [ownW_fin _ (by omega)]; simp [finLsC])
  rwa [ownW_fin _ (by omega)] at this

theorem la_reads (hS : HonStatic h.c) (hm : OsMemF rd h.c b h.own) :
    ReadsAt rd (osPtrF h.c b (13 + 2 * h.c.levels.length + 5)) (finLaC h.c h.G h.T h.recs) := by
  have := h.fin_reads hS hm (k := 5) (by omega) (by rw [ownW_fin _ (by omega)]; simp [finLaC])
  rwa [ownW_fin _ (by omega)] at this

theorem ich_reads (hS : HonStatic h.c) (hm : OsMemF rd h.c b h.own) :
    ReadsAt rd (osPtrF h.c b (13 + 2 * h.c.levels.length + 6)) (finIchC h.c h.G h.T h.recs h.li h.tr.2.1) := by
  have := h.fin_reads hS hm (k := 6) (by omega) (by rw [ownW_fin _ (by omega)]; simp [finIchC])
  rwa [ownW_fin _ (by omega)] at this

theorem rc_reads (hS : HonStatic h.c) (hm : OsMemF rd h.c b h.own) {l : ℕ} (hl : l < h.c.yrLevel)
    (hlen : (finRcC h.c h.G h.T h.recs h.li l).length ≤ 2 * ((osLvAt h.c l).queries / resBatch + 1)) :
    ReadsAt rd (osPtrF h.c b (20 + 2 * h.c.levels.length + l)) (finRcC h.c h.G h.T h.recs h.li l) := by
  have := h.reads hm (hS.rcLt hl) (by unfold osIxQbp; omega) (j := 20 + 2 * h.c.levels.length + l)
    (by rw [hS.rc hl, ownW_rc]; exact hlen)
  rwa [ownW_rc] at this

/-! ## OsHonest's query reads -/

/-- **OsHonest's `qMem` at level `l`**, the cap cells and flags at the query nodes given. -/
theorem qMem_at (hS : HonStatic h.c) (hm : OsMemF rd h.c b h.own) (hL : h.Ls.length = h.c.levels.length)
    (hrl : ∀ i < h.c.levels.length, (h.L i).rounds.length = (osLvAt h.c i).folds) {l : ℕ}
    (hl : l < h.c.levels.length) (hfin : (oqS h.c l).final = 1 → l = h.c.yrLevel)
    (hcd : (oqS h.c l).cd = (osLvAt h.c l).capDepth) (hcd1 : 1 ≤ (oqS h.c l).cd)
    (qs : ℕ → ℕ) (rows : ℕ → List K) (sibs : ℕ → List Digest)
    (hq : ∀ k < oqQ h.c l, qs k < 2 ^ ((oqS h.c l).pd + (oqS h.c l).cd))
    (hv : ∀ k < oqQ h.c l,
      h.cv l (2 * (2 ^ (oqS h.c l).cd + qs k / 2 ^ (oqS h.c l).pd)) =
          (digestHalves (climbD (merkleLeafDigest (rows k)) (qs k) (sibs k))).1 ∧
        h.cv l (2 * (2 ^ (oqS h.c l).cd + qs k / 2 ^ (oqS h.c l).pd) + 1) =
          (digestHalves (climbD (merkleLeafDigest (rows k)) (qs k) (sibs k))).2 ∧
        h.fv l (2 ^ ((oqS h.c l).cd - 1) + qs k / 2 ^ ((oqS h.c l).pd + 1)) = 1) :
    RoundsAt rd (osPtrF h.c b 5 * gen ^ (2 * (osLvAt h.c l).foldsOff)) (h.L l).rounds ∧
    ((oqS h.c l).final = 1 → WordsAt rd (osHsPtr h.c b l) (if l = h.c.yrLevel then h.hsFC else [])) ∧
    ∀ k < oqQ h.c l,
      LoadHolds rd (osPtrF h.c b 0 * gen ^ (4 * (osLvAt h.c l).capOff))
        (2 * (2 ^ (oqS h.c l).cd + qs k / 2 ^ (oqS h.c l).pd))
        (digestHalves (climbD (merkleLeafDigest (rows k)) (qs k) (sibs k))).1 ∧
      LoadHolds rd (osPtrF h.c b 0 * gen ^ (4 * (osLvAt h.c l).capOff))
        (2 * (2 ^ (oqS h.c l).cd + qs k / 2 ^ (oqS h.c l).pd) + 1)
        (digestHalves (climbD (merkleLeafDigest (rows k)) (qs k) (sibs k))).2 ∧
      LoadHolds rd (osPtrF h.c b 1 * gen ^ (osLvAt h.c l).capOff)
        (2 ^ ((oqS h.c l).cd - 1) + qs k / 2 ^ ((oqS h.c l).pd + 1)) 1 := by
  refine ⟨h.roundsAt_of hS hm hL hrl hl, fun hf ↦ ?_, fun k hk ↦ ?_⟩
  · have := hfin hf
    have e := h.hsv_words hS hm
    simp only [this, ↓reduceIte]
    exact e
  · obtain ⟨v0, v1, vf⟩ := hv k hk
    exact h.cap_loads hS hm hl hcd hcd1 (hq k hk) v0 v1 vf

end OsHD

end
end LeanVM.Guest.B1.Whir
