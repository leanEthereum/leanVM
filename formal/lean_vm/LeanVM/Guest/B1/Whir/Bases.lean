/-
  LeanVM.Guest.B1.Whir.Bases

  The basis rows of the terminal's residuals: each level's coefficients `d_t`, its scale.
-/

module

public import LeanVM.Guest.B1.Whir.Flat

/-!
# The basis rows (G:1699-1718)

For each level and each coordinate `t` of its message (the fold challenges after its folds, then
the tail challenges, `X t`), the guest reads `X t`, its vanishing inverse `inv_t`, stores
`d_t = (1 + X t)/(X t·inv_t)` in `basis_d` and multiplies the level's scale, from its batching
scalar `β`, by `X t·inv_t`; the scale goes to `level_scale` (`osBases_sound`). A coordinate whose
coefficient `X t·inv_t` is zero leaves no valuation (`1 + X t = d_t·X t·inv_t`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- **One coordinate**: its coefficient is not zero, its `d` stored, the scale multiplied by it. -/
theorem osBasisBlk_val {bd slot : ℕ} {src : ℕ × ℕ} {inv sc k : ℕ} {cv : E}
    (hinv : word inv 0 0 ≠ 0) (hc : LoadHolds rd (σ (.n src.1)) src.2 cv)
    (h : AllOk C rd σ (osBasisBlk bd slot src inv sc k).1) :
    cv * word inv 0 0 ≠ 0 ∧ LoadHolds rd (σ (.n bd)) slot ((1 + cv) / (cv * word inv 0 0)) ∧
      σ (.n (osBasisBlk bd slot src inv sc k).2.1) = σ (.n sc) * (cv * word inv 0 0) := by
  by_cases h1 : inv = 1
  · subst h1
    simp only [osBasisBlk, ↓reduceIte, allOk_cons, allOk_nil, and_true, StmtOk,
      Atom.Holds] at h ⊢
    obtain ⟨l0, c1, a2, m2, l3, m4⟩ := h
    have e0 := loadHolds_unique l0 hc
    rw [word_one, mul_one]
    rw [a2, c1, word_one, e0] at m2
    have hne : cv ≠ 0 := by
      rintro rfl
      simp at m2
    refine ⟨hne, ?_, by rw [m4, e0]⟩
    rwa [← eq_div_of_mul_eq hne m2.symm]
  · have hc1 : (inv = 1) = False := eq_false h1
    simp only [osBasisBlk, hc1, ↓reduceIte, allOk_cons, allOk_nil, and_true, StmtOk,
      Atom.Holds] at h ⊢
    obtain ⟨l0, c1, m2, c3, a4, m4, l5, m6⟩ := h
    have e0 := loadHolds_unique l0 hc
    rw [m2, c1, e0] at m4
    rw [a4, c3, word_one, e0] at m4
    have hne : cv * word inv 0 0 ≠ 0 := by
      intro h0
      have hcv : cv = 0 := (mul_eq_zero.mp h0).resolve_right hinv
      rw [h0, hcv] at m4
      simp at m4
    refine ⟨hne, ?_, by rw [m6, m2, c1, e0]⟩
    rwa [← eq_div_of_mul_eq hne m4.symm]

/-- The default coordinate. -/
abbrev coordD : ℕ × (ℕ × ℕ) × ℕ := (0, (0, 0), 0)

/-- **A basis row**: every coordinate's coefficient is not zero and its `d` stored; the scale
multiplied by every coefficient. -/
theorem osBasisRow_val {bd : ℕ} : ∀ (cs : List (ℕ × (ℕ × ℕ) × ℕ)) (sc k : ℕ) (cv : ℕ → E),
    (∀ t < cs.length, word (cs.getD t coordD).2.2 0 0 ≠ 0 ∧
      LoadHolds rd (σ (.n (cs.getD t coordD).2.1.1)) (cs.getD t coordD).2.1.2 (cv t)) →
    AllOk C rd σ (osBasisRow bd cs sc k).1 →
    (∀ t < cs.length, cv t * word (cs.getD t coordD).2.2 0 0 ≠ 0 ∧
      LoadHolds rd (σ (.n bd)) (cs.getD t coordD).1
        ((1 + cv t) / (cv t * word (cs.getD t coordD).2.2 0 0))) ∧
    σ (.n (osBasisRow bd cs sc k).2.1) =
      σ (.n sc) * ∏ t ∈ Finset.range cs.length, (cv t * word (cs.getD t coordD).2.2 0 0)
  | [], sc, k, cv, _, _ => by simp [osBasisRow]
  | (slot, src, inv) :: rest, sc, k, cv, hin, hok => by
    simp only [osBasisRow] at hok ⊢
    rw [allOk_append] at hok
    obtain ⟨h0, hrest⟩ := hok
    obtain ⟨hi0, hc0⟩ := hin 0 (by simp)
    simp only [List.getD_cons_zero] at hi0 hc0
    obtain ⟨n0, d0, s0⟩ := osBasisBlk_val (bd := bd) (slot := slot) (sc := sc) (k := k) hi0 hc0 h0
    obtain ⟨hr, hs⟩ := osBasisRow_val rest (osBasisBlk bd slot src inv sc k).2.1
      (osBasisBlk bd slot src inv sc k).2.2 (fun t ↦ cv (t + 1))
      (fun t ht ↦ hin (t + 1) (by simp; omega)) hrest
    refine ⟨fun t ht ↦ ?_, ?_⟩
    · rcases t with _ | t
      · exact ⟨n0, d0⟩
      · exact hr t (by simpa using ht)
    · rw [hs, s0, List.length_cons, Finset.prod_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      ring

/-- A level's coordinate `t`: its source (a fold challenge, then a tail challenge). -/
def coordSrc (tch : ℕ) (lv : OsLv) (t : ℕ) : ℕ × ℕ :=
  if t < lv.prefixLen then (osFch, lv.resFoldOff + t) else (tch, t - lv.prefixLen)

/-- A level's vanishing inverse at coordinate `t`. -/
abbrev invW (lv : OsLv) (t : ℕ) : E := word (vanishInv (lv.vanish + t)) 0 0

theorem osBasisCoords_getD {c : OsCfg} {tch lvl t : ℕ} {lv : OsLv}
    (ht : t < lv.prefixLen + c.yrLog) :
    (osBasisCoords c tch lvl lv).getD t coordD =
      (lvl * ligColsCap + t, coordSrc tch lv t, vanishInv (lv.vanish + t)) := by
  simp [osBasisCoords, coordSrc, List.getD_eq_getElem?_getD, ht]

/-- What a level's basis row reads: its scalar `β` and its coordinates `X`. -/
def BasisIn (rd : Reader) (σ : Val) (c : OsCfg) (tch L : ℕ) (lv : OsLv) (β : E) (X : ℕ → E) :
    Prop :=
  LoadHolds rd (σ (.n osBetas)) L β ∧ ∀ t < lv.prefixLen + c.yrLog, invW lv t ≠ 0 ∧
    LoadHolds rd (σ (.n (coordSrc tch lv t).1)) (coordSrc tch lv t).2 (X t)

/-- What it stores: the coefficients' `d` in `basis_d`, the scale in `level_scale`. -/
def BasisOut (rd : Reader) (σ : Val) (c : OsCfg) (bd ls L : ℕ) (lv : OsLv) (β : E) (X : ℕ → E) :
    Prop :=
  (∀ t < lv.prefixLen + c.yrLog, X t * invW lv t ≠ 0 ∧
    LoadHolds rd (σ (.n bd)) (L * ligColsCap + t) ((1 + X t) / (X t * invW lv t))) ∧
  LoadHolds rd (σ (.n ls)) L (β * ∏ t ∈ Finset.range (lv.prefixLen + c.yrLog), (X t * invW lv t))

/-- **Every level's basis row** (G:1699-1718). -/
theorem osBases_sound {c : OsCfg} {tch bd ls : ℕ} (β : ℕ → E) (X : ℕ → ℕ → E) :
    ∀ (levels : List OsLv) (lvl k : ℕ),
      (∀ i (hi : i < levels.length), BasisIn rd σ c tch (lvl + i) levels[i] (β (lvl + i))
        (X (lvl + i))) →
      AllOk C rd σ (osBases c tch bd ls lvl levels k).1 →
      ∀ i (hi : i < levels.length), BasisOut rd σ c bd ls (lvl + i) levels[i] (β (lvl + i))
        (X (lvl + i))
  | [], _, _, _, _, i, hi => absurd hi (by simp)
  | lv :: rest, lvl, k, hin, hok, i, hi => by
    simp only [osBases] at hok
    simp only [allOk_append, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds] at hok
    obtain ⟨⟨⟨lb, hrow⟩, ls0⟩, hrest⟩ := hok
    rcases i with _ | i
    · obtain ⟨hb, hx⟩ := hin 0 (by simp)
      simp only [Nat.add_zero, List.getElem_cons_zero] at hb hx ⊢
      have eb := loadHolds_unique lb hb
      have hlen : (osBasisCoords c tch lvl lv).length = lv.prefixLen + c.yrLog := by
        simp [osBasisCoords]
      obtain ⟨hr, hs⟩ := osBasisRow_val (bd := bd) (osBasisCoords c tch lvl lv) k (k + 1) (X lvl)
        (fun t ht ↦ by
          rw [hlen] at ht
          rw [osBasisCoords_getD ht]
          exact hx t ht) hrow
      refine ⟨fun t ht ↦ ?_, ?_⟩
      · have := hr t (by rw [hlen]; exact ht)
        rw [osBasisCoords_getD ht] at this
        exact this
      · rw [hs, eb, hlen] at ls0
        rwa [Finset.prod_congr rfl fun t ht ↦ by
          rw [osBasisCoords_getD (Finset.mem_range.mp ht)]] at ls0
    · have := osBases_sound β X rest (lvl + 1) _ (fun j hj ↦ by
        have := hin (j + 1) (by simp; omega)
        rwa [show lvl + (j + 1) = lvl + 1 + j by ring] at this) hrest i (by simpa using hi)
      rwa [show lvl + 1 + i = lvl + (i + 1) by ring] at this

end
end LeanVM.Guest.B1.Whir
