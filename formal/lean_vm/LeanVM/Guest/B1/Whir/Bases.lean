/-
  LeanVM.Guest.B1.Whir.Bases

  The basis rows of the terminal's residuals: each level's coefficients `d_t`, its scale and the
  product of its coordinates.
-/

module

public import LeanVM.Guest.B1.Whir.Flat

/-!
# The basis rows (G:1778-1801)

For each non-final level and each coordinate `t` of its message (the fold challenges after its
folds, then the tail challenges, `X t`), the guest reads `X t`, stores
`d_t = (1 + X t)/(X t·inv_t)` in `basis_d` and multiplies the level's scale, from its batching
scalar `β`, by `X t·inv_t`, and the product of the coordinates by `X t`; the scale goes to
`level_scale`, the product to `level_after` (`osBases_sound`). A coordinate whose coefficient
`X t·inv_t` is zero leaves no valuation (`1 + X t = d_t·X t·inv_t`, `inv_t ≠ 0`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- The running product's value before a coordinate: `1` before the first. -/
def optVal (σ : Val) : Option ℕ → E
  | none => 1
  | some x => σ (.n x)

theorem coef_ne {cv inv d : E} (hinv : inv ≠ 0) (h : 1 + cv = d * (cv * inv)) : cv * inv ≠ 0 := by
  intro h0
  rw [h0, mul_zero] at h
  have hc : cv = 1 := by
    have h' : cv + 1 = 0 := by rw [add_comm]; exact h
    rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h'; exact h'
  rw [hc, one_mul] at h0
  exact hinv h0

theorem aft_val {after : Option ℕ} {k j : ℕ}
    (ha : AllOk C rd σ (match after with
      | none => (([] : List Stmt), k, j + 4)
      | some x => ([osMul (j + 4) x k], j + 4, j + 5)).1) :
    σ (.n (match after with
      | none => (([] : List Stmt), k, j + 4)
      | some x => ([osMul (j + 4) x k], j + 4, j + 5)).2.1) = optVal σ after * σ (.n k) := by
  rcases after with _ | x
  · simp [optVal]
  · simp only [allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_mul] at ha
    simpa [optVal] using ha

/-- **One coordinate**: its coefficient is not zero, its `d` stored, the scale multiplied by it,
the product by the coordinate. -/
theorem osBasisBlk_val {bd slot : ℕ} {src : ℕ × ℕ} {inv sc : ℕ} {after : Option ℕ} {k : ℕ} {cv : E}
    (hinv : word inv 0 ≠ 0) (hc : LoadHolds rd (σ (.n src.1)) src.2 cv)
    (h : AllOk C rd σ (osBasisBlk bd slot src inv sc after k).1) :
    cv * word inv 0 ≠ 0 ∧ LoadHolds rd (σ (.n bd)) slot ((1 + cv) / (cv * word inv 0)) ∧
      σ (.n (osBasisBlk bd slot src inv sc after k).2.1) = σ (.n sc) * (cv * word inv 0) ∧
      σ (.n (osBasisBlk bd slot src inv sc after k).2.2.1) = optVal σ after * cv := by
  have key : ∀ (j a : ℕ), σ (.n a) = optVal σ after * σ (.n k) →
      AllOk C rd σ (osLd k src.1 src.2 :: (if inv = 1 then (([] : List Stmt), k, k + 1)
        else ([osCst (k + 1) (word inv 0), osMul (k + 2) k (k + 1)], k + 2, k + 3)).1 ++
        [osCst j (word 1 0), osAdd (j + 1) j k,
          osMul (j + 1) (j + 2) (if inv = 1 then (([] : List Stmt), k, k + 1)
            else ([osCst (k + 1) (word inv 0), osMul (k + 2) k (k + 1)], k + 2, k + 3)).2.1,
          osLd (j + 2) bd slot, osMul (j + 3) sc (if inv = 1 then (([] : List Stmt), k, k + 1)
            else ([osCst (k + 1) (word inv 0), osMul (k + 2) k (k + 1)], k + 2, k + 3)).2.1]) →
      cv * word inv 0 ≠ 0 ∧ LoadHolds rd (σ (.n bd)) slot ((1 + cv) / (cv * word inv 0)) ∧
        σ (.n (j + 3)) = σ (.n sc) * (cv * word inv 0) ∧ σ (.n a) = optVal σ after * cv := by
    intro j a hav hm
    by_cases h1 : inv = 1
    · subst h1
      simp only [↓reduceIte, allOk_cons, allOk_append, allOk_nil, and_true,
        stmtOk_atom, holds_load, holds_const, holds_add, holds_mul] at hm ⊢
      obtain ⟨l0, c1, a2, m2, l3, m4⟩ := hm
      have e0 := loadHolds_unique l0 hc
      rw [word_one, mul_one]
      rw [a2, c1, word_one, e0] at m2
      have hne : cv ≠ 0 := by
        have := coef_ne (inv := 1) one_ne_zero (by rw [mul_one]; exact m2)
        simpa using this
      refine ⟨hne, ?_, by rw [m4, e0], by rw [hav, e0]⟩
      rwa [← eq_div_of_mul_eq hne m2.symm]
    · simp only [h1, ↓reduceIte, List.cons_append, List.nil_append, allOk_cons,
        allOk_nil, and_true, stmtOk_atom, holds_load, holds_const, holds_add, holds_mul] at hm ⊢
      obtain ⟨l0, c1, m2, c3, a4, m4, l5, m6⟩ := hm
      have e0 := loadHolds_unique l0 hc
      rw [m2, c1, e0] at m4
      rw [a4, c3, word_one, e0] at m4
      have hne : cv * word inv 0 ≠ 0 := coef_ne hinv m4
      refine ⟨hne, ?_, by rw [m6, m2, c1, e0], by rw [hav, e0]⟩
      rwa [← eq_div_of_mul_eq hne m4.symm]
  unfold osBasisBlk at h ⊢
  simp only [] at h ⊢
  rw [allOk_append] at h
  exact key _ _ (aft_val h.2) h.1

/-- The default coordinate. -/
abbrev coordD : ℕ × (ℕ × ℕ) × ℕ := (0, (0, 0), 0)

/-- **A basis row**: every coordinate's coefficient is not zero and its `d` stored; the scale
multiplied by every coefficient, the product by every coordinate. -/
theorem osBasisRow_val {bd : ℕ} : ∀ (cs : List (ℕ × (ℕ × ℕ) × ℕ)) (sc : ℕ) (after : Option ℕ)
    (k : ℕ) (cv : ℕ → E),
    (∀ t < cs.length, word (cs.getD t coordD).2.2 0 ≠ 0 ∧
      LoadHolds rd (σ (.n (cs.getD t coordD).2.1.1)) (cs.getD t coordD).2.1.2 (cv t)) →
    AllOk C rd σ (osBasisRow bd cs sc after k).1 →
    (∀ t < cs.length, cv t * word (cs.getD t coordD).2.2 0 ≠ 0 ∧
      LoadHolds rd (σ (.n bd)) (cs.getD t coordD).1
        ((1 + cv t) / (cv t * word (cs.getD t coordD).2.2 0))) ∧
    σ (.n (osBasisRow bd cs sc after k).2.1) =
      σ (.n sc) * ∏ t ∈ Finset.range cs.length, (cv t * word (cs.getD t coordD).2.2 0) ∧
    (after.isSome ∨ cs ≠ [] → σ (.n (osBasisRow bd cs sc after k).2.2.1) =
      optVal σ after * ∏ t ∈ Finset.range cs.length, cv t)
  | [], sc, after, k, cv, _, _ => by
    refine ⟨fun t ht ↦ absurd ht (by simp), by simp [osBasisRow], fun h ↦ ?_⟩
    rcases after with _ | x
    · simp at h
    · simp [osBasisRow, optVal]
  | (slot, src, inv) :: rest, sc, after, k, cv, hin, hok => by
    simp only [osBasisRow] at hok ⊢
    rw [allOk_append] at hok
    obtain ⟨h0, hrest⟩ := hok
    obtain ⟨hi0, hc0⟩ := hin 0 (by simp)
    simp only [List.getD_cons_zero] at hi0 hc0
    obtain ⟨n0, d0, s0, a0⟩ := osBasisBlk_val (bd := bd) (slot := slot) (sc := sc) (after := after)
      (k := k) hi0 hc0 h0
    obtain ⟨hr, hs, ha⟩ := osBasisRow_val rest (osBasisBlk bd slot src inv sc after k).2.1
      (some (osBasisBlk bd slot src inv sc after k).2.2.1)
      (osBasisBlk bd slot src inv sc after k).2.2.2 (fun t ↦ cv (t + 1))
      (fun t ht ↦ hin (t + 1) (by simp; omega)) hrest
    refine ⟨fun t ht ↦ ?_, ?_, fun _ ↦ ?_⟩
    · rcases t with _ | t
      · exact ⟨n0, d0⟩
      · exact hr t (by simpa using ht)
    · rw [hs, s0, List.length_cons, Finset.prod_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      ring
    · rw [ha (Or.inl rfl), List.length_cons, Finset.prod_range_succ']
      simp only [optVal, a0]
      ring

/-- A level's coordinate `t`: its source (a fold challenge, then a tail challenge). -/
def coordSrc (tch : ℕ) (lv : OsLv) (t : ℕ) : ℕ × ℕ :=
  if t < lv.prefixLen then (osFch, lv.resFoldOff + t) else (tch, t - lv.prefixLen)

/-- A level's vanishing inverse at coordinate `t`. -/
abbrev invW (lv : OsLv) (t : ℕ) : E := word (vanishInv (lv.vanish + t)) 0

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

/-- What it stores: the coefficients' `d` in `basis_d`, the scale in `level_scale`, the product
of the coordinates in `level_after`. -/
def BasisOut (rd : Reader) (σ : Val) (c : OsCfg) (bd ls la L : ℕ) (lv : OsLv) (β : E)
    (X : ℕ → E) : Prop :=
  (∀ t < lv.prefixLen + c.yrLog, X t * invW lv t ≠ 0 ∧
    LoadHolds rd (σ (.n bd)) (L * ligColsCap + t) ((1 + X t) / (X t * invW lv t))) ∧
  LoadHolds rd (σ (.n ls)) L (β * ∏ t ∈ Finset.range (lv.prefixLen + c.yrLog), (X t * invW lv t)) ∧
  LoadHolds rd (σ (.n la)) L (∏ t ∈ Finset.range (lv.prefixLen + c.yrLog), X t)

/-- **Every non-final level's basis row** (G:1778-1801). -/
theorem osBases_sound {c : OsCfg} {tch bd ls la : ℕ} (β : ℕ → E) (X : ℕ → ℕ → E)
    (hpos : ∀ lv : OsLv, 1 ≤ lv.prefixLen + c.yrLog) :
    ∀ (levels : List OsLv) (lvl k : ℕ),
      (∀ i (hi : i < levels.length), BasisIn rd σ c tch (lvl + i) levels[i] (β (lvl + i))
        (X (lvl + i))) →
      AllOk C rd σ (osBases c tch bd ls la lvl levels k).1 →
      ∀ i (hi : i < levels.length), BasisOut rd σ c bd ls la (lvl + i) levels[i] (β (lvl + i))
        (X (lvl + i))
  | [], _, _, _, _, i, hi => absurd hi (by simp)
  | lv :: rest, lvl, k, hin, hok, i, hi => by
    simp only [osBases] at hok
    simp only [allOk_append, allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_load, osLd] at hok
    obtain ⟨⟨⟨lb, hrow⟩, ls0, la0⟩, hrest⟩ := hok
    rcases i with _ | i
    · obtain ⟨hb, hx⟩ := hin 0 (by simp)
      simp only [Nat.add_zero, List.getElem_cons_zero] at hb hx ⊢
      have eb := loadHolds_unique lb hb
      have hlen : (osBasisCoords c tch lvl lv).length = lv.prefixLen + c.yrLog := by
        simp [osBasisCoords]
      obtain ⟨hr, hs, ha⟩ := osBasisRow_val (bd := bd) (osBasisCoords c tch lvl lv) k none (k + 1)
        (X lvl) (fun t ht ↦ by
          rw [hlen] at ht
          rw [osBasisCoords_getD ht]
          exact hx t ht) hrow
      have hne : osBasisCoords c tch lvl lv ≠ [] := by
        intro h0; have := hpos lv; rw [← hlen, h0] at this; simp at this
      refine ⟨fun t ht ↦ ?_, ?_, ?_⟩
      · have := hr t (by rw [hlen]; exact ht)
        rw [osBasisCoords_getD ht] at this
        exact this
      · rw [hs, eb, hlen] at ls0
        rwa [Finset.prod_congr rfl fun t ht ↦ by
          rw [osBasisCoords_getD (Finset.mem_range.mp ht)]] at ls0
      · rw [ha (Or.inr hne), hlen, optVal, one_mul] at la0
        exact la0
    · have := osBases_sound β X hpos rest (lvl + 1) _ (fun j hj ↦ by
        have := hin (j + 1) (by simp; omega)
        rwa [show lvl + (j + 1) = lvl + 1 + j by ring] at this) hrest i (by simpa using hi)
      rwa [show lvl + 1 + i = lvl + (i + 1) by ring] at this

end
end LeanVM.Guest.B1.Whir
