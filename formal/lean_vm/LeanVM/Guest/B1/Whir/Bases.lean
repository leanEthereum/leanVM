/-
  LeanVM.Guest.B1.Whir.Bases

  The basis rows of the terminal's residuals: each level's coefficients `d_t`, its scale and the
  product of its coordinates.
-/

module

public import LeanVM.Guest.B1.Whir.SlowSpec

/-!
# The basis rows

For each non-final level and each coordinate `t` of its message (the fold challenges after its
folds, then the tail challenges, `X t`), the guest first takes the product of the coordinates
`after` (`osAfterRow_val`) and its zero flag `z = is_zero(after)`; then per coordinate it stores
`d_t = (1 + X t)/(X t·inv_t·(1 + z) + z)` in `basis_d` (`dZ`: the factored coefficient where
`after ≠ 0`, `1 + X t` where it is zero) and multiplies the level's scale, from its batching scalar
`β`, by `X t·inv_t`; the scale goes to `level_scale`, `after` to `level_after` (`osBases_sound`).
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

/-- **The product of the coordinates.** -/
theorem osAfterRow_val : ∀ (srcs : List (ℕ × ℕ)) (prev : Option ℕ) (k : ℕ) (X : ℕ → E),
    (∀ t < srcs.length, LoadHolds rd (σ (.n (srcs.getD t (0, 0)).1)) (srcs.getD t (0, 0)).2 (X t)) →
    AllOk C rd σ (osAfterRow srcs prev k).1 → (prev.isSome ∨ srcs ≠ []) →
    σ (.n ((osAfterRow srcs prev k).2.1.getD 0)) =
      optVal σ prev * ∏ t ∈ Finset.range srcs.length, X t
  | [], prev, k, X, _, _, h => by
    rcases prev with _ | x
    · simp at h
    · simp [osAfterRow, optVal]
  | src :: rest, none, k, X, hX, hok, _ => by
    simp only [osAfterRow, allOk_cons, stmtOk_atom, holds_load, osLd] at hok ⊢
    have e0 := loadHolds_unique hok.1 (by simpa using hX 0 (by simp))
    rw [osAfterRow_val rest (some k) (k + 1) (fun t ↦ X (t + 1))
      (fun t ht ↦ by simpa using hX (t + 1) (by simp; omega)) hok.2 (Or.inl rfl),
      List.length_cons, Finset.prod_range_succ', optVal, optVal, e0]
    ring
  | src :: rest, some p, k, X, hX, hok, _ => by
    simp only [osAfterRow, allOk_cons, stmtOk_atom, holds_load, holds_mul, osLd, osMul] at hok ⊢
    have e0 := loadHolds_unique hok.1 (by simpa using hX 0 (by simp))
    rw [osAfterRow_val rest (some (k + 1)) (k + 2) (fun t ↦ X (t + 1))
      (fun t ht ↦ by simpa using hX (t + 1) (by simp; omega)) hok.2.2 (Or.inl rfl),
      List.length_cons, Finset.prod_range_succ', optVal, optVal, hok.2.1, e0]
    ring

/-- The product's statements take the values `k ..` and the product is the one before or among
them. -/
theorem osAfterRow_next : ∀ (srcs : List (ℕ × ℕ)) (prev : Option ℕ) (k : ℕ),
    k ≤ (osAfterRow srcs prev k).2.2 ∧ ((osAfterRow srcs prev k).2.1 = prev ∨
      ∃ a, (osAfterRow srcs prev k).2.1 = some a ∧ k ≤ a ∧ a < (osAfterRow srcs prev k).2.2)
  | [], prev, k => ⟨le_rfl, Or.inl rfl⟩
  | _ :: rest, none, k => by
    obtain ⟨h1, h2⟩ := osAfterRow_next rest (some k) (k + 1)
    simp only [osAfterRow]
    refine ⟨by omega, Or.inr ?_⟩
    rcases h2 with h2 | ⟨a, ha, h3, h4⟩
    · exact ⟨k, h2, le_rfl, by omega⟩
    · exact ⟨a, ha, by omega, h4⟩
  | _ :: rest, some q, k => by
    obtain ⟨h1, h2⟩ := osAfterRow_next rest (some (k + 1)) (k + 2)
    simp only [osAfterRow]
    refine ⟨by omega, Or.inr ?_⟩
    rcases h2 with h2 | ⟨a, ha, h3, h4⟩
    · exact ⟨k + 1, h2, by omega, by omega⟩
    · exact ⟨a, ha, by omega, h4⟩

/-- The coefficient's `d` at a zero flag `z`. -/
def dZv (cv inv z : E) : E := (1 + cv) / (cv * inv * (1 + z) + z)

/-- **One coordinate**: its `d` stored, the scale multiplied by its coefficient. -/
theorem osBasisBlk_val {bd slot : ℕ} {src : ℕ × ℕ} {inv sc z nz : ℕ} {k : ℕ} {cv zv : E}
    (hz : (zv = 0 ∧ cv * word inv 0 ≠ 0) ∨ zv = 1) (hzv : σ (.n z) = zv) (hnz : σ (.n nz) = 1 + zv)
    (hc : LoadHolds rd (σ (.n src.1)) src.2 cv)
    (h : AllOk C rd σ (osBasisBlk bd slot src inv sc z nz k).1) :
    LoadHolds rd (σ (.n bd)) slot (dZv cv (word inv 0) zv) ∧
      σ (.n (osBasisBlk bd slot src inv sc z nz k).2.1) = σ (.n sc) * (cv * word inv 0) := by
  have hne := coef_div_ne (b := cv * word inv 0) hz
  unfold osBasisBlk at h ⊢
  by_cases h1 : inv = 1
  · subst h1
    simp only [↓reduceIte, List.cons_append, List.nil_append, allOk_cons, allOk_nil, and_true,
      stmtOk_atom, holds_load, holds_const, holds_add, holds_mul, osLd, osCst, osAdd, osMul] at h ⊢
    obtain ⟨l0, c1, a2, c3, m4, a5, m6, m7, l8, m9⟩ := h
    have e0 := loadHolds_unique l0 hc
    rw [word_one, mul_one] at hne
    rw [m4, e0, hnz] at a5
    rw [a5, hzv, c3, word_one] at m6
    rw [a2, c1, word_one, e0, eq_div_of_mul_eq hne m6.symm, mul_one_div] at m7
    refine ⟨?_, by rw [m9, e0, word_one, mul_one]⟩
    have e : dZv cv (word 1 0) zv = (1 + cv) / (cv * (1 + zv) + zv) := by rw [dZv, word_one, mul_one]
    rw [e, ← m7]
    exact l8
  · simp only [h1, ↓reduceIte, List.cons_append, List.nil_append, allOk_cons, allOk_nil, and_true,
      stmtOk_atom, holds_load, holds_const, holds_add, holds_mul, osLd, osCst, osAdd, osMul] at h ⊢
    obtain ⟨l0, c1, m2, c3, a4, c5, m6, a7, m8, m9, l10, m11⟩ := h
    have e0 := loadHolds_unique l0 hc
    rw [m2, c1, e0] at m6
    rw [m6, hnz] at a7
    rw [a7, hzv, c5, word_one] at m8
    rw [a4, c3, word_one, e0, eq_div_of_mul_eq hne m8.symm, mul_one_div] at m9
    refine ⟨?_, by rw [m11, m2, c1, e0]⟩
    rw [dZv, ← m9]
    exact l10

/-- The default coordinate. -/
abbrev coordD : ℕ × (ℕ × ℕ) × ℕ := (0, (0, 0), 0)

/-- **A basis row**: every coordinate's `d` stored; the scale multiplied by every coefficient. -/
theorem osBasisRow_val {bd z nz : ℕ} {zv : E} (hzv : σ (.n z) = zv) (hnz : σ (.n nz) = 1 + zv) :
    ∀ (cs : List (ℕ × (ℕ × ℕ) × ℕ)) (sc : ℕ) (k : ℕ) (cv : ℕ → E),
    (∀ t < cs.length, ((zv = 0 ∧ cv t * word (cs.getD t coordD).2.2 0 ≠ 0) ∨ zv = 1) ∧
      LoadHolds rd (σ (.n (cs.getD t coordD).2.1.1)) (cs.getD t coordD).2.1.2 (cv t)) →
    AllOk C rd σ (osBasisRow bd cs sc z nz k).1 →
    (∀ t < cs.length, LoadHolds rd (σ (.n bd)) (cs.getD t coordD).1
        (dZv (cv t) (word (cs.getD t coordD).2.2 0) zv)) ∧
    σ (.n (osBasisRow bd cs sc z nz k).2.1) =
      σ (.n sc) * ∏ t ∈ Finset.range cs.length, (cv t * word (cs.getD t coordD).2.2 0)
  | [], sc, k, cv, _, _ => ⟨fun t ht ↦ absurd ht (by simp), by simp [osBasisRow]⟩
  | (slot, src, inv) :: rest, sc, k, cv, hin, hok => by
    simp only [osBasisRow] at hok ⊢
    rw [allOk_append] at hok
    obtain ⟨h0, hrest⟩ := hok
    obtain ⟨hi0, hc0⟩ := hin 0 (by simp)
    simp only [List.getD_cons_zero] at hi0 hc0
    obtain ⟨d0, s0⟩ := osBasisBlk_val (bd := bd) (slot := slot) (sc := sc) (k := k) hi0 hzv hnz hc0 h0
    obtain ⟨hr, hs⟩ := osBasisRow_val hzv hnz rest (osBasisBlk bd slot src inv sc z nz k).2.1
      (osBasisBlk bd slot src inv sc z nz k).2.2 (fun t ↦ cv (t + 1))
      (fun t ht ↦ hin (t + 1) (by simp; omega)) hrest
    refine ⟨fun t ht ↦ ?_, ?_⟩
    · rcases t with _ | t
      · exact d0
      · exact hr t (by simpa using ht)
    · rw [hs, s0, List.length_cons, Finset.prod_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero]
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

/-- A level's `d` at coordinate `t`: `dZv` at the zero flag of the coordinates' product. -/
def dZ (lv : OsLv) (n : ℕ) (X : ℕ → E) (t : ℕ) : E :=
  dZv (X t) (invW lv t) (zeroOf (∏ s ∈ Finset.range n, X s))

/-- What a level's basis row reads: its scalar `β` and its coordinates `X`. -/
def BasisIn (rd : Reader) (σ : Val) (c : OsCfg) (tch L : ℕ) (lv : OsLv) (β : E) (X : ℕ → E) :
    Prop :=
  LoadHolds rd (σ (.n osBetas)) L β ∧ ∀ t < lv.prefixLen + c.yrLog, invW lv t ≠ 0 ∧
    LoadHolds rd (σ (.n (coordSrc tch lv t).1)) (coordSrc tch lv t).2 (X t)

/-- What it stores: the coefficients' `d` in `basis_d`, the scale in `level_scale`, the product
of the coordinates in `level_after`. -/
def BasisOut (rd : Reader) (σ : Val) (c : OsCfg) (bd ls la L : ℕ) (lv : OsLv) (β : E)
    (X : ℕ → E) : Prop :=
  (∀ t < lv.prefixLen + c.yrLog,
    LoadHolds rd (σ (.n bd)) (L * ligColsCap + t) (dZ lv (lv.prefixLen + c.yrLog) X t)) ∧
  LoadHolds rd (σ (.n ls)) L (β * ∏ t ∈ Finset.range (lv.prefixLen + c.yrLog), (X t * invW lv t)) ∧
  LoadHolds rd (σ (.n la)) L (∏ t ∈ Finset.range (lv.prefixLen + c.yrLog), X t)

/-- A product's factors are not zero where the product is not. -/
theorem prod_ne_factor {n : ℕ} {X : ℕ → E} (h : ∏ s ∈ Finset.range n, X s ≠ 0) {t : ℕ}
    (ht : t < n) : X t ≠ 0 :=
  fun h0 ↦ h (Finset.prod_eq_zero (Finset.mem_range.mpr ht) h0)

/-- **A non-final level's basis row.** -/
theorem osBasisLv_sound {c : OsCfg} {tch bd ls la lvl : ℕ} {lv : OsLv} {k : ℕ} {β : E} {X : ℕ → E}
    (hiz : ∀ a r, C "is_zero" a r → MeaningIsZero a r) (hpos : 1 ≤ lv.prefixLen + c.yrLog)
    (hin : BasisIn rd σ c tch lvl lv β X)
    (hok : AllOk C rd σ (osBasisLv c tch bd ls la lvl lv k).1) :
    BasisOut rd σ c bd ls la lvl lv β X := by
  set n := lv.prefixLen + c.yrLog with hn
  have hlen : (osBasisCoords c tch lvl lv).length = n := by simp [osBasisCoords, n]
  have hcs : ∀ t < n, (osBasisCoords c tch lvl lv).getD t coordD =
      (lvl * ligColsCap + t, coordSrc tch lv t, vanishInv (lv.vanish + t)) :=
    fun t ht ↦ osBasisCoords_getD ht
  unfold osBasisLv at hok
  simp only at hok
  set cs := osBasisCoords c tch lvl lv with hcsd
  set af := osAfterRow (cs.map (·.2.1)) none (k + 1) with haf
  set r := osBasisRow bd cs k af.2.2 (af.2.2 + 2) (af.2.2 + 3) with hr
  simp only [allOk_cons, allOk_append, allOk_nil, and_true, stmtOk_atom, stmtOk_call, holds_load,
    holds_const, holds_add, osLd, osCst, osAdd, List.map_cons, List.map_nil] at hok
  obtain ⟨⟨⟨⟨lb, haok⟩, hz, c1, a2⟩, hrow⟩, ls0, la0⟩ := hok
  have eb := loadHolds_unique lb hin.1
  -- the product
  have hX : ∀ t < (cs.map (·.2.1)).length,
      LoadHolds rd (σ (.n ((cs.map (·.2.1)).getD t (0, 0)).1)) ((cs.map (·.2.1)).getD t (0, 0)).2 (X t) := by
    intro t ht
    rw [List.length_map, hlen] at ht
    have e : (cs.map (·.2.1)).getD t (0, 0) = coordSrc tch lv t := by
      rw [List.getD_eq_getElem _ _ (by simp [hlen]; exact ht), List.getElem_map,
        ← List.getD_eq_getElem _ coordD (by rw [hlen]; exact ht), hcs t ht]
    rw [e]; exact (hin.2 t ht).2
  have ha : σ (.n (af.2.1.getD 0)) = ∏ t ∈ Finset.range n, X t := by
    have := osAfterRow_val (C := C) (rd := rd) (σ := σ) _ none (k + 1) X hX haok
      (Or.inr (by intro h0; have := congrArg List.length h0; simp [hlen] at this; omega))
    rw [List.length_map, hlen, optVal, one_mul] at this
    exact this
  -- the flag
  set P := ∏ t ∈ Finset.range n, X t with hP
  have hzv : σ (.n af.2.2) = zeroOf P := by rw [zeroOf_of_meaning (hiz _ _ hz), ha]
  have hnz : σ (.n (af.2.2 + 2)) = 1 + zeroOf P := by rw [a2, c1, hzv, word_one]
  -- the row
  obtain ⟨hd, hs⟩ := osBasisRow_val (C := C) (bd := bd) hzv hnz cs k (af.2.2 + 3) X (fun t ht ↦ by
    rw [hlen] at ht
    rw [hcs t ht]
    refine ⟨?_, (hin.2 t ht).2⟩
    by_cases h0 : P = 0
    · exact Or.inr (zeroOf_eq_one h0)
    · exact Or.inl ⟨zeroOf_eq_zero h0, mul_ne_zero (prod_ne_factor h0 ht) (hin.2 t ht).1⟩) hrow
  refine ⟨fun t ht ↦ ?_, ?_, ?_⟩
  · have := hd t (by rw [hlen]; exact ht)
    rw [hcs t ht] at this
    exact this
  · rw [hs, eb, hlen] at ls0
    rwa [Finset.prod_congr rfl fun t ht ↦ by
      rw [hcs t (Finset.mem_range.mp ht)]] at ls0
  · rwa [ha] at la0

/-- **Every non-final level's basis row**. -/
theorem osBases_sound {c : OsCfg} {tch bd ls la : ℕ} (β : ℕ → E) (X : ℕ → ℕ → E)
    (hiz : ∀ a r, C "is_zero" a r → MeaningIsZero a r)
    (hpos : ∀ lv : OsLv, 1 ≤ lv.prefixLen + c.yrLog) :
    ∀ (levels : List OsLv) (lvl k : ℕ),
      (∀ i (hi : i < levels.length), BasisIn rd σ c tch (lvl + i) levels[i] (β (lvl + i))
        (X (lvl + i))) →
      AllOk C rd σ (osBases c tch bd ls la lvl levels k).1 →
      ∀ i (hi : i < levels.length), BasisOut rd σ c bd ls la (lvl + i) levels[i] (β (lvl + i))
        (X (lvl + i))
  | [], _, _, _, _, i, hi => absurd hi (by simp)
  | lv :: rest, lvl, k, hin, hok, i, hi => by
    simp only [osBases, allOk_append] at hok
    rcases i with _ | i
    · obtain ⟨hb, hx⟩ := hin 0 (by simp)
      simp only [Nat.add_zero, List.getElem_cons_zero] at hb hx ⊢
      exact osBasisLv_sound hiz (hpos lv) ⟨hb, hx⟩ hok.1
    · have := osBases_sound β X hiz hpos rest (lvl + 1) _ (fun j hj ↦ by
        have := hin (j + 1) (by simp; omega)
        rwa [show lvl + (j + 1) = lvl + 1 + j by ring] at this) hok.2 i (by simpa using hi)
      rwa [show lvl + 1 + i = lvl + (i + 1) by ring] at this

end
end LeanVM.Guest.B1.Whir
