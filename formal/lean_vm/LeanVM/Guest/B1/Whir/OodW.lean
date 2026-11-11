/-
  LeanVM.Guest.B1.Whir.OodW

  The out-of-domain claims' weights at the terminal point, summed.
-/

module

public import LeanVM.Guest.B1.Whir.Flat

/-!
# The out-of-domain weights (G:1854-1864)

The weight of out-of-domain claim `s` of the commitment level `ol - 1` read: its scalar from
`ood_scalars`, times `1 + z_t + p_t` over its point `z` (in `ood_z`) and the terminal point's
coordinates `p` from the level's folds on (`osOodWeight_val`); the weights summed over the
levels (`osOodWeights_val`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- The running sum's value: `0` before the first weight. -/
def accVal (σ : Val) : Option ℕ → E
  | none => 0
  | some x => σ (.n x)

/-- **The factors of a weight**: the scalar times `Π (1 + z_t + p_t)`. -/
theorem osOodFacs_val : ∀ (cs : List (ℕ × ℕ × ℕ)) (sc k : ℕ) (z p : ℕ → E),
    (∀ t < cs.length, LoadHolds rd (σ (.n osOodz)) (cs.getD t (0, 0, 0)).1 (z t) ∧
      LoadHolds rd (σ (.n (cs.getD t (0, 0, 0)).2.1)) (cs.getD t (0, 0, 0)).2.2 (p t)) →
    AllOk C rd σ (osOodFacs sc cs k).1 →
    σ (.n (osOodFacs sc cs k).2.1) = σ (.n sc) * ∏ t ∈ Finset.range cs.length, (1 + z t + p t)
  | [], sc, k, _, _, _, _ => by simp [osOodFacs]
  | (zo, src) :: rest, sc, k, z, p, hin, hok => by
    simp only [osOodFacs] at hok ⊢
    rw [allOk_append] at hok
    obtain ⟨h0, hr⟩ := hok
    simp only [allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_load, holds_const, holds_add,
      holds_mul] at h0
    obtain ⟨c0, l1, a2, l3, a4, m5⟩ := h0
    obtain ⟨hz, hp⟩ := hin 0 (by simp)
    simp only [List.getD_cons_zero] at hz hp
    have ih := osOodFacs_val rest (k + 5) (k + 6) (fun t ↦ z (t + 1)) (fun t ↦ p (t + 1))
      (fun t ht ↦ hin (t + 1) (by simp; omega)) hr
    rw [ih, m5, a4, a2, c0, word_one, loadHolds_unique l1 hz, loadHolds_unique l3 hp,
      List.length_cons, Finset.prod_range_succ']
    ring

/-- A weight's coordinates `(z slot, source)`. -/
def oodCoords (c : OsCfg) (tch prevCols ol s : ℕ) (lv : OsLv) : List (ℕ × ℕ × ℕ) :=
  (List.range (prevCols - c.yrLog + c.yrLog)).map fun t ↦
    ((oodSamples * ol + s) * ligColsCap + t,
      if t < prevCols - c.yrLog then (osFch, lv.foldsOff + t) else (tch, t - (prevCols - c.yrLog)))

theorem osOodWeight_eq (c : OsCfg) (tch prevCols ol s : ℕ) (lv : OsLv) (k : ℕ) :
    osOodWeight c tch prevCols ol s lv k =
      (osLd k osOodSc (oodSamples * ol + s) :: (osOodFacs k (oodCoords c tch prevCols ol s lv) (k + 1)).1,
        (osOodFacs k (oodCoords c tch prevCols ol s lv) (k + 1)).2) := rfl

/-- **A weight**: its scalar `λs`, its point `z` and the terminal coordinates `p`. -/
theorem osOodWeight_val {c : OsCfg} {tch prevCols ol s : ℕ} {lv : OsLv} {k : ℕ} {lam : E}
    {z p : ℕ → E} (hl : LoadHolds rd (σ (.n osOodSc)) (oodSamples * ol + s) lam)
    (hz : ∀ t < prevCols - c.yrLog + c.yrLog,
      LoadHolds rd (σ (.n osOodz)) ((oodSamples * ol + s) * ligColsCap + t) (z t))
    (hp : ∀ t < prevCols - c.yrLog + c.yrLog,
      LoadHolds rd (σ (.n (if t < prevCols - c.yrLog then osFch else tch)))
        (if t < prevCols - c.yrLog then lv.foldsOff + t else t - (prevCols - c.yrLog)) (p t))
    (hok : AllOk C rd σ (osOodWeight c tch prevCols ol s lv k).1) :
    σ (.n (osOodWeight c tch prevCols ol s lv k).2.1) =
      lam * ∏ t ∈ Finset.range (prevCols - c.yrLog + c.yrLog), (1 + z t + p t) := by
  rw [osOodWeight_eq] at hok ⊢
  rw [allOk_cons] at hok
  obtain ⟨h0, hr⟩ := hok
  simp only [stmtOk_atom, holds_load, osLd] at h0
  have hlen : (oodCoords c tch prevCols ol s lv).length = prevCols - c.yrLog + c.yrLog := by
    simp [oodCoords]
  rw [osOodFacs_val _ k (k + 1) z p (fun t ht ↦ by
    rw [hlen] at ht
    have hg : (oodCoords c tch prevCols ol s lv).getD t (0, 0, 0) =
        ((oodSamples * ol + s) * ligColsCap + t,
          if t < prevCols - c.yrLog then (osFch, lv.foldsOff + t) else (tch, t - (prevCols - c.yrLog))) := by
      simp [oodCoords, List.getD_eq_getElem?_getD, ht]
    rw [hg]
    refine ⟨hz t ht, ?_⟩
    have := hp t ht
    split_ifs at this ⊢ <;> exact this) hr, hlen, loadHolds_unique h0 hl]

theorem osAcc_val {acc : Option ℕ} {w k : ℕ} (h : AllOk C rd σ (osAcc acc w k).1) :
    accVal σ (osAcc acc w k).2.1 = accVal σ acc + σ (.n w) := by
  rcases acc with _ | x
  · simp [osAcc, accVal]
  · simp only [osAcc, allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_add, osAdd] at h
    simp [osAcc, accVal, h]

theorem osAcc_some {acc : Option ℕ} {w k : ℕ} : ∃ x, (osAcc acc w k).2.1 = some x := by
  rcases acc with _ | x <;> simp [osAcc]

/-- **The weights summed**: from the running sum `acc`, every level's two weights `W i 0`,
`W i 1` added. -/
theorem osOodWeights_val {c : OsCfg} {tch : ℕ} :
    ∀ (lvs : List OsLv) (pc : ℕ → ℕ) (ol : ℕ) (acc : Option ℕ) (k : ℕ) (W : ℕ → ℕ → E),
      (∀ i < lvs.length, ∀ s < 2, ∀ k, AllOk C rd σ
        (osOodWeight c tch (pc i) (ol + i) s (lvs.getD i default) k).1 →
          σ (.n (osOodWeight c tch (pc i) (ol + i) s (lvs.getD i default) k).2.1) = W i s) →
      (∀ i < lvs.length, pc (i + 1) = (lvs.getD i default).logCols) →
      AllOk C rd σ (osOodWeights c tch (pc 0) ol lvs acc k).1 →
      accVal σ (osOodWeights c tch (pc 0) ol lvs acc k).2.1 =
        accVal σ acc + ∑ i ∈ Finset.range lvs.length, (W i 0 + W i 1)
  | [], _, _, acc, _, _, _, _, _ => by simp [osOodWeights]
  | lv :: rest, pc, ol, acc, k, W, hW, hpc, hok => by
    simp only [osOodWeights, allOk_append] at hok ⊢
    obtain ⟨⟨⟨⟨h0, ha0⟩, h1⟩, ha1⟩, hr⟩ := hok
    have e0 := hW 0 (by simp) 0 (by omega) _ (by simpa using h0)
    have e1 := hW 0 (by simp) 1 (by omega) _ (by simpa using h1)
    simp only [Nat.add_zero, List.getD_cons_zero] at e0 e1
    have ih := fun (acc' : Option ℕ) (k' : ℕ) ↦
      osOodWeights_val rest (fun i ↦ pc (i + 1)) (ol + 1) acc' k' (fun i s ↦ W (i + 1) s)
      (fun i hi s hs k' h ↦ by
        have := hW (i + 1) (by simp; omega) s hs k'
        simp only [List.getD_cons_succ, show ol + (i + 1) = ol + 1 + i by ring] at this
        exact this h)
      (fun i hi ↦ by
        have := hpc (i + 1) (by simp; omega)
        simpa using this)
    have hp1 : pc 1 = lv.logCols := by simpa using hpc 0 (by simp)
    simp only [hp1] at ih
    rw [ih _ _ hr, osAcc_val ha1, osAcc_val ha0, e0, e1, List.length_cons, Finset.sum_range_succ']
    ring

end
end LeanVM.Guest.B1.Whir
