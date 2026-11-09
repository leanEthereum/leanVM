/-
  LeanVM.Guest.B1.Whir.OodW

  The terminal's out-of-domain weights: each committed level's sample against the point.
-/

module

public import LeanVM.Guest.B1.Whir.Flat

/-!
# The out-of-domain weights (G:1747-1756)

The commitment level `ol ≥ 1` reads (its out-of-domain point `z` in `ood_z`, its scalar `λ` in
`ood`) weighs `λ·Π_t (1 + z_t + c_t)` over the message coordinates `c` after the previous level's
folds (`osOodWeight_val`); the weights are summed (`osOodWeights_sound`, `oodSum`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

abbrev oodD : ℕ × ℕ × ℕ := (0, 0, 0)

/-- **The factors**: `sc·Π_t (1 + z_t + c_t)`. -/
theorem osOodFacs_val : ∀ (cs : List (ℕ × ℕ × ℕ)) (sc k : ℕ) (Z Y : ℕ → E),
    (∀ t < cs.length, LoadHolds rd (σ (.n osOodz)) (cs.getD t oodD).1 (Z t) ∧
      LoadHolds rd (σ (.n (cs.getD t oodD).2.1)) (cs.getD t oodD).2.2 (Y t)) →
    AllOk C rd σ (osOodFacs sc cs k).1 →
    σ (.n (osOodFacs sc cs k).2.1) = σ (.n sc) * ∏ t ∈ Finset.range cs.length, (1 + Z t + Y t)
  | [], sc, k, _, _, _, _ => by simp [osOodFacs]
  | (zo, src) :: rest, sc, k, Z, Y, hin, hok => by
    simp only [osOodFacs] at hok ⊢
    rw [allOk_append] at hok
    obtain ⟨h0, hrest⟩ := hok
    simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds] at h0
    obtain ⟨c0, l1, a2, l3, a4, m5⟩ := h0
    obtain ⟨hz, hy⟩ := hin 0 (by simp)
    simp only [List.getD_cons_zero] at hz hy
    have := osOodFacs_val rest (k + 5) (k + 6) (fun t ↦ Z (t + 1)) (fun t ↦ Y (t + 1))
      (fun t ht ↦ hin (t + 1) (by simp; omega)) hrest
    rw [this, m5, a4, a2, loadHolds_unique l3 hy, loadHolds_unique l1 hz, c0, word_one, List.length_cons,
      Finset.prod_range_succ']
    ring

/-- The source of the coordinate `t` of the weight after `zf` fold challenges. -/
def oodSrc (tch zf : ℕ) (lv : OsLv) (t : ℕ) : ℕ × ℕ :=
  if t < zf then (osFch, lv.foldsOff + t) else (tch, t - zf)

/-- What the weight of the level `ol` reads: its scalar, point and coordinates. -/
def OodIn (rd : Reader) (σ : Val) (c : OsCfg) (tch prevCols ol : ℕ) (lv : OsLv) (lam : E)
    (Z Y : ℕ → E) : Prop :=
  LoadHolds rd (σ (.n osOod)) (ol * oodSlots) lam ∧
    ∀ t < prevCols - c.yrLog + c.yrLog,
      LoadHolds rd (σ (.n osOodz)) (ol * ligColsCap + t) (Z t) ∧
      LoadHolds rd (σ (.n (oodSrc tch (prevCols - c.yrLog) lv t).1))
        (oodSrc tch (prevCols - c.yrLog) lv t).2 (Y t)

/-- **One weight**. -/
theorem osOodWeight_val {c : OsCfg} {tch prevCols ol : ℕ} {lv : OsLv} {k : ℕ} {lam : E}
    {Z Y : ℕ → E} (hin : OodIn rd σ c tch prevCols ol lv lam Z Y)
    (hok : AllOk C rd σ (osOodWeight c tch prevCols ol lv k).1) :
    σ (.n (osOodWeight c tch prevCols ol lv k).2.1) =
      lam * ∏ t ∈ Finset.range (prevCols - c.yrLog + c.yrLog), (1 + Z t + Y t) := by
  simp only [osOodWeight, allOk_cons, StmtOk, Atom.Holds] at hok ⊢
  obtain ⟨l0, hf⟩ := hok
  have hlen : ((List.range (prevCols - c.yrLog + c.yrLog)).map fun t ↦
      (ol * ligColsCap + t, if t < prevCols - c.yrLog then (osFch, lv.foldsOff + t)
        else (tch, t - (prevCols - c.yrLog)))).length = prevCols - c.yrLog + c.yrLog := by simp
  have := osOodFacs_val _ k (k + 1) Z Y (fun t ht ↦ by
    rw [hlen] at ht
    have := hin.2 t ht
    simpa [List.getD_eq_getElem?_getD, ht, oodSrc] using this) hf
  rw [this, hlen, loadHolds_unique l0 hin.1]

/-- The weights of the levels `ol ..`, after `prevCols` message coordinates. -/
def oodSum (c : OsCfg) (Λ : ℕ → E) (Z Y : ℕ → ℕ → E) : ℕ → ℕ → List OsLv → E
  | _, _, [] => 0
  | prevCols, ol, lv :: rest =>
    Λ ol * ∏ t ∈ Finset.range (prevCols - c.yrLog + c.yrLog), (1 + Z ol t + Y ol t) +
      oodSum c Λ Z Y lv.logCols (ol + 1) rest

/-- What every weight reads. -/
def OodAll (rd : Reader) (σ : Val) (c : OsCfg) (tch : ℕ) (Λ : ℕ → E) (Z Y : ℕ → ℕ → E) :
    ℕ → ℕ → List OsLv → Prop
  | _, _, [] => True
  | prevCols, ol, lv :: rest => OodIn rd σ c tch prevCols ol lv (Λ ol) (Z ol) (Y ol) ∧
    OodAll rd σ c tch Λ Z Y lv.logCols (ol + 1) rest

/-- The running sum's value. -/
def accVal (σ : Val) : Option ℕ → E
  | none => 0
  | some x => σ (.n x)

/-- **The weights, summed** onto the running sum. -/
theorem osOodWeights_sound {c : OsCfg} {tch : ℕ} (Λ : ℕ → E) (Z Y : ℕ → ℕ → E) :
    ∀ (levels : List OsLv) (prevCols ol : ℕ) (acc : Option ℕ) (k : ℕ),
      OodAll rd σ c tch Λ Z Y prevCols ol levels →
      AllOk C rd σ (osOodWeights c tch prevCols ol levels acc k).1 →
      (acc ≠ none ∨ levels ≠ []) → ∃ x, (osOodWeights c tch prevCols ol levels acc k).2.1 = some x ∧
        σ (.n x) = accVal σ acc + oodSum c Λ Z Y prevCols ol levels
  | [], _, _, acc, _, _, _, h => by
    rcases acc with _ | x
    · simp at h
    · exact ⟨x, rfl, by simp [accVal, oodSum]⟩
  | lv :: rest, prevCols, ol, acc, k, hin, hok, _ => by
    obtain ⟨h1, hrest⟩ := hin
    simp only [osOodWeights] at hok ⊢
    rw [allOk_append, allOk_append] at hok
    obtain ⟨⟨hw, ha⟩, ht⟩ := hok
    have hv := osOodWeight_val h1 hw
    rcases acc with _ | x
    · obtain ⟨y, hy, hv'⟩ := osOodWeights_sound Λ Z Y rest lv.logCols (ol + 1) _ _ hrest ht
        (Or.inl (by simp))
      refine ⟨y, hy, ?_⟩
      rw [hv']
      simp only [accVal, oodSum, hv]
      ring
    · simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds] at ha
      obtain ⟨y, hy, hv'⟩ := osOodWeights_sound Λ Z Y rest lv.logCols (ol + 1) _ _ hrest ht
        (Or.inl (by simp))
      refine ⟨y, hy, ?_⟩
      rw [hv']
      simp only [accVal, oodSum, ha, hv]
      ring

end
end LeanVM.Guest.B1.Whir
