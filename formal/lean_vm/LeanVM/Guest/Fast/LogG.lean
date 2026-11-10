module

public import LeanVM.Guest.Fast.GLanesCheck
public import LeanVM.Guest.B1.Sig.Codeword

/-!
# The exponent searches, computable

`logG x bound` (`B1/Sig/Codeword.lean`), the first `k < bound` with `x = g^k`, decides equality
classically and computes `g^k` for each candidate. `logGT x bound` reads the lanes of `g^k` off the
literal table `gLanes` instead and compares `x`'s low lane with them, its other limb zero:
`logG_eq_logGT` for `bound ≤ 256`.
-/

namespace LeanVM.Guest.Fast

open LeanVM.Parameters LeanVM.Guest.B1.Sig

@[expose] public section

/-- The index of `w` among the first `m` entries of `tab`, counted from `i` (`0` if absent). -/
def idxBelow (w : ℕ) : List ℕ → ℕ → ℕ → ℕ
  | [], _, _ => 0
  | _, _, 0 => 0
  | t :: ts, i, m + 1 => if w = t then i else idxBelow w ts (i + 1) m

/-- **The exponent `k < bound` with `x = g^k`** (`0` if none), off the lanes `gLanes`. -/
def logGT (x : E) (bound : ℕ) : ℕ :=
  if x.limb 1 = 0 then idxBelow (x.limb 0).lane.toNat gLanes 0 bound else 0

/-- **`logGT` off lanes given**: `gLanes`, built once by the caller (`logGTWith_gLanes`). -/
def logGTWith (lanes : List ℕ) (x : E) (bound : ℕ) : ℕ :=
  if x.limb 1 = 0 then idxBelow (x.limb 0).lane.toNat lanes 0 bound else 0

theorem logGTWith_gLanes : logGTWith gLanes = logGT := rfl

theorem lane_toNat_inj {a b : K} : a.lane.toNat = b.lane.toNat ↔ a = b := by
  constructor
  · intro h
    have : a.lane = b.lane := UInt64.toNat_inj.mp h
    have ha : K.ofLane a.lane = a := rfl
    have hb : K.ofLane b.lane = b := rfl
    rw [← ha, ← hb, this]
  · rintro rfl; rfl

theorem eq_ofK_iff (x : E) (a : K) :
    x = ofK a ↔ x.limb 1 = 0 ∧ (x.limb 0).lane.toNat = a.lane.toNat := by
  rw [lane_toNat_inj]
  constructor
  · rintro rfl; simp
  · rintro ⟨h1, h0⟩
    apply E.ext; intro i
    fin_cases i <;> simp [h0, h1]

theorem idxBelow_range' (w : ℕ) (f : ℕ → ℕ) :
    ∀ (n s : ℕ), idxBelow w ((List.range' s n).map f) s n =
      (((List.range' s n).find? fun k ↦ decide (w = f k)).getD 0)
  | 0, s => by simp [idxBelow]
  | n + 1, s => by
      rw [List.range'_succ, List.map_cons, List.find?_cons]
      simp only [idxBelow]
      by_cases h : w = f s
      · simp [h]
      · simp only [h, ↓reduceIte, decide_false]
        exact idxBelow_range' w f n (s + 1)

theorem idxBelow_take (w : ℕ) : ∀ (tab : List ℕ) (i m : ℕ),
    idxBelow w tab i m = idxBelow w (tab.take m) i m
  | [], _, _ => by simp [idxBelow]
  | _ :: _, _, 0 => by simp [idxBelow]
  | t :: ts, i, m + 1 => by
      simp only [idxBelow, List.take_succ_cons]
      rw [idxBelow_take w ts (i + 1) m]

/-- **`logG` off the table.** -/
theorem logG_eq_logGT (x : E) {bound : ℕ} (hb : bound ≤ 256) : logG x bound = logGT x bound := by
  classical
  have htab : gLanes.take bound = (List.range' 0 bound).map fun k ↦ (addressOfIndex
      k).lane.toNat := by
    rw [gLanes_eq, ← List.map_take, List.take_range, Nat.min_eq_left hb, List.range_eq_range']
    apply List.map_congr_left
    intro k hk
    rw [List.mem_range'_1] at hk
    rw [gpowK_eq (by unfold u128Bound; omega)]
  unfold logG logGT
  by_cases hx : x.limb 1 = 0
  · simp only [hx, ↓reduceIte]
    rw [idxBelow_take, htab, idxBelow_range', List.range_eq_range']
    congr 2
    funext k
    simp only [eq_ofK_iff, hx, true_and]
  · simp only [hx, ↓reduceIte]
    have : (List.range bound).find? (fun k ↦ decide (x = ofK (addressOfIndex k))) = none := by
      rw [List.find?_eq_none]
      intro k _
      simp only [decide_eq_true_eq, eq_ofK_iff]
      exact fun h ↦ hx h.1
    rw [this]; rfl

theorem logG_lt (x : E) {bound : ℕ} (hb : 0 < bound) : logG x bound < bound := by
  unfold logG
  cases h : (List.range bound).find? (fun k ↦ decide (x = ofK (addressOfIndex k))) with
  | none => simpa using hb
  | some k => simpa using List.mem_range.mp (List.mem_of_find?_eq_some h)

end
end LeanVM.Guest.Fast
