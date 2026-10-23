/-
  LeanVM.Protocol.ToCompPoly.Restriction

  A table restricted to the coordinates of a partial point, and when that restriction is
  identically zero: the notion a knowledge state function tracks while the coordinates of a
  point are drawn one at a time. Candidate for CompPoly.
-/

module

public import LeanVM.Protocol.ToCompPoly.Multilinear
import Mathlib.Tactic.LinearCombination

/-!
# A table on a partial point

A *partial point* (`Partial R`) fixes some coordinates and leaves the others free. A table is
*zero on* a partial point (`RestrictedZero`) when its multilinear extension vanishes at every
completion of the fixed coordinates by a cube point: the restriction of the extension to the
fixed coordinates is identically zero as a polynomial in the free ones. On the empty partial
point this says the table is zero (`restrictedZero_empty_iff`); with every coordinate fixed it
says the extension vanishes at the point (`restrictedZero_of_all`). Partial points are built by
placing a vector at an offset (`Partial.ofVector`) and putting two side by side
(`Partial.or`).

The one fact a proof system uses: a table that is not zero on a partial point is zero on it with
one more coordinate fixed for at most one value of that coordinate
(`card_filter_restrictedZero_update_le`). The extension is affine in the new coordinate, so
vanishing at two values is vanishing at every value, the cube's included.
-/

namespace LeanVM.Protocol

open CompPoly CMlPolynomialEval

@[expose] public section

variable {R : Type}

/-- A partial point: for each coordinate, its value if fixed. -/
abbrev Partial (R : Type) : Type := ℕ → Option R

/-- The empty partial point: nothing fixed. -/
def Partial.empty : Partial R := fun _ ↦ Option.none

/-- A vector placed at an offset: coordinates `off` to `off + k - 1` fixed to `v`, the others
free. -/
def Partial.ofVector (off : ℕ) {k : ℕ} (v : Vector R k) : Partial R :=
  fun i ↦ if h : off ≤ i ∧ i < off + k then some (v[i - off]'(by omega)) else none

/-- Two partial points side by side: a coordinate the first fixes, at its value; otherwise the
second's. -/
def Partial.or (σ τ : Partial R) : Partial R := fun i ↦ (σ i).or (τ i)

/-- The empty vector fixes nothing. -/
theorem Partial.ofVector_zero (off : ℕ) (v : Vector R 0) :
    Partial.ofVector off v = Partial.empty := by
  funext i
  simp [Partial.ofVector, Partial.empty]

/-- One more entry fixes one more coordinate, the one after the others. -/
theorem Partial.ofVector_push (off : ℕ) {k : ℕ} (v : Vector R k) (c : R) :
    Partial.ofVector off (v.push c) =
      Function.update (Partial.ofVector off v) (off + k) (some c) := by
  funext i
  by_cases hi : i = off + k
  · subst hi
    simp [Partial.ofVector]
  · rw [Function.update_of_ne hi]
    simp only [Partial.ofVector]
    split_ifs with h₁ h₂ h₂
    · rw [Vector.getElem_push_lt (by omega)]
    · omega
    · omega
    · rfl

/-- Nothing beside a partial point is the partial point. -/
theorem Partial.empty_or (τ : Partial R) : Partial.empty.or τ = τ := rfl

/-- A coordinate fixed in the first of two partial points side by side is fixed in both. -/
theorem Partial.update_or (σ τ : Partial R) (i : ℕ) (c : R) :
    Partial.or (Function.update σ i (some c)) τ = Function.update (σ.or τ) i (some c) := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp [Partial.or]
  · simp [Partial.or, Function.update_of_ne hj]

/-- The challenges of `c` from offset `off` on, placed at coordinates `0, 1, …`: the partial point
a table on the last coordinates of a longer point sees while that point is drawn. -/
def Partial.ofSuffix (off : ℕ) {j : ℕ} (c : Vector R j) : Partial R :=
  fun i ↦ if h : off + i < j then some c[off + i] else Option.none

/-- Before the offset is reached, nothing is fixed. -/
theorem Partial.ofSuffix_of_le (off : ℕ) {j : ℕ} (c : Vector R j) (h : j ≤ off) :
    Partial.ofSuffix off c = Partial.empty := by
  funext i
  simp only [Partial.ofSuffix, Partial.empty]
  rw [dite_eq_right (by omega)]

/-- A challenge before the offset fixes nothing. -/
theorem Partial.ofSuffix_push_of_lt (off : ℕ) {j : ℕ} (c : Vector R j) (x : R) (h : j < off) :
    Partial.ofSuffix off (c.push x) = Partial.ofSuffix off c := by
  rw [Partial.ofSuffix_of_le _ _ (by omega), Partial.ofSuffix_of_le _ _ h.le]

/-- A challenge past the offset fixes one more coordinate. -/
theorem Partial.ofSuffix_push_of_le (off : ℕ) {j : ℕ} (c : Vector R j) (x : R) (h : off ≤ j) :
    Partial.ofSuffix off (c.push x) =
      Function.update (Partial.ofSuffix off c) (j - off) (some x) := by
  funext i
  by_cases hi : i = j - off
  · subst hi
    simp only [Partial.ofSuffix, Function.update_self]
    rw [dite_eq_left (by omega), Vector.getElem_push, dite_eq_right (by omega)]
  · rw [Function.update_of_ne hi]
    simp only [Partial.ofSuffix]
    by_cases hlt : off + i < j
    · rw [dite_eq_left (by omega), dite_eq_left hlt, Vector.getElem_push, dite_eq_left hlt]
    · rw [dite_eq_right (by omega), dite_eq_right hlt]

/-- The coordinate the next challenge past the offset will fix is free. -/
theorem Partial.ofSuffix_next (off : ℕ) {j : ℕ} (c : Vector R j) :
    Partial.ofSuffix off c (j - off) = Option.none := by
  simp only [Partial.ofSuffix]
  rw [dite_eq_right (by omega)]

/-- With every coordinate past the offset drawn, the partial point fixes the suffix. -/
theorem Partial.ofSuffix_all {k : ℕ} (off : ℕ) (c : Vector R (off + k)) (i : ℕ) (hi : i < k) :
    Partial.ofSuffix off c i = some c[off + i] := by
  simp only [Partial.ofSuffix]
  rw [dite_eq_left (by omega)]


variable [CommRing R]

/-- The point of a partial point at a completion `b`: the fixed coordinates, the others the bits
of `b`. -/
def Partial.point {n : ℕ} (σ : Partial R) (b : Fin (2 ^ n)) : Vector R n :=
  Vector.ofFn fun k ↦ (σ k).getD (boolVec b)[k]

/-- A table is zero on a partial point when its extension vanishes at every completion of the
fixed coordinates by a cube point. -/
def RestrictedZero {n : ℕ} (t : CMlPolynomialEval R n) (σ : Partial R) : Prop :=
  ∀ b : Fin (2 ^ n), evalMle t (σ.point b) = 0

instance [DecidableEq R] {n : ℕ} (t : CMlPolynomialEval R n) (σ : Partial R) :
    Decidable (RestrictedZero t σ) :=
  inferInstanceAs (Decidable (∀ _b : Fin (2 ^ n), _ = _))

/-- The point of the empty partial point at a completion is the cube point itself. -/
@[simp] theorem Partial.point_empty {n : ℕ} (b : Fin (2 ^ n)) :
    (Partial.empty : Partial R).point b = boolVec b := by
  apply Vector.ext
  intro k hk
  simp [Partial.point, Partial.empty]

/-- On the empty partial point, zero means the table is zero. -/
theorem restrictedZero_empty_iff {n : ℕ} (t : CMlPolynomialEval R n) :
    RestrictedZero t Partial.empty ↔ ∀ i : Fin (2 ^ n), t[i] = 0 := by
  simp only [RestrictedZero, Partial.point_empty, evalMle_boolVec]

/-- The difference of two tables, entry by entry. -/
def diffTable {n : ℕ} (t t' : CMlPolynomialEval R n) : CMlPolynomialEval R n :=
  Vector.ofFn fun i ↦ t[i] - t'[i]

/-- The extension of a difference is the difference of the extensions. -/
theorem evalMle_diffTable {n : ℕ} (t t' : CMlPolynomialEval R n) (p : Vector R n) :
    evalMle (diffTable t t') p = evalMle t p - evalMle t' p := by
  simp only [evalMle_eq_sum, diffTable, Fin.getElem_fin, Vector.getElem_ofFn, sub_mul,
    Finset.sum_sub_distrib]

/-- A difference zero on the empty partial point means the two tables are equal. -/
theorem diffTable_restrictedZero_empty_iff {n : ℕ} (t t' : CMlPolynomialEval R n) :
    RestrictedZero (diffTable t t') Partial.empty ↔ t = t' := by
  rw [restrictedZero_empty_iff]
  constructor
  · intro h
    apply Vector.ext
    intro i hi
    have := h ⟨i, hi⟩
    simp only [diffTable, Fin.getElem_fin, Vector.getElem_ofFn] at this
    exact sub_eq_zero.mp this
  · rintro rfl i
    simp [diffTable]

/-- When every coordinate is fixed, zero means the extension vanishes at the point. -/
theorem restrictedZero_of_all {n : ℕ} (t : CMlPolynomialEval R n) (σ : Partial R) (p : Vector R n)
    (hp : ∀ k (hk : k < n), σ k = some p[k]) :
    RestrictedZero t σ ↔ evalMle t p = 0 := by
  have hpoint : ∀ b : Fin (2 ^ n), σ.point b = p := fun b ↦ by
    apply Vector.ext
    intro k hk
    simp [Partial.point, hp k hk]
  simp only [RestrictedZero, hpoint]
  exact ⟨fun h ↦ h ⟨0, Nat.two_pow_pos n⟩, fun h _ ↦ h⟩

/-- The point of a partial point with one more coordinate fixed. -/
private theorem Partial.point_update {n : ℕ} (σ : Partial R) (k : ℕ) (hk : k < n) (c : R)
    (b : Fin (2 ^ n)) :
    Partial.point (Function.update σ k (some c)) b = (σ.point b).set k c := by
  apply Vector.ext
  intro j hj
  by_cases hjk : j = k
  · subst hjk
    simp [Partial.point]
  · simp [Partial.point, Function.update_of_ne hjk, Vector.getElem_set_ne hk hj (Ne.symm hjk)]

/-- Fixing a coordinate beyond the table's variables changes nothing. -/
private theorem Partial.point_update_of_le {n : ℕ} (σ : Partial R) (k : ℕ) (hk : n ≤ k) (c : R)
    (b : Fin (2 ^ n)) :
    Partial.point (Function.update σ k (some c)) b = σ.point b := by
  apply Vector.ext
  intro j hj
  simp [Partial.point, Function.update_of_ne (show j ≠ k by omega)]

/-- Setting a coordinate of a completion to its own value changes nothing. -/
private theorem Partial.point_set_self {n : ℕ} (σ : Partial R) (k : ℕ) (hk : k < n)
    (b : Fin (2 ^ n)) : (σ.point b).set k ((σ.point b)[k]) = σ.point b :=
  Vector.set_getElem_self hk

/-- Flip bit `k` of a cube index to `β`: the cube point that differs from `b` in coordinate `k`
at most, and has `β` there. -/
private def setBitIndex {n : ℕ} (b : Fin (2 ^ n)) (k : ℕ) (hk : k < n) (β : Bool) : Fin (2 ^ n) :=
  ⟨b.val ^^^ (if b.val.testBit k == β then 0 else 2 ^ k),
    Nat.xor_lt_two_pow b.isLt (by
      split
      · exact Nat.two_pow_pos n
      · exact Nat.pow_lt_pow_right (by norm_num) hk)⟩

private theorem testBit_setBitIndex {n : ℕ} (b : Fin (2 ^ n)) (k : ℕ) (hk : k < n) (β : Bool)
    (i : ℕ) : (setBitIndex b k hk β).val.testBit i = if i = k then β else b.val.testBit i := by
  simp only [setBitIndex, Nat.testBit_xor]
  by_cases hi : i = k
  · subst hi
    simp only [↓reduceIte]
    split <;> rename_i h
    · simp_all
    · cases β <;> cases hb : b.val.testBit i <;> simp_all [Nat.testBit_two_pow_self]
  · simp only [hi, ↓reduceIte]
    split <;> simp [Ne.symm hi]

/-- A completion with coordinate `k` free and then set to `0` or `1` is another completion. -/
private theorem Partial.point_set_bool {n : ℕ} (σ : Partial R) (k : ℕ) (hk : k < n)
    (hσ : σ k = Option.none) (b : Fin (2 ^ n)) (β : Bool) :
    (σ.point b).set k (if β then 1 else 0) = σ.point (setBitIndex b k hk β) := by
  apply Vector.ext
  intro j hj
  by_cases hjk : j = k
  · subst hjk
    simp [Partial.point, hσ, boolVec, testBit_setBitIndex]
  · rw [Vector.getElem_set_ne hk hj (Ne.symm hjk)]
    simp [Partial.point, boolVec, testBit_setBitIndex, hjk]

/-- **Zero stays zero.** A table zero on a partial point is zero on it with one more coordinate
fixed, if that coordinate was free: the extension is affine in the coordinate and vanishes at
both cube values. -/
theorem restrictedZero_update_of_none {n : ℕ} {t : CMlPolynomialEval R n} {σ : Partial R}
    (h : RestrictedZero t σ) {k : ℕ} (hσ : σ k = Option.none) (c : R) :
    RestrictedZero t (Function.update σ k (some c)) := by
  intro b
  by_cases hk : k < n
  · rw [Partial.point_update σ k hk c b, evalMle_set t _ hk]
    have h0 := h (setBitIndex b k hk false)
    have h1 := h (setBitIndex b k hk true)
    rw [← Partial.point_set_bool σ k hk hσ b] at h0 h1
    simp only [Bool.false_eq_true, ite_false, ite_true] at h0 h1
    rw [h0, h1]
    ring
  · rw [Partial.point_update_of_le σ k (by omega) c b]
    exact h b

open scoped Classical in
/-- **One escape at most.** A table that is not zero on a partial point is zero on it with one
more coordinate fixed for at most one value of that coordinate: its extension is affine in
the coordinate, so vanishing at two values is vanishing everywhere. -/
theorem card_filter_restrictedZero_update_le [IsDomain R] [Fintype R] {n : ℕ}
    (t : CMlPolynomialEval R n) (σ : Partial R) (k : ℕ)
    (hne : ¬ RestrictedZero t σ) :
    (Finset.univ.filter fun c ↦ RestrictedZero t (Function.update σ k (some c))).card ≤ 1 := by
  refine Finset.card_le_one.mpr fun c₁ h₁ c₂ h₂ ↦ ?_
  rw [Finset.mem_filter] at h₁ h₂
  by_contra hc
  apply hne
  by_cases hk : k < n
  · intro b
    have e₁ := h₁.2 b
    have e₂ := h₂.2 b
    rw [Partial.point_update σ k hk c₁ b, evalMle_set t _ hk] at e₁
    rw [Partial.point_update σ k hk c₂ b, evalMle_set t _ hk] at e₂
    -- `A + c·(B − A) = 0` at two distinct `c`: both `A` and `B` vanish.
    set A := evalMle t ((σ.point b).set k 0) with hA
    set B := evalMle t ((σ.point b).set k 1) with hB
    have hBA : B = A := by
      have : (c₁ - c₂) * (B - A) = 0 := by linear_combination e₁ - e₂
      rcases mul_eq_zero.mp this with h | h
      · exact absurd (sub_eq_zero.mp h) hc
      · exact sub_eq_zero.mp h
    have hA0 : A = 0 := by
      rw [hBA] at e₁
      linear_combination e₁
    have := evalMle_set t (σ.point b) hk ((σ.point b)[k])
    rw [Partial.point_set_self σ k hk b] at this
    rw [this, ← hA, ← hB, hBA, hA0]
    ring
  · intro b
    have := h₁.2 b
    rwa [Partial.point_update_of_le σ k (by omega) c₁ b] at this

/-- **One escape at most**, counted by `Nat.card`: no decidability in the statement. -/
theorem natCard_restrictedZero_update_le [IsDomain R] [Finite R] {n : ℕ}
    (t : CMlPolynomialEval R n) (σ : Partial R) (k : ℕ) (hne : ¬ RestrictedZero t σ) :
    Nat.card {c // RestrictedZero t (Function.update σ k (some c))} ≤ 1 := by
  have := Fintype.ofFinite R
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  convert card_filter_restrictedZero_update_le t σ k hne

end
end LeanVM.Protocol
