/-
  LeanVM.Protocol.ToArkLib.Typed.Schedule

  The slots of the typed components and their errors, as closed forms: a sumcheck round, a
  sequence of rounds, a sequence of challenges. Candidate for ArkLib.
-/

module

public import LeanVM.Protocol.ToArkLib.Typed.Append
public import LeanVM.Protocol.ToArkLib.Typed.PassThrough
public import LeanVM.Protocol.ToArkLib.Typed.SampleChallenge
public import LeanVM.Protocol.ToArkLib.Typed.SendChecked

/-!
# Typed slots and their errors

The slots of leanVM's components, built from the one-message and one-challenge slots in
sequence, each with the errors it charges:

* `roundSlot C d`: a sumcheck round, the `d + 1` coefficients then one challenge;
* `roundsSlot C d m`: `m` rounds, `roundsErrors C d e m` charging `e` per challenge;
* `drawsSlot C k`: `k` challenges, `drawsErrors C e k` charging `e` each.

A component built by appending components at these slots has the slot in its type by the
definitions alone.

The errors summed along every path are bounded in closed form (`Errors.Bounded`): `m · e` for
`m` rounds, `k · e` for `k` challenges, and for the grand-product argument
`((μ + 1)(nside − 1) + 2μ² + 3μ + 3) · u` (`gkrErrors_bounded`).
-/

namespace LeanVM.Protocol.Typed

open Interaction Interaction.Oracle
open scoped NNReal

@[expose] public section

variable (C : Type) [SampleableType C]

/-- A sumcheck round of degree `d`: the coefficients, then the challenge. -/
abbrev roundSlot (d : ℕ) : Slot := (saySlot (Vector C (d + 1))).append (drawSlot C)

/-- The error `e` on a round's challenge. -/
abbrev roundErrors (d : ℕ) (e : ℝ≥0) : Errors (roundSlot C d).tree (roundSlot C d).roles :=
  Errors.append (sayTree (Vector C (d + 1))) (sayRoles _) (sayErrors _) (drawErrors C e)

/-- `m` sumcheck rounds of degree `d`. -/
def roundsSlot (d : ℕ) : ℕ → Slot
  | 0 => doneSlot
  | m + 1 => (roundSlot C d).append (roundsSlot d m)

/-- The error `e` on each round's challenge. -/
def roundsErrors (d : ℕ) (e : ℝ≥0) : (m : ℕ) → Errors (roundsSlot C d m).tree (roundsSlot C d m).roles
  | 0 => doneErrors
  | m + 1 => Errors.append (roundSlot C d).tree (roundSlot C d).roles (roundErrors C d e)
      (roundsErrors d e m)

/-- `k` challenges. -/
def drawsSlot : ℕ → Slot
  | 0 => doneSlot
  | k + 1 => (drawsSlot k).append (drawSlot C)

/-- The error `e` on each challenge. -/
def drawsErrors (e : ℝ≥0) : (k : ℕ) → Errors (drawsSlot C k).tree (drawsSlot C k).roles
  | 0 => doneErrors
  | k + 1 => Errors.append (drawsSlot C k).tree (drawsSlot C k).roles (drawsErrors e k)
      (drawErrors C e)

/-- Each round's error at most another's makes the rounds' errors at most theirs. -/
theorem roundsErrors_le (d : ℕ) {e e' : ℝ≥0} (h : e ≤ e') : (m : ℕ) →
    Errors.Le (roundsSlot C d m).tree (roundsSlot C d m).roles (roundsErrors C d e m)
      (roundsErrors C d e' m)
  | 0 => trivial
  | m + 1 => Errors.Le.append (roundSlot C d).tree (roundSlot C d).roles
      (Errors.Le.append (sayTree _) (sayRoles _) (Errors.Le.refl _ _ _) ⟨h, fun _ ↦ trivial⟩)
      (roundsErrors_le d h m)

/-- The error `f p` on the `p`-th challenge. -/
def drawsErrorsOf (f : ℕ → ℝ≥0) : (k : ℕ) → Errors (drawsSlot C k).tree (drawsSlot C k).roles
  | 0 => doneErrors
  | k + 1 => Errors.append (drawsSlot C k).tree (drawsSlot C k).roles (drawsErrorsOf f k)
      (drawErrors C (f k))

/-! ## The grand-product argument -/

/-- One layer of the grand-product argument over `nside` trees, radix `2 ^ ρ`, at depth `m`: the
combiner, `m` rounds on a cofactor of degree `2 ^ ρ`, each tree's `2 ^ ρ` values at the
descendants, and the `ρ` combination challenges. -/
abbrev stepSlot (nside ρ m : ℕ) : Slot :=
  (((drawSlot C).append (roundsSlot C (2 ^ ρ) m)).append
    (saySlot (Fin nside → Vector C (2 ^ ρ)))).append (drawsSlot C ρ)

/-- The error of one layer, with the combiner's error given: `2 ^ ρ · u` on each round and `u`
on each combination challenge. -/
abbrev stepErrors (nside ρ m : ℕ) (combiner u : ℝ≥0) :
    Errors (stepSlot C nside ρ m).tree (stepSlot C nside ρ m).roles :=
  Errors.append _ _ (Errors.append _ _ (Errors.append (drawSlot C).tree (drawSlot C).roles
    (drawErrors C combiner) (roundsErrors C (2 ^ ρ) (((2 ^ ρ : ℕ) : ℝ≥0) * u) m))
    (sayErrors _)) (drawsErrors C u ρ)

/-- `k` layers of radix four from depth `m`. -/
def stepsSlot (nside : ℕ) : ℕ → ℕ → Slot
  | 0, _ => doneSlot
  | k + 1, m => (stepSlot C nside 2 m).append (stepsSlot nside k (m + 2))

/-- The error of `k` layers of radix four: `(nside − 1) · u` on each combiner. -/
def stepsErrors (nside : ℕ) (u : ℝ≥0) :
    (k m : ℕ) → Errors (stepsSlot C nside k m).tree (stepsSlot C nside k m).roles
  | 0, _ => doneErrors
  | k + 1, m => Errors.append (stepSlot C nside 2 m).tree (stepSlot C nside 2 m).roles
      (stepErrors C nside 2 m (((nside - 1 : ℕ) : ℝ≥0) * u) u) (stepsErrors nside u k (m + 2))

/-- The binary layer at the roots, present when `μ` is odd (`r = μ mod 2`). -/
def oddSlot (nside : ℕ) : ℕ → Slot
  | 0 => doneSlot
  | _ + 1 => stepSlot C nside 1 0

/-- The error of the binary layer. -/
def oddErrors (nside : ℕ) (u : ℝ≥0) :
    (r : ℕ) → Errors (oddSlot C nside r).tree (oddSlot C nside r).roles
  | 0 => doneErrors
  | _ + 1 => stepErrors C nside 1 0 (((nside - 1 : ℕ) : ℝ≥0) * u) u

/-- The grand-product argument for `nside` trees of `2 ^ μ` leaves, from the roots down: one
binary layer first when `μ` is odd, then layers of radix four. -/
abbrev gkrSlot (nside μ : ℕ) : Slot := (oddSlot C nside (μ % 2)).append (stepsSlot C nside (μ / 2) (μ % 2))

/-- The error of the grand-product argument: `(nside − 1) · u` on each combiner, `2 ^ ρ · u` on
each round of radix `2 ^ ρ`, `u` on each combination challenge. -/
abbrev gkrErrors (u : ℝ≥0) (nside μ : ℕ) :
    Errors (gkrSlot C nside μ).tree (gkrSlot C nside μ).roles :=
  Errors.append (oddSlot C nside (μ % 2)).tree (oddSlot C nside (μ % 2)).roles
    (oddErrors C nside u (μ % 2)) (stepsErrors C nside u (μ / 2) (μ % 2))

/-! ## Bounds along a path -/

/-- No error on the empty slot. -/
theorem doneErrors_bounded : Errors.Bounded doneSlot.tree doneSlot.roles doneErrors 0 :=
  fun _ ↦ le_rfl

/-- No error on a message. -/
theorem sayErrors_bounded (M : Type) : Errors.Bounded (sayTree M) (sayRoles M) (sayErrors M) 0 :=
  fun _ ↦ le_rfl

omit [SampleableType C] in
/-- A challenge's error. -/
theorem drawErrors_bounded (e : ℝ≥0) : Errors.Bounded (drawTree C) (drawRoles C) (drawErrors C e) e :=
  fun _ ↦ le_of_eq (add_zero e)

/-- A round's error. -/
theorem roundErrors_bounded (d : ℕ) (e : ℝ≥0) :
    Errors.Bounded (roundSlot C d).tree (roundSlot C d).roles (roundErrors C d e) e :=
  ((sayErrors_bounded _).append (drawErrors_bounded C e)).mono (zero_add e).le

/-- `m` rounds' errors: `m · e`. -/
theorem roundsErrors_bounded (d : ℕ) (e : ℝ≥0) : (m : ℕ) →
    Errors.Bounded (roundsSlot C d m).tree (roundsSlot C d m).roles (roundsErrors C d e m) (m * e)
  | 0 => doneErrors_bounded.mono (by simp)
  | m + 1 => ((roundErrors_bounded C d e).append (roundsErrors_bounded d e m)).mono
      (le_of_eq (by push_cast; ring))

/-- `k` challenges' errors: `k · e`. -/
theorem drawsErrors_bounded (e : ℝ≥0) : (k : ℕ) →
    Errors.Bounded (drawsSlot C k).tree (drawsSlot C k).roles (drawsErrors C e k) (k * e)
  | 0 => doneErrors_bounded.mono (by simp)
  | k + 1 => ((drawsErrors_bounded e k).append (drawErrors_bounded C e)).mono
      (le_of_eq (by push_cast; ring))

/-- One layer's errors: the combiner's, `2 ^ ρ · u` per round, `u` per combination challenge. -/
theorem stepErrors_bounded (nside ρ m : ℕ) (combiner u : ℝ≥0) :
    Errors.Bounded (stepSlot C nside ρ m).tree (stepSlot C nside ρ m).roles
      (stepErrors C nside ρ m combiner u) (combiner + m * (((2 ^ ρ : ℕ) : ℝ≥0) * u) + ρ * u) :=
  ((((drawErrors_bounded C combiner).append (roundsErrors_bounded C (2 ^ ρ) _ m)).append
    (sayErrors_bounded _)).append (drawsErrors_bounded C u ρ)).mono (le_of_eq (by ring))

/-- `k` layers of radix four from depth `m`. -/
theorem stepsErrors_bounded (nside : ℕ) (u : ℝ≥0) : (k m : ℕ) →
    Errors.Bounded (stepsSlot C nside k m).tree (stepsSlot C nside k m).roles
      (stepsErrors C nside u k m) (((k * ((nside - 1) + (m + 2 * k) * 4 + 2) : ℕ) : ℝ≥0) * u)
  | 0, _ => doneErrors_bounded.mono (by simp)
  | k + 1, m => by
    refine ((stepErrors_bounded C nside 2 m _ u).append (stepsErrors_bounded nside u k (m + 2))).mono ?_
    have hnat : (nside - 1) + m * 2 ^ 2 + 2 + k * ((nside - 1) + (m + 2 + 2 * k) * 4 + 2) ≤
        (k + 1) * ((nside - 1) + (m + 2 * (k + 1)) * 4 + 2) := by
      nlinarith
    calc _ = (((nside - 1) + m * 2 ^ 2 + 2 + k * ((nside - 1) + (m + 2 + 2 * k) * 4 + 2) : ℕ) :
          ℝ≥0) * u := by
          push_cast
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hnat) zero_le

/-- The binary layer. -/
theorem oddErrors_bounded (nside : ℕ) (u : ℝ≥0) : (r : ℕ) →
    Errors.Bounded (oddSlot C nside r).tree (oddSlot C nside r).roles (oddErrors C nside u r)
      ((((nside - 1) + 1 : ℕ) : ℝ≥0) * u)
  | 0 => doneErrors_bounded.mono zero_le
  | _ + 1 => (stepErrors_bounded C nside 1 0 _ u).mono (le_of_eq (by push_cast; ring))

/-- **The grand-product argument's errors**: at most
`((μ + 1)(nside − 1) + 2μ² + 3μ + 3) · u` along every path. -/
theorem gkrErrors_bounded (u : ℝ≥0) (nside μ : ℕ) :
    Errors.Bounded (gkrSlot C nside μ).tree (gkrSlot C nside μ).roles (gkrErrors C u nside μ)
      ((((μ + 1) * (nside - 1) + 2 * μ * μ + 3 * μ + 3 : ℕ) : ℝ≥0) * u) := by
  refine ((oddErrors_bounded C nside u (μ % 2)).append
    (stepsErrors_bounded C nside u (μ / 2) (μ % 2))).mono ?_
  have hnat : (nside - 1) + 1 + μ / 2 * ((nside - 1) + (μ % 2 + 2 * (μ / 2)) * 4 + 2) ≤
      (μ + 1) * (nside - 1) + 2 * μ * μ + 3 * μ + 3 := by
    rw [Nat.mod_add_div μ 2]
    have hk : μ / 2 * 2 ≤ μ := Nat.div_mul_le_self μ 2
    nlinarith [Nat.mul_le_mul_right (nside - 1) hk, Nat.mul_le_mul_right μ hk]
  calc _ = (((nside - 1) + 1 + μ / 2 * ((nside - 1) + (μ % 2 + 2 * (μ / 2)) * 4 + 2) : ℕ) :
        ℝ≥0) * u := by
        push_cast
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hnat) zero_le

end
end LeanVM.Protocol.Typed
