/-
  LeanVM.Protocol.Hotwire.ShiftEq

  The shifted equality weight summed out: the verifier's `shift_eq` recurrence, and the prover's
  `ShiftEq` fold.
-/

module

public import LeanVM.Protocol.Hotwire.Eq
import Mathlib.Tactic.Ring

/-!
# The shift weight

The state link weighs each row's successor state at cycle `j` by `eq(ζ, j + 1)`, for `j + 1 < 2^n`
(`crates/verifier/src/link.rs`'s module docstring). Over a commutative ring `F`:

* `shiftEq_eq_shiftSum`: the verifier's `shift_eq` recurrence (`shiftEq`) is
  `P(ζ, r) = Σ_{j + 1 < 2^n} eq(r, j)·eq(ζ, j + 1)` (`shiftSum`). Its one step is
  `shiftSum_cons`: split on the lowest bit of `j`; the even `j` carry nothing into the next bit,
  the odd ones carry one;
* `shiftEq_of_charTwo`: in characteristic two `shiftEq` is the Rust's loop as written,
  `shift := shift·(1 + z + x) + carry·(1 + x)·z`, `carry *= x·(1 + z)`;
* `shiftForm_fold`: the prover's table `j ↦ a·eq(ζ, j) + b·eq(ζ, j + 1)·[j + 1 < 2^n]`
  (`ShiftEq::at`, `crates/lean_vm_core/src/link/index.rs`) with its lowest
  variable bound at `x` is the same form over the other `n − 1` variables, with the coefficients
  `ShiftEq::fold` computes.
-/

namespace LeanVM.Protocol.Hotwire

open Finset

@[expose] public section

variable {F : Type*} [CommRing F]

/-- `P(ζ, r) = Σ_{j + 1 < 2^n} eq(r, j)·eq(ζ, j + 1)` for `ζ` of `n` coordinates: `eq(ζ, ·)`
shifted down by one, at `r`. The verifier's test `shift_eq_is_the_shifted_eq_summed_out`
evaluates this sum. -/
def shiftSum (ζ r : List F) : F :=
  ∑ j ∈ range (2 ^ ζ.length), if j + 1 < 2 ^ ζ.length then eqAt r j * eqAt ζ (j + 1) else 0

/-- One step of the verifier's `shift_eq`, on `(shift, carry)` at the coordinates `(ζ_h, r_h)`:
`shift := shift·eq(ζ_h, r_h) + carry·(1 − r_h)·ζ_h`, then `carry := carry·r_h·(1 − ζ_h)` (with the
old `carry` in the first). In characteristic two, as the Rust writes it, `shift·(1 + z + x) +
carry·(1 + x)·z` and `carry·x·(1 + z)` (`shiftStep_of_charTwo`). -/
def shiftStep (acc : F × F) (zx : F × F) : F × F :=
  (acc.1 * eq1 zx.1 zx.2 + acc.2 * (1 - zx.2) * zx.1, acc.2 * zx.2 * (1 - zx.1))

/-- The verifier's `shift_eq(zeta, r)`: `shiftStep` over the coordinates in order, from
`shift = 0`, `carry = 1`. -/
def shiftEq (ζ r : List F) : F := ((ζ.zip r).foldl shiftStep (0, 1)).1

/-- `shiftStep` as the Rust writes it, in characteristic two. -/
theorem shiftStep_of_charTwo [CharP F 2] (s c z x : F) :
    shiftStep (s, c) (z, x) = (s * (1 + z + x) + c * (1 + x) * z, c * x * (1 + z)) := by
  simp only [shiftStep, eq1_of_charTwo, CharTwo.sub_eq_add]

/-- **`shift_eq` as the Rust writes it** (`crates/verifier/src/link.rs`), in characteristic two:
the loop over `zeta.iter().zip(r)` from `(shift, carry) = (0, 1)`, `shift := shift·(1 + z + x) +
carry·(1 + x)·z`, `carry *= x·(1 + z)`. -/
theorem shiftEq_of_charTwo [CharP F 2] (ζ r : List F) :
    shiftEq ζ r = ((ζ.zip r).foldl (fun acc zx ↦ (acc.1 * (1 + zx.1 + zx.2) +
      acc.2 * (1 + zx.2) * zx.1, acc.2 * (zx.2 * (1 + zx.1)))) (0, 1)).1 := by
  have h : (shiftStep : F × F → F × F → F × F) = fun acc zx ↦ (acc.1 * (1 + zx.1 + zx.2) +
      acc.2 * (1 + zx.2) * zx.1, acc.2 * (zx.2 * (1 + zx.1))) := by
    funext ⟨s, c⟩ ⟨z, x⟩
    rw [shiftStep_of_charTwo, mul_assoc c x]
  rw [shiftEq, h]

/-- `Π_h r_h·(1 − ζ_h)`: the weight of every bit carrying, the final `carry`. -/
def shiftCarry : List F → List F → F
  | z :: zs, x :: xs => x * (1 - z) * shiftCarry zs xs
  | _, _ => 1

@[simp] theorem shiftSum_nil (r : List F) : shiftSum [] r = 0 := by simp [shiftSum]

/-- The sum's one step, on its lowest coordinate: an even `j = 2j'` gives `j + 1 = 2j' + 1`,
weight `(1 − x)·z·eq(r', j')·eq(ζ', j')`; an odd `j = 2j' + 1` gives `j + 1 = 2(j' + 1)`, weight
`x·(1 − z)·eq(r', j')·eq(ζ', j' + 1)`, a carry. -/
theorem shiftSum_cons (z x : F) (ζ r : List F) (h : ζ.length = r.length) :
    shiftSum (z :: ζ) (x :: r) = (1 - x) * z * eqPt ζ r + x * (1 - z) * shiftSum ζ r := by
  rw [← sum_eqAt_mul_eqAt ζ r h, shiftSum, shiftSum, mul_sum, mul_sum, ← sum_add_distrib,
    List.length_cons, pow_succ, mul_comm _ 2, sum_range_two_mul]
  refine sum_congr rfl fun j hj => ?_
  have hj : j < 2 ^ ζ.length := mem_range.mp hj
  have h1 : 2 * j + 1 < 2 * 2 ^ ζ.length := by omega
  have h2 : 2 * j + 1 + 1 < 2 * 2 ^ ζ.length ↔ j + 1 < 2 ^ ζ.length := by omega
  rw [ite_eq_left h1, show 2 * j + 1 + 1 = 2 * (j + 1) by ring, eqAt_cons_two_mul,
    eqAt_cons_two_mul_add_one, eqAt_cons_two_mul_add_one]
  by_cases h3 : j + 1 < 2 ^ ζ.length
  · rw [ite_eq_left (by omega), ite_eq_left h3, eqAt_cons_two_mul]; ring
  · rw [ite_eq_right (by omega), ite_eq_right h3]; ring

/-- `shift_eq`'s loop from any `(shift, carry)`: `(shift·eq(ζ, r) + carry·P(ζ, r),
carry·Π_h r_h·(1 − ζ_h))`. -/
theorem foldl_shiftStep : ∀ (ζ r : List F), ζ.length = r.length → ∀ s c : F,
    (ζ.zip r).foldl shiftStep (s, c) = (s * eqPt ζ r + c * shiftSum ζ r, c * shiftCarry ζ r)
  | [], [], _, s, c => by simp [shiftCarry]
  | z :: ζ, x :: r, h, s, c => by
    have h' : ζ.length = r.length := by simpa using h
    rw [List.zip_cons_cons, List.foldl_cons, shiftStep, foldl_shiftStep ζ r h', eqPt_cons,
      shiftSum_cons z x ζ r h', shiftCarry]
    simp only [Prod.mk.injEq]
    constructor <;> ring
  | [], _ :: _, h, _, _ => by simp at h
  | _ :: _, [], h, _, _ => by simp at h

/-- **The verifier's `shift_eq` is the shift weight**: for `ζ`, `r` of `n` coordinates, the
recurrence `shift := shift·eq(ζ_h, r_h) + carry·(1 − r_h)·ζ_h`, `carry := carry·r_h·(1 − ζ_h)`
from `shift = 0`, `carry = 1` ends at `Σ_{j + 1 < 2^n} eq(r, j)·eq(ζ, j + 1)`. -/
theorem shiftEq_eq_shiftSum (ζ r : List F) (h : ζ.length = r.length) : shiftEq ζ r = shiftSum ζ r := by
  rw [shiftEq, foldl_shiftStep ζ r h]
  ring

/-- The prover's table `a·eq(ζ, j) + b·eq(ζ, j + 1)·[j + 1 < 2^n]` over `j < 2^n`, `n = |ζ|`:
`ShiftEq::at` (`crates/lean_vm_core/src/link/index.rs`), `ShiftEq::new(a, b,
ζ)`'s values. -/
def shiftForm (a b : F) (ζ : List F) (j : ℕ) : F :=
  a * eqAt ζ j + if j + 1 < 2 ^ ζ.length then b * eqAt ζ (j + 1) else 0

/-- The verifier's sum weighs the prover's table at `(a, b) = (0, 1)`. -/
theorem shiftSum_eq_sum_shiftForm (ζ r : List F) :
    shiftSum ζ r = ∑ j ∈ range (2 ^ ζ.length), eqAt r j * shiftForm 0 1 ζ j := by
  simp [shiftSum, shiftForm, mul_ite]

/-- **The prover's fold** (`ShiftEq::fold`): binding the lowest variable of the table at `x`,
the table `j' ↦ (1 − x)·f(2j') + x·f(2j' + 1)` over the other `n − 1` variables, gives the same
form over `ζ' = ζ_1, …` with `a' = a·eq(ζ_0, x) + b·ζ_0·(1 − x)` and `b' = b·x·(1 − ζ_0)`. In
characteristic two these read `a·(1 + ζ_0 + x) + b·ζ_0·(1 + x)` and `b·x·(1 + ζ_0)`, as the
code writes them (`eq1_of_charTwo`). -/
theorem shiftForm_fold (a b z x : F) (ζ : List F) (j : ℕ) (hj : j < 2 ^ ζ.length) :
    (1 - x) * shiftForm a b (z :: ζ) (2 * j) + x * shiftForm a b (z :: ζ) (2 * j + 1) =
      shiftForm (a * eq1 z x + b * z * (1 - x)) (b * x * (1 - z)) ζ j := by
  unfold shiftForm
  rw [List.length_cons, pow_succ, mul_comm _ 2, ite_eq_left (by omega : 2 * j + 1 < 2 * 2 ^ ζ.length),
    show 2 * j + 1 + 1 = 2 * (j + 1) by ring, eqAt_cons_two_mul, eqAt_cons_two_mul_add_one]
  unfold eq1
  by_cases h3 : j + 1 < 2 ^ ζ.length
  · rw [ite_eq_left (by omega), ite_eq_left h3, eqAt_cons_two_mul]; ring
  · rw [ite_eq_right (by omega), ite_eq_right h3]; ring

end

end LeanVM.Protocol.Hotwire
