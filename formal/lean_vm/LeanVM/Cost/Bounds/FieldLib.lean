module

public import LeanVM.Cost.Bounds.Basic
public import LeanVM.Cost.Extractor.GsRun

/-!
# Bounds: the field's functions, compiled

One bound per function of `K = GF(2^64)` (CompPoly's `BF64`, `Cost/Rules.lean`'s `powSq`) as the
extractor's chain compiles it, for every bound that calls it:

* `powTwoPow_cost`: `a^(2^k)` by `k` squarings, `5 + 39·k` exactly (a square is a call of the
  compiled product `kMulC`, price `27`);
* **`invK_cost`**: the inverse (Itoh–Tsujii), at most `2823`;
* `powSq_cost`: `a^n` by squaring, `73` per bit and `5` (`powSq_cost_le`, `powSq_cost_le'`: for
  `n ≤ 3`, `n ≤ 15`).
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Cost LeanVM.Cost.Library LeanVM.Parameters

public section

variable (P : MachineProgram)

/-- `a^(2^k)` by `k` squarings (`powTwoPow.c11`): `5 + 39·k` exactly. -/
theorem powTwoPow_cost (hP : Includes P Auto.BF64.powTwoPow.c11.costDeps) :
    ∀ (k : ℕ) (a : BF64), k < 2 ^ 64 →
      machineCost P Auto.BF64.powTwoPow.c11.costIdx [encodeValue a, encodeValue k] = 5 + 39 * k := by
  intro k
  induction k with
  | zero => intro a _; rw [Auto.BF64.powTwoPow.c11.costEq_zero P hP]
  | succ k ih =>
    intro a hk
    rw [Auto.BF64.powTwoPow.c11.costEq_succ P hP, ih (a * a) (by omega)]
    cost_simp
    omega

/-- **The inverse in `K`** (Itoh–Tsujii, `invItohTsujii.c10`): at most `2823`. -/
theorem invK_cost (hP : Includes P Auto.BF64.invItohTsujii.c10.costDeps) (a : BF64) :
    machineCost P Auto.BF64.invItohTsujii.c10.costIdx [encodeValue a] ≤ 2823 := by
  have h6 : Includes P Auto.BF64.powTwoPow.c11.costDeps := by includes
  rw [Auto.BF64.invItohTsujii.c10.costEq P hP]
  simp (disch := omega) only [powTwoPow_cost P h6]
  split_ifs <;> omega

/-- `a^n` by squaring (`powSq.c101`): `73` per bit, `5` at the end. -/
theorem powSq_cost (hP : Includes P Auto.LeanVM.Cost.Rewrite.powSq.c101.costDeps) (a : K) (n : ℕ)
    (hn : n < 2 ^ 64) :
    machineCost P Auto.LeanVM.Cost.Rewrite.powSq.c101.costIdx [encodeValue a, encodeValue n] ≤
      5 + 73 * (Nat.log2 n + 1) := by
  have := le_of_halving (fun x : K × ℕ ↦ x.2 < 2 ^ 64) (fun x ↦ x.2)
    (fun x ↦ machineCost P Auto.LeanVM.Cost.Rewrite.powSq.c101.costIdx [encodeValue x.1, encodeValue x.2]) 73 5
    (fun x hx h0 ↦ by
      rw [Auto.LeanVM.Cost.Rewrite.powSq.c101.costEq P hP, h0]
      simp)
    (fun x hx hpos ↦ by
      right
      refine ⟨(x.1 * x.1, x.2 / 2), by dsimp only; omega, le_refl _, ?_⟩
      rw [Auto.LeanVM.Cost.Rewrite.powSq.c101.costEq P hP, limbs_of_lt hx,
        limbs_of_lt (by omega : x.2 % 2 < 2 ^ 64)]
      simp only [show x.2 ≠ 0 by omega, ↓reduceIte]
      split_ifs <;> omega)
    (a, n) hn
  simpa using this

theorem powSq_cost_le (hP : Includes P Auto.LeanVM.Cost.Rewrite.powSq.c101.costDeps) (a : K) (n : ℕ)
    (hn : n ≤ 3) : machineCost P Auto.LeanVM.Cost.Rewrite.powSq.c101.costIdx [encodeValue a, encodeValue n] ≤ 151 := by
  refine (powSq_cost P hP a n (by omega)).trans ?_
  have := log2_lt_of (k := 2) (by norm_num) (by omega : n < 2 ^ 2)
  omega

theorem powSq_cost_le' (hP : Includes P Auto.LeanVM.Cost.Rewrite.powSq.c101.costDeps) (a : K) (n : ℕ)
    (hn : n ≤ 15) : machineCost P Auto.LeanVM.Cost.Rewrite.powSq.c101.costIdx [encodeValue a, encodeValue n] ≤ 297 := by
  refine (powSq_cost P hP a n (by omega)).trans ?_
  have := log2_lt_of (k := 4) (by norm_num) (by omega : n < 2 ^ 4)
  omega

end

end LeanVM.Cost.Bounds
