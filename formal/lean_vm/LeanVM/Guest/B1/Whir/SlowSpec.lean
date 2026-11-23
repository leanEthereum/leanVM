/-
  LeanVM.Guest.B1.Whir.SlowSpec

  What `open_stacked` takes of `level_residual_slow`: the unfactored sum over a level's queries,
  read at its zero flag.
-/

module

public import LeanVM.Guest.B1.Whir.ResQuery
public import LeanVM.Guest.B1.Whir.IsZeroDef

/-!
# The slow residual, as `open_stacked` reads it

A non-final level whose challenges' product is zero has no factored residual: its coefficients
`b_t = c_t·inv_t` vanish somewhere, so `open_stacked` divides by `1` and scales the factored sum by
zero. Its residual is then `level_residual_slow`'s value, `λ²·Σ_k λ^k·Π_t (1 + c_t + c_t·inv_t·
chain_t(x_k))` over its `Q` positions `x_k` (`slowVal`), and `0` on every other level.

* `zeroOf a`: `is_zero`'s value, `1` at `a = 0`, else `0` (`MeaningIsZero`, `zeroOf_of_meaning`).
* `slowQuery vals inv cs n x`: `residual_query_slow`'s product at `x`.
* `SlowRet Q pre yr vo`: on `[positions, fold_cs, tail_cs, λ, z]`, for the positions and challenges
  read there, the value `slowVal`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value

@[expose] public section

/-- `is_zero`'s value. -/
def zeroOf (a : E) : E := if a = 0 then 1 else 0

/-- **`is_zero`'s meaning, as `open_stacked` reads it**: it returns `zeroOf` of its word. -/
theorem zeroOf_of_meaning {w r : E} (h : MeaningIsZero [w] [r]) : r = zeroOf w := (List.cons.inj h).1

/-- `is_zero` on every word, at the relations `H` admits. -/
def IsZeroC (H : CallRel → Reader → Prop) : Prop := ∀ C rd, H C rd → ∀ w, C "is_zero" [w] [zeroOf w]

/-- `residual_query_slow`'s product at the position `x`, over the challenges `cs` and the
vanishing inverses `inv`. -/
def slowQuery (vals : List E) (inv cs : ℕ → E) (n : ℕ) (x : E) : E :=
  ∏ t ∈ Finset.range n, (1 + cs t + cs t * inv t * residualChain vals x t)

/-- `level_residual_slow`'s value at the zero flag `z`: `0` at `z = 0`, else the unfactored sum
over the `Q` positions `pos`. -/
def slowVal (Q n vo : ℕ) (pos cs : ℕ → E) (lam z : E) : E :=
  if z = 0 then 0 else
    lam ^ 2 * ∑ k ∈ Finset.range Q, lam ^ k *
      slowQuery (osVals vo n) (fun t ↦ word (vanishInv (vo + t)) 0) cs n (pos k)

/-- **What `open_stacked` takes of `level_residual_slow__L{Q}_L{pre}_L{yr}_L{vo}`**: on
`[positions, fold_cs, tail_cs, λ, z]`, the `Q` positions at `positions`, the `pre` fold challenges at
`fold_cs` and the `yr` tail challenges at `tail_cs` read, it returns `slowVal`. -/
def SlowRet (Q pre yr vo : ℕ) (rd : Reader) (args rets : List E) : Prop :=
  ∀ (pos cs : ℕ → E), (∀ k < Q, LoadHolds rd (args.getD 0 0) k (pos k)) →
    (∀ t < pre, LoadHolds rd (args.getD 1 0) t (cs t)) →
    (∀ j < yr, LoadHolds rd (args.getD 2 0) j (cs (pre + j))) →
    rets = [slowVal Q (pre + yr) vo pos cs (args.getD 3 0) (args.getD 4 0)]

theorem slowVal_congr {Q n vo : ℕ} {pos pos' cs cs' : ℕ → E} (lam z : E)
    (hp : ∀ k < Q, pos k = pos' k) (hc : ∀ t < n, cs t = cs' t) :
    slowVal Q n vo pos cs lam z = slowVal Q n vo pos' cs' lam z := by
  unfold slowVal slowQuery
  split_ifs
  · rfl
  · rw [Finset.sum_congr rfl fun k hk ↦ by
      rw [hp k (Finset.mem_range.mp hk), Finset.prod_congr rfl fun t ht ↦ by
        rw [hc t (Finset.mem_range.mp ht)]]]

theorem zeroOf_01 (a : E) : zeroOf a = 0 ∨ zeroOf a = 1 := by
  unfold zeroOf; split_ifs <;> simp

theorem zeroOf_eq_zero {a : E} (h : a ≠ 0) : zeroOf a = 0 := by simp [zeroOf, h]

theorem zeroOf_eq_one {a : E} (h : a = 0) : zeroOf a = 1 := by simp [zeroOf, h]

/-- `μ` at `λ`: `1/λ`, and `1` at `λ = 0`. -/
def lamInvOf (lam : E) : E := (lam + zeroOf lam)⁻¹

theorem lamAdd_ne (lam : E) : lam + zeroOf lam ≠ 0 := by
  by_cases h : lam = 0
  · rw [zeroOf_eq_one h, h, zero_add]; exact one_ne_zero
  · rw [zeroOf_eq_zero h, add_zero]; exact h

theorem lam_mul_lamInvOf {lam : E} (h : lam ≠ 0) : lam * lamInvOf lam = 1 := by
  have e : lam + zeroOf lam = lam := by rw [zeroOf_eq_zero h, add_zero]
  have e2 := mul_inv_cancel₀ h
  show lam * (lam + zeroOf lam)⁻¹ = 1
  rw [e]
  exact e2

theorem lamInvOf_mul (lam : E) : lamInvOf lam * (lam + zeroOf lam) = 1 := by
  have e := inv_mul_cancel₀ (lamAdd_ne lam)
  exact e

/-- The coefficient's divisor at a zero flag: the coefficient where the product is not zero,
else `1`. -/
theorem coef_div_ne {b z : E} (h : (z = 0 ∧ b ≠ 0) ∨ z = 1) : b * (1 + z) + z ≠ 0 := by
  rcases h with ⟨rfl, hb⟩ | rfl
  · simpa using hb
  · rw [CharTwo.add_self_eq_zero, mul_zero, zero_add]; exact one_ne_zero

end
end LeanVM.Guest.B1.Whir
