/-
  LeanVM.Guest.B1.Opening.Residual

  The expansion of the guest's inline `residual_query`, and the factoring of the induced weight's
  coordinates it rests on.
-/

module

public import LeanVM.Guest.B1.Common.Atoms

/-!
# `residual_query` (G:1419-1427, TRIAGE #41)

`residual_query(basis_chain, row_d, vanish, n)` is `Π_{t<n} (d_t + chain_t)` over the row
`d_t = row_d[t]`, `chain_0` the query position and
`chain_{t+1} = chain_t·(chain_t + VALS[vanish + t])` (`LIG_VANISH_VALS`, the subspace roots,
`subspaceRoots`, V:1709). Its expansion from the value `b`, the position at `x`, the row at `r`
and the constants `vals` (`open_stacked`'s query loops number it) is `residualT x r vals b`.

* `residualT_sound`: the template's value is `Π_{t<n} (d_t + chain_t)`.
* `residual_factor`: `1 + c·(1 + x·inv) = (c·inv)·((1 + c)/(c·inv) + x)` when `c·inv ≠ 0`, so the
  product of `inducedWeight`'s factors (V:1715) at one query is `Π_t (c_t·inv_t)` (the level's
  scale, `open_stacked`'s `level_scale`) times the template's value at `d_t = (1 + c_t)/(c_t·inv_t)`
  (`basis_d`, G:1706-1714): `residual_prod`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader} {σ : Val}

/-- Coordinate `t + 1`'s block (`t < vals.length`) from its first value `B = b + 2 + 6t`. -/
def residualBlkT (x r : V) (vals : List E) (b t : ℕ) : List Stmt :=
  let B := b + 2 + 6 * t
  let chainPrev : V := if t = 0 then x else .n (B - 4)
  let prefixPrev : V := if t = 0 then .n (b + 1) else .n (B - 1)
  [.atom (.const (.n B) (vals.getD t 0)), .atom (.add (.n (B + 1)) chainPrev (.n B)),
    .atom (.mul (.n (B + 2)) chainPrev (.n (B + 1))), .atom (.load (.n (B + 3)) r (t + 1)),
    .atom (.add (.n (B + 4)) (.n (B + 3)) (.n (B + 2))), .atom (.mul (.n (B + 5)) prefixPrev (.n (B + 4)))]

/-- **`residual_query(position, row_d, vanish, vals.length + 1)`** from the value `b`. -/
def residualT (x r : V) (vals : List E) (b : ℕ) : List Stmt :=
  [.atom (.load (.n b) r 0), .atom (.add (.n (b + 1)) (.n b) x)] ++
    ((List.range vals.length).map (residualBlkT x r vals b)).flatten

/-- The value `residual_query` returns. -/
def residualV (b n : ℕ) : ℕ := if n = 0 then b + 1 else b + 2 + 6 * (n - 1) + 5

/-- The subspace-vanishing walk from the position `x`. -/
def residualChain (vals : List E) (x : E) : ℕ → E
  | 0 => x
  | t + 1 => residualChain vals x t * (residualChain vals x t + vals.getD t 0)

/-- `Π_{t<n} (d_t + chain_t)`, left to right. -/
def residualProd (vals : List E) (x : E) (d : ℕ → E) : ℕ → E
  | 0 => 1
  | n + 1 => residualProd vals x d n * (d n + residualChain vals x n)

/-! ## The factoring -/

/-- **A coordinate's factor** (G:1684-1692): `1 + c·(1 + x·inv) = (c·inv)·((1 + c)/(c·inv) + x)`. -/
theorem residual_factor {c inv x : E} (h : c * inv ≠ 0) :
    1 + c * (1 + x * inv) = c * inv * ((1 + c) / (c * inv) + x) := by
  have e : c * inv * ((1 + c) / (c * inv)) = 1 + c := mul_div_cancel₀ _ h
  rw [mul_add (c * inv), e]
  ring

/-- **The product of `inducedWeight`'s factors** (V:1715) at one query is the level's scale times
`residual_query`'s value at `d_t = (1 + c_t)/(c_t·inv_t)`. -/
theorem residual_prod (vals : List E) (x : E) (c inv : ℕ → E) (n : ℕ)
    (h : ∀ t < n, c t * inv t ≠ 0) :
    (∏ t ∈ Finset.range n, (1 + c t * (1 + residualChain vals x t * inv t))) =
      (∏ t ∈ Finset.range n, (c t * inv t)) *
        residualProd vals x (fun t ↦ (1 + c t) / (c t * inv t)) n := by
  induction n with
  | zero => simp [residualProd]
  | succ n ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ, ih (fun t ht => h t (by omega)),
      residual_factor (h n (by omega)), residualProd]
    ring

/-! ## The honest values -/

/-- The honest value at offset `o` of `residualT`: `d_0`, `d_0 + x`, then per coordinate `t + 1`
the constant, `chain_t + c`, `chain_{t+1}`, `d_{t+1}`, `d_{t+1} + chain_{t+1}`, the product. -/
def residualVal (vals : List E) (x : E) (d : ℕ → E) (o : ℕ) : E :=
  if o = 0 then d 0 else if o = 1 then d 0 + x
  else
    let t := (o - 2) / 6
    [vals.getD t 0, residualChain vals x t + vals.getD t 0, residualChain vals x (t + 1), d (t + 1),
      d (t + 1) + residualChain vals x (t + 1), residualProd vals x d (t + 2)].getD ((o - 2) % 6) 0

end
end LeanVM.Guest.B1
