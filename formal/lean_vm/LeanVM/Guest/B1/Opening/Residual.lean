/-
  LeanVM.Guest.B1.Opening.Residual

  The values of the guest's inline `residual_query` (the subspace chain and the prefix product),
  and the factoring of the induced weight's coordinates they rest on.
-/

module

public import LeanVM.Guest.B1.Common.Atoms

/-!
# `residual_query` (G:1462-1479)

`residual_query(position, row_d, hs, vanish, n_cols, n_hs, hs_bits)` walks the chain
`chain_0 = x` (the position), `chain_(t+1) = chain_t·(chain_t + VALS[vanish + t])` (`LIG_VANISH_VALS`,
the subspace roots: `residualChain`), and returns the prefix product `Π_(t < n_cols) (d_t + chain_t)`
over the row `d_t = row_d[t]` (`residualProd`) and the high part's share
`chain_(n_cols)·novel_eval(hs, chain_0 .. chain_2)`. The template and its soundness are
`Whir.osResQuery` and `Whir.osResQuery_val` (`Whir/ResQuery.lean`); `NovelEval.residual_high_eq`
reads the share against the verifier.

* `residual_factor`: `1 + c·(1 + x·inv) = (c·inv)·((1 + c)/(c·inv) + x)` when `c·inv ≠ 0`, so the
  product of `inducedWeight`'s factors (V:1715) at one query is `Π_t (c_t·inv_t)` (the level's
  scale, `open_stacked`'s `level_scale`) times the prefix product at `d_t = (1 + c_t)/(c_t·inv_t)`
  (`basis_d`): `residual_prod`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- The subspace-vanishing walk from the position `x`. -/
def residualChain (vals : List E) (x : E) : ℕ → E
  | 0 => x
  | t + 1 => residualChain vals x t * (residualChain vals x t + vals.getD t 0)

/-- `Π_{t<n} (d_t + chain_t)`, left to right. -/
def residualProd (vals : List E) (x : E) (d : ℕ → E) : ℕ → E
  | 0 => 1
  | n + 1 => residualProd vals x d n * (d n + residualChain vals x n)

/-! ## The factoring -/

/-- **A coordinate's factor** (G:1638-1646): `1 + c·(1 + x·inv) = (c·inv)·((1 + c)/(c·inv) + x)`. -/
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

end
end LeanVM.Guest.B1
