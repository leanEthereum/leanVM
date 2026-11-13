module

public import LeanVM.Cost.Bounds.PMSolve.Lift
import all CompPoly.Univariate.Raw.Core
import all CompPoly.Univariate.Raw.Ops
import all CompPoly.Univariate.Raw.Division
import all CompPoly.Univariate.Basic
import all CompPoly.LinearAlgebra.PolynomialMatrix.Basic
import all CompPoly.LinearAlgebra.PolynomialMatrix.Operations
import all LeanVM.Protocol.Extraction.Fast.GSData

/-!
# Bounds: the remainders of the GS data, compiled

The GS data's remainders: the reversal remainder with the reversed modulus's inverse supplied
(`modByMonicCachedC`, `rawModByMonicCached`), on its first branch (dividend shorter than the
modulus: the guard only) or on its cached branch (precision `k ≤ K`: two truncated products, two
reversals, a subtraction, no Newton iteration): **`modByMonicCachedC_cost`**, at most
`100·|p| + 200·|q| + LBq + LB + 600`, `LBq`, `LB` the two truncated products' prices
(`LowBound`: `rawMulLowFFTC`, a hypothesis). Also: `reverseC_cost`,
`modByMonicWithC_first_cost` (CompPoly's `modByMonicWith` on `fftModContext`'s first branch),
`limbCount_le_of_lt`.
-/

namespace LeanVM.Cost.Bounds.PMSolve

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Cost.Bounds.Decoder
open LeanVM.Cost.Extractor LeanVM.Parameters CompPoly LeanVM.Extraction.Fast
open CompPoly.PolynomialMatrix CompPoly.PolynomialMatrix.Approximant

open LeanVM.Cost.Auto.CompPoly.PolynomialMatrix

public section

/-- **The truncated product's price** (`rawMulLowFFTC`, a hypothesis): at precision
`k ≤ N`, at most `LB` (the factors are truncated to `k` first). -/
@[expose] def LowBound (P : MachineProgram) (N LB : ℕ) : Prop :=
  ∀ (k : ℕ) (a b : CPolynomial.Raw K), k ≤ N →
    machineCost P rawMulLowFFTC.costIdx [encodeValue k, encodeValue a, encodeValue b] ≤ LB

/-- **The product's price** (`mulViaFFTC`, `fftMulContext.mul`, a hypothesis): on
factors whose product has at most `N` coefficients (`|f| + |g| ≤ N + 1`), at most `MB`. -/
@[expose] def MulBound (P : MachineProgram) (N MB : ℕ) : Prop :=
  ∀ f g : CPolynomial K, f.val.size + g.val.size ≤ N + 1 →
    machineCost P mulViaFFTC.costIdx [encodeValue f, encodeValue g] ≤ MB

/-- **Newton's inverse's price** (`inverseModXFFTC`, a hypothesis): at precision
`k ≤ N`, at most `IB`. -/
@[expose] def InvBound (P : MachineProgram) (N IB : ℕ) : Prop :=
  ∀ (k : ℕ) (a : CPolynomial.Raw K), k ≤ N →
    machineCost P inverseModXFFTC.costIdx [encodeValue k, encodeValue a] ≤ IB

variable (P : MachineProgram)

/-- A number below `2^(64·L)` has at most `L` limbs. -/
theorem limbCount_le_of_lt {n L : ℕ} (hL : 1 ≤ L) (h : n < 2 ^ (64 * L)) : limbCount n ≤ L := by
  unfold limbCount
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.log2_zero]
    omega
  · have := (Nat.log2_lt (Nat.pos_iff_ne_zero.1 hn)).2 h
    omega

/-- `Raw.reverse n p`: at most `29·n + 15`. -/
theorem reverseC_cost (hP : Includes P Auto.CompPoly.CPolynomial.Raw.reverse.c421.costDeps)
    (n : ℕ) (hn : n < 2 ^ 62) (p : CPolynomial.Raw K) :
    machineCost P Auto.CompPoly.CPolynomial.Raw.reverse.c421.costIdx [encodeValue n, encodeValue p] ≤
      29 * n + 15 := by
  rw [Auto.CompPoly.CPolynomial.Raw.reverse.c421.costEq P hP]
  have hf := fun i ↦ RunsApp.of_spec (us := [encodeValue n, encodeValue p]) (vs := [encodeValue i])
    (Auto.CompPoly.CPolynomial.Raw.reverse.c421.lam0.costSpec P (by includes) n p i)
  have := ofFnFrom_cost P (by includes) (n := n) (by omega) _
    (.closure Auto.CompPoly.CPolynomial.Raw.reverse.c421.lam0.costIdx [encodeValue n, encodeValue p])
    hf 10 (fun i ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append]
      rw [Auto.CompPoly.CPolynomial.Raw.reverse.c421.lam0.costEq P (by includes)]
      have := i.isLt
      cost_simp
      omega) 0 (by omega)
  have hl := ofFnFrom_length (fun i : Fin n ↦ p.coeff (n - 1 - i.val))
  rw [hl]
  omega

theorem size_reverse (n : ℕ) (p : CPolynomial.Raw K) : (CPolynomial.Raw.reverse n p).size = n := by
  simp [CPolynomial.Raw.reverse]

/-- `modByMonicWith fftModContext p M`, `M` monic and longer than `p`: the first branch, at most
`42·|p| + 81·|M| + 99`. -/
theorem modByMonicWithC_first_cost (hP : Includes P modByMonicWith.c558.costDeps)
    (p M : CPolynomial K) (hM : M.monic = true) (hpM : p.val.size < M.val.size)
    (hMs : M.val.size < 2 ^ 60) :
    machineCost P modByMonicWith.c558.costIdx [encodeValue p, encodeValue M] ≤
      42 * p.val.size + 81 * M.val.size + 99 := by
  rw [modByMonicWith.c558.costEq P hP]
  have := listBeqK_cost P (by includes) M.val.toList (↑(0 : CPolynomial K) : Array K).toList
  have := modByMonicFFTC_first_cost P (by includes) _ _ hM hpM hMs
  have hz : (↑(0 : CPolynomial K) : Array K).size = 0 := rfl
  simp only [Array.length_toList, hz] at *
  split <;> omega

/-- **The remainder with the inverse supplied** (`rawModByMonicCached`), `p`, `q` canonical, `q`
monic: on the first branch, or on the cached branch (`k ≤ K ≤ Nq`, the supplied inverse of any
size: it is truncated): at most `100·|p| + 200·|q| + LBq + LB + 600`, `LBq` the quotient's
truncated product (precision `k ≤ Nq`), `LB` the back-product's (precision `|q| − 1 ≤ Nb`). -/
theorem rawModByMonicCachedC_cost
    (hP : Includes P Auto.LeanVM.Extraction.Fast.rawModByMonicCached.c573.costDeps)
    {N Nb Nq LB LBq : ℕ} (hLB : LowBound P Nb LB) (hLq : LowBound P Nq LBq)
    (inv : CPolynomial.Raw K) (Kp : ℕ)
    (p q : CPolynomial K) (hq : q.monic = true) (hN : N < 2 ^ 58) (hKp : Kp < 2 ^ 64) (hKq : Kp ≤ Nq)
    (hpN : p.val.size ≤ N)
    (hqN : q.val.size ≤ N) (hqb : q.val.size ≤ Nb + 1)
    (hk : p.val.size < q.val.size ∨ p.val.size - q.val.size + 1 ≤ Kp) :
    machineCost P Auto.LeanVM.Extraction.Fast.rawModByMonicCached.c573.costIdx
        [encodeValue inv, encodeValue Kp, encodeValue p.val, encodeValue q.val] ≤
      100 * p.val.size + 200 * q.val.size + LBq + LB + 600 := by
  rw [Auto.LeanVM.Extraction.Fast.rawModByMonicCached.c573.costEq P hP]
  have hpt := cpoly_trim_eq p
  have hqt := cpoly_trim_eq q
  have hlc : (CPolynomial.Raw.leadingCoeff q.val == 1) = true := by
    simpa [CPolynomial.monic, CPolynomial.leadingCoeff, CPolynomial.Raw.leadingCoeff, hqt] using hq
  have := trimLen_cost P (by includes) p.val p.val.size (by omega)
  have := trimLen_cost P (by includes) q.val q.val.size (by omega)
  have := listBeqK_cost P (by includes) p.val.toList p.val.toList
  have := listBeqK_cost P (by includes) q.val.toList q.val.toList
  have := getLastDC_cost P (by includes) q.val 0 (by omega)
  have h1 : (Array.extract p.val 0 (CompPolyLib.trimLen p.val p.val.size)).size ≤ p.val.size := by
    simp
  have h2 : (Array.extract q.val 0 (CompPolyLib.trimLen q.val q.val.size)).size ≤ q.val.size := by
    simp
  have hp64 : p.val.size < 2 ^ 64 := by omega
  have hq64 : q.val.size < 2 ^ 64 := by omega
  have hq1 : 1 ≤ q.val.size := by
    by_contra h0
    have h0' : q.val.size = 0 := by omega
    simp [CPolynomial.monic, CPolynomial.leadingCoeff, Array.getLastD, h0'] at hq
  simp only [hpt, hqt, beq_self_eq_true, Bool.true_and, hlc, ↓reduceIte, Array.length_toList]
    at *
  rw [limbs_of_lt hp64, limbs_of_lt hq64]
  split
  · omega
  · rename_i hge
    have hkK : p.val.size - q.val.size + 1 ≤ Kp := by omega
    simp only [hkK, ↓reduceIte]
    have := reverseC_cost P (by includes) p.val.size (by omega) p.val
    set k := p.val.size - q.val.size + 1 with hkdef
    have hrevP := size_reverse p.val.size p.val
    have hl1 := hLq k (CPolynomial.Raw.reverse p.val.size p.val) inv (by omega)
    set ql := FFT.fftRawMulLowContext.mulLow k (CPolynomial.Raw.reverse p.val.size p.val) inv
    have hql : ql.size ≤ k := FFT.fftRawMulLowContext.size_le k _ _
    have := reverseC_cost P (by includes) k (by omega) ql
    have hrq := size_reverse k ql
    have hl2 := hLB (q.val.size - 1) q.val (CPolynomial.Raw.reverse k ql) (by omega)
    set pl := FFT.fftRawMulLowContext.mulLow (q.val.size - 1) q.val (CPolynomial.Raw.reverse k ql)
    have hpl : pl.size ≤ q.val.size - 1 := FFT.fftRawMulLowContext.size_le _ _ _
    have ht : (CPolynomial.Raw.truncate (q.val.size - 1) p.val).size ≤ q.val.size - 1 := by
      simp [CPolynomial.Raw.truncate]
    have := subRawC_cost P (by includes) (CPolynomial.Raw.truncate (q.val.size - 1) p.val) pl
      (by omega) (by omega)
    have h3 : (Array.extract p.val 0 (q.val.size - 1)).size ≤ q.val.size := by
      simp only [Array.size_extract]; omega
    have hm : max (CPolynomial.Raw.truncate (q.val.size - 1) p.val).size pl.size ≤ q.val.size :=
      max_le (by omega) (by omega)
    cost_simp
    omega

/-- **`modByMonicCached`**: the raw remainder, `5` more. -/
theorem modByMonicCachedC_cost (hP : Includes P modByMonicCachedC.costDeps)
    {N Nb Nq LB LBq : ℕ} (hLB : LowBound P Nb LB) (hLq : LowBound P Nq LBq)
    (inv : CPolynomial.Raw K) (Kp : ℕ)
    (p q : CPolynomial K) (hq : q.monic = true) (hN : N < 2 ^ 58) (hKp : Kp < 2 ^ 64) (hKq : Kp ≤ Nq)
    (hpN : p.val.size ≤ N)
    (hqN : q.val.size ≤ N) (hqb : q.val.size ≤ Nb + 1)
    (hk : p.val.size < q.val.size ∨ p.val.size - q.val.size + 1 ≤ Kp) :
    machineCost P modByMonicCachedC.costIdx
        [encodeValue inv, encodeValue Kp, encodeValue p, encodeValue q] ≤
      100 * p.val.size + 200 * q.val.size + LBq + LB + 605 := by
  rw [modByMonicCachedC.costEq P hP]
  have := rawModByMonicCachedC_cost P (by includes) hLB hLq inv Kp p q hq hN hKp hKq hpN hqN hqb hk
  omega

end

end LeanVM.Cost.Bounds.PMSolve
