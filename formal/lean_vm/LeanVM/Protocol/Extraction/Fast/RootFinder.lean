module

public import LeanVM.Protocol.Extraction.Fast.DecoderFast
public import CompPoly.Univariate.Roots.Shoup.Correctness
public import CompPoly.Bivariate.GuruswamiSudan.Root.FieldRoots.FiniteField
import all CompPoly.Univariate.Raw.Modular
import all LeanVM.Protocol.Extraction.Extractor

/-!
# The extractor's root finder, restated

The extractor's `fieldRootCtx` (`LeanVM/Protocol/Extraction/Extractor.lean`) finds the roots in `K` of a polynomial
`p` as its `gcd` with `X^(2^64) − X`, split by Shoup's trace splitter (`p = 2`, `k = 64`). Its
code, at `fieldRootCtx`'s contexts, costs more than the algorithm needs; `rootsInFieldFast`
restates it, the root context `fieldRootCtxFast` (**`fieldRootCtxFast_eq`**: it is
`fieldRootCtx`) runs it:

* **remainders without quotients**: `ModContext.remainderOnly` for `ModContext.naive`
  (`rawModContext_remainderOnly_eq_naive`), and the `gcd` by `rawGcdMonicFast`/`gcdMonicFast`
  (`Fast/DecoderFast.lean`), whose long division computes `X^k` by `k` products per step;
* **the splitter's Frobenius powers cached per factor**: the statement's splitter
  (`shoupSplitCandidatesWith`) recomputes the powers `X^(2^i) mod u`, `i < 64`, for every factor
  `u` and every trace coordinate (`64` of them); CompPoly's cached splitter
  (`shoupSplitCandidatesCachedWith`, equal by `shoupSplitCandidatesWith_eq_cached`) computes them
  once per factor;
* **the Frobenius powers by squaring the previous one** (`frobeniusPowersFast`,
  **`frobeniusPowersFast_eq`**): CompPoly's `modularXPowersWith u 2 64` computes each
  `X^(2^i) mod u` from `X` by `i` modular squarings, `2016` in all; `frobeniusPowersFast` squares
  the previous power, `64` in all (the binary exponentiation of `2^i` is `i` squarings, then one
  product by `1 mod u`: `powModBinaryAuxWith_two_pow`);
* **the trace coordinate's constants by squaring** (`traceCoordFast`, **`traceCoordFast_eq`**):
  `β^(2^i)`, `i < 64`, each from the previous by one squaring, not by `i` squarings anew.

Credits: copied from CompPoly (github.com/Verified-zkEVM/CompPoly at
`572f997390aa4fc131ef30b1186fa1dcf292ca10`, Apache-2.0, "Copyright (c) 2026 CompPoly Contributors"),
and edited (the functions called, the contexts fixed at `K`'s): the texts of
`rootsInFiniteFieldWith` (`Univariate/Roots/Backend.lean`), `finiteFieldRootProductWith`
(`Univariate/Roots/RootProduct.lean`), `tracePowersWithCache`, `traceCoordinatePolynomialFromPowers`,
`shoupRefineFactorCachedWith`, `shoupRefineFactorsCachedWith`, `shoupRefineBasisCachedWith`,
`shoupSplitCandidatesCachedWith`, `shoupSplitLinearFactorsWith`
(`Univariate/Roots/Shoup/Basic.lean`) and `powModWith` (`Univariate/Raw/Modular.lean`).
-/

namespace LeanVM.Extraction.Fast

open LeanVM.Parameters
open CompPoly CompPoly.GuruswamiSudan CompPoly.CPolynomial.Roots.FiniteField

public section

/-! ## Frobenius powers by squaring -/

/-- `x ↦ x² mod u` at `K`'s contexts. -/
@[expose] def sqMod (u c : CPolynomial.Raw K) : CPolynomial.Raw K :=
  CPolynomial.Raw.mulModWith CPolynomial.Raw.MulContext.naive
    CPolynomial.Raw.ModContext.remainderOnly u c c

/-- The binary exponentiation of `2^j`: `j` squarings, then one product by the accumulator. -/
theorem powModBinaryAuxWith_two_pow (u acc : CPolynomial.Raw K) (j : ℕ) :
    ∀ c : CPolynomial.Raw K,
      CPolynomial.Raw.powModBinaryAuxWith CPolynomial.Raw.MulContext.naive
          CPolynomial.Raw.ModContext.remainderOnly u (2 ^ j) acc c =
        CPolynomial.Raw.mulModWith CPolynomial.Raw.MulContext.naive
          CPolynomial.Raw.ModContext.remainderOnly u acc ((sqMod u)^[j] c) := by
  induction j with
  | zero =>
    intro c
    rw [show (2 : ℕ) ^ 0 = 0 + 1 from rfl, CPolynomial.Raw.powModBinaryAuxWith]
    simp only [Nat.zero_add, Nat.mod_succ, beq_self_eq_true, ↓reduceIte, Function.iterate_zero,
      id]
    rw [show (1 : ℕ) / 2 = 0 from rfl, CPolynomial.Raw.powModBinaryAuxWith]
  | succ j ih =>
    intro c
    have h2 : 2 ^ (j + 1) = (2 ^ (j + 1) - 1) + 1 := by
      have := Nat.one_le_two_pow (n := j + 1); omega
    rw [h2, CPolynomial.Raw.powModBinaryAuxWith, ← h2]
    have hodd : (2 ^ (j + 1) % 2 == 1) = false := by
      rw [Nat.pow_succ, Nat.mul_mod_left]; rfl
    have hhalf : 2 ^ (j + 1) / 2 = 2 ^ j := by
      rw [Nat.pow_succ, Nat.mul_div_cancel _ (by norm_num)]
    simp only [hodd, Bool.false_eq_true, ↓reduceIte, hhalf]
    rw [ih, Function.iterate_succ_apply]
    rfl

/-- `[c, c² mod u, c⁴ mod u, …]`, `n` entries, each the square of the previous. -/
@[expose] def squaringsFrom (u : CPolynomial.Raw K) : ℕ → CPolynomial.Raw K → List (CPolynomial.Raw K)
  | 0, _ => []
  | n + 1, c => c :: squaringsFrom u n (sqMod u c)

theorem squaringsFrom_eq (u : CPolynomial.Raw K) (n : ℕ) :
    ∀ c, squaringsFrom u n c = (List.range n).map fun i ↦ (sqMod u)^[i] c := by
  induction n with
  | zero => intro c; rfl
  | succ n ih =>
    intro c
    rw [squaringsFrom, ih, List.range_succ_eq_map, List.map_cons, List.map_map]
    rfl

/-- **The Frobenius powers `X^(2^i) mod u`, `i < k`**, each the square of the previous one
(`modularXPowersWith u 2 k`). -/
@[expose] def frobeniusPowersFast (u : CPolynomial K) (k : ℕ) : Array (CPolynomial K) :=
  let oneMod :=
    if u.val.trim == 0 then
      (1 : CPolynomial.Raw K)
    else
      CPolynomial.Raw.ModContext.remainderOnly.modByMonic (1 : CPolynomial.Raw K)
        (CPolynomial.Raw.monicNormalize u.val)
  ((squaringsFrom u.val k CPolynomial.Raw.X).map fun c ↦
    CPolynomial.ofArray (CPolynomial.Raw.mulModWith CPolynomial.Raw.MulContext.naive
      CPolynomial.Raw.ModContext.remainderOnly u.val oneMod c)).toArray

theorem frobeniusPowersFast_eq (u : CPolynomial K) (k : ℕ) :
    frobeniusPowersFast u k =
      modularXPowersWith CPolynomial.Raw.MulContext.naive
        CPolynomial.Raw.ModContext.remainderOnly u 2 k := by
  rw [frobeniusPowersFast, modularXPowersWith, ← Array.toList_inj, Array.toList_ofFn,
    List.toList_toArray, squaringsFrom_eq, List.map_map, List.ofFn_eq_map]
  rw [← List.map_coe_finRange_eq_range, List.map_map]
  refine List.map_congr_left fun i _ ↦ ?_
  simp only [Function.comp_apply, xPowModWith, CPolynomial.Raw.powModWith]
  rw [powModBinaryAuxWith_two_pow]

theorem traceCtx_p : traceCtx.p = 2 := rfl

theorem traceCtx_k : traceCtx.k = 64 := rfl

/-! ## The trace coordinate's constants by squaring -/

/-- **`traceCoordinatePolynomialFromPowers traceCtx`**: `Σ_{i<64} β^(2^i)·powers[i]`, each
`β^(2^i)` the square of the previous. -/
@[expose] def traceCoordFast (beta : K) (powers : Array (CPolynomial K)) : CPolynomial K :=
  ((List.range 64).foldl
    (fun (state : CPolynomial K × K) i ↦
      (state.1 + CPolynomial.C state.2 * powers.getD i 0, state.2 * state.2))
    (0, beta)).1

theorem traceCoordFast_fold (beta : K) (powers : Array (CPolynomial K)) (n : ℕ) :
    (List.range n).foldl
        (fun (state : CPolynomial K × K) i ↦
          (state.1 + CPolynomial.C state.2 * powers.getD i 0, state.2 * state.2))
        (0, beta) =
      ((List.range n).foldl
          (fun acc i ↦ acc + CPolynomial.C (beta ^ (2 ^ i)) * powers.getD i 0) 0,
        beta ^ (2 ^ n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil, Prod.mk.injEq, true_and]
    rw [← pow_two, ← pow_mul, ← Nat.pow_succ]

theorem traceCoordFast_eq :
    traceCoordFast = traceCoordinatePolynomialFromPowers traceCtx := by
  funext beta powers
  rw [traceCoordFast, traceCoordFast_fold, traceCoordinatePolynomialFromPowers, traceCtx_p,
    traceCtx_k]

/-! ## Shoup's cached splitter, restated -/

/-- `tracePowersWithCache` at `K`'s contexts, with `frobeniusPowersFast`. -/
@[expose] def tracePowersFast (u : CPolynomial K) (cache : ShoupTracePowerCache K) :
    Array (CPolynomial K) × ShoupTracePowerCache K :=
  match lookupTracePowers u cache with
  | some powers => (powers, cache)
  | none =>
      let powers := frobeniusPowersFast u 64
      (powers, (u, powers) :: cache)

theorem tracePowersFast_eq :
    tracePowersFast = tracePowersWithCache CPolynomial.Raw.MulContext.naive
      CPolynomial.Raw.ModContext.remainderOnly traceCtx := by
  funext u cache
  rw [tracePowersFast, tracePowersWithCache, frobeniusPowersFast_eq, traceCtx_p, traceCtx_k]
  cases lookupTracePowers u cache <;> rfl

theorem gcdMonicFast_eq_fun : (gcdMonicFast : CPolynomial K → CPolynomial K → CPolynomial K) =
    CPolynomial.gcdMonic := by
  funext p q
  exact gcdMonicFast_eq p q

/-- `shoupRefineFactorCachedWith` at `K`'s contexts. -/
@[expose] def refineFactorFast (beta : K) (cache : ShoupTracePowerCache K) (u : CPolynomial K) :
    ShoupTracePowerCache K × Array (CPolynomial K) :=
  let u := CPolynomial.monicNormalize u
  if u == 0 || u == 1 then
    (cache, #[])
  else if isRepresentedLinearFactor u then
    (cache, #[u])
  else
    let (powers, cache) := tracePowersFast u cache
    let tracePoly := traceCoordFast beta powers
    let children :=
      traceCtx.baseConstants.foldl
        (fun children c ↦
          let child := CPolynomial.monicNormalize
            (gcdMonicFast u (tracePoly - CPolynomial.C c))
          pushNontrivialChild children child)
        #[]
    (cache, children)

/-- `shoupRefineFactorsCachedWith` at `K`'s contexts. -/
@[expose] def refineFactorsFast (beta : K) (cache : ShoupTracePowerCache K)
    (factors : Array (CPolynomial K)) : ShoupTracePowerCache K × Array (CPolynomial K) :=
  factors.foldl
    (fun state factor ↦
      let (cache, out) := state
      let (cache, children) := refineFactorFast beta cache factor
      (cache, out ++ children))
    (cache, #[])

/-- `shoupSplitCandidatesCachedWith` at `K`'s contexts. -/
@[expose] def splitCandidatesFast (p : CPolynomial K) : Array (CPolynomial K) :=
  let p := CPolynomial.monicNormalize p
  if p == 0 || p == 1 then
    #[]
  else if isRepresentedLinearFactor p then
    #[p]
  else
    (traceCtx.basis.toList.foldl
      (fun state beta ↦
        let (cache, factors) := state
        refineFactorsFast beta cache factors)
      (([] : ShoupTracePowerCache K), #[p])).2

theorem splitCandidatesFast_eq :
    splitCandidatesFast = shoupSplitCandidatesWith CPolynomial.Raw.MulContext.naive
      CPolynomial.Raw.ModContext.remainderOnly traceCtx := by
  rw [shoupSplitCandidatesWith_eq_cached]
  funext p
  simp only [splitCandidatesFast, shoupSplitCandidatesCachedWith, shoupRefineBasisCachedWith,
    refineFactorsFast, shoupRefineFactorsCachedWith, refineFactorFast,
    shoupRefineFactorCachedWith, tracePowersFast_eq, traceCoordFast_eq, gcdMonicFast_eq_fun]

/-! ## The roots -/

/-- `finiteFieldRootProductWith` at `K`'s contexts, with `rawGcdMonicFast`: the product of the
distinct linear factors of `p`, `gcd(p, X^(2^64) − X)`. -/
@[expose] def rootProductFast (p : CPolynomial K) : CPolynomial K :=
  CPolynomial.ofArray
    (if p.val.trim == 0 then
      0
    else
      let pMonic := CPolynomial.Raw.monicNormalize p.val
      rawGcdMonicFast pMonic
        (CPolynomial.Raw.xPowSubXModWith CPolynomial.Raw.MulContext.naive
          CPolynomial.Raw.ModContext.remainderOnly traceCtx.q pMonic))

theorem rootProductFast_eq (p : CPolynomial K) :
    rootProductFast p = finiteFieldRootProductWith CPolynomial.Raw.MulContext.naive
      CPolynomial.Raw.ModContext.remainderOnly traceCtx.toFiniteFieldContext p := by
  simp only [rootProductFast, finiteFieldRootProductWith,
    CPolynomial.Raw.Roots.FiniteField.finiteFieldRootProductWith, rawGcdMonicFast_eq]

/-- **The roots in `K`** (`rootsInFiniteFieldWith` at `K`'s contexts): `rootProductFast`, split
by the cached splitter with `frobeniusPowersFast`, `traceCoordFast` and `gcdMonicFast`. -/
@[expose] def rootsInFieldFast (p : CPolynomial K) : Array K :=
  if p == 0 then
    #[]
  else if p.val.size ≤ 1 then
    #[]
  else if p.val.size = 2 && !(p.coeff 1 == 0) then
    CPolynomial.rootsFromLinearFactors p #[p]
  else
    let rootProduct := rootProductFast p
    let factors := representedLinearFactorsOnly (splitCandidatesFast rootProduct)
    CPolynomial.rootsFromLinearFactors p factors

theorem rootsInFieldFast_eq : rootsInFieldFast = fieldRootCtx.rootsInField := by
  funext p
  show _ = rootsInFiniteFieldWith CPolynomial.Raw.MulContext.naive CPolynomial.Raw.ModContext.naive
    traceCtx.toFiniteFieldContext
    (shoupLinearFactorProductSplitterWith CPolynomial.Raw.MulContext.naive
      CPolynomial.Raw.ModContext.naive traceCtx) p
  rw [← rawModContext_remainderOnly_eq_naive]
  simp only [rootsInFieldFast, rootsInFiniteFieldWith, rootProductFast_eq, splitCandidatesFast_eq]
  rfl

/-- **The statement's root finder, restated** (`rootsInFieldFast`); its contracts
`fieldRootCtx`'s, transported. -/
@[expose] def fieldRootCtxFast : FieldRootContext K where
  rootsInField := rootsInFieldFast
  sound p a h := by
    rw [rootsInFieldFast_eq] at h
    exact fieldRootCtx.sound p a h
  complete p a hp hroot := by
    rw [rootsInFieldFast_eq]
    exact fieldRootCtx.complete p a hp hroot

theorem fieldRootCtxFast_eq : fieldRootCtxFast = fieldRootCtx :=
  fieldRootContext_ext rootsInFieldFast_eq

end

end LeanVM.Extraction.Fast
