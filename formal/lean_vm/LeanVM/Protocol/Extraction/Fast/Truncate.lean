module

public import LeanVM.Protocol.Extraction.Fast.RothRuckenstein
public import CompPoly.Bivariate.GuruswamiSudan.Root.RothRuckenstein.Lemmas
public import CompPoly.Bivariate.GuruswamiSudan.Root.Common.Lemmas

/-!
# Roth–Ruckenstein, truncated

Roth–Ruckenstein's recursion (`prefixesWithFuelFast`) substitutes `Y := a + X·Y` into the whole
of `Q`, whose `X`-degree is about `ℓ·k`; a step only reads the coefficients of `X^0` after the
`X`-adic factor is stripped. `prefixesTrunc` keeps `Q` modulo `X^M` instead, `M = k` at the start:
coefficient `X^i` of the substitution depends only on coefficients `X^{≤ i}` (`truncateX_substituteFast`),
and stripping `X^s` loses `s` of the precision, so the child is kept modulo `X^(M−s)`. When the
truncated polynomial does not determine the step (it is zero modulo `X^M`: a repeated root may
have stripped more than one power of `X` per step), the step falls back to the exact recursion,
on the exact polynomial recomputed from the original (`E ()`, the replayed residuals). The
precision adapts: no fallback while each step strips at most one power, as at simple roots.

* `xAdicOrder?_of_truncateX`: an order `s < M` seen modulo `X^M` is the order;
* `divXPower_truncateX`: stripping commutes with truncation, at `M − s`;
* `stripXAdicFactor_stripXAdicFactor`: stripping is idempotent;
* **`prefixesTrunc_eq`**: `prefixesTrunc` is `prefixesWithFuelFast`, on the same input.

Per substitution about `ℓ²·M/2` operations, `M ≤ k`, instead of `ℓ²·w/2`, `w ≈ ℓ·k`.

Credits: the `X`-adic order lemmas (`cbivar_xAdicOrder?_some_exists`, …), `cbivar_coeff_divXPower`,
`cbivar_coeff_truncateX` and `initialCoefficientPolynomial_coeff_fold` are CompPoly's
(github.com/Verified-zkEVM/CompPoly at `572f997390aa4fc131ef30b1186fa1dcf292ca10`, Apache-2.0,
"Copyright (c) 2026 CompPoly Contributors"; `Bivariate/GuruswamiSudan/Root/{RothRuckenstein,Common}/Lemmas.lean`,
Valerii Huhnin), used, not copied.
-/

namespace LeanVM.Extraction.Fast

open CompPoly CompPoly.GuruswamiSudan

public section

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]

/-! ## Truncation, order and stripping -/

omit [DecidableEq F] in
/-- An order `s` seen modulo `X^M` is the order. -/
theorem xAdicOrder?_of_truncateX {S : CBivariate F} {M s : ℕ}
    (h : CBivariate.xAdicOrder? (CBivariate.truncateX S M) = some s) :
    s < M ∧ CBivariate.xAdicOrder? S = some s := by
  obtain ⟨y₀, -, hy₀⟩ := cbivar_xAdicOrder?_some_exists h
  rw [cbivar_coeff_truncateX] at hy₀
  have hsM : s < M := by
    by_contra hc
    exact hy₀ (by simp [hc])
  have hy₀' : CBivariate.coeff S s y₀ ≠ 0 := by simpa [hsM] using hy₀
  refine ⟨hsM, ?_⟩
  cases ht : CBivariate.xAdicOrder? S with
  | none =>
    exact absurd (by rw [cbivar_xAdicOrder?_none_eq_zero ht, CBivariate.coeff_zero]) hy₀'
  | some t =>
    congr 1
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · obtain ⟨y₁, -, hy₁⟩ := cbivar_xAdicOrder?_some_exists ht
      apply hy₁
      have := cbivar_xAdicOrder?_some_coeff_eq_zero_of_lt (y := y₁) h (i := t) hlt
      rw [cbivar_coeff_truncateX] at this
      simpa [show t < M by omega] using this
    · exact hy₀' (cbivar_xAdicOrder?_some_coeff_eq_zero_of_lt ht hgt)

omit [DecidableEq F] in
/-- Stripping `X^s` commutes with truncation, at `M − s`. -/
theorem divXPower_truncateX (S : CBivariate F) (M s : ℕ) :
    CBivariate.divXPower (CBivariate.truncateX S M) s =
      CBivariate.truncateX (CBivariate.divXPower S s) (M - s) := by
  refine CBivariate.eq_iff_coeff.2 fun i j ↦ ?_
  rw [cbivar_coeff_divXPower, cbivar_coeff_truncateX, cbivar_coeff_truncateX,
    cbivar_coeff_divXPower]
  by_cases h : i + s < M
  · simp [h, show i < M - s by omega]
  · simp [h, show ¬ i < M - s by omega]

omit [DecidableEq F] in
theorem stripXAdicFactor_of_order {S : CBivariate F} {s : ℕ}
    (h : CBivariate.xAdicOrder? S = some s) :
    CBivariate.stripXAdicFactor S = CBivariate.divXPower S s := by
  rw [CBivariate.stripXAdicFactor, h]

omit [DecidableEq F] in
/-- Stripping is idempotent. -/
theorem stripXAdicFactor_stripXAdicFactor (S : CBivariate F) :
    CBivariate.stripXAdicFactor (CBivariate.stripXAdicFactor S) =
      CBivariate.stripXAdicFactor S := by
  cases h : CBivariate.xAdicOrder? S with
  | none =>
    obtain rfl := cbivar_xAdicOrder?_none_eq_zero h
    rfl
  | some s =>
    rw [stripXAdicFactor_of_order h]
    obtain ⟨y₀, -, hy₀⟩ := cbivar_xAdicOrder?_some_exists h
    have h0 : CBivariate.xAdicOrder? (CBivariate.divXPower S s) = some 0 := by
      cases ht : CBivariate.xAdicOrder? (CBivariate.divXPower S s) with
      | none =>
        have := congrArg (fun Q ↦ CBivariate.coeff Q 0 y₀) (cbivar_xAdicOrder?_none_eq_zero ht)
        rw [cbivar_coeff_divXPower, Nat.zero_add, CBivariate.coeff_zero] at this
        exact absurd this hy₀
      | some t =>
        congr 1
        by_contra ht0
        apply hy₀
        have := cbivar_xAdicOrder?_some_coeff_eq_zero_of_lt (y := y₀) ht (i := 0) (by omega)
        rwa [cbivar_coeff_divXPower, Nat.zero_add] at this
    rw [stripXAdicFactor_of_order h0]
    refine CBivariate.eq_iff_coeff.2 fun i j ↦ ?_
    rw [cbivar_coeff_divXPower, Nat.add_zero]

/-! ## The substitution modulo `X^M` -/

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
theorem substCoeff_eq_sum (Q : CBivariate F) (a : F) (i j N : ℕ) (hN : Q.val.size ≤ N) :
    substCoeff Q a i j = ∑ y ∈ Finset.range N,
      if j ≤ y ∧ j ≤ i then CBivariate.coeff Q (i - j) y * (y.choose j : F) * a ^ (y - j)
      else 0 := by
  rw [substCoeff, ← Finset.sum_range_add_sum_Ico _ hN]
  rw [Finset.sum_eq_zero (s := Finset.Ico _ N) fun y hy ↦ by
    rw [cbivar_coeff_eq_zero_of_y_size_le Q (Finset.mem_Ico.1 hy).1]; simp, add_zero]
  rfl

/-- **Coefficient `X^i` of the substitution reads only coefficients `X^{≤ i}`.** -/
theorem truncateX_substituteFast [CharP F 2] (Q : CBivariate F) (a : F) (M : ℕ) :
    CBivariate.truncateX (substituteFast (CBivariate.truncateX Q M) a) M =
      CBivariate.truncateX (substituteFast Q a) M := by
  refine CBivariate.eq_iff_coeff.2 fun i j ↦ ?_
  rw [cbivar_coeff_truncateX, cbivar_coeff_truncateX]
  split
  · rename_i hi
    rw [coeff_substituteFast, coeff_substituteFast,
      substCoeff_eq_sum _ a i j (max Q.val.size (CBivariate.truncateX Q M).val.size)
        (le_max_right _ _),
      substCoeff_eq_sum _ a i j (max Q.val.size (CBivariate.truncateX Q M).val.size)
        (le_max_left _ _)]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    rw [cbivar_coeff_truncateX]
    split <;> rename_i h
    · simp only [show i - j < M by omega, ↓reduceIte]
    · rfl
  · rfl

/-! ## The truncated recursion -/

/-- **Roth–Ruckenstein's prefixes, truncated**: `q` is the polynomial modulo `X^M` (its
`X`-adic factor not yet stripped), `E ()` the exact polynomial the untruncated recursion
receives, computed only if the truncation does not determine a step. -/
@[expose] def prefixesTrunc (fieldRoots : FieldRootContext F) :
    ℕ → CBivariate F → ℕ → (Unit → CBivariate F) → ℕ → CPolynomial F → Array (CPolynomial F)
  | 0, _q, _M, _E, _depth, pref => #[pref]
  | fuel + 1, q, M, E, depth, pref =>
    match CBivariate.xAdicOrder? q with
    | some s =>
      if s < M then
        let Qn := CBivariate.divXPower q s
        (rootsInFieldForNonzeroEquation fieldRoots (initialCoefficientPolynomial Qn)).foldl
          (fun out a ↦
            out ++ prefixesTrunc fieldRoots fuel
              (CBivariate.truncateX (substituteFast Qn a) (M - s)) (M - s)
              (fun _ ↦ residualFast (CBivariate.stripXAdicFactor (E ())) a) (depth + 1)
              (extendPrefix pref depth a))
          #[]
      else prefixesWithFuelFast fieldRoots (fuel + 1) (E ()) depth pref
    | none => prefixesWithFuelFast fieldRoots (fuel + 1) (E ()) depth pref

theorem prefixesTrunc_eq [CharP F 2] (fieldRoots : FieldRootContext F) (fuel : ℕ) :
    ∀ (S : CBivariate F) (M : ℕ) (E : Unit → CBivariate F) (depth : ℕ) (pref : CPolynomial F),
      CBivariate.stripXAdicFactor S = CBivariate.stripXAdicFactor (E ()) →
      prefixesTrunc fieldRoots fuel (CBivariate.truncateX S M) M E depth pref =
        prefixesWithFuelFast fieldRoots fuel (E ()) depth pref := by
  induction fuel with
  | zero => intro S M E depth pref _; rfl
  | succ fuel ih =>
    intro S M E depth pref hSE
    rw [prefixesTrunc]
    cases hq : CBivariate.xAdicOrder? (CBivariate.truncateX S M) with
    | none => rfl
    | some s =>
      obtain ⟨hsM, hS⟩ := xAdicOrder?_of_truncateX hq
      simp only [hsM, ↓reduceIte]
      have hstrip : CBivariate.stripXAdicFactor (E ()) = CBivariate.divXPower S s := by
        rw [← hSE, stripXAdicFactor_of_order hS]
      have hQn : CBivariate.divXPower (CBivariate.truncateX S M) s =
          CBivariate.truncateX (CBivariate.divXPower S s) (M - s) := divXPower_truncateX S M s
      have hne : CBivariate.divXPower S s ≠ 0 := by
        obtain ⟨y₀, -, hy₀⟩ := cbivar_xAdicOrder?_some_exists hS
        intro h0
        have := congrArg (fun Q ↦ CBivariate.coeff Q 0 y₀) h0
        simp only [cbivar_coeff_divXPower, Nat.zero_add, CBivariate.coeff_zero] at this
        exact hy₀ this
      have hinit : initialCoefficientPolynomial (CBivariate.divXPower (CBivariate.truncateX S M) s) =
          initialCoefficientPolynomial (CBivariate.divXPower S s) := by
        refine CPolynomial.eq_iff_coeff.2 fun j ↦ ?_
        rw [coeff_initialCoefficientPolynomial, coeff_initialCoefficientPolynomial, hQn,
          cbivar_coeff_truncateX]
        simp only [show 0 < M - s by omega, ↓reduceIte]
      rw [prefixesWithFuelFast, stripFast_eq, hstrip, initialCoeffFast_eq]
      simp only [beq_iff_eq, hne, ↓reduceIte, hinit]
      congr 1
      funext out a
      congr 1
      rw [hQn, truncateX_substituteFast]
      refine ih _ _ _ _ _ ?_
      simp only [residualFast, stripFast_eq, stripXAdicFactor_stripXAdicFactor]

/-! ## The exact polynomial as data -/

/-- The exact polynomial after the roots `path` from `Q₀`: each step strips the `X`-adic factor and
takes the residual at the root (what `prefixesTrunc`'s fallback `E` computes, as data). -/
@[expose] def replayPath (Q₀ : CBivariate F) (path : List F) : CBivariate F :=
  path.foldl (fun q a ↦ residualFast (stripFast q) a) Q₀

/-- **`prefixesTrunc` with its fallback as data**: the exact polynomial `replayPath Q₀ path`,
computed only where the truncation does not determine a step. No function argument changes from
call to call. -/
@[expose] def prefixesTruncD (fieldRoots : FieldRootContext F) :
    ℕ → CBivariate F → ℕ → CBivariate F → List F → ℕ → CPolynomial F → Array (CPolynomial F)
  | 0, _q, _M, _Q₀, _path, _depth, pref => #[pref]
  | fuel + 1, q, M, Q₀, path, depth, pref =>
    match CBivariate.xAdicOrder? q with
    | some s =>
      if s < M then
        let Qn := divXPowerFast q s
        (rootsInFieldForNonzeroEquation fieldRoots (initialCoeffFast Qn)).foldl
          (fun out a ↦
            out ++ prefixesTruncD fieldRoots fuel
              (CBivariate.truncateX (substituteFast Qn a) (M - s)) (M - s) Q₀ (path ++ [a])
              (depth + 1) (extendPrefix pref depth a))
          #[]
      else prefixesWithFuelFast fieldRoots (fuel + 1) (replayPath Q₀ path) depth pref
    | none => prefixesWithFuelFast fieldRoots (fuel + 1) (replayPath Q₀ path) depth pref

theorem prefixesTruncD_eq (fieldRoots : FieldRootContext F) (fuel : ℕ) :
    ∀ (q : CBivariate F) (M : ℕ) (Q₀ : CBivariate F) (path : List F) (depth : ℕ)
      (pref : CPolynomial F),
      prefixesTruncD fieldRoots fuel q M Q₀ path depth pref =
        prefixesTrunc fieldRoots fuel q M (fun _ ↦ replayPath Q₀ path) depth pref := by
  induction fuel with
  | zero => intro q M Q₀ path depth pref; rfl
  | succ fuel ih =>
    intro q M Q₀ path depth pref
    rw [prefixesTruncD, prefixesTrunc]
    simp only [divXPowerFast_eq, initialCoeffFast_eq]
    cases CBivariate.xAdicOrder? q with
    | none => rfl
    | some s =>
      dsimp only
      split
      · congr 1
        funext out a
        rw [ih]
        congr 2
        funext _
        simp [replayPath, List.foldl_append, stripFast_eq]
      · rfl

end

end LeanVM.Extraction.Fast
