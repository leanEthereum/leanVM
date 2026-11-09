module

public import CompPoly.Bivariate.GuruswamiSudan.Root.RothRuckenstein.Correctness
import all CompPoly.Bivariate.GuruswamiSudan.Root.RothRuckenstein.Correctness
public import Mathlib.Data.Nat.Choose.Lucas
public import Mathlib.Algebra.CharP.Two
public import LeanVM.Protocol.Extraction.Fast.RootSteps

/-!
# Roth–Ruckenstein's substitution, fast

CompPoly's `substituteYRootPlusXY Q a` computes `Q(X, a + X·Y)` monomial by monomial: for each of
the `|Q|` terms `c·X^x·Y^y` it adds the `y + 1` monomials `c·C(y, t)·a^(y−t)·X^(x+t)·Y^t` to a
dense accumulator, each addition costing the accumulator's size, and computes `C(y, t)` as a
natural number. That is about `|Q|²·ℓ/2` operations per substitution, for a `Y`-degree `ℓ`.

`substituteFast Q a` computes the same polynomial `Y`-coefficient by `Y`-coefficient (a Taylor
shift): the coefficient of `Y^t` is `X^t·Σ_{t ≤ y} C(y, t)·a^(y−t)·Q_y(X)`, about `ℓ²/2` scaled
additions of the `Q_y`, i.e. `ℓ·|Q|` operations. In characteristic `2`, `C(y, t)` is `1` or `0` as
it is odd or even (`chooseOdd`, Lucas' theorem bit by bit), so no binomial is computed.

* `coeff_substituteFast`: the coefficient of `X^i·Y^j` in `substituteFast Q a`;
* `coeff_substituteYRootPlusXY`: the same for CompPoly's, from its fold form;
* **`substituteFast_eq`**: `substituteFast Q a = substituteYRootPlusXY Q a`.

Then CompPoly's chain from the substitution to the root context, copied with `substituteFast`:
`residualFast`, `prefixesWithFuelFast` (a recursive definition, equal by induction),
`rootsYDegreeLtFast` and `rothRuckensteinRootContextFast` (its contracts CompPoly's, transported);
**`rothRuckensteinRootContextFast_eq`**: the context is CompPoly's `rothRuckensteinRootContext`.

Credits: copied from CompPoly (github.com/Verified-zkEVM/CompPoly at
`572f997390aa4fc131ef30b1186fa1dcf292ca10`, Apache-2.0, "Copyright (c) 2026 CompPoly
Contributors"; `Bivariate/GuruswamiSudan/Root/RothRuckenstein/{Algorithm,Correctness}.lean`,
Valerii Huhnin) and edited (the substitution called): the texts of
`transformedRothRuckensteinResidual`, `transformedRothRuckensteinRootPrefixesWithFuel`,
`transformedRothRuckensteinRootsYDegreeLt` and `rothRuckensteinRootContext`. Used, not copied:
`substituteYRootPlusXY` and its fold lemma `substituteYRootPlusXY_coeff_fold`.
-/

namespace LeanVM.Extraction.Fast

open CompPoly CompPoly.GuruswamiSudan

public section

/-! ## Binomial parity -/

/-- Whether `C(n, k)` is odd: bit by bit, no bit of `k` above the bit of `n` (Lucas). -/
@[expose] def chooseOdd : ℕ → ℕ → Bool
  | 0, k => k == 0
  | n + 1, k => decide (k % 2 ≤ (n + 1) % 2) && chooseOdd ((n + 1) / 2) (k / 2)
decreasing_by omega

theorem choose_mod_two (n k : ℕ) : n.choose k % 2 = if chooseOdd n k then 1 else 0 := by
  induction n using Nat.strong_induction_on generalizing k with
  | _ n ih =>
  rcases n with _ | n
  · rcases k with _ | k <;> simp [chooseOdd]
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hl := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := 2) (n := n + 1) (k := k)
    have ih' := ih ((n + 1) / 2) (by omega) (k / 2)
    unfold Nat.ModEq at hl
    rw [hl, Nat.mul_mod, ih']
    have hk : k % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have hn : (n + 1) % 2 < 2 := Nat.mod_lt _ (by norm_num)
    rw [chooseOdd]
    interval_cases hka : k % 2 <;> interval_cases hna : (n + 1) % 2 <;>
      split <;> simp_all

/-- In characteristic `2`, `C(n, k)` is `1` if it is odd, `0` otherwise. -/
theorem natCast_choose {F : Type*} [Field F] [CharP F 2] (n k : ℕ) :
    (n.choose k : F) = if chooseOdd n k then 1 else 0 := by
  rw [← Nat.mod_add_div (n.choose k) 2, choose_mod_two]
  push_cast
  rw [CharTwo.two_eq_zero]
  split <;> simp

/-! ## The substitution -/

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]

/-- `X^t·p`: `t` zeros, then `p`'s coefficients. -/
@[expose] def shiftX (t : ℕ) (p : CPolynomial F) : CPolynomial F :=
  CPolynomial.ofArray (Array.replicate t 0 ++ p.val)

omit [DecidableEq F] in
theorem coeff_shiftX (t : ℕ) (p : CPolynomial F) (i : ℕ) :
    (shiftX t p).coeff i = if t ≤ i then p.coeff (i - t) else 0 := by
  rw [shiftX, CPolynomial.coeff_ofArray]
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_append, Array.size_replicate]
  split <;> rename_i h
  · simp [h, show ¬ t ≤ i by omega]
  · simp only [show t ≤ i by omega, ↓reduceIte]

/-- The `Y^t` coefficient of `Q(X, a + X·Y)` before the factor `X^t`:
`Σ_{t ≤ y < |Q|, C(y, t) odd} a^(y−t)·Q_y`. -/
@[expose] def taylorCoeff (Q : CBivariate F) (a : F) (t : ℕ) : CPolynomial F :=
  (List.range' t (Q.val.size - t)).foldl
    (fun acc y ↦ if chooseOdd y t then acc + a ^ (y - t) • Q.val.coeff y else acc) 0

/-- **Roth–Ruckenstein's substitution `Y := a + X·Y`, fast** (characteristic `2`): `Y`-coefficient
`t` is `X^t·taylorCoeff Q a t`. -/
@[expose] def substituteFast (Q : CBivariate F) (a : F) : CBivariate F :=
  CPolynomial.ofArray (Array.ofFn fun t : Fin Q.val.size ↦ shiftX t.val (taylorCoeff Q a t.val))

/-! ## Equal to CompPoly's -/

private theorem foldl_add_eq {α M : Type*} [AddCommMonoid M] (f : α → M) (l : List α) (acc : M) :
    l.foldl (fun acc x ↦ acc + f x) acc = acc + (l.map f).sum := by
  induction l generalizing acc with
  | nil => simp
  | cons x l ih => simp [ih, add_assoc]

private theorem sum_range' {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m n : ℕ) :
    ((List.range' m n).map f).sum = ∑ i ∈ Finset.range n, f (m + i) := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range'_concat, Finset.sum_range_succ, ih]

/-- The coefficient of `X^i·Y^j` in `Q(X, a + X·Y)`: `Σ_{j ≤ y < |Q|} C(y, j)·a^(y−j)·Q_y[i − j]`
for `j ≤ i`, `0` otherwise. -/
@[expose] def substCoeff (Q : CBivariate F) (a : F) (i j : ℕ) : F :=
  ∑ y ∈ Finset.range Q.val.size,
    if j ≤ y ∧ j ≤ i then (Q.val.coeff y).coeff (i - j) * (y.choose j : F) * a ^ (y - j) else 0

omit [DecidableEq F] in
theorem coeff_taylorCoeff (Q : CBivariate F) (a : F) (t i : ℕ) :
    (taylorCoeff Q a t).coeff i = ∑ k ∈ Finset.range (Q.val.size - t),
      if chooseOdd (t + k) t then a ^ (t + k - t) * (Q.val.coeff (t + k)).coeff i else 0 := by
  have h : ∀ (l : List ℕ) (acc : CPolynomial F),
      (l.foldl (fun acc y ↦ if chooseOdd y t then acc + a ^ (y - t) • Q.val.coeff y else acc)
        acc).coeff i =
      acc.coeff i + (l.map fun y ↦
        if chooseOdd y t then a ^ (y - t) * (Q.val.coeff y).coeff i else 0).sum := by
    intro l
    induction l with
    | nil => simp
    | cons y l ih =>
      intro acc
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]
      split
      · rw [CPolynomial.coeff_add, CPolynomial.coeff_smul, add_assoc]
      · rw [zero_add]
  rw [taylorCoeff, h, CPolynomial.coeff_zero, zero_add, sum_range']

theorem coeff_substituteFast [CharP F 2] (Q : CBivariate F) (a : F) (i j : ℕ) :
    CBivariate.coeff (substituteFast Q a) i j = substCoeff Q a i j := by
  show CPolynomial.coeff (CPolynomial.coeff (substituteFast Q a) j) i = _
  rw [substituteFast, CPolynomial.coeff_ofArray, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn,
    substCoeff]
  by_cases hj : j < Q.val.size
  · simp only [hj, ↓reduceDIte, Option.getD_some]
    rw [coeff_shiftX, coeff_taylorCoeff]
    by_cases hji : j ≤ i
    · simp only [hji, ↓reduceIte, and_true]
      rw [← Finset.sum_range_add_sum_Ico _ hj.le, Finset.sum_Ico_eq_sum_range,
        Finset.sum_eq_zero (s := Finset.range j) fun y hy ↦
          ite_eq_right_iff.2 fun h ↦ absurd h (by have := Finset.mem_range.1 hy; omega),
        zero_add]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [natCast_choose]
      simp only [Nat.le_add_right, ↓reduceIte]
      split <;> ring
    · simp only [hji, ↓reduceIte, and_false]
      simp
  · simp only [hj, ↓reduceDIte, Option.getD_none]
    rw [CPolynomial.coeff_zero]
    refine (Finset.sum_eq_zero fun y hy ↦ ite_eq_right_iff.2 fun h ↦ ?_).symm
    have := Finset.mem_range.1 hy
    omega

theorem coeff_substituteYRootPlusXY (Q : CBivariate F) (a : F) (i j : ℕ) :
    CBivariate.coeff (substituteYRootPlusXY Q a) i j = substCoeff Q a i j := by
  rw [substituteYRootPlusXY_coeff_fold]
  simp only [foldl_add_eq, zero_add, sum_range']
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  set q := Q.val.coeff y
  -- the sum over `t`: only `t = j` remains, when `j ≤ y`
  have ht : ∀ x, (∑ t ∈ Finset.range (y + 1),
      if i = x + t ∧ j = t then q.coeff x * (y.choose t : F) * a ^ (y - t) else 0) =
      if j ≤ y ∧ i = x + j then q.coeff x * (y.choose j : F) * a ^ (y - j) else 0 := by
    intro x
    by_cases hj : j ≤ y
    · rw [Finset.sum_eq_single j]
      · simp only [hj, true_and, and_true]
      · intro t _ htj
        rw [ite_eq_right_iff]
        exact fun h ↦ absurd h.2.symm htj
      · intro h
        exact absurd (Finset.mem_range.2 (by omega)) h
    · rw [ite_eq_right_iff.2 fun h ↦ absurd h.1 hj]
      refine Finset.sum_eq_zero fun t ht ↦ ite_eq_right_iff.2 fun h ↦ ?_
      have := Finset.mem_range.1 ht
      omega
  simp only [ht]
  -- the sum over `x`: only `x = i - j` remains
  rw [Finset.sum_eq_single (i - j)]
  · simp only [show (i = i - j + j) ↔ j ≤ i by omega]
  · intro x _ hx
    rw [ite_eq_right_iff]
    intro h
    omega
  · intro hx
    rw [ite_eq_right_iff]
    intro _
    rw [CPolynomial.coeff_eq_zero_of_size_le _ (by simpa using hx), zero_mul, zero_mul]

/-- **The fast substitution is CompPoly's** (characteristic `2`). -/
theorem substituteFast_eq [CharP F 2] (Q : CBivariate F) (a : F) :
    substituteFast Q a = substituteYRootPlusXY Q a :=
  CBivariate.eq_iff_coeff.2 fun i j ↦ by
    rw [coeff_substituteFast, coeff_substituteYRootPlusXY]

/-! ## Roth–Ruckenstein's roots with the fast substitution

CompPoly's chain from the substitution to the root context, copied with `substituteFast` for
`substituteYRootPlusXY` (`Algorithm.lean`, `Correctness.lean`), each copy proved equal. -/

/-- `transformedRothRuckensteinResidual`, fast. -/
@[expose] def residualFast (Q : CBivariate F) (a : F) : CBivariate F :=
  stripFast (substituteFast Q a)

/-- `transformedRothRuckensteinRootPrefixesWithFuel`, fast. -/
@[expose] def prefixesWithFuelFast (fieldRoots : FieldRootContext F) :
    ℕ → CBivariate F → ℕ → CPolynomial F → Array (CPolynomial F)
  | 0, _Q, _depth, pref => #[pref]
  | fuel + 1, Q, depth, pref =>
      let Qnorm := stripFast Q
      if Qnorm == (0 : CBivariate F) then
        #[]
      else
        (rootsInFieldForNonzeroEquation fieldRoots (initialCoeffFast Qnorm)).foldl
          (fun out coeff ↦
            out ++ prefixesWithFuelFast fieldRoots fuel (residualFast Qnorm coeff) (depth + 1)
              (extendPrefix pref depth coeff))
          #[]

/-- `rothRuckensteinRootsYDegreeLt`, fast. -/
@[expose] def rootsYDegreeLtFast (fieldRoots : FieldRootContext F) (Q : CBivariate F) (k : ℕ) :
    Array (CPolynomial F) :=
  (prefixesWithFuelFast fieldRoots k Q 0 default).filter fun p ↦ isRootYDegreeLtBool Q k p

section CharTwo

variable [CharP F 2]

theorem residualFast_eq (Q : CBivariate F) (a : F) :
    residualFast Q a = transformedRothRuckensteinResidual Q a := by
  rw [residualFast, stripFast_eq, substituteFast_eq, transformedRothRuckensteinResidual]

theorem prefixesWithFuelFast_eq (fieldRoots : FieldRootContext F) (fuel : ℕ) (Q : CBivariate F)
    (depth : ℕ) (pref : CPolynomial F) :
    prefixesWithFuelFast fieldRoots fuel Q depth pref =
      transformedRothRuckensteinRootPrefixesWithFuel fieldRoots fuel Q depth pref := by
  induction fuel generalizing Q depth pref with
  | zero => rw [prefixesWithFuelFast, transformedRothRuckensteinRootPrefixesWithFuel]
  | succ fuel ih =>
    rw [prefixesWithFuelFast, transformedRothRuckensteinRootPrefixesWithFuel]
    simp only [ih, residualFast_eq, stripFast_eq, initialCoeffFast_eq]

theorem rootsYDegreeLtFast_eq (fieldRoots : FieldRootContext F) :
    rootsYDegreeLtFast fieldRoots = rothRuckensteinRootsYDegreeLt fieldRoots := by
  funext Q k
  rw [rootsYDegreeLtFast, rothRuckensteinRootsYDegreeLt, transformedRothRuckensteinRootsYDegreeLt,
    transformedRothRuckensteinRootPrefixes, prefixesWithFuelFast_eq]

/-- **Roth–Ruckenstein's root context, fast**: CompPoly's `rothRuckensteinRootContext` with
`rootsYDegreeLtFast`, its contracts CompPoly's. -/
@[expose] def rothRuckensteinRootContextFast (fieldRoots : FieldRootContext F) :
    GSRootContext F where
  rootsYDegreeLt := rootsYDegreeLtFast fieldRoots
  sound := by
    rw [rootsYDegreeLtFast_eq]
    exact (rothRuckensteinRootContext F fieldRoots).sound
  complete := by
    rw [rootsYDegreeLtFast_eq]
    exact (rothRuckensteinRootContext F fieldRoots).complete

theorem rothRuckensteinRootContextFast_eq (fieldRoots : FieldRootContext F) :
    rothRuckensteinRootContextFast fieldRoots = rothRuckensteinRootContext F fieldRoots := by
  rw [rothRuckensteinRootContextFast, rothRuckensteinRootContext]
  congr 1
  exact rootsYDegreeLtFast_eq fieldRoots

end CharTwo

end

end LeanVM.Extraction.Fast
