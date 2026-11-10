module

public import LeanVM.Cost.Bounds.Decoder.PreTest
public import LeanVM.Cost.Decoder.Memory

/-!
# Bound: the cursor's length, compiled

`cursorLength D p q` (`Cost/Decoder/Memory.lean`, `cursorLenWith (discreteLogWith D)`): the
quotient `q / p` limb by limb (`limbQuotC`, an inverse in `GF(2^64)`), its logarithm, kept when
at most `2^32` and `q = p · a`.

* **`cursorLength_cost`**: the logarithm (`discreteLogWithC`) at most `Lg`, its logarithms
  word-sized: at most `Lg + 3214`;
* **`cursorLenWith_le`**: the length is at most `2^32`, for every logarithm.
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Cost LeanVM.Cost.Decoder LeanVM.Parameters LeanVM.Guest.Fast LeanVM.Extraction.Fast

public section

variable (P : MachineProgram)

/-- **The cursor's length is at most `2^32`**, for every logarithm `dl`. -/
theorem cursorLenWith_le (dl : K → Option ℕ) (p q : E) : cursorLenWith dl p q ≤ 2 ^ 32 := by
  unfold cursorLenWith
  dsimp only
  generalize dl (limbQuot p q) = o
  rcases o with _ | n
  · simp
  · rw [Option.filter_some]
    split_ifs with h
    · simp only [decide_eq_true_eq] at h
      simpa using h.1
    · simp

/-- The quotient limb by limb (`limbQuotC`): an inverse in `GF(2^64)` and `46`, at most `2869`. -/
theorem limbQuot_cost (hP : Includes P limbQuotC.costDeps) (p q : E) :
    machineCost P limbQuotC.costIdx [encodeValue p, encodeValue q] ≤ 2869 := by
  rw [limbQuotC.costEq P hP]
  have h0 := invK_cost P (by includes) (p.limb 0)
  have h1 := invK_cost P (by includes) (p.limb 1)
  split_ifs <;> omega

/-- **The cursor's length** (`cursorLengthC`), the logarithm at most `Lg`, its logarithms
word-sized: at most `Lg + 3214`. -/
theorem cursorLength_cost (hP : Includes P cursorLengthC.costDeps) (D : DiscreteLogTables) (Lg : ℕ)
    (hLg : ∀ x : K, machineCost P discreteLogWithC.costIdx [encodeValue D, encodeValue x] ≤ Lg)
    (hD : ∀ x m, discreteLogWith D x = some m → m < 2 ^ 64) (p q : E) :
    machineCost P cursorLengthC.costIdx [encodeValue D, encodeValue p, encodeValue q] ≤
      Lg + 3214 := by
  have hdl : ∀ a : K, RunsApp P (.closure cursorLengthC.lam0.costIdx [encodeValue D])
      [encodeValue a] (encodeValue (discreteLogWith D a)) :=
    fun a ↦ RunsApp.of_spec (cursorLengthC.lam0.costSpec P (by includes) D a)
  rw [cursorLengthC.costEq P hP, cursorLenWithC.costEq P (by includes) _ _ hdl]
  have h1 := limbQuot_cost P (by includes) p q
  have h2 : appCost P (.closure cursorLengthC.lam0.costIdx [encodeValue D])
      [encodeValue (limbQuot p q)] ≤ Lg + 4 := by
    rw [appCost_fn, List.singleton_append, cursorLengthC.lam0.costEq P (by includes),
      List.length_singleton]
    have := hLg (limbQuot p q)
    omega
  have hlam : ∀ n : ℕ, RunsApp P (.closure cursorLenWithC.lam0.costIdx
      [encodeValue p, encodeValue q, encodeValue (limbQuot p q)]) [encodeValue n]
      (encodeValue (decide (n ≤ 2 ^ 32 ∧ q = E.ofLimbs (p.limb 0 * limbQuot p q)
        (p.limb 1 * limbQuot p q)))) :=
    fun n ↦ RunsApp.of_spec (cursorLenWithC.lam0.costSpec P (by includes) p q _ n)
  rw [optionFilterNatC.costEq P (by includes) _ _ hlam]
  generalize ho : discreteLogWith D (limbQuot p q) = o
  cases o with
  | none => simp only [Option.filter_none]; omega
  | some n =>
    have hn := hD _ n ho
    have h3 : appCost P (.closure cursorLenWithC.lam0.costIdx
        [encodeValue p, encodeValue q, encodeValue (limbQuot p q)]) [encodeValue n] ≤ 307 := by
      rw [appCost_fn]
      simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [cursorLenWithC.lam0.costEq P (by includes), Nat.one_shiftLeft,
        limbs_of_lt hn, limbs_two_pow (by norm_num)]
      simp only [max_self]
      split_ifs <;> omega
    dsimp only
    generalize Option.filter _ (some n) = o'
    cases o' <;> dsimp only <;> split_ifs <;> omega

end

end LeanVM.Cost.Bounds
