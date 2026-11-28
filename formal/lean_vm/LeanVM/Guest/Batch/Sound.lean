/-
  LeanVM.Guest.Batch.Sound

  The batching's group of challenges: children with a false claim leave a batched gap that
  vanishes at a fraction at most `(2n + 4)/|E|` of `λ` and the column challenges.
-/

module

public import LeanVM.Guest.Batch.Bytecode
public import LeanVM.Guest.Batch.Split
public import LeanVM.Guest.Batch.Group
import LeanVM.Protocol.Field

/-!
# The batched gap

The batching combines the children's claims with the powers of one challenge `λ`, child `i`'s
fresh claim, folded at the column challenges `c`, with `λ^(2i)` and its carried claim with
`λ^(2i+1)` (`lambdaPowers`). Against the true values on the split table `T`, the claimed less the
true is the gaps' polynomial (`claim_sub_eq_sum`):

`G(λ, c) = Σ_{m < 2n} gap_m(c)·λ^m`, `gap_{2i}(c) = fold(c, values_i) − T̃(p_i ++ c)`,
`gap_{2i+1} = v_i − T̃(q_i)`.

By `mle_splitTable_append`, `gap_{2i}(c) = Σ_j eq(c, j)·(values_i[j] − split_values(p_i)[j])`,
multilinear in `c`, of total degree `splitLog`; `gap_{2i+1}` is a constant. A false fresh claim
(`values_i ≠ split_values(p_i)`) makes `gap_{2i}` nonzero, a false carried claim `gap_{2i+1}`. So
`G` is a nonzero polynomial of total degree at most `2(n − 1) + splitLog = 2n + 4` in `(λ, c)`,
and `avg_gap_le`: it vanishes at a fraction at most `(2n + 4)/|E|` of them, its top coefficient
first (`avgL_poly_le`).
-/

namespace LeanVM.Guest.Batch

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom
open LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Protocol.Hotwire (eqAt)
open Finset
open scoped ENNReal

@[expose] public section

attribute [local instance 1100] LeanVM.Parameters.instFintypeK

/-! ## The gaps -/

/-- The flattened pairs of lambdas. -/
abbrev flat2 (l : List (E × E)) : List E := l.flatMap fun p ↦ [p.1, p.2]

/-- Claimed less true values, combined by pairs of lambdas, is the lambdas' combination of the
gaps. -/
theorem sub_pairs {α : Type} (cs : List α) (l : List (E × E)) (hl : l.length = cs.length)
    (a b a' b' : α → E) :
    sumE (List.zipWith (fun c l ↦ l.1 * a c + l.2 * b c) cs l) -
        sumE (List.zipWith (fun c l ↦ l.1 * a' c + l.2 * b' c) cs l) =
      dot (flat2 l) (cs.flatMap fun c ↦ [a c - a' c, b c - b' c]) := by
  induction cs generalizing l with
  | nil => simp [sumE, dot]
  | cons c cs ih =>
    obtain _ | ⟨x, l⟩ := l
    · simp at hl
    · simp only [List.zipWith_cons_cons, Tables.sumE_eq, List.sum_cons,
        List.flatMap_cons, List.cons_append, List.nil_append, Tables.dot_cons] at ih ⊢
      rw [← ih l (by simpa using hl)]
      ring

/-- **The gaps** the children's claims leave on the table `t` at the column challenges `column`,
claimed less true, in the order of their lambdas: each child's fresh claim folded at `column`,
then its carried claim. -/
def gapsAt (t : List E) (cs : List ChildClaims) (column : List E) : List E :=
  cs.flatMap fun c ↦
    [foldColumns column c.freshClaim.values - multilinearEval t (c.freshClaim.point ++ column),
      c.carriedClaim.bytecodeValue - multilinearEval t c.carriedClaim.bytecodePoint]

theorem length_gapsAt (t : List E) (cs : List ChildClaims) (column : List E) :
    (gapsAt t cs column).length = 2 * cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [gapsAt, List.flatMap_cons, List.length_append] at ih ⊢; simp [ih]; ring

/-- The lambdas of `λ`, flattened, are its first `2n` powers. -/
theorem flat2_lambdaPowers (lam : E) : ∀ n, flat2 (lambdaPowers lam n) =
    (List.range (2 * n)).map (lam ^ ·)
  | 0 => rfl
  | n + 1 => by
    have ih := flat2_lambdaPowers lam n
    simp only [flat2, lambdaPowers] at ih ⊢
    rw [List.range_succ, List.map_append, List.flatMap_append, ih,
      show 2 * (n + 1) = 2 * n + 1 + 1 by ring, List.range_succ, List.range_succ, List.map_append,
      List.map_append, List.append_assoc]
    simp

theorem length_lambdaPowers (lam : E) (n : ℕ) : (lambdaPowers lam n).length = n := by
  simp [lambdaPowers]

/-- **The claimed less the true batched value is the gaps' polynomial in `λ`.** -/
theorem claim_sub_eq_sum (t : List E) (cs : List ChildClaims) (lam : E) (column : List E) :
    batchedClaim cs (lambdaPowers lam cs.length) column -
        splitTrue t cs (lambdaPowers lam cs.length) column =
      ∑ m ∈ range (2 * cs.length), (gapsAt t cs column).getD m 0 * lam ^ m := by
  rw [batchedClaim, splitTrue, sub_pairs cs _ (length_lambdaPowers _ _), ← gapsAt,
    flat2_lambdaPowers, Tables.dot_eq_sum _ _ (by simp [length_gapsAt])]
  simp only [List.length_map, List.length_range]
  refine sum_congr rfl fun m hm ↦ ?_
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (mem_range.mp hm),
    Option.map_some, Option.getD_some, mul_comm]

/-- A gap of a child, by its index. -/
theorem getD_gapsAt (t : List E) (column : List E) :
    ∀ (cs : List ChildClaims) (i : ℕ) (hi : i < cs.length),
      (gapsAt t cs column).getD (2 * i) 0 = foldColumns column cs[i].freshClaim.values -
          multilinearEval t (cs[i].freshClaim.point ++ column) ∧
        (gapsAt t cs column).getD (2 * i + 1) 0 = cs[i].carriedClaim.bytecodeValue -
          multilinearEval t cs[i].carriedClaim.bytecodePoint
  | [], _, hi => absurd hi (Nat.not_lt_zero _)
  | c :: cs, 0, _ => by simp [gapsAt]
  | c :: cs, i + 1, hi => by
    have ih := getD_gapsAt t column cs i (by simpa using hi)
    simp only [gapsAt, List.flatMap_cons] at ih ⊢
    rw [show 2 * (i + 1) = 2 * i + 2 by ring, show 2 * i + 2 + 1 = 2 * i + 1 + 2 by ring,
      List.getD_append_right _ _ _ _ (by simp), List.getD_append_right _ _ _ _ (by simp)]
    simpa using ih

/-- A deferred claim that holds of the split program has its shape: the split table's length,
`n · 2^splitLog` for `n` instructions, a power of two, makes `n` one. -/
theorem _root_.LeanVM.Node.DeferredBytecodeClaim.HoldsWithShape.hasBytecodeShape
    {bytecode : List K} {claim : DeferredBytecodeClaim} (h : claim.HoldsWithShape bytecode) :
    claim.HasBytecodeShape bytecode := by
  unfold DeferredBytecodeClaim.HasBytecodeShape deferredVariableCount instructionVariableCount
  have hl := h.1
  rw [length_splitTable] at hl
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (Dvd.intro _ hl.symm)
  rw [hk, ← pow_add] at hl
  rw [hk, Nat.log2_two_pow]
  exact Nat.pow_right_injective le_rfl hl

/-! ## The gaps on the split table -/

/-- **A fresh claim's gap is multilinear in the column challenges**: its errors folded. -/
theorem freshGap_eq {bytecode : List K} {c : ChildClaims}
    (hn : bytecode.length >>> bytecodeSlotBits = 2 ^ c.freshClaim.point.length)
    (hv : c.freshClaim.values.length = (splitColumns tables).length)
    {column : List E} (hcol : column.length = splitLog) :
    foldColumns column c.freshClaim.values -
        multilinearEval ((splitTable bytecode).map ofK) (c.freshClaim.point ++ column) =
      ∑ j ∈ range (2 ^ splitLog), eqAt column j * (c.freshClaim.values.getD j 0 -
        (splitValues bytecode c.freshClaim.point).getD j 0) := by
  rw [foldColumns_eq hcol (by rw [hv, length_splitColumns]; decide), mle_splitTable_append hn hcol,
    ← sum_sub_distrib]
  refine sum_congr rfl fun j _ ↦ ?_
  ring

/-- The split values have one entry per split column. -/
theorem length_splitValues (bytecode : List K) (point : List E) :
    (splitValues bytecode point).length = (splitColumns tables).length := by
  simp [splitValues]

/-- **A false fresh claim leaves an error**: some split column's value differs. -/
theorem exists_ne_of_not_holds {bytecode : List K} {c : ChildClaims}
    (hv : c.freshClaim.values.length = (splitColumns tables).length)
    (hf : ¬ c.freshClaim.Holds bytecode) :
    ∃ j < 2 ^ splitLog, c.freshClaim.values.getD j 0 -
      (splitValues bytecode c.freshClaim.point).getD j 0 ≠ 0 := by
  by_contra hz
  push Not at hz
  apply hf
  refine List.ext_getElem (by rw [hv, length_splitValues]) fun j h1 h2 ↦ ?_
  have hj : j < 2 ^ splitLog := by
    rw [hv, length_splitColumns] at h1; exact h1.trans (by decide)
  have := sub_eq_zero.mp (hz j hj)
  rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this

/-! ## The group's escape -/

/-- **The batched gap vanishes rarely.** For children of the split program's shapes, the table
`2^n` entries with `n` instruction coordinates and `splitLog` column ones, one of whose claims is
false: the fraction of `λ` then of `splitLog` column challenges at which the batched claim is the
true one is at most `(2·|cs| + 4)/|E|`. -/
theorem avg_gap_le {bytecode : List K} {cs : List ChildClaims}
    (hn : bytecode.length >>> bytecodeSlotBits = 2 ^ instructionVariableCount bytecode)
    (hs : ∀ c ∈ cs, ChildHasBytecodeShape bytecode c)
    (hfalse : ∃ c ∈ cs, ¬ c.freshClaim.Holds bytecode ∨
      c.carriedClaim.bytecodeValue ≠
        multilinearEval ((splitTable bytecode).map ofK) c.carriedClaim.bytecodePoint) :
    invE * ∑ lam : E, avgL splitLog (fun column ↦ ind (batchedClaim cs (lambdaPowers lam cs.length)
        column = splitTrue ((splitTable bytecode).map ofK) cs (lambdaPowers lam cs.length) column)) ≤
      invE * (2 * cs.length + 4 : ℕ) := by
  set t := (splitTable bytecode).map ofK
  set a : ℕ → List E → E := fun m column ↦ (gapsAt t cs column).getD m 0
  -- the event is the gaps' polynomial vanishing
  have hev : ∀ (lam : E) (column : List E), (batchedClaim cs (lambdaPowers lam cs.length) column =
      splitTrue t cs (lambdaPowers lam cs.length) column) ↔
        ∑ m ∈ range (2 * cs.length), a m column * lam ^ m = 0 := by
    intro lam column
    rw [← claim_sub_eq_sum, sub_eq_zero]
  simp_rw [hev]
  rw [← avgL_comm]
  -- the coefficients: a fresh claim's multilinear, a carried claim's constant
  have hfresh : ∀ i (hi : i < cs.length) (column : List E), column.length = splitLog →
      a (2 * i) column = ∑ j ∈ range (2 ^ splitLog), eqAt column j *
        (cs[i].freshClaim.values.getD j 0 - (splitValues bytecode cs[i].freshClaim.point).getD j 0) := by
    intro i hi column hcol
    have hsi := hs cs[i] (List.getElem_mem hi)
    rw [show a (2 * i) column = _ from (getD_gapsAt t column cs i hi).1]
    exact freshGap_eq (by rw [hsi.1]; exact hn) hsi.2.1 hcol
  have hcarried : ∀ i (hi : i < cs.length) (column : List E),
      a (2 * i + 1) column = cs[i].carriedClaim.bytecodeValue -
        multilinearEval t cs[i].carriedClaim.bytecodePoint :=
    fun i hi column ↦ (getD_gapsAt t column cs i hi).2
  refine avgL_poly_le splitLog a (fun m ↦ if m % 2 = 0 then splitLog * invE else 0)
    (invE * (2 * cs.length + 4 : ℕ)) (2 * cs.length) (fun m hm hne ↦ ?_) ?_
  · rcases Nat.even_or_odd' m with ⟨i, rfl | rfl⟩
    · have hi : i < cs.length := by omega
      simp only [show 2 * i % 2 = 0 by omega, ↓reduceIte]
      refine ⟨?_, ?_⟩
      · -- some error is nonzero, or the gap would vanish
        have hd : ∃ j < 2 ^ splitLog, cs[i].freshClaim.values.getD j 0 -
            (splitValues bytecode cs[i].freshClaim.point).getD j 0 ≠ 0 := by
          by_contra hz
          push Not at hz
          exact hne fun column hcol ↦ by
            rw [hfresh i hi column hcol]
            exact sum_eq_zero fun j hj ↦ by rw [hz j (mem_range.mp hj), mul_zero]
        refine le_trans (avgL_mono splitLog fun column hcol ↦ le_of_eq ?_)
          (avgL_eqAt_le splitLog _ hd)
        rw [hfresh i hi column hcol]
      · have : 2 * i + splitLog ≤ 2 * cs.length + 4 := by simp only [splitLog]; omega
        calc invE * ((2 * i : ℕ) : ℝ≥0∞) + splitLog * invE
            = invE * ((2 * i + splitLog : ℕ) : ℝ≥0∞) := by push_cast; ring
          _ ≤ invE * (2 * cs.length + 4 : ℕ) := by gcongr
    · have hi : i < cs.length := by omega
      simp only [show (2 * i + 1) % 2 = 1 by omega, one_ne_zero, ↓reduceIte, add_zero]
      refine ⟨?_, ?_⟩
      · have hc : cs[i].carriedClaim.bytecodeValue -
            multilinearEval t cs[i].carriedClaim.bytecodePoint ≠ 0 := fun h0 ↦
          hne fun column _ ↦ by rw [hcarried i hi column, h0]
        refine le_of_eq_of_le (b := avgL splitLog fun _ ↦ 0) ?_ (by rw [avgL_const])
        congr 1
        funext column
        rw [hcarried i hi column, ind_of_not hc]
      · gcongr
        omega
  · -- a false claim makes its coefficient nonzero
    obtain ⟨c, hc, hf⟩ := hfalse
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
    rcases hf with hf | hf
    · refine ⟨2 * i, by omega, fun hz ↦ ?_⟩
      obtain ⟨j, hj, hd⟩ := exists_ne_of_not_holds (hs _ hc).2.1 hf
      have h1 := avgL_eqAt_le splitLog (fun j ↦ cs[i].freshClaim.values.getD j 0 -
        (splitValues bytecode cs[i].freshClaim.point).getD j 0) ⟨j, hj, hd⟩
      have h2 : avgL splitLog (fun column ↦ ind (∑ j ∈ range (2 ^ splitLog), eqAt column j *
          (cs[i].freshClaim.values.getD j 0 -
            (splitValues bytecode cs[i].freshClaim.point).getD j 0) = 0)) = 1 := by
        rw [← avgL_const splitLog 1]
        refine le_antisymm (avgL_mono splitLog fun _ _ ↦ ind_le_one _)
          (avgL_mono splitLog fun column hcol ↦ ?_)
        rw [← hfresh i hi column hcol, hz column hcol, ind_of rfl]
      rw [h2, invE, show (Fintype.card E : ℝ≥0∞) = 2 ^ 128 by exact_mod_cast LeanVM.Protocol.card_E]
        at h1
      have : (splitLog : ℝ≥0∞) * (2 ^ 128)⁻¹ < 1 := by
        rw [← div_eq_mul_inv, ENNReal.div_lt_iff (Or.inl (by simp)) (Or.inl (by simp)), one_mul]
        simp only [splitLog]
        norm_num
      exact absurd h1 (not_le.mpr this)
    · refine ⟨2 * i + 1, by omega, fun hz ↦ hf ?_⟩
      have h0 := hz (List.replicate splitLog 0) (List.length_replicate ..)
      rw [hcarried i hi] at h0
      exact sub_eq_zero.mp h0

end
end LeanVM.Guest.Batch
