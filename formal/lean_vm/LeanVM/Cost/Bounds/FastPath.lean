module

public import LeanVM.Cost.Bounds.FieldLib
public import LeanVM.Cost.Bounds.ListLib
public import LeanVM.Cost.Bounds.SortedMap
public import LeanVM.Cost.Extractor.Runner

/-!
# Bounds: the novel-basis transforms

The inverse novel-basis transform (`novelInv`, compiled as `novelInvC`, `Cost/Extractor/Runner.lean`)
the descent's step up and level 0's stack run per lane, and its parts (the list functions they
call: `Bounds/ListLib.lean`; the field's: `Bounds/FieldLib.lean`). With `N = 2^m` the buffer:

* `subspacePoly_cost` (`47·2^j + 12`), `novelTwiddles_cost` (`83·N + 2866`);
* **`novelInvStage_cost`** (`174·N + 2890`) per butterfly stage, **`novelInv_cost`** (`κ` stages
  over `2^κ`).

Word-size hypotheses: the buffers below `2^62` entries.
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Cost LeanVM.Cost.Extractor LeanVM.Cost.Library LeanVM.Parameters LeanVM.Extraction

public section

variable (P : MachineProgram)

/-! ## List functions -/

/-! ## Field arithmetic: the subspace polynomial and the inverse -/

/-- A product over `range n` (`prodRange.c103`): `B + 41` per factor, `5` at the end. -/
theorem prodRange_cost (hP : Includes P Auto.LeanVM.Cost.Rewrite.prodRange.c103.costDeps)
    (f : ℕ → K) (fVal : MachineValue) (hf : ∀ a : ℕ, RunsApp P fVal [encodeValue a] (encodeValue (f a))) (B : ℕ)
    (hB : ∀ a : ℕ, a < 2 ^ 64 → appCost P fVal [encodeValue a] ≤ B) :
    ∀ n, n < 2 ^ 64 →
      machineCost P Auto.LeanVM.Cost.Rewrite.prodRange.c103.costIdx [fVal, encodeValue n] ≤
        (B + 41) * n + 5 := by
  intro n
  induction n with
  | zero => intro _; rw [Auto.LeanVM.Cost.Rewrite.prodRange.c103.costEq_zero P hP f fVal hf]; omega
  | succ n ih =>
    intro hn
    rw [Auto.LeanVM.Cost.Rewrite.prodRange.c103.costEq_succ P hP f fVal hf, limbs_of_lt hn]
    have := ih (by omega)
    have := hB n (by omega)
    nlinarith

/-- **The subspace polynomial** `W_j(x)` (`subspacePoly.c102`): `2^j` products, at most
`47·2^j + 12`. -/
theorem subspacePoly_cost (hP : Includes P Auto.LeanVM.Extraction.subspacePoly.c102.costDeps)
    (j : ℕ) (hj : j < 64) (x : K) :
    machineCost P Auto.LeanVM.Extraction.subspacePoly.c102.costIdx [encodeValue j, encodeValue x] ≤
      47 * 2 ^ j + 12 := by
  rw [Auto.LeanVM.Extraction.subspacePoly.c102.costEq P hP, limbs_shift hj,
    limbs_of_lt (by omega : j < 2 ^ 64)]
  have := prodRange_cost P (by includes) _
    (.closure Auto.LeanVM.Extraction.subspacePoly.c102.lam0.costIdx [encodeValue x])
    (fun a ↦ RunsApp.of_spec (Auto.LeanVM.Extraction.subspacePoly.c102.lam0.costSpec P
      (by includes) x a)) 6
    (fun a ha ↦ by
      rw [appCost_fn, List.singleton_append,
        Auto.LeanVM.Extraction.subspacePoly.c102.lam0.costEq P (by includes), limbs_of_lt ha]
      rfl)
    (2 ^ j) (Nat.pow_lt_pow_right (by norm_num) hj)
  omega

/-- `Nat.testBit` (`testBit.c108`): `9` on words. -/
theorem testBit_cost (hP : Includes P Auto.Nat.testBit.c108.costDeps) (a b : ℕ) (ha : a < 2 ^ 64)
    (hb : b < 2 ^ 64) : machineCost P Auto.Nat.testBit.c108.costIdx [encodeValue a, encodeValue b] ≤ 9 := by
  rw [Auto.Nat.testBit.c108.costEq P hP, limbs_of_lt ha, limbs_of_lt hb,
    limbs_of_lt (lt_of_le_of_lt (Nat.shiftRight_le a b) ha),
    limbs_of_lt (lt_of_le_of_lt (Nat.and_le_left (n := 1) (m := a >>> b)) (by norm_num))]
  omega

/-! ## The novel-basis transforms -/

theorem pow_split {i m : ℕ} (h : i < m) : 2 ^ i * 2 ^ (m - (i + 1)) * 2 = 2 ^ m := by
  rw [← pow_add, ← pow_succ]; congr 1; omega

/-- **Stage `i`'s twiddles** over `2^m` (`novelTwiddles.c99`): `2^(m−i−1)` subspace polynomials
of `2^i` factors and one inverse: at most `83·2^m + 2866`. -/
theorem novelTwiddles_cost (hP : Includes P Auto.LeanVM.Extraction.novelTwiddles.c99.costDeps)
    (m i : ℕ) (hi : i < m) (hm : m ≤ 62) :
    machineCost P Auto.LeanVM.Extraction.novelTwiddles.c99.costIdx [encodeValue m, encodeValue i] ≤
      83 * 2 ^ m + 2866 := by
  rw [Auto.LeanVM.Extraction.novelTwiddles.c99.costEq P hP]
  have hsub := subspacePoly_cost P (by includes) i (by omega) (K.ofBits (2 ^ i))
  have hinv := invK_cost P (by includes) (subspacePoly i (K.ofBits (2 ^ i)))
  have hw : 2 ^ (m - (i + 1)) < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hof := ofFnFrom_cost P (by includes) hw _
    (.closure Auto.LeanVM.Extraction.novelTwiddles.c99.lam0.costIdx
      [encodeValue m, encodeValue i, encodeValue (subspacePoly i (K.ofBits (2 ^ i)))⁻¹])
    (fun a ↦ RunsApp.of_spec (Auto.LeanVM.Extraction.novelTwiddles.c99.lam0.costSpec P
      (by includes) m i _ a)) (47 * 2 ^ i + 54)
    (fun a ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      have hw2 : (a : ℕ) * 2 ^ (i + 1) < 2 ^ 64 := by
        have h2 : 2 ^ (m - (i + 1)) * 2 ^ (i + 1) = 2 ^ m := by rw [← pow_add]; congr 1; omega
        have h3 : 2 ^ m ≤ 2 ^ 62 := Nat.pow_le_pow_right (by norm_num) hm
        have h4 : (a : ℕ) * 2 ^ (i + 1) < 2 ^ (m - (i + 1)) * 2 ^ (i + 1) :=
          Nat.mul_lt_mul_of_pos_right a.isLt (by positivity)
        omega
      rw [Auto.LeanVM.Extraction.novelTwiddles.c99.lam0.costEq P (by includes), limbs_of_lt hw2,
        limbs_of_lt (by omega : i < 2 ^ 64), limbs_shift (by omega : i + 1 < 64),
        limbs_of_lt (by omega : i + 1 < 2 ^ 64), limbs_two_pow (by omega : i + 1 < 64),
        limbs_of_lt (by have := a.isLt; omega : (a : ℕ) < 2 ^ 64)]
      have := subspacePoly_cost P (by includes) i (by omega) (K.ofBits (↑a * 2 ^ (i + 1)))
      omega) 0 (Nat.zero_le _)
  rw [ofFnFrom_length, limbs_shift (by omega : i < 64), limbs_of_lt (by omega : i < 2 ^ 64),
    limbs_of_lt (by omega : m < 2 ^ 64), limbs_of_lt (by omega : i + 1 < 2 ^ 64),
    limbs_shift (by omega : m - (i + 1) < 64), limbs_of_lt (by omega : m - (i + 1) < 2 ^ 64)]
  have e := pow_split hi
  have h1 : 2 ^ i * 2 ≤ 2 ^ m := by
    have := Nat.pow_le_pow_right (n := 2) (by norm_num) (show i + 1 ≤ m by omega)
    rw [pow_succ] at this; omega
  have h2 : 2 ^ (m - (i + 1)) * 2 ≤ 2 ^ m := by
    have := Nat.pow_le_pow_right (n := 2) (by norm_num) (show m - (i + 1) + 1 ≤ m by omega)
    rw [pow_succ] at this; omega
  rw [limbs_two_pow (by omega : i < 64)]
  simp only [max_self, Nat.sub_zero] at hof ⊢
  nlinarith

/-- **An inverse butterfly stage** over `2^m` (`novelInvStage.c98`): at most `174·2^m + 2890`. -/
theorem novelInvStage_cost (hP : Includes P Auto.LeanVM.Extraction.novelInvStage.c98.costDeps)
    (m i : ℕ) (hi : i < m) (hm : m ≤ 62) (b : Array K) :
    machineCost P Auto.LeanVM.Extraction.novelInvStage.c98.costIdx [encodeValue m, encodeValue i, encodeValue b] ≤
      174 * 2 ^ m + 2890 := by
  rw [Auto.LeanVM.Extraction.novelInvStage.c98.costEq P hP]
  have htw := novelTwiddles_cost P (by includes) m i hi hm
  have hN : 2 ^ m < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hof := ofFnFrom_cost P (by includes) hN _
    (.closure Auto.LeanVM.Extraction.novelInvStage.c98.lam0.costIdx
      [encodeValue m, encodeValue i, encodeValue b, encodeValue (novelTwiddles m i)])
    (fun a ↦ RunsApp.of_spec (Auto.LeanVM.Extraction.novelInvStage.c98.lam0.costSpec P
      (by includes) m i b _ a)) 74
    (fun a ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      have ha : (a : ℕ) < 2 ^ 64 := by have := a.isLt; omega
      have hpi : (a : ℕ) + 2 ^ i < 2 ^ 64 := by
        have := a.isLt
        have : 2 ^ m ≤ 2 ^ 62 := Nat.pow_le_pow_right (by norm_num) hm
        have : 2 ^ i ≤ 2 ^ 62 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      rw [Auto.LeanVM.Extraction.novelInvStage.c98.lam0.costEq P (by includes), limbs_of_lt hpi,
        limbs_of_lt (by omega : i < 2 ^ 64), limbs_shift (by omega : i + 1 < 64),
        limbs_of_lt (by omega : i + 1 < 2 ^ 64), limbs_two_pow (by omega : i + 1 < 64),
        limbs_of_lt ha, limbs_shift (by omega : i < 64), limbs_two_pow (by omega : i < 64)]
      have := testBit_cost P (by includes) a i ha (by omega)
      split_ifs <;> simp only [max_self] <;> omega) 0 (Nat.zero_le _)
  rw [ofFnFrom_length, limbs_shift (by omega : m < 64), limbs_of_lt (by omega : m < 2 ^ 64)]
  simp only [Nat.sub_zero] at hof
  omega

/-- **The inverse transform** over `2^κ` (`novelInvC`: a fold of `novelInvStage` over
`range κ`): at most `κ·(174·2^κ + 2906) + 15·κ + 16`. -/
theorem novelInv_cost (hP : Includes P novelInvC.costDeps) (κ : ℕ) (hκ : κ ≤ 62) (y : Array K) :
    machineCost P novelInvC.costIdx [encodeValue κ, encodeValue y] ≤
      κ * (174 * 2 ^ κ + 2906) + 15 * κ + 16 := by
  rw [novelInvC.costEq P hP]
  have := listFoldl_le P (by includes) _ (.closure novelInvC.lam0.costIdx [encodeValue κ])
    (fun a b ↦ RunsApp.of_spec (novelInvC.lam0.costSpec P (by includes) κ a b))
    (174 * 2 ^ κ + 2895) (fun _ ↦ True) (List.range κ) y trivial
    (fun acc _ i hi ↦ ⟨trivial, by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [novelInvC.lam0.costEq P (by includes)]
      have := novelInvStage_cost P (by includes) κ i (List.mem_range.1 hi) hκ acc
      omega⟩)
  rw [List.length_range] at this
  have hr := rangeLoop_cost P (by includes) κ [] (by omega)
  nlinarith

theorem leafAt_length_le (leaves : Array (List K)) (h w v : ℕ) (hl : ∀ l ∈ leaves, l.length ≤ w) :
    (leafAt leaves h w v).length ≤ w := by
  unfold leafAt
  rw [Array.getD_eq_getD_getElem?]
  generalize hx : leaves[v % 2 ^ h]? = o
  cases o with
  | none => simp
  | some l => exact hl l (Array.mem_of_getElem? hx)

end

end LeanVM.Cost.Bounds
