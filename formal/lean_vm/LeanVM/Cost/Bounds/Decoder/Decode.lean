module

public import LeanVM.Cost.Bounds.Decoder.Prune
public import LeanVM.Cost.Bounds.Decoder.Prefixes
public import LeanVM.Cost.Prices

/-!
# Bound: the decoder's parameter search, compiled

The parameter search of a lane (`gsMultiplicityAt`: one `gsPass` per multiplicity up to
`gsMultiplicityBoundAt`), compiled in the decoder's chain (`Cost/Extractor/PMLane.lean`):
**`decoderSearchC_cost`**, and the parameters at the multiplicity found (`decoderParamsAtC_cost`).
The lane and the decoder on the approximant-basis interpolation are bounded in
`Bounds/PMLane/Decode.lean`.
-/

namespace LeanVM.Cost.Bounds.Decoder

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library
open LeanVM.Cost.Extractor LeanVM.Parameters CompPoly LeanVM.Extraction LeanVM.Extraction.Fast

/-! The functions compiled on demand, by their short names. -/
open LeanVM.Cost.Auto.LeanVM.Extraction.Fast LeanVM.Cost.Auto.LeanVM.Extraction
open CompPoly.GuruswamiSudan

public section

variable (P : MachineProgram)

/-! ## The parameter search -/

theorem decoderMul_lt {a b i j : ℕ} (ha : a < 2 ^ i) (hb : b < 2 ^ j) : a * b < 2 ^ (i + j) := by
  rw [Nat.pow_add]
  exact Nat.mul_lt_mul'' ha hb

/-- `gsParamsAt k n A m`: at most `17`, the sizes word-sized. -/
theorem decoderParamsAtC_cost (hP : Includes P gsParamsAt.c672.costDeps) {k n A m : ℕ}
    (hn : n < 2 ^ 32) (hA : A ≤ n) (hm : m < 2 ^ 20) :
    machineCost P gsParamsAt.c672.costIdx [encodeValue k, encodeValue n, encodeValue A, encodeValue m] ≤ 17 := by
  rw [gsParamsAt.c672.costEq P hP]
  have hmA : m * A < 2 ^ 52 := decoderMul_lt (i := 20) (j := 32) hm (by omega)
  rw [limbs_of_lt (show m < 2 ^ 64 by omega), limbs_of_lt (show A < 2 ^ 64 by omega),
    limbs_of_lt (show m * A < 2 ^ 64 by omega), limbs_of_lt (show n < 2 ^ 64 by omega)]
  simp

/-- **One parameter check** (`gsPass k n (n − A) (gsParamsAt k n A m)`): at most `78`, the sizes
word-sized. -/
theorem decoderPassC_cost (hP : Includes P gsPass.c675.costDeps) {k n A m : ℕ}
    (hk : k < 2 ^ 32) (hn : n < 2 ^ 32) (hA : A ≤ n) (hm : m < 2 ^ 20) :
    machineCost P gsPass.c675.costIdx [encodeValue k, encodeValue n, encodeValue (n - A), encodeValue (gsParamsAt k n A m)] ≤
      78 := by
  rw [gsPass.c675.costEq P (by includes), gsNumConstraints.c676.costEq P (by includes),
    gsNumVars.c677.costEq P (by includes)]
  dsimp only [gsParamsAt]
  have hmA : m * A < 2 ^ 52 := decoderMul_lt (i := 20) (j := 32) hm (by omega)
  have hmm : m * (m + 1) < 2 ^ 41 := decoderMul_lt (i := 20) (j := 21) hm (by omega)
  have hmm2 : m * (m + 1) / 2 ≤ m * (m + 1) := Nat.div_le_self _ _
  have hnm : n * (m * (m + 1) / 2) < 2 ^ 73 := decoderMul_lt (i := 32) (j := 41) hn (by omega)
  have hW1 : (m * A - 1) / (k - 1) ≤ (m * A - 1) := Nat.div_le_self _ _
  have hW2 : (k - 1) * ((m * A - 1) / (k - 1)) ≤ (m * A - 1) := Nat.mul_div_le _ _
  have hprod : ((m * A - 1) / (k - 1) + 1) *
      (2 * (m * A - 1) + 2 - (k - 1) * ((m * A - 1) / (k - 1))) < 2 ^ 106 :=
    decoderMul_lt (i := 53) (j := 53) (by omega) (by omega)
  have hnv : gsNumVars k (m * A - 1) < 2 ^ 106 := (Nat.div_le_self _ _).trans_lt hprod
  have hm1 : m * (n - (n - A)) < 2 ^ 52 := by rw [show n - (n - A) = A by omega]; exact hmA
  have hl := fun x (h : x < 2 ^ 64) ↦ limbs_of_lt h
  simp (disch := omega) only [hl]
  have h1 := limbs_le_two (x := gsNumConstraints n m) (by unfold gsNumConstraints; omega)
  have h4 := limbs_le_two (x := n * (m * (m + 1) / 2)) (by omega)
  have h2 := limbs_le_two (x := gsNumVars k (m * A - 1)) (by omega)
  have h3 := limbs_le_two
    (x := ((m * A - 1) / (k - 1) + 1) * (2 * (m * A - 1) + 2 - (k - 1) * ((m * A - 1) / (k - 1))))
    (by omega)
  simp only [Nat.max_self, Nat.mul_one]
  split_ifs <;> omega

/-- `gsMultiplicityBoundAt k n A`: at most `19`, the sizes word-sized. -/
theorem decoderMultBoundC_cost (hP : Includes P gsMultiplicityBoundAt.c678.costDeps) {k n A : ℕ}
    (hk : k < 2 ^ 31) (hn : n < 2 ^ 32) (hA : A ≤ n) :
    machineCost P gsMultiplicityBoundAt.c678.costIdx [encodeValue k, encodeValue n, encodeValue A] ≤ 19 := by
  rw [gsMultiplicityBoundAt.c678.costEq P hP]
  have h1 : (k - 1) * n < 2 ^ 63 := decoderMul_lt (i := 31) (j := 32) (by omega) hn
  have h2 : A * A < 2 ^ 64 := decoderMul_lt (i := 32) (j := 32) (by omega) (by omega)
  have h3 : ((k - 1) * n + 1) / (A * A - (k - 1) * n) ≤ (k - 1) * n + 1 := Nat.div_le_self _ _
  have hl := fun x (h : x < 2 ^ 64) ↦ limbs_of_lt h
  simp (disch := omega) only [hl]
  simp

theorem decoderMultiplicity_le (k n A : ℕ) :
    gsMultiplicityAt k n A ≤ gsMultiplicityBoundAt k n A := by
  unfold gsMultiplicityAt
  cases h : (List.range' 1 (gsMultiplicityBoundAt k n A)).find?
      (fun m ↦ gsPass k n (n - A) (gsParamsAt k n A m)) with
  | none => simp
  | some m =>
    have := List.mem_range'.1 (List.mem_of_find?_eq_some h)
    simp only [Option.getD_some]
    omega

/-- **The parameter search** (`gsMultiplicityAt k n A`: a check per multiplicity below
`b = gsMultiplicityBoundAt k n A`): at most `138·b + 66`, the sizes word-sized, `b < 2^20`. -/
theorem decoderSearchC_cost (hP : Includes P gsMultiplicityAt.c673.costDeps) {k n A : ℕ}
    (hk : k < 2 ^ 31) (hn : n < 2 ^ 32) (hA : A ≤ n) (hb : gsMultiplicityBoundAt k n A < 2 ^ 20) :
    machineCost P gsMultiplicityAt.c673.costIdx [encodeValue k, encodeValue n, encodeValue A] ≤
      138 * gsMultiplicityBoundAt k n A + 66 := by
  rw [gsMultiplicityAt.c673.costEq P hP]
  have h1 := decoderMultBoundC_cost P (by includes) hk hn hA
  have h2 := rangeC_cost P (by includes) (gsMultiplicityBoundAt k n A) 1 (by omega)
  have hf := fun m ↦ RunsApp.of_spec (us := [encodeValue k, encodeValue n, encodeValue A]) (vs := [encodeValue m])
    (gsMultiplicityAt.c673.lam0.costSpec P (by includes) k n A m)
  have h3 := findNat_cost P (by includes) _
    (.closure gsMultiplicityAt.c673.lam0.costIdx [encodeValue k, encodeValue n, encodeValue A]) hf 109
    (List.range' 1 (gsMultiplicityBoundAt k n A)) (fun m hm ↦ by
      have hm' := List.mem_range'.1 hm
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [gsMultiplicityAt.c673.lam0.costEq P (by includes),
        limbs_of_lt (show n < 2 ^ 64 by omega), limbs_of_lt (show A < 2 ^ 64 by omega)]
      have := decoderParamsAtC_cost P (by includes) (k := k) hn hA (m := m) (by omega)
      have := decoderPassC_cost P (by includes) (k := k) (by omega) hn hA (m := m) (by omega)
      simp only [Nat.max_self]
      omega)
  simp only [List.length_range'] at h3
  cases List.find? (fun m ↦ gsPass k n (n - A) (gsParamsAt k n A m))
    (List.range' 1 (gsMultiplicityBoundAt k n A)) <;> dsimp only <;> omega

end

end LeanVM.Cost.Bounds.Decoder
