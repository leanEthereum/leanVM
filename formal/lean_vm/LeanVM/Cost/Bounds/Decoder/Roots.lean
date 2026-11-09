module

public import LeanVM.Cost.Bounds.Decoder.Interpolate
public import LeanVM.Cost.Bounds.Sizes.RootFinder
public import LeanVM.Cost.Bounds.Sizes.Splitter
public import LeanVM.Cost.Extractor.Roots
import all CompPoly.Univariate.Raw.Core
import all CompPoly.Univariate.Raw.Ops
import all CompPoly.Univariate.Raw.Context
import all CompPoly.Univariate.Raw.Division
import all CompPoly.Univariate.Raw.Modular
import all CompPoly.Univariate.Basic
import all CompPoly.Univariate.Roots.Shoup.Basic
import all CompPoly.Univariate.Roots.Splitter

/-!
# Bound: arithmetic modulo a polynomial over `K`, compiled

The prices of the root finder's arithmetic (`Cost/Extractor/Roots.lean`) on polynomials of at
most `B` coefficients, `B` word-sized:

* `monicNormalize` (an inverse and a scaling), the remainder-only long division
  (`modByMonicRemainderOnly.go`: each step rebuilds the remainder, `≤ 117·A + 82` for a
  remainder of `≤ A` coefficients);
* the product modulo `u` (`mulModWithC_cost`: `≤ mulModBound B = 582·B² + 430·B + 2960`), the
  binary powering (`powModBinaryAuxC_cost`: `log₂ n + 1` steps of two products), `X^q − X mod u`
  (`xPowSubXModC_cost`);
* the remainder `p mod q` (`rawModFastC_cost`) and the monic gcd (`rawGcdMonicWithFuelC_cost`,
  `gcdMonicFastC_cost`: at most `2·B + 1` remainders).

**Honest-cost note.** The remainder-only long division rebuilds the whole remainder at each step
(`subScaledShift` over all `|a|` coefficients, then a trim), so a remainder of `p` by `q` costs
`O(|p|²)`, not `O(|q|·(|p| − |q| + 1))`; the Euclidean gcd is then `O(B³)`, not `O(B²)`.
-/

namespace LeanVM.Cost.Bounds.Decoder

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library
open LeanVM.Cost.Extractor LeanVM.Parameters CompPoly LeanVM.Extraction.Fast
open CompPoly.CPolynomial.Roots.FiniteField

/-! The functions compiled on demand, by their short names. -/
open LeanVM.Cost.Auto.CompPoly.CPolynomial.Raw LeanVM.Cost.Auto.LeanVM.Extraction.Fast

open LeanVM.Extraction.Fast.PMDegree (val_size_le_natDegree_add_one)

public section

variable (P : MachineProgram)

theorem size_zero_raw : (0 : CPolynomial.Raw K).size = 0 := rfl

theorem size_one_raw : (1 : CPolynomial.Raw K).size = 1 := by
  change (#[] |>.push (1 : K)).size = 1
  simp

theorem size_X_raw : (CPolynomial.Raw.X : CPolynomial.Raw K).size = 2 := by
  simp [CPolynomial.Raw.X]

theorem toList_zero_raw : Array.toList (0 : CPolynomial.Raw K) = [] := rfl

/-- `getLastD`: at most `7`. -/
theorem getLastDC_cost (hP : Includes P Auto.Array.getLastD.c32.costDeps) (a : Array K) (v : K)
    (ha : a.size < 2 ^ 64) : machineCost P Auto.Array.getLastD.c32.costIdx [encodeValue a, encodeValue v] ≤ 7 := by
  rw [Auto.Array.getLastD.c32.costEq P hP]
  cost_simp
  omega

theorem trim_size_le' (p : CPolynomial.Raw K) : p.trim.size ≤ p.size := raw_trim_size_le p

/-- **`monicNormalize`** (raw): at most `92·|p| + 2884`. -/
theorem monicNormalizeRawC_cost (hP : Includes P monicNormalize.c28.costDeps)
    (p : CPolynomial.Raw K) (hp : p.size < 2 ^ 60) :
    machineCost P monicNormalize.c28.costIdx [encodeValue p] ≤ 92 * p.size + 2884 := by
  rw [monicNormalize.c28.costEq P hP]
  have ht := trim_size_le' p
  have := trimLen_cost P (by includes) p p.size (by omega)
  have := trimLen_cost P (by includes) p.trim p.trim.size (by omega)
  have : (Array.extract p 0 (CompPolyLib.trimLen p p.size)).size ≤ p.size := by simp
  have : (Array.extract p.trim 0 (CompPolyLib.trimLen p.trim p.trim.size)).size ≤ p.size := by
    simp; omega
  have := beqNilK_cost P (by includes) p.trim.toList
  have := getLastDC_cost P (by includes) p.trim.trim 0 (by have := trim_size_le' p.trim; omega)
  have := invK_cost P (by includes) p.trim.leadingCoeff
  have := smulK_cost P (by includes) p.trim.leadingCoeff⁻¹ p.trim
  simp only [size_zero_raw, toList_zero_raw] at *
  split_ifs <;> omega

/-- One coefficient of `p − scale·X^shift·q`: at most `54`. -/
theorem subScaledShiftLamC_cost (hP : Includes P subScaledShift.c45.lam0.costDeps)
    (p q : CPolynomial.Raw K) (scale : K) (shift : ℕ) (j : Fin p.size) (hp : p.size < 2 ^ 64)
    (hq : q.size < 2 ^ 64) (hs : shift < 2 ^ 64) :
    machineCost P subScaledShift.c45.lam0.costIdx [encodeValue p, encodeValue q, encodeValue scale, encodeValue shift, encodeValue j] ≤
      54 := by
  rw [subScaledShift.c45.lam0.costEq P hP]
  have := j.isLt
  cost_simp
  split_ifs <;> omega

/-- **`p − scale·X^shift·q`** (`subScaledShift`, the array rebuilt then trimmed): at most
`96·|p| + 32`. -/
theorem subScaledShiftC_cost (hP : Includes P subScaledShift.c45.costDeps)
    (p q : CPolynomial.Raw K) (scale : K) (shift : ℕ) (hp : p.size < 2 ^ 60)
    (hq : q.size < 2 ^ 64) (hs : shift < 2 ^ 64) :
    machineCost P subScaledShift.c45.costIdx [encodeValue p, encodeValue q, encodeValue scale, encodeValue shift] ≤
      96 * p.size + 32 := by
  rw [subScaledShift.c45.costEq P hP]
  have hf := fun j ↦ RunsApp.of_spec (us := [encodeValue p, encodeValue q, encodeValue scale, encodeValue shift]) (vs := [encodeValue j])
    (subScaledShift.c45.lam0.costSpec P (by includes) p q scale shift j)
  have := ofFnFrom_cost P (by includes) (n := p.size) (by omega) _
    (.closure subScaledShift.c45.lam0.costIdx [encodeValue p, encodeValue q, encodeValue scale, encodeValue shift]) hf 58
    (fun j ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      have := subScaledShiftLamC_cost P (by includes) p q scale shift j (by omega) hq hs
      omega)
    0 (by omega)
  generalize hA : (CPolynomial.Raw.mk (Array.ofFn fun j : Fin p.size ↦
    p.coeff ↑j - (if shift ≤ ↑j ∧ ↑j - shift < q.size then scale * q.coeff (↑j - shift) else 0)))
      = A at *
  have hAs : A.size = p.size := by rw [← hA]; simp [CPolynomial.Raw.mk]
  have := trimLen_cost P (by includes) A A.size (by omega)
  have : (Array.extract A 0 (CompPolyLib.trimLen A A.size)).size ≤ A.size := by simp
  simp only [length_ofFnFrom, Nat.sub_zero] at *
  omega

/-- **The remainder-only long division** (`modByMonicRemainderOnly.go`, `n` steps, remainders of
at most `A` coefficients): at most `(117·A + 82)·n + 5`. -/
theorem modGoC_cost (hP : Includes P modByMonicRemainderOnly.go.c44.costDeps)
    (q : CPolynomial.Raw K) (A : ℕ) (hA : A < 2 ^ 60) (hq : q.size < 2 ^ 64) :
    ∀ (n : ℕ) (a : CPolynomial.Raw K), n < 2 ^ 63 → a.size ≤ A →
      machineCost P modByMonicRemainderOnly.go.c44.costIdx [encodeValue n, encodeValue a, encodeValue q] ≤
        (117 * A + 82) * n + 5 := by
  intro n
  induction n with
  | zero => intro a _ _; rw [modByMonicRemainderOnly.go.c44.costEq_zero P hP]; omega
  | succ n ih =>
    intro a hn ha
    rw [modByMonicRemainderOnly.go.c44.costEq_succ P hP]
    have hsub := subScaledShift_size_le a q a.leadingCoeff (a.size - q.size)
    have := ih (a.subScaledShift q a.leadingCoeff (a.size - q.size)) (by omega) (by omega)
    have := subScaledShiftC_cost P (by includes) a q a.leadingCoeff (a.size - q.size) (by omega)
      hq (by omega)
    have := trimLen_cost P (by includes) a a.size (by omega)
    have : (Array.extract a 0 (CompPolyLib.trimLen a a.size)).size ≤ a.size := by simp
    have := getLastDC_cost P (by includes) a.trim 0 (by have := trim_size_le' a; omega)
    cost_simp
    have e : (117 * A + 82) * (n + 1) = (117 * A + 82) * n + 117 * A + 82 := by ring
    split_ifs <;> omega

theorem naive_mul_size_le (p q : CPolynomial.Raw K) :
    (CPolynomial.Raw.MulContext.naive.mul p q).size ≤ p.size + q.size :=
  (raw_trim_size_le _).trans (size_mulRaw_le p q)

/-- **A product modulo `u`** (`mulModWith`: the schoolbook product, then the remainder by
`monicNormalize u`): at most `mulModBound B`. -/
theorem mulModWithC_cost (hP : Includes P mulModWith.c54.costDeps) {B : ℕ} (hB : B < 2 ^ 28)
    (u p q : CPolynomial.Raw K) (hu : u.size ≤ B) (hp : p.size ≤ B) (hq : q.size ≤ B) :
    machineCost P mulModWith.c54.costIdx [encodeValue u, encodeValue p, encodeValue q] ≤ mulModBound B := by
  rw [mulModWith.c54.costEq P hP]
  have := mulK_cost P (by includes) p q (by omega) (by omega)
  have h1 : q.size * p.size ≤ B * B := Nat.mul_le_mul hq hp
  have h2 : p.size * p.size ≤ B * B := Nat.mul_le_mul hp hp
  have ht := trim_size_le' u
  have := trimLen_cost P (by includes) u u.size (by omega)
  have : (Array.extract u 0 (CompPolyLib.trimLen u u.size)).size ≤ u.size := by simp
  have := beqNilK_cost P (by includes) u.trim.toList
  have := monicNormalizeRawC_cost P (by includes) u (by omega)
  have hm := naive_mul_size_le p q
  have := modGoC_cost P (by includes) u.monicNormalize (2 * B) (by omega)
    (by have := raw_monicNormalize_size_le u; omega)
    (CPolynomial.Raw.MulContext.naive.mul p q).size (CPolynomial.Raw.MulContext.naive.mul p q)
    (by omega) (by omega)
  have h3 : (117 * (2 * B) + 82) * (CPolynomial.Raw.MulContext.naive.mul p q).size ≤
      (117 * (2 * B) + 82) * (2 * B) := Nat.mul_le_mul_left _ (by omega)
  have e : (117 * (2 * B) + 82) * (2 * B) = 468 * (B * B) + 164 * B := by ring
  simp only [size_zero_raw, toList_zero_raw] at *
  unfold mulModBound
  split_ifs <;> omega

theorem sqModC_cost (hP : Includes P sqMod.c71.costDeps) {B : ℕ} (hB : B < 2 ^ 28)
    (u c : CPolynomial.Raw K) (hu : u.size ≤ B) (hc : c.size ≤ B) :
    machineCost P sqMod.c71.costIdx [encodeValue u, encodeValue c] ≤ mulModBound B + 4 := by
  rw [sqMod.c71.costEq P hP]
  have := mulModWithC_cost P (by includes) hB u c c hu hc hc
  omega

theorem mulModWith_size_le {u a b : CPolynomial.Raw K} {B : ℕ} (hu : u.trim ≠ 0)
    (huB : u.size ≤ B) :
    (CPolynomial.Raw.mulModWith CPolynomial.Raw.MulContext.naive
      CPolynomial.Raw.ModContext.remainderOnly u a b).size ≤ B := by
  have := mulModWith_size_lt u a b hu
  have := trim_size_le' u
  omega

/-- **The binary powering modulo `u`** (`powModBinaryAuxWith`: per bit of `n` a squaring and at
most one product): at most `5 + (2·mulModBound B + 41)·(log₂ n + 1)`, `n < 2^65`. -/
theorem powModBinaryAuxC_cost (hP : Includes P powModBinaryAuxWith.c53.costDeps) {B : ℕ}
    (hB : B < 2 ^ 28) (u : CPolynomial.Raw K) (hu : u.trim ≠ 0) (huB : u.size ≤ B)
    (n : ℕ) (acc c : CPolynomial.Raw K) (hn : n < 2 ^ 65) (hacc : acc.size ≤ B)
    (hc : c.size ≤ B) :
    machineCost P powModBinaryAuxWith.c53.costIdx [encodeValue u, encodeValue n, encodeValue acc, encodeValue c] ≤
      5 + (2 * mulModBound B + 41) * (Nat.log2 n + 1) := by
  have key := le_of_halving
    (fun x : ℕ × CPolynomial.Raw K × CPolynomial.Raw K ↦
      x.2.1.size ≤ B ∧ x.2.2.size ≤ B ∧ x.1 < 2 ^ 65)
    (fun x ↦ x.1)
    (fun x ↦ machineCost P powModBinaryAuxWith.c53.costIdx [encodeValue u, encodeValue x.1, encodeValue x.2.1, encodeValue x.2.2])
    (2 * mulModBound B + 41) 5
    (fun x _ h0 ↦ by
      obtain ⟨n, acc, c⟩ := x
      dsimp only at h0 ⊢
      subst h0
      rw [powModBinaryAuxWith.c53.costEq_zero P hP])
    (fun x hI hpos ↦ by
      obtain ⟨n, acc, c⟩ := x
      obtain ⟨hacc, hc, hn⟩ := hI
      dsimp only at hpos hacc hc hn ⊢
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      right
      refine ⟨((k + 1) / 2,
        if ((k + 1) % 2 == 1) = true then CPolynomial.Raw.mulModWith
          CPolynomial.Raw.MulContext.naive CPolynomial.Raw.ModContext.remainderOnly u acc c
        else acc,
        CPolynomial.Raw.mulModWith CPolynomial.Raw.MulContext.naive
          CPolynomial.Raw.ModContext.remainderOnly u c c), ⟨?_, ?_, ?_⟩, le_rfl, ?_⟩
      · dsimp only
        split_ifs
        · exact mulModWith_size_le hu huB
        · exact hacc
      · exact mulModWith_size_le hu huB
      · dsimp only; omega
      · dsimp only
        rw [powModBinaryAuxWith.c53.costEq_succ P hP]
        have := mulModWithC_cost P (by includes) hB u acc c huB hacc hc
        have := mulModWithC_cost P (by includes) hB u c c huB hc hc
        have := limbs_le_two (x := k + 1) (by omega)
        have := limbs_le_two (x := k) (by omega)
        rw [limbs_of_lt (show (k + 1) % 2 < 2 ^ 64 by omega)]
        split_ifs <;> omega)
  exact key (n, acc, c) ⟨hacc, hc, hn⟩


theorem powModWith_size_le {u base : CPolynomial.Raw K} {B : ℕ} (hu : u.trim ≠ 0)
    (huB : u.size ≤ B) (e : ℕ) :
    (CPolynomial.Raw.powModWith CPolynomial.Raw.MulContext.naive
      CPolynomial.Raw.ModContext.remainderOnly u base e).size ≤ B := by
  rw [CPolynomial.Raw.powModWith]
  have : (u.trim == 0) = false := by simpa using hu
  simp only [this, Bool.false_eq_true, ↓reduceIte]
  have := powModBinaryAuxWith_size_lt u hu e _ base (remainderOnly_size_lt u 1 raw_one_trim hu)
  have := trim_size_le' u
  omega

theorem xModWith_size_le {u : CPolynomial.Raw K} {B : ℕ} (hu : u.trim ≠ 0) (huB : u.size ≤ B) :
    (CPolynomial.Raw.xModWith CPolynomial.Raw.ModContext.remainderOnly u).size ≤ B := by
  rw [CPolynomial.Raw.xModWith]
  have : (u.trim == 0) = false := by simpa using hu
  simp only [this, Bool.false_eq_true, ↓reduceIte]
  have := remainderOnly_size_lt u _ raw_X_trim hu
  have := trim_size_le' u
  omega

/-- **`base^e mod u`** (`powModWith`): at most
`116·B + 3142 + (2·mulModBound B + 41)·(log₂ e + 1)`. -/
theorem powModWithC_cost (hP : Includes P powModWith.c52.costDeps) {B : ℕ} (hB : B < 2 ^ 28)
    (hB1 : 1 ≤ B) (u base : CPolynomial.Raw K) (hu : u.trim ≠ 0) (huB : u.size ≤ B)
    (hbase : base.size ≤ B) (e : ℕ) (he : e < 2 ^ 65) :
    machineCost P powModWith.c52.costIdx [encodeValue u, encodeValue base, encodeValue e] ≤
      116 * B + 3142 + (2 * mulModBound B + 41) * (Nat.log2 e + 1) := by
  rw [powModWith.c52.costEq P hP]
  have ht := trim_size_le' u
  have := trimLen_cost P (by includes) u u.size (by omega)
  have : (Array.extract u 0 (CompPolyLib.trimLen u u.size)).size ≤ u.size := by simp
  have := beqNilK_cost P (by includes) u.trim.toList
  have := monicNormalizeRawC_cost P (by includes) u (by omega)
  have := modGoC_cost P (by includes) u.monicNormalize 1 (by omega)
    (by have := raw_monicNormalize_size_le u; omega) (Array.size 1) 1
    (by rw [size_one_raw]; omega) (by rw [size_one_raw])
  have hz : (u.trim == 0) = false := by simpa using hu
  simp only [hz, Bool.false_eq_true, ↓reduceIte, size_one_raw, toList_zero_raw,
    size_zero_raw] at *
  have := powModBinaryAuxC_cost P (by includes) hB u hu huB e
    (CPolynomial.Raw.ModContext.remainderOnly.modByMonic 1 u.monicNormalize) base he
    (by have := remainderOnly_size_lt u 1 raw_one_trim hu; omega) hbase
  omega

/-- **`X mod u`** (`xModWith`): at most `116·B + 3578`. -/
theorem xModWithC_cost (hP : Includes P xModWith.c56.costDeps) {B : ℕ} (hB : B < 2 ^ 28)
    (u : CPolynomial.Raw K) (huB : u.size ≤ B) :
    machineCost P xModWith.c56.costIdx [encodeValue u] ≤ 116 * B + 3578 := by
  rw [xModWith.c56.costEq P hP, X.c55.costEq P (by includes)]
  have ht := trim_size_le' u
  have := trimLen_cost P (by includes) u u.size (by omega)
  have : (Array.extract u 0 (CompPolyLib.trimLen u u.size)).size ≤ u.size := by simp
  have := beqNilK_cost P (by includes) u.trim.toList
  have := monicNormalizeRawC_cost P (by includes) u (by omega)
  have := modGoC_cost P (by includes) u.monicNormalize 2 (by omega)
    (by have := raw_monicNormalize_size_le u; omega) (Array.size CPolynomial.Raw.X)
    CPolynomial.Raw.X (by rw [size_X_raw]; omega) (by rw [size_X_raw])
  simp only [size_X_raw, size_zero_raw, toList_zero_raw] at *
  split_ifs <;> omega

/-- **`p − q`** (raw): at most `71·max(|p|, |q|) + 72`. -/
theorem subRawC_cost (hP : Includes P sub.c49.costDeps) (p q : CPolynomial.Raw K)
    (hp : p.size < 2 ^ 60) (hq : q.size < 2 ^ 60) :
    machineCost P sub.c49.costIdx [encodeValue p, encodeValue q] ≤ 71 * max p.size q.size + 72 := by
  rw [sub.c49.costEq P hP]
  have hf := fun a ↦ RunsApp.of_spec (us := []) (vs := [encodeValue a])
    (sub.c49.lam0.costSpec P (by includes) a)
  have hm := listMap_le P Auto.List.map.c30.costIdx (.closure sub.c49.lam0.costIdx [])
    (Auto.List.map.c30.costEq_nil P (by includes) _ _ hf)
    (Auto.List.map.c30.costEq_cons P (by includes) _ _ hf) 1 q.toList
    (fun a _ ↦ by rw [appCost_fn, List.nil_append, sub.c49.lam0.costEq P (by includes)]; simp)
  have hn : q.neg.size = q.size := by simp [CPolynomial.Raw.neg]
  have := addK_cost P (by includes) p q.neg (by omega) (by omega)
  rw [hn] at this
  simp only [Array.length_toList, List.length_map] at hm ⊢
  omega

/-- **`X^q − X mod u`** (`xPowSubXModWith`, `q < 2^65`). -/
theorem xPowSubXModC_cost (hP : Includes P xPowSubXModWith.c48.costDeps) {B : ℕ}
    (hB : B < 2 ^ 28) (hB2 : 2 ≤ B) (u : CPolynomial.Raw K) (hu : u.trim ≠ 0) (huB : u.size ≤ B)
    (q : ℕ) (hq : q < 2 ^ 65) :
    machineCost P xPowSubXModWith.c48.costIdx [encodeValue q, encodeValue u] ≤
      303 * B + 6811 + (2 * mulModBound B + 41) * (Nat.log2 q + 1) := by
  rw [xPowSubXModWith.c48.costEq P hP, X.c55.costEq P (by includes)]
  have := powModWithC_cost P (by includes) hB (by omega) u CPolynomial.Raw.X hu huB
    (by rw [size_X_raw]; omega) q hq
  have := xModWithC_cost P (by includes) hB u huB
  have h1 := powModWith_size_le (base := CPolynomial.Raw.X) hu huB q
  have h2 := xModWith_size_le hu huB
  have := subRawC_cost P (by includes)
    (CPolynomial.Raw.powModWith CPolynomial.Raw.MulContext.naive
      CPolynomial.Raw.ModContext.remainderOnly u CPolynomial.Raw.X q)
    (CPolynomial.Raw.xModWith CPolynomial.Raw.ModContext.remainderOnly u) (by omega) (by omega)
  omega

theorem raw_C_smul_size_le (c : K) (p : CPolynomial.Raw K) :
    (CPolynomial.Raw.C c • p).size ≤ p.size := raw_C_mul_size_le c p

/-- **`p mod q`** (`rawModFast`: both scaled by `q`'s leading inverse, the long division): at
most `rawModBound B`. -/
theorem rawModFastC_cost (hP : Includes P rawModFast.c35.costDeps) {B : ℕ} (hB : B < 2 ^ 28)
    (p q : CPolynomial.Raw K) (hp : p.size ≤ B) (hq : q.size ≤ B) :
    machineCost P rawModFast.c35.costIdx [encodeValue p, encodeValue q] ≤ rawModBound B := by
  rw [rawModFast.c35.costEq P hP]
  have ht := trim_size_le' q
  have := trimLen_cost P (by includes) q q.size (by omega)
  have : (Array.extract q 0 (CompPolyLib.trimLen q q.size)).size ≤ q.size := by simp
  have := getLastDC_cost P (by includes) q.trim 0 (by omega)
  have := invK_cost P (by includes) q.leadingCoeff
  have hC : (CPolynomial.Raw.C q.leadingCoeff⁻¹).size = 1 := rfl
  have h1 := mulK_cost P (by includes) (CPolynomial.Raw.C q.leadingCoeff⁻¹) p (by omega)
    (by omega)
  have h2 := mulK_cost P (by includes) (CPolynomial.Raw.C q.leadingCoeff⁻¹) q (by omega)
    (by omega)
  have hs := raw_C_smul_size_le q.leadingCoeff⁻¹ p
  have := modGoC_cost P (by includes) (CPolynomial.Raw.C q.leadingCoeff⁻¹ * q) B (by omega)
    (by have := raw_C_mul_size_le q.leadingCoeff⁻¹ q; omega)
    (CPolynomial.Raw.C q.leadingCoeff⁻¹ • p).size (CPolynomial.Raw.C q.leadingCoeff⁻¹ • p)
    (by omega) (by omega)
  have h3 : (117 * B + 82) * (CPolynomial.Raw.C q.leadingCoeff⁻¹ • p).size ≤
      (117 * B + 82) * B := Nat.mul_le_mul_left _ (hs.trans hp)
  have e : (117 * B + 82) * B = 117 * (B * B) + 82 * B := by ring
  rw [hC] at h1 h2
  unfold rawModBound
  omega

/-- **The Euclidean chain** (`rawGcdMonicWithFuelFast`, `fuel` steps): at most
`gcdStepBound B·fuel + 137·B + 2934`. -/
theorem rawGcdWithFuelC_cost (hP : Includes P rawGcdMonicWithFuelFast.c34.costDeps) {B : ℕ}
    (hB : B < 2 ^ 28) :
    ∀ (fuel : ℕ) (p q : CPolynomial.Raw K), fuel < 2 ^ 63 → p.size ≤ B → q.size ≤ B →
      machineCost P rawGcdMonicWithFuelFast.c34.costIdx [encodeValue fuel, encodeValue p, encodeValue q] ≤
        gcdStepBound B * fuel + 137 * B + 2934 := by
  intro fuel
  induction fuel with
  | zero =>
    intro p q _ hp _
    rw [rawGcdMonicWithFuelFast.c34.costEq_zero P hP]
    have := monicNormalizeRawC_cost P (by includes) p (by omega)
    omega
  | succ n ih =>
    intro p q hn hp hq
    rw [rawGcdMonicWithFuelFast.c34.costEq_succ P hP]
    have ⟨hq', hr'⟩ := rawGcdStep_size_le hp hq
    have hpt := trim_size_le' p
    have := trimLen_cost P (by includes) p p.size (by omega)
    have : (Array.extract p 0 (CompPolyLib.trimLen p p.size)).size ≤ p.size := by simp
    have := trimLen_cost P (by includes) q q.size (by omega)
    have : (Array.extract q 0 (CompPolyLib.trimLen q q.size)).size ≤ q.size := by simp
    have := beqNilK_cost P (by includes) q.trim.toList
    have := monicNormalizeRawC_cost P (by includes) p.trim (by omega)
    have := rawModFastC_cost P (by includes) hB p.trim q.trim (by omega) hq'
    have := ih q.trim (rawModFast p.trim q.trim) (by omega) hq' hr'
    simp only [size_zero_raw, toList_zero_raw] at *
    cost_simp
    have e : gcdStepBound B * (n + 1) = gcdStepBound B * n + gcdStepBound B := by ring
    unfold gcdStepBound at *
    split_ifs <;> omega

/-- **The monic gcd** (raw, `|p| + |q| + 1` steps of fuel): at most `gcdBound B − 21·B − 18`. -/
theorem rawGcdMonicFastC_cost (hP : Includes P rawGcdMonicFast.c33.costDeps) {B : ℕ}
    (hB : B < 2 ^ 28) (p q : CPolynomial.Raw K) (hp : p.size ≤ B) (hq : q.size ≤ B) :
    machineCost P rawGcdMonicFast.c33.costIdx [encodeValue p, encodeValue q] ≤
      gcdStepBound B * (2 * B + 1) + 137 * B + 2944 := by
  rw [rawGcdMonicFast.c33.costEq P hP]
  have := rawGcdWithFuelC_cost P (by includes) hB (p.size + q.size + 1) p q (by omega) hp hq
  have h1 : gcdStepBound B * (p.size + q.size + 1) ≤ gcdStepBound B * (2 * B + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  cost_simp
  omega

/-- **The monic gcd** (`gcdMonicFast`): at most `gcdBound B`. -/
theorem gcdMonicFastC_cost (hP : Includes P gcdMonicFast.c77.costDeps) {B : ℕ}
    (hB : B < 2 ^ 28) (p q : CPolynomial K) (hp : p.val.size ≤ B) (hq : q.val.size ≤ B) :
    machineCost P gcdMonicFast.c77.costIdx [encodeValue p, encodeValue q] ≤ gcdBound B := by
  rw [gcdMonicFast.c77.costEq P hP]
  have := rawGcdMonicFastC_cost P (by includes) hB p.val q.val hp hq
  have hs := rawGcdMonicWithFuelFast_size_le (p.val.size + q.val.size + 1) hp hq
  have hs' : (rawGcdMonicFast p.val q.val).size ≤ B := hs
  have := ofArray_cost P (by includes) (rawGcdMonicFast p.val q.val) (by omega)
  unfold gcdBound
  omega


/-! ## The root product -/

theorem monic_trim_ne_zero (u : CPolynomial.Raw K) (hu : u.trim ≠ 0) :
    (CPolynomial.Raw.monicNormalize u).trim ≠ 0 := by
  have h1 := monicNormalize_getLastD u hu
  have hs := monicNormalize_size u hu
  have hpos : 0 < u.trim.size := by
    rcases Nat.eq_zero_or_pos u.trim.size with h | h
    · exact absurd (Array.eq_empty_of_size_eq_zero h) hu
    · exact h
  have ht : (CPolynomial.Raw.monicNormalize u).trim = CPolynomial.Raw.monicNormalize u :=
    CPolynomial.Raw.Trim.trim_eq_iff_size_eq_zero_or_getLastD_ne_zero.2
      (Or.inr (by rw [h1]; exact one_ne_zero))
  rw [ht]
  intro h
  rw [h, size_zero_raw] at hs
  omega

/-- **The root product** (`rootProductFast`: `gcd(p, X^(2^64) − X mod p)`): at most
`rootProductBound B`. -/
theorem rootProductFastC_cost (hP : Includes P rootProductFast.c25.costDeps) {B : ℕ}
    (hB : B < 2 ^ 28) (hB2 : 2 ≤ B) (p : CPolynomial K) (hp : p.val.size ≤ B) :
    machineCost P rootProductFast.c25.costIdx [encodeValue p] ≤ rootProductBound B := by
  rw [rootProductFast.c25.costEq P hP]
  have ht := trim_size_le' p.val
  have := trimLen_cost P (by includes) p.val p.val.size (by omega)
  have : (Array.extract p.val 0 (CompPolyLib.trimLen p.val p.val.size)).size ≤ p.val.size := by
    simp
  have := beqNilK_cost P (by includes) p.val.trim.toList
  have hq : LeanVM.Extraction.traceCtx.q = 2 ^ 64 := rfl
  have h64 : (1 <<< 64 : ℕ) = 2 ^ 64 := rfl
  rw [hq, h64]
  have := limbs_le_two (x := 2 ^ 64) (by norm_num)
  simp only [size_zero_raw, toList_zero_raw] at *
  generalize hR : (if (p.val.trim == 0) = true then (0 : CPolynomial.Raw K) else
    rawGcdMonicFast p.val.monicNormalize (CPolynomial.Raw.xPowSubXModWith
      CPolynomial.Raw.MulContext.naive CPolynomial.Raw.ModContext.remainderOnly (2 ^ 64)
      p.val.monicNormalize)) = R
  have hmn := raw_monicNormalize_size_le p.val
  have hRs : R.size ≤ B := by
    rw [← hR]
    split
    · rw [size_zero_raw]; omega
    · rename_i h
      have hu : p.val.trim ≠ 0 := by simpa using h
      exact rawGcdMonicWithFuelFast_size_le _ (by omega)
        ((xPowSubXModWith_size_lt _ (monic_trim_ne_zero _ hu) _).le.trans
          ((trim_size_le' _).trans (by omega)))
  have := ofArray_cost P (by includes) R (by omega)
  unfold rootProductBound gcdBound
  split
  · omega
  · rename_i h
    have hu : p.val.trim ≠ 0 := by simpa using h
    have hmu := monic_trim_ne_zero _ hu
    have := monicNormalizeRawC_cost P (by includes) p.val (by omega)
    have hx := xPowSubXModC_cost P (by includes) hB hB2 p.val.monicNormalize hmu (by omega)
      (2 ^ 64) (by norm_num)
    have hl : Nat.log2 (2 ^ 64) = 64 := Nat.log2_two_pow
    rw [hl] at hx
    have hxs := (xPowSubXModWith_size_lt _ hmu (2 ^ 64)).le.trans
      ((trim_size_le' _).trans hmn)
    have := rawGcdMonicFastC_cost P (by includes) hB p.val.monicNormalize
      (CPolynomial.Raw.xPowSubXModWith CPolynomial.Raw.MulContext.naive
        CPolynomial.Raw.ModContext.remainderOnly (2 ^ 64) p.val.monicNormalize) (by omega)
      (by omega)
    omega

/-! ## The Frobenius powers and the trace polynomial -/

theorem length_squaringsFrom (u : CPolynomial.Raw K) :
    ∀ (n : ℕ) (c : CPolynomial.Raw K), (squaringsFrom u n c).length = n
  | 0, _ => rfl
  | n + 1, c => by rw [squaringsFrom, List.length_cons, length_squaringsFrom u n]

/-- **The squarings modulo `u`** (`squaringsFrom`, `n` of them): at most
`(mulModBound B + 22)·n + 5`. -/
theorem squaringsFromC_cost (hP : Includes P squaringsFrom.c70.costDeps) {B : ℕ}
    (hB : B < 2 ^ 28) (u : CPolynomial K) (hu : u ≠ 0) (huB : u.val.size ≤ B) :
    ∀ (n : ℕ) (c : CPolynomial.Raw K), n < 2 ^ 63 → c.size ≤ B →
      machineCost P squaringsFrom.c70.costIdx [encodeValue u.val, encodeValue n, encodeValue c] ≤
        (mulModBound B + 22) * n + 5 := by
  intro n
  induction n with
  | zero => intro c _ _; rw [squaringsFrom.c70.costEq_zero P hP]; omega
  | succ n ih =>
    intro c hn hc
    rw [squaringsFrom.c70.costEq_succ P hP]
    have := sqModC_cost P (by includes) hB u.val c huB hc
    have := ih (sqMod u.val c) (by omega) (by have := sqMod_size_lt hu c; omega)
    cost_simp
    have e : (mulModBound B + 22) * (n + 1) = (mulModBound B + 22) * n + mulModBound B + 22 := by
      ring
    omega

/-- **The Frobenius powers** (`frobeniusPowersFast u k`: `k` squarings, each then reduced
`mod u`): at most `frobBound B k`. -/
theorem frobeniusPowersFastC_cost (hP : Includes P frobeniusPowersFast.c68.costDeps) {B : ℕ}
    (hB : B < 2 ^ 28) (hB2 : 2 ≤ B) (u : CPolynomial K) (hu : u ≠ 0) (huB : u.val.size ≤ B)
    (k : ℕ) (hk : k < 2 ^ 63) :
    machineCost P frobeniusPowersFast.c68.costIdx [encodeValue u, encodeValue k] ≤ frobBound B k := by
  rw [frobeniusPowersFast.c68.costEq P hP, X.c55.costEq P (by includes)]
  have hu' := cpoly_trim_ne_zero hu
  have hz : (u.val.trim == 0) = false := by simpa using hu'
  simp only [hz, Bool.false_eq_true, ↓reduceIte]
  have ht := trim_size_le' u.val
  have := trimLen_cost P (by includes) u.val u.val.size (by omega)
  have : (Array.extract u.val 0 (CompPolyLib.trimLen u.val u.val.size)).size ≤ u.val.size := by
    simp
  have := beqNilK_cost P (by includes) u.val.trim.toList
  have := monicNormalizeRawC_cost P (by includes) u.val (by omega)
  have := modGoC_cost P (by includes) u.val.monicNormalize 1 (by omega)
    (by have := raw_monicNormalize_size_le u.val; omega) (Array.size 1) 1
    (by rw [size_one_raw]; omega) (by rw [size_one_raw])
  have := squaringsFromC_cost P (by includes) hB u hu huB k CPolynomial.Raw.X hk
    (by rw [size_X_raw]; omega)
  have hone := remainderOnly_size_lt u.val 1 raw_one_trim hu'
  have hf := fun c ↦ RunsApp.of_spec
    (us := [encodeValue u, encodeValue (CPolynomial.Raw.ModContext.remainderOnly.modByMonic 1
      u.val.monicNormalize)]) (vs := [encodeValue c])
    (frobeniusPowersFast.c68.lam0.costSpec P (by includes) u
      (CPolynomial.Raw.ModContext.remainderOnly.modByMonic 1 u.val.monicNormalize) c)
  have hm := listMap_le P Auto.List.map.c30.costIdx
    (.closure frobeniusPowersFast.c68.lam0.costIdx [encodeValue u, encodeValue (CPolynomial.Raw.ModContext.remainderOnly.modByMonic 1
      u.val.monicNormalize)])
    (Auto.List.map.c30.costEq_nil P (by includes) _ _ hf)
    (Auto.List.map.c30.costEq_cons P (by includes) _ _ hf) (mulModBound B + 21 * B + 21)
    (squaringsFrom u.val k CPolynomial.Raw.X)
    (fun c hc ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [frobeniusPowersFast.c68.lam0.costEq P (by includes)]
      have hcs : c.size ≤ B := by
        rcases squaringsFrom_size_lt hu k CPolynomial.Raw.X c hc with rfl | h
        · rw [size_X_raw]; omega
        · omega
      have := mulModWithC_cost P (by includes) hB u.val
        (CPolynomial.Raw.ModContext.remainderOnly.modByMonic 1 u.val.monicNormalize) c huB
        (by omega) hcs
      have hms := mulModWith_size_le (a := CPolynomial.Raw.ModContext.remainderOnly.modByMonic 1
        u.val.monicNormalize) (b := c) hu' huB
      have := ofArray_cost P (by includes) (CPolynomial.Raw.mulModWith
        CPolynomial.Raw.MulContext.naive CPolynomial.Raw.ModContext.remainderOnly u.val
        (CPolynomial.Raw.ModContext.remainderOnly.modByMonic 1 u.val.monicNormalize) c)
        (by omega)
      omega)
  simp only [length_squaringsFrom, List.length_map, size_one_raw, toList_zero_raw,
    size_zero_raw] at *
  have e : (mulModBound B + 21 * B + 21 + 13) * k + (mulModBound B + 22) * k + k =
      (2 * mulModBound B + 21 * B + 57) * k := by ring
  unfold frobBound
  omega

/-- **The trace polynomial** (`traceCoordFast`: `Σ_{i<64} β^(2^i)·powers[i]`): at most
`traceBound B`, its value of at most `B + 1` coefficients. -/
theorem traceCoordFastC_cost (hP : Includes P traceCoordFast.c72.costDeps) {B : ℕ}
    (hB : B < 2 ^ 28) (beta : K) (powers : Array (CPolynomial K))
    (hpw : ∀ q ∈ powers, q.val.size ≤ B) :
    machineCost P traceCoordFast.c72.costIdx [encodeValue beta, encodeValue powers] ≤ traceBound B := by
  rw [traceCoordFast.c72.costEq P hP]
  have := rangeLoop_cost P (by includes) 64 [] (by norm_num)
  have hg : ∀ i, (powers.getD i 0).val.size ≤ B := by
    intro i
    rw [Array.getD_eq_getD_getElem?]
    cases h : powers[i]? with
    | none => simp [size_zero_val]
    | some q => exact hpw q (Array.mem_of_getElem? h)
  have hf := listFoldl_le P (by includes) _ (.closure traceCoordFast.c72.lam0.costIdx [encodeValue powers])
    (fun st i ↦ RunsApp.of_spec (us := [encodeValue powers]) (vs := [encodeValue st, encodeValue i])
      (traceCoordFast.c72.lam0.costSpec P (by includes) powers st i))
    (154 * B + 410) (fun st : CPolynomial K × K ↦ st.1.val.size ≤ B + 1) (List.range 64)
    (0, beta) (by show (0 : CPolynomial K).val.size ≤ _; simp [size_zero_val])
    (fun st hst i _ ↦ by
      have hC : (CPolynomial.C st.2).val.size ≤ 1 :=
        (raw_trim_size_le _).trans (by simp [CPolynomial.Raw.C])
      have hm := cpoly_mul_size_le (CPolynomial.C st.2) (powers.getD i 0)
      refine ⟨?_, ?_⟩
      · have := cpoly_add_size_le st.1 (CPolynomial.C st.2 * powers.getD i 0)
        have := hg i
        dsimp only
        omega
      · simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
        rw [traceCoordFast.c72.lam0.costEq P (by includes)]
        have := cK_cost P (by includes) st.2
        have := hg i
        have h1 := mulK_cost P (by includes) (CPolynomial.C st.2).val (powers.getD i 0).val
          (by omega) (by omega)
        have h2 : (powers.getD i 0).val.size * (CPolynomial.C st.2).val.size ≤ B :=
          (Nat.mul_le_mul (hg i) hC).trans (by omega)
        have h3 : (CPolynomial.C st.2).val.size * (CPolynomial.C st.2).val.size ≤ 1 :=
          Nat.mul_le_mul hC hC
        have := addK_cost P (by includes) st.1.val (CPolynomial.C st.2 * powers.getD i 0).val
          (by omega) (by omega)
        omega)
  simp only [List.length_range] at hf
  unfold traceBound
  omega


/-! ## Shoup's splitter

Each factor priced at its own size: the cache's entries hold their factor's own Frobenius powers
(`CacheInv`, `lookup_mem`: a hit is the factor's own entry), so a factor of `b` coefficients costs
`refineFactorBound b C L` (cubic in `b`: its gcds), at most `b·refineSlope B + 441107 + …` for
`b ≤ B` (`refineFactorBound_le`); summed over a trace coordinate's factors, whose sizes sum to at
most `2·B` (`facInv_sum_natDegree_le`), `refineFactorsBound` (`≈ 2·468·B³`), not `B` factors at
`B` coefficients each (`≈ 468·B⁴`). -/

/-- The cache's entries: factors of at most `C` coefficients, each factor's powers of at most its
own size. -/
@[expose] def CacheInv (C : ℕ) (cache : ShoupTracePowerCache K) : Prop :=
  ∀ e ∈ cache, e.1.val.size ≤ C ∧ ∀ q ∈ e.2, q.val.size ≤ e.1.val.size

/-- **A cache hit is the factor's own entry.** -/
theorem lookup_mem (u : CPolynomial K) :
    ∀ (cache : ShoupTracePowerCache K) (powers : Array (CPolynomial K)),
      lookupTracePowers u cache = some powers → (u, powers) ∈ cache
  | [], _, h => by simp [lookupTracePowers] at h
  | (v, pw) :: rest, powers, h => by
    unfold lookupTracePowers at h
    split at h
    · rename_i huv
      cases h
      rw [beq_iff_eq.1 huv]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (lookup_mem u rest powers h)

/-- **The cache lookup** (`lookupTracePowers`: the factor compared with each entry's), the factor
of at most `B` coefficients, the entries of at most `C`: at most `(18·B + 3·C + 24)·|cache| + 3`. -/
theorem lookupC_cost (hP : Includes P Auto.CompPoly.CPolynomial.Roots.FiniteField.lookupTracePowers.c67.costDeps) {B C : ℕ}
    (u : CPolynomial K) (hu : u.val.size ≤ B) :
    ∀ cache : ShoupTracePowerCache K, CacheInv C cache →
      machineCost P Auto.CompPoly.CPolynomial.Roots.FiniteField.lookupTracePowers.c67.costIdx [encodeValue u, encodeValue cache] ≤
        (18 * B + 3 * C + 24) * cache.length + 3 := by
  intro cache
  induction cache with
  | nil => intro _; rw [Auto.CompPoly.CPolynomial.Roots.FiniteField.lookupTracePowers.c67.costEq_nil P hP]; omega
  | cons e rest ih =>
    intro hc
    obtain ⟨v, pw⟩ := e
    rw [Auto.CompPoly.CPolynomial.Roots.FiniteField.lookupTracePowers.c67.costEq_cons P hP]
    have hv := (hc (v, pw) (by simp)).1
    have := ih (fun e he ↦ hc e (by simp [he]))
    have := listBeqK_cost P (by includes) u.val.toList v.val.toList
    simp only [Array.length_toList, List.length_cons] at *
    have e : (18 * B + 3 * C + 24) * (rest.length + 1) =
        (18 * B + 3 * C + 24) * rest.length + 18 * B + 3 * C + 24 := by ring
    split_ifs <;> omega

theorem tracePowersFast_props {C : ℕ} (u : CPolynomial K) (hu0 : u ≠ 0) (hu : u.val.size ≤ C)
    (cache : ShoupTracePowerCache K) (hc : CacheInv C cache) :
    (∀ q ∈ (tracePowersFast u cache).1, q.val.size ≤ u.val.size) ∧
      CacheInv C (tracePowersFast u cache).2 ∧
      (tracePowersFast u cache).2.length ≤ cache.length + 1 := by
  unfold tracePowersFast
  cases h : lookupTracePowers u cache with
  | some powers =>
    exact ⟨(hc _ (lookup_mem u cache powers h)).2, hc, by simp⟩
  | none =>
    refine ⟨fun q hq ↦ (frobeniusPowersFast_size_lt hu0 64 hq).le, ?_, by simp⟩
    intro e he
    rcases List.mem_cons.1 he with rfl | he
    · exact ⟨hu, fun q hq ↦ (frobeniusPowersFast_size_lt hu0 64 hq).le⟩
    · exact hc e he

/-- **The Frobenius powers of a factor, cached** (`tracePowersFast`): at most
`(18·B + 3·C + 24)·|cache| + frobBound B 64 + 24`. -/
theorem tracePowersFastC_cost (hP : Includes P tracePowersFast.c66.costDeps) {B C : ℕ}
    (hB : B < 2 ^ 28) (hB2 : 2 ≤ B) (u : CPolynomial K) (hu0 : u ≠ 0) (hu : u.val.size ≤ B)
    (cache : ShoupTracePowerCache K) (hc : CacheInv C cache) :
    machineCost P tracePowersFast.c66.costIdx [encodeValue u, encodeValue cache] ≤
      (18 * B + 3 * C + 24) * cache.length + frobBound B 64 + 24 := by
  rw [tracePowersFast.c66.costEq P hP]
  have := lookupC_cost P (by includes) u hu cache hc
  have := frobeniusPowersFastC_cost P (by includes) hB hB2 u hu0 hu 64 (by norm_num)
  cases lookupTracePowers u cache <;> dsimp only <;> omega

theorem size_C_le' (c : K) : (CPolynomial.C c : CPolynomial K).val.size ≤ 1 :=
  (raw_trim_size_le _).trans (by simp [CPolynomial.Raw.C])

theorem size_one_cpoly : (1 : CPolynomial K).val.size ≤ 1 := size_one_K

/-- **A child pushed** (`pushNontrivialChild`): at most `21·|child| + |children| + 40`. -/
theorem pushChildC_cost (hP : Includes P Auto.CompPoly.CPolynomial.Roots.FiniteField.pushNontrivialChild.c78.costDeps)
    (children : Array (CPolynomial K)) (child : CPolynomial K) :
    machineCost P Auto.CompPoly.CPolynomial.Roots.FiniteField.pushNontrivialChild.c78.costIdx [encodeValue children, encodeValue child] ≤
      21 * child.val.size + children.size + 40 := by
  rw [Auto.CompPoly.CPolynomial.Roots.FiniteField.pushNontrivialChild.c78.costEq P hP]
  have := beqNilK_cost P (by includes) child.val.toList
  have := listBeqK_cost P (by includes) child.val.toList (↑(1 : CPolynomial K) : Array K).toList
  have := size_one_cpoly
  simp only [Array.length_toList, size_zero_val, toList_zero_val] at *
  split_ifs <;> omega

theorem cpoly_monicNormalize_size_le (p : CPolynomial K) :
    (CPolynomial.monicNormalize p).val.size ≤ p.val.size :=
  (raw_trim_size_le _).trans (raw_monicNormalize_size_le _)

/-- `monicNormalize` of a polynomial: at most `113·|p| + 2901`. -/
theorem monicNormalizeC_cost (hP : Includes P Auto.CompPoly.CPolynomial.monicNormalize.c61.costDeps)
    (p : CPolynomial K) (hp : p.val.size < 2 ^ 60) :
    machineCost P Auto.CompPoly.CPolynomial.monicNormalize.c61.costIdx [encodeValue p] ≤
      113 * p.val.size + 2901 := by
  rw [Auto.CompPoly.CPolynomial.monicNormalize.c61.costEq P hP]
  have := monicNormalizeRawC_cost P (by includes) p.val hp
  have := raw_monicNormalize_size_le p.val
  have := ofArray_cost P (by includes) p.val.monicNormalize (by omega)
  omega

theorem gcdMonicFast_size_le {u v : CPolynomial K} {B : ℕ} (hu : u.val.size ≤ B)
    (hv : v.val.size ≤ B) : (gcdMonicFast u v).val.size ≤ B :=
  (raw_trim_size_le _).trans (rawGcdMonicWithFuelFast_size_le _ hu hv)

theorem cpoly_sub_C_size_le (T : CPolynomial K) (c : K) {B : ℕ} (hT : T.val.size ≤ B)
    (hB : 1 ≤ B) : (T - CPolynomial.C c).val.size ≤ B := by
  have h : T - CPolynomial.C c = T + -CPolynomial.C c := sub_eq_add_neg _ _
  rw [h]
  have := cpoly_add_size_le T (-CPolynomial.C c)
  rw [neg_val_size] at this
  have := size_C_le' c
  omega

/-- **One child** (`gcd(u, T − c)`, normalized, pushed): at most `refineLamBound B`. -/
theorem refineLamC_cost (hP : Includes P refineFactorFast.c65.lam0.costDeps) {B : ℕ}
    (hB : B < 2 ^ 28) (hB1 : 1 ≤ B) (u T : CPolynomial K) (hu : u.val.size ≤ B)
    (hT : T.val.size ≤ B) (children : Array (CPolynomial K)) (hch : children.size ≤ 2) (c : K) :
    machineCost P refineFactorFast.c65.lam0.costIdx [encodeValue u, encodeValue T, encodeValue children, encodeValue c] ≤
      refineLamBound B := by
  rw [refineFactorFast.c65.lam0.costEq P hP]
  have hC := size_C_le' c
  have := cK_cost P (by includes) c
  have hf := fun a ↦ RunsApp.of_spec (us := []) (vs := [encodeValue a])
    (sub.c49.lam0.costSpec P (by includes) a)
  have hm := listMap_le P Auto.List.map.c30.costIdx (.closure sub.c49.lam0.costIdx [])
    (Auto.List.map.c30.costEq_nil P (by includes) _ _ hf)
    (Auto.List.map.c30.costEq_cons P (by includes) _ _ hf) 1 (CPolynomial.C c).val.toList
    (fun a _ ↦ by rw [appCost_fn, List.nil_append, sub.c49.lam0.costEq P (by includes)]; simp)
  have hn : (-CPolynomial.C c).val.size ≤ 1 := by rw [neg_val_size]; exact hC
  have := addK_cost P (by includes) T.val (-CPolynomial.C c).val (by omega) (by omega)
  have hs := cpoly_sub_C_size_le T c hT hB1
  have := gcdMonicFastC_cost P (by includes) hB u (T - CPolynomial.C c) hu hs
  have hg := gcdMonicFast_size_le hu hs
  have := monicNormalizeC_cost P (by includes) (gcdMonicFast u (T - CPolynomial.C c)) (by omega)
  have hmn := cpoly_monicNormalize_size_le (gcdMonicFast u (T - CPolynomial.C c))
  have := pushChildC_cost P (by includes) children
    (CPolynomial.monicNormalize (gcdMonicFast u (T - CPolynomial.C c)))
  simp only [Array.length_toList, List.length_map] at *
  unfold refineLamBound
  omega


theorem baseConstants_size' : LeanVM.Extraction.traceCtx.baseConstants.size = 2 := by
  rw [LeanVM.Extraction.traceCtx.baseConstants_size, traceCtx_p]

theorem basis_size' : LeanVM.Extraction.traceCtx.basis.size = 64 := by
  rw [LeanVM.Extraction.traceCtx.basis_size, traceCtx_k]

/-- `isRepresentedLinearFactor`: at most `15`. -/
theorem isReprC_cost
    (hP : Includes P Auto.CompPoly.CPolynomial.Roots.FiniteField.isRepresentedLinearFactor.c59.costDeps)
    (p : CPolynomial K) (hp : p.val.size < 2 ^ 64) :
    machineCost P Auto.CompPoly.CPolynomial.Roots.FiniteField.isRepresentedLinearFactor.c59.costIdx
      [encodeValue p] ≤ 15 := by
  rw [Auto.CompPoly.CPolynomial.Roots.FiniteField.isRepresentedLinearFactor.c59.costEq P hP]
  cost_simp
  split_ifs <;> omega

theorem refineFactorFast_cacheInv {C : ℕ} (beta : K) (cache : ShoupTracePowerCache K)
    (u : CPolynomial K) (hu : u.val.size ≤ C) (hc : CacheInv C cache) :
    CacheInv C (refineFactorFast beta cache u).1 := by
  unfold refineFactorFast
  dsimp only
  split
  · exact hc
  · split
    · exact hc
    · rename_i h0 _
      have hm0 : CPolynomial.monicNormalize u ≠ 0 := by
        simp only [Bool.or_eq_true, beq_iff_eq, not_or] at h0; exact h0.1
      obtain ⟨-, hc', -⟩ := tracePowersFast_props _ hm0
        ((cpoly_monicNormalize_size_le u).trans hu) cache hc
      generalize tracePowersFast (CPolynomial.monicNormalize u) cache = tp at hc' ⊢
      obtain ⟨pw, c'⟩ := tp
      exact hc'

theorem natDegree_le_of_size_le {p : CPolynomial K} {B : ℕ} (h : p.val.size ≤ B) :
    p.natDegree ≤ B - 1 := (natDegree_le_size_sub_one p).trans (by omega)

/-- **One factor refined by one trace coordinate** (`refineFactorFast`: normalized; unless
trivial or linear, its Frobenius powers from the cache, its trace polynomial, a gcd per base
constant), the factor of at most `B` coefficients, the cache's entries of at most `C`: at most
`refineFactorBound B C |cache|`. -/
theorem refineFactorFastC_cost (hP : Includes P refineFactorFast.c65.costDeps) {B : ℕ}
    (hB : B < 2 ^ 28) (hB2 : 2 ≤ B) (beta : K) {C : ℕ} (cache : ShoupTracePowerCache K)
    (hc : CacheInv C cache) (u : CPolynomial K) (hu : u.val.size ≤ B) (huC : u.val.size ≤ C) :
    machineCost P refineFactorFast.c65.costIdx [encodeValue beta, encodeValue cache, encodeValue u] ≤
      refineFactorBound B C cache.length := by
  rw [refineFactorFast.c65.costEq P hP]
  have hmn := cpoly_monicNormalize_size_le u
  have := monicNormalizeC_cost P (by includes) u (by omega)
  have := beqNilK_cost P (by includes) (CPolynomial.monicNormalize u).val.toList
  have := listBeqK_cost P (by includes) (CPolynomial.monicNormalize u).val.toList
    (↑(1 : CPolynomial K) : Array K).toList
  have := size_one_cpoly
  have := isReprC_cost P (by includes) (CPolynomial.monicNormalize u) (by omega)
  simp only [Array.length_toList, size_zero_val, toList_zero_val] at *
  unfold refineFactorBound
  split_ifs
  all_goals try omega
  all_goals
    rename_i h2 _
    have hm0 : CPolynomial.monicNormalize u ≠ 0 := by
      simp only [Bool.or_eq_true, beq_iff_eq, not_or] at h2; exact h2.1
    have := tracePowersFastC_cost P (by includes) hB hB2 _ hm0 (by omega) cache hc
    obtain ⟨hpw', -, -⟩ := tracePowersFast_props _ hm0 (by omega : _ ≤ C) cache hc
    generalize tracePowersFast (CPolynomial.monicNormalize u) cache = tp at hpw' ⊢
    obtain ⟨pw, c'⟩ := tp
    dsimp only at hpw' ⊢
    have hpw : ∀ q ∈ pw, q.val.size ≤ B := fun q hq ↦ (hpw' q hq).trans (by omega)
    have := traceCoordFastC_cost P (by includes) hB beta pw hpw
    have hT : (traceCoordFast beta pw).val.size ≤ B := by
      have := traceCoordFast_natDegree_le beta pw (B - 1) fun q hq ↦
        natDegree_le_of_size_le (hpw q hq)
      have := val_size_le_natDegree_add_one (traceCoordFast beta pw)
      omega
    have hf := listFoldl_le_idx P (by includes)
      (fun ch c ↦ pushNontrivialChild ch (CPolynomial.monicNormalize (gcdMonicFast
        (CPolynomial.monicNormalize u) (traceCoordFast beta pw - CPolynomial.C c))))
      (.closure refineFactorFast.c65.lam0.costIdx [encodeValue (CPolynomial.monicNormalize u),
        encodeValue (traceCoordFast beta pw)])
      (fun ch c ↦ RunsApp.of_spec (us := [encodeValue (CPolynomial.monicNormalize u),
        encodeValue (traceCoordFast beta pw)]) (vs := [encodeValue ch, encodeValue c])
        (refineFactorFast.c65.lam0.costSpec P (by includes) (CPolynomial.monicNormalize u)
          (traceCoordFast beta pw) ch c))
      (refineLamBound B + 2) (fun k ch ↦ ch.size + k ≤ 2) LeanVM.Extraction.traceCtx.baseConstants.toList
      (fun k ch hch c _ ↦ by
        refine ⟨?_, ?_⟩
        · have := (pushNontrivialChild_bounds ch (CPolynomial.monicNormalize (gcdMonicFast
            (CPolynomial.monicNormalize u) (traceCoordFast beta pw - CPolynomial.C c)))).1
          omega
        · simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
          have := refineLamC_cost P (by includes) hB (by omega) (CPolynomial.monicNormalize u)
            (traceCoordFast beta pw) (by omega) hT ch (by omega) c
          omega)
      LeanVM.Extraction.traceCtx.baseConstants.toList #[] (fun _ h ↦ h)
      (by simp [baseConstants_size'])
    simp only [Array.length_toList, baseConstants_size'] at hf ⊢
    omega


theorem refineFactorsFast_eq_foldl (beta : K) (cache : ShoupTracePowerCache K)
    (factors : Array (CPolynomial K)) :
    refineFactorsFast beta cache factors = factors.toList.foldl
      (fun st f ↦ ((refineFactorFast beta st.1 f).1, st.2 ++ (refineFactorFast beta st.1 f).2))
      (cache, #[]) := by
  rw [refineFactorsFast, ← Array.foldl_toList]

theorem refineFactorsFast_cacheInv {C : ℕ} (beta : K) (factors : Array (CPolynomial K))
    (hf : ∀ u ∈ factors, u.val.size ≤ C) (cache : ShoupTracePowerCache K)
    (hc : CacheInv C cache) : CacheInv C (refineFactorsFast beta cache factors).1 := by
  rw [refineFactorsFast_eq_foldl]
  suffices ∀ (l : List (CPolynomial K)) (st : ShoupTracePowerCache K × Array (CPolynomial K)),
      (∀ u ∈ l, u.val.size ≤ C) → CacheInv C st.1 →
      CacheInv C (l.foldl (fun st f ↦ ((refineFactorFast beta st.1 f).1,
        st.2 ++ (refineFactorFast beta st.1 f).2)) st).1 from
    this _ _ (fun u hu ↦ hf u (by simpa using hu)) hc
  intro l
  induction l with
  | nil => intro st _ h; exact h
  | cons f l ih =>
    intro st hl h
    exact ih _ (fun u hu ↦ hl u (by simp [hu]))
      (refineFactorFast_cacheInv beta st.1 f (hl f (by simp)) h)

/-- **A factor's refinement, linear in its size**: for `b ≤ B`,
`refineFactorBound b C L ≤ b·refineSlope B + 441107 + (18·b + 3·C + 24)·L`. -/
theorem refineFactorBound_le {b B : ℕ} (hb : b ≤ B) (C L : ℕ) :
    refineFactorBound b C L ≤ b * refineSlope B + 441107 + (18 * b + 3 * C + 24) * L := by
  have h2 : b * b ≤ b * B := Nat.mul_le_mul_left b hb
  have h3 : b * (b * b) ≤ b * (B * B) := Nat.mul_le_mul_left b (Nat.mul_le_mul hb hb)
  have e1 : refineFactorBound b C L = 468 * (b * (b * b)) + 76214 * (b * b) + 92578 * b +
      441107 + (18 * b + 3 * C + 24) * L := by
    unfold refineFactorBound frobBound mulModBound traceBound refineLamBound gcdBound gcdStepBound
      rawModBound
    ring
  have e2 : b * refineSlope B = 468 * (b * (B * B)) + 76214 * (b * B) + 92578 * b := by
    unfold refineSlope; ring
  omega

/-- `List.foldl`, the closure's price depending on the element, an invariant of the accumulator
and the elements left. -/
theorem listFoldl_le_sum {α β : Type} [MachineEncoding α] [MachineEncoding β]
    (hP : Includes P listFoldl.costDeps) (f : α → β → α) (fVal : MachineValue)
    (hf : ∀ a b, RunsApp P fVal [encodeValue a, encodeValue b] (encodeValue (f a b)))
    (g : β → ℕ) (J : α → List β → Prop)
    (hJ : ∀ acc b l, J acc (b :: l) → J (f acc b) l ∧ appCost P fVal [encodeValue acc, encodeValue b] ≤ g b) :
    ∀ (l : List β) (init : α), J init l →
      machineCost P listFoldl.costIdx [fVal, encodeValue init, encodeValue l] ≤
        (l.map fun b ↦ g b + 11).sum + 3 := by
  intro l
  induction l with
  | nil => intro init _; rw [listFoldl.costEq_nil P hP f fVal hf]; simp
  | cons b l ih =>
    intro init hI
    rw [listFoldl.costEq_cons P hP f fVal hf]
    obtain ⟨hI', h2⟩ := hJ init b l hI
    have := ih (f init b) hI'
    simp only [List.map_cons, List.sum_cons]
    omega

theorem sum_map_affine {α : Type} (l : List α) (s : α → ℕ) (c1 c0 : ℕ) :
    (l.map fun u ↦ s u * c1 + c0).sum = (l.map s).sum * c1 + c0 * l.length := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring

/-- **The factors refined by one trace coordinate** (`refineFactorsFast`), each factor priced at
its own size: factors of `2` to `B` coefficients, at most `F` of them, their sizes summing to at
most `S`, the cache's length plus `F` at most `L`: at most `refineFactorsBound B S F L`. -/
theorem refineFactorsFastC_cost (hP : Includes P refineFactorsFast.c63.costDeps) {B : ℕ}
    (hB : B < 2 ^ 28) (beta : K) (cache : ShoupTracePowerCache K)
    (hc : CacheInv B cache) (factors : Array (CPolynomial K))
    (hf : ∀ u ∈ factors, 2 ≤ u.val.size ∧ u.val.size ≤ B) {S F L : ℕ}
    (hS : (factors.toList.map fun u ↦ u.val.size).sum ≤ S) (hF : factors.size ≤ F)
    (hL : cache.length + F ≤ L) :
    machineCost P refineFactorsFast.c63.costIdx [encodeValue beta, encodeValue cache, encodeValue factors] ≤
      refineFactorsBound B S F L := by
  rw [refineFactorsFast.c63.costEq P hP]
  have hspec := fun st f ↦ RunsApp.of_spec (us := [encodeValue beta]) (vs := [encodeValue st, encodeValue f])
    (refineFactorsFast.c63.lam0.costSpec P (by includes) beta st f)
  have hfold := listFoldl_le_sum P (by includes) _ (.closure refineFactorsFast.c63.lam0.costIdx
    [encodeValue beta]) hspec (fun u ↦ u.val.size * refineSlope B + 441107 +
      (18 * u.val.size + 3 * B + 24) * L + 2 * F + 19)
    (fun st l ↦ CacheInv B st.1 ∧ st.1.length + l.length ≤ L ∧ st.2.size + 2 * l.length ≤ 2 * F ∧
      ∀ u ∈ l, 2 ≤ u.val.size ∧ u.val.size ≤ B)
    (fun st f l hst ↦ by
      obtain ⟨c0, out⟩ := st
      obtain ⟨hc0, hl0, ho0, hl⟩ := hst
      have hfs := hl f (by simp)
      have hcl := refineFactorFast_cache_length beta c0 f
      have hch := (refineFactorFast_children beta c0 f).1
      have hci := refineFactorFast_cacheInv beta c0 f hfs.2 hc0
      simp only [List.length_cons] at hl0 ho0
      refine ⟨?_, ?_⟩
      · try dsimp only at hl0 ho0 ⊢
        generalize refineFactorFast beta c0 f = r at hcl hch hci ⊢
        obtain ⟨c1, ch⟩ := r
        dsimp only at hcl hch hci ⊢
        refine ⟨hci, by omega, ?_, fun u hu ↦ hl u (by simp [hu])⟩
        rw [Array.size_append]
        omega
      · simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
        rw [refineFactorsFast.c63.lam0.costEq_mk P (by includes)]
        have := refineFactorFastC_cost P (by includes) (B := f.val.size) (by omega) hfs.1 beta c0 hc0
          f le_rfl hfs.2
        have hmono : refineFactorBound f.val.size B c0.length ≤ refineFactorBound f.val.size B L := by
          unfold refineFactorBound
          have := Nat.mul_le_mul_left (18 * f.val.size + 3 * B + 24)
            (show c0.length ≤ L by omega)
          omega
        have hlin := refineFactorBound_le hfs.2 B L
        generalize refineFactorFast beta c0 f = r at hch this ⊢
        obtain ⟨c1, ch⟩ := r
        dsimp only at hch ⊢
        omega)
    factors.toList (cache, #[])
    ⟨hc, by simp; omega, by simp; omega, fun u hu ↦ hf u (by simpa using hu)⟩
  have e : (factors.toList.map fun u ↦ u.val.size * refineSlope B + 441107 +
      (18 * u.val.size + 3 * B + 24) * L + 2 * F + 19 + 11) =
      (factors.toList.map fun u ↦ u.val.size * (refineSlope B + 18 * L) +
        (441107 + (3 * B + 24) * L + 2 * F + 30)) := by
    refine List.map_congr_left fun u _ ↦ ?_
    ring
  rw [e, sum_map_affine] at hfold
  simp only [Array.length_toList] at hfold
  have h1 : (factors.toList.map fun u ↦ u.val.size).sum * (refineSlope B + 18 * L) ≤
      S * (refineSlope B + 18 * L) := Nat.mul_le_mul_right _ hS
  have h2 : (441107 + (3 * B + 24) * L + 2 * F + 30) * factors.size ≤
      (441107 + (3 * B + 24) * L + 2 * F + 30) * F := Nat.mul_le_mul_left _ hF
  have e2 : refineFactorsBound B S F L = S * (refineSlope B + 18 * L) +
      (441107 + (3 * B + 24) * L + 2 * F + 30) * F + 3 * F + 15 := by
    unfold refineFactorsBound; ring
  omega


theorem facInv_size_le {P : Polynomial K} (hP : P ≠ 0) {F : List (CPolynomial K)}
    (h : FacInv P F) : ∀ f ∈ F, f.val.size ≤ P.natDegree + 1 := by
  intro f hf
  have hd := Polynomial.natDegree_le_of_dvd (h.2 f hf).1 hP
  rw [← CPolynomial.natDegree_toPoly] at hd
  have := val_size_le_natDegree_add_one f
  omega

/-- **Shoup's splitter, cached** (`splitCandidatesFast`): at most `splitBound B`. -/
theorem splitCandidatesFastC_cost (hP : Includes P splitCandidatesFast.c60.costDeps) {B : ℕ}
    (hB : B < 2 ^ 28) (hB2 : 2 ≤ B) (p : CPolynomial K) (hp : p.val.size ≤ B) :
    machineCost P splitCandidatesFast.c60.costIdx [encodeValue p] ≤ splitBound B := by
  rw [splitCandidatesFast.c60.costEq P hP]
  have hmn := cpoly_monicNormalize_size_le p
  have := monicNormalizeC_cost P (by includes) p (by omega)
  have := beqNilK_cost P (by includes) (CPolynomial.monicNormalize p).val.toList
  have := listBeqK_cost P (by includes) (CPolynomial.monicNormalize p).val.toList
    (↑(1 : CPolynomial K) : Array K).toList
  have := size_one_cpoly
  have := isReprC_cost P (by includes) (CPolynomial.monicNormalize p) (by omega)
  simp only [Array.length_toList, size_zero_val, toList_zero_val] at *
  unfold splitBound
  split_ifs
  all_goals try omega
  all_goals
    rename_i h2 _
    simp only [Bool.or_eq_true, beq_iff_eq, not_or] at h2
    obtain ⟨hm0, hm1⟩ := h2
    -- the basis
    have hl1 := fun i ↦ RunsApp.of_spec (us := []) (vs := [encodeValue i])
      (splitCandidatesFast.c60.lam1.costSpec P (by includes) i)
    have hob := ofFnFrom_cost P (by includes) (n := 64) (by norm_num) _
      (.closure splitCandidatesFast.c60.lam1.costIdx []) hl1 5 (fun i ↦ by
        simp only [appCost_fn, List.nil_append, List.length_nil]
        rw [splitCandidatesFast.c60.lam1.costEq P (by includes)]
        have hi := i.isLt
        have : (1 <<< (i : ℕ) : ℕ) < 2 ^ 64 := by
          rw [Nat.one_shiftLeft]; exact Nat.pow_lt_pow_right (by norm_num) hi
        cost_simp
        omega) 0 (by norm_num)
    -- the stages
    set m := CPolynomial.monicNormalize p with hm
    have hP0 : m.toPoly ≠ 0 := toPoly_ne_zero hm0
    have hd1 : m.natDegree + 1 ≤ B := by
      have := natDegree_le_size_sub_one m
      have : 1 ≤ m.val.size := by
        rcases Nat.eq_zero_or_pos m.val.size with h | h
        · exact absurd (Subtype.ext (Array.eq_empty_of_size_eq_zero h)) hm0
        · exact h
      omega
    have hdeg : m.toPoly.natDegree = m.natDegree := (CPolynomial.natDegree_toPoly m).symm
    have hspec := fun st b ↦ RunsApp.of_spec (us := []) (vs := [encodeValue st, encodeValue b])
      (splitCandidatesFast.c60.lam0.costSpec P (by includes) st b)
    have hfold := listFoldl_le_idx P (by includes) _ (.closure splitCandidatesFast.c60.lam0.costIdx [])
      hspec (refineFactorsBound B (2 * B) B (64 * B) + 8)
      (fun k st ↦ FacInv m.toPoly st.2.toList ∧ CacheInv B st.1 ∧
        st.1.length + k * m.natDegree ≤ 64 * m.natDegree)
      LeanVM.Extraction.traceCtx.basis.toList
      (fun k st hst b _ ↦ by
        obtain ⟨c0, fs⟩ := st
        obtain ⟨hfi, hc0, hl0⟩ := hst
        dsimp only at hfi hc0 hl0 ⊢
        have hlen := facInv_length_le hP0 hfi
        rw [hdeg, Array.length_toList] at hlen
        have hsum := facInv_sum_natDegree_le hP0 hfi
        rw [hdeg] at hsum
        have hfs : ∀ u ∈ fs, 2 ≤ u.val.size ∧ u.val.size ≤ B := fun u hu ↦ by
          have h1 := facInv_size_le hP0 hfi u (by simpa using hu)
          have h2 := (hfi.2 u (by simpa using hu)).2
          have h3 := natDegree_le_size_sub_one u
          omega
        have hS : (fs.toList.map fun u ↦ u.val.size).sum ≤ 2 * B := by
          have : (fs.toList.map fun u ↦ u.val.size).sum ≤
              (fs.toList.map CPolynomial.natDegree).sum + fs.toList.length := by
            have := list_sum_map_le (l := fs.toList) (f := fun u ↦ u.val.size)
              (g := fun u ↦ u.natDegree + 1) fun u _ ↦ val_size_le_natDegree_add_one u
            refine this.trans (le_of_eq ?_)
            clear this
            induction fs.toList with
            | nil => simp
            | cons x l ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring
          rw [Array.length_toList] at this
          omega
        have hbd := refineFactorsFast_bounds b c0 fs m.natDegree (fun u hu ↦ by
          have := Polynomial.natDegree_le_of_dvd (hfi.2 u (by simpa using hu)).1 hP0
          rw [← CPolynomial.natDegree_toPoly, hdeg] at this
          exact this)
        refine ⟨⟨refineFactorsFast_facInv b c0 fs hfi,
          refineFactorsFast_cacheInv b fs (fun u hu ↦ (hfs u hu).2) c0 hc0,
          ?_⟩, ?_⟩
        · have := hbd.2.2
          have e : (k + 1) * m.natDegree = k * m.natDegree + m.natDegree := by ring
          omega
        · simp only [appCost_fn, List.nil_append, List.length_nil]
          rw [splitCandidatesFast.c60.lam0.costEq_mk P (by includes)]
          have e : (k + 1) * m.natDegree = k * m.natDegree + m.natDegree := by ring
          have hcl : c0.length + B ≤ 64 * B := by
            have := Nat.mul_le_mul_left 64 (show m.natDegree ≤ B by omega)
            omega
          have := refineFactorsFastC_cost P (by includes) hB b c0 hc0 fs hfs hS
            (F := B) (L := 64 * B) (by omega) hcl
          omega)
      LeanVM.Extraction.traceCtx.basis.toList ([], #[m]) (fun _ h ↦ h)
      ⟨(⟨by simp, by
          intro f hf
          simp at hf
          subst hf
          exact ⟨dvd_refl _, one_le_natDegree_monicNormalize hm0 hm1⟩⟩ : FacInv _ _),
        fun e he ↦ by simp at he, by simp [basis_size']⟩
    simp only [Array.length_toList, basis_size', length_ofFnFrom] at hfold hob ⊢
    omega


/-! ## The roots read off the linear factors -/

/-- `List.any` (`any.c15`): `11` per element and the predicate's price, `3`. -/
theorem anyC_cost (hP : Includes P Auto.List.any.c15.costDeps) {α : Type} [MachineEncoding α]
    (p : α → Bool) (pVal : MachineValue) (hp : ∀ a, RunsApp P pVal [encodeValue a] (encodeValue (p a))) (B : ℕ) :
    ∀ l : List α, (∀ a ∈ l, appCost P pVal [encodeValue a] ≤ B) →
      machineCost P Auto.List.any.c15.costIdx [encodeValue l, pVal] ≤ (B + 11) * l.length + 3 := by
  intro l
  induction l with
  | nil => intro _; rw [Auto.List.any.c15.costEq_nil P hP p pVal hp]; omega
  | cons a l ih =>
    intro hB
    rw [Auto.List.any.c15.costEq_cons P hP a l p pVal hp]
    have h1 := ih fun a' ha ↦ hB a' (by simp [ha])
    have h2 := hB a (by simp)
    simp only [List.length_cons]
    split_ifs <;> nlinarith

/-- `Array.contains` over `K`: at most `18·|as| + 9`. -/
theorem containsC_cost (hP : Includes P Auto.Array.contains.c14.costDeps) (as : Array K)
    (a : K) : machineCost P Auto.Array.contains.c14.costIdx [encodeValue as, encodeValue a] ≤ 18 * as.size + 9 := by
  rw [Auto.Array.contains.c14.costEq P hP]
  have hp := fun x ↦ RunsApp.of_spec (us := [encodeValue a]) (vs := [encodeValue x])
    (Auto.Array.contains.c14.lam0.costSpec P (by includes) a x)
  have := anyC_cost P (by includes) _ (.closure Auto.Array.contains.c14.lam0.costIdx [encodeValue a]) hp 4
    as.toList (fun x _ ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [Auto.Array.contains.c14.lam0.costEq P (by includes)])
  simp only [Array.length_toList] at this
  omega

/-- `Array.eraseDups` over `K` (each element looked up in the output): at most
`(19·n + 31)·n + 9`, `n` elements. -/
theorem eraseDupsC_cost (hP : Includes P Auto.Array.eraseDups.c12.costDeps) (xs : Array K) :
    machineCost P Auto.Array.eraseDups.c12.costIdx [encodeValue xs] ≤ (19 * xs.size + 31) * xs.size + 9 := by
  rw [Auto.Array.eraseDups.c12.costEq P hP]
  have hspec := fun out x ↦ RunsApp.of_spec (us := []) (vs := [encodeValue out, encodeValue x])
    (Auto.Array.eraseDups.c12.lam0.costSpec P (by includes) out x)
  have := listFoldl_le_idx P (by includes) _ (.closure Auto.Array.eraseDups.c12.lam0.costIdx [])
    hspec (19 * xs.size + 17) (fun k out ↦ out.size + k ≤ xs.size) xs.toList
    (fun k out hout x _ ↦ by
      refine ⟨?_, ?_⟩
      · split_ifs
        · omega
        · simp only [Array.size_push]; omega
      · simp only [appCost_fn, List.nil_append, List.length_nil]
        rw [Auto.Array.eraseDups.c12.lam0.costEq P (by includes)]
        have := containsC_cost P (by includes) out x
        split_ifs <;> omega)
    xs.toList #[] (fun _ h ↦ h) (by simp)
  simp only [Array.length_toList] at this
  have e : (19 * xs.size + 31) * xs.size = (19 * xs.size + 17 + 11) * xs.size + 3 * xs.size := by
    ring
  omega

/-- A factor's root (`linearRootOfFactor?`): at most `2877`. -/
theorem linearRootC_cost (hP : Includes P Auto.CompPoly.CPolynomial.linearRootOfFactor?.c9.costDeps)
    (f : CPolynomial K) (hf : f.val.size < 2 ^ 64) :
    machineCost P Auto.CompPoly.CPolynomial.linearRootOfFactor?.c9.costIdx [encodeValue f] ≤ 2877 := by
  rw [Auto.CompPoly.CPolynomial.linearRootOfFactor?.c9.costEq P hP]
  have := invK_cost P (by includes) (f.coeff 1)
  cost_simp
  split_ifs <;> omega

theorem rootsFromLinearFactorsC_cost
    (hP : Includes P Auto.CompPoly.CPolynomial.rootsFromLinearFactors.c6.costDeps)
    (p : CPolynomial K) (factors : Array (CPolynomial K)) {B F : ℕ} (hp : p.val.size ≤ B)
    (hF : factors.size ≤ F) (hfs : ∀ f ∈ factors, f.val.size < 2 ^ 64) :
    machineCost P Auto.CompPoly.CPolynomial.rootsFromLinearFactors.c6.costIdx
      [encodeValue p, encodeValue factors] ≤ rootsFromBound B F := by
  rw [Auto.CompPoly.CPolynomial.rootsFromLinearFactors.c6.costEq P hP]
  have hf := fun f ↦ RunsApp.of_spec (us := []) (vs := [encodeValue f])
    (Auto.CompPoly.CPolynomial.rootsFromLinearFactors.c6.lam0.costSpec P (by includes) f)
  have h1 := filterMap_cost P (by includes) _
    (.closure Auto.CompPoly.CPolynomial.rootsFromLinearFactors.c6.lam0.costIdx []) hf 2879
    factors.toList (fun f hfm ↦ by
      simp only [appCost_fn, List.nil_append, List.length_nil]
      rw [Auto.CompPoly.CPolynomial.rootsFromLinearFactors.c6.lam0.costEq P (by includes)]
      have := linearRootC_cost P (by includes) f (hfs f (by simpa using hfm))
      omega)
  generalize hc : List.filterMap CPolynomial.linearRootOfFactor? factors.toList = cands
  have hcl : cands.length ≤ factors.size := by
    rw [← hc, ← Array.length_toList]; exact List.length_filterMap_le _ _
  rw [Auto.CompPoly.CPolynomial.validateRootCandidates.c17.costEq P (by includes)]
  have hv := fun a ↦ RunsApp.of_spec (us := [encodeValue p]) (vs := [encodeValue a])
    (Auto.CompPoly.CPolynomial.validateRootCandidates.c17.lam0.costSpec P (by includes) p a)
  have h2 := filter_cost P (by includes) _
    (.closure Auto.CompPoly.CPolynomial.validateRootCandidates.c17.lam0.costIdx [encodeValue p]) hv
    (46 * B + 22) cands.toArray.toList (fun a _ ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [Auto.CompPoly.CPolynomial.validateRootCandidates.c17.lam0.costEq P (by includes)]
      have := evalHornerC_cost P (by includes) a p
      omega)
  have hval : (p.validateRootCandidates cands.toArray).size ≤ cands.length := by
    unfold CPolynomial.validateRootCandidates
    have := List.length_filter_le (fun a ↦ CPolynomial.evalHorner a p == 0) cands
    simpa using this
  have h3 := eraseDupsC_cost P (by includes) (p.validateRootCandidates cands.toArray)
  have h4 := Nat.mul_le_mul_left (19 * (p.validateRootCandidates cands.toArray).size + 31)
    (show (p.validateRootCandidates cands.toArray).size ≤ F by omega)
  have h5 : (19 * (p.validateRootCandidates cands.toArray).size + 31) * F ≤ (19 * F + 31) * F :=
    Nat.mul_le_mul_right _ (by omega)
  have h6 : (46 * B + 22 + 15) * cands.length ≤ (46 * B + 37) * F :=
    Nat.mul_le_mul (by omega) (by omega)
  have h7 : (2879 + 16) * factors.size ≤ 2895 * F := Nat.mul_le_mul_left _ hF
  have h8 := (List.length_filter_le (fun a ↦ CPolynomial.evalHorner a p == 0) cands)
  simp only [Array.length_toList, List.size_toArray] at *
  unfold rootsFromBound
  have e : (46 * B + 2940) * F = (46 * B + 37) * F + 2903 * F := by ring
  omega


theorem representedLinearFactorsOnly_props (fs : Array (CPolynomial K)) :
    (representedLinearFactorsOnly fs).size ≤ fs.size ∧
      ∀ f ∈ representedLinearFactorsOnly fs, f ∈ fs ∧ isRepresentedLinearFactor f = true := by
  unfold representedLinearFactorsOnly
  rw [← Array.foldl_toList]
  suffices ∀ (l : List (CPolynomial K)) (out : Array (CPolynomial K)),
      (∀ f ∈ out, f ∈ fs ∧ isRepresentedLinearFactor f = true) → (∀ f ∈ l, f ∈ fs) →
      (l.foldl (fun out factor ↦ if isRepresentedLinearFactor factor then out.push factor else out)
        out).size ≤ out.size + l.length ∧
      ∀ f ∈ l.foldl (fun out factor ↦ if isRepresentedLinearFactor factor then out.push factor
        else out) out, f ∈ fs ∧ isRepresentedLinearFactor f = true by
    have := this fs.toList #[] (by simp) (fun f hf ↦ by simpa using hf)
    simpa using this
  intro l
  induction l with
  | nil => intro out h _; exact ⟨by simp, h⟩
  | cons x l ih =>
    intro out h hl
    rw [List.foldl_cons]
    split_ifs with hx
    · have := ih (out.push x) (fun f hf ↦ by
        rcases Array.mem_push.1 hf with hf | rfl
        · exact h f hf
        · exact ⟨hl _ (by simp), hx⟩) (fun f hf ↦ hl f (by simp [hf]))
      simp only [Array.size_push, List.length_cons] at this ⊢
      exact ⟨by omega, this.2⟩
    · have := ih out h (fun f hf ↦ hl f (by simp [hf]))
      simp only [List.length_cons] at this ⊢
      exact ⟨by omega, this.2⟩

/-- **The linear factors kept** (`representedLinearFactorsOnly`, `F` factors): at most
`(F + 33)·F + 3·F + 9`. -/
theorem representedLinearFactorsOnlyC_cost
    (hP : Includes P Auto.CompPoly.CPolynomial.Roots.FiniteField.representedLinearFactorsOnly.c57.costDeps) (fs : Array (CPolynomial K))
    {F : ℕ} (hF : fs.size ≤ F) (hfs : ∀ f ∈ fs, f.val.size < 2 ^ 64) :
    machineCost P Auto.CompPoly.CPolynomial.Roots.FiniteField.representedLinearFactorsOnly.c57.costIdx [encodeValue fs] ≤ (F + 33) * F + 3 * F + 9 := by
  rw [Auto.CompPoly.CPolynomial.Roots.FiniteField.representedLinearFactorsOnly.c57.costEq P hP]
  have hspec := fun out f ↦ RunsApp.of_spec (us := []) (vs := [encodeValue out, encodeValue f])
    (Auto.CompPoly.CPolynomial.Roots.FiniteField.representedLinearFactorsOnly.c57.lam0.costSpec P (by includes) out f)
  have := listFoldl_le_idx P (by includes) _ (.closure Auto.CompPoly.CPolynomial.Roots.FiniteField.representedLinearFactorsOnly.c57.lam0.costIdx [])
    hspec (F + 22) (fun k out ↦ out.size + k ≤ fs.size) fs.toList
    (fun k out hout f hf ↦ by
      refine ⟨?_, ?_⟩
      · split_ifs
        · simp only [Array.size_push]; omega
        · omega
      · simp only [appCost_fn, List.nil_append, List.length_nil]
        rw [Auto.CompPoly.CPolynomial.Roots.FiniteField.representedLinearFactorsOnly.c57.lam0.costEq P (by includes)]
        have := isReprC_cost P (by includes) f (hfs f (by simpa using hf))
        split_ifs <;> omega)
    fs.toList #[] (fun _ h ↦ h) (by simp)
  simp only [Array.length_toList] at this
  have : (F + 22 + 11) * fs.size ≤ (F + 33) * F := Nat.mul_le_mul (by omega) hF
  omega

theorem splitCandidatesFast_zero : splitCandidatesFast 0 = #[] := by
  have hm : CPolynomial.monicNormalize (0 : CPolynomial K) = 0 :=
    CPolynomial.toPoly_inj.1 (by rw [toPoly_monicNormalize, CPolynomial.toPoly_zero, normalize_zero])
  unfold splitCandidatesFast
  simp [hm]

/-- **The roots in `K`** (`rootsInFieldFast`: the root product, split by Shoup's trace, the
roots read off the linear factors), `p` of at most `B` coefficients: at most `rootsBound B`. -/
theorem rootsInFieldC_cost (hP : Includes P rootsInFieldC.costDeps) {B : ℕ} (hB : B < 2 ^ 28)
    (hB2 : 2 ≤ B) (p : CPolynomial K) (hp : p.val.size ≤ B) :
    machineCost P rootsInFieldC.costIdx [encodeValue p] ≤ rootsBound B := by
  rw [rootsInFieldC.costEq P hP]
  have := beqNilK_cost P (by includes) p.val.toList
  simp only [size_zero_val, toList_zero_val] at *
  have hA := rootsFromLinearFactorsC_cost P (by includes) p #[p] (B := B) (F := 1) hp (by simp)
    (by simp; omega)
  have hBig : p ≠ 0 →
      machineCost P rootProductFast.c25.costIdx [encodeValue p] +
        machineCost P splitCandidatesFast.c60.costIdx [encodeValue (rootProductFast p)] +
        machineCost P
          Auto.CompPoly.CPolynomial.Roots.FiniteField.representedLinearFactorsOnly.c57.costIdx
          [encodeValue (splitCandidatesFast (rootProductFast p))] +
        machineCost P Auto.CompPoly.CPolynomial.rootsFromLinearFactors.c6.costIdx
          [encodeValue p, encodeValue (representedLinearFactorsOnly (splitCandidatesFast (rootProductFast p)))] ≤
      rootProductBound B + splitBound B + ((B + 33) * B + 3 * B + 9) + rootsFromBound B B := by
    intro hp0
    have hrd := rootProductFast_natDegree_le hp0
    have hps := natDegree_le_size_sub_one p
    have hrs : (rootProductFast p).val.size ≤ B := by
      have := val_size_le_natDegree_add_one (rootProductFast p)
      omega
    have := rootProductFastC_cost P (by includes) hB hB2 p hp
    have := splitCandidatesFastC_cost P (by includes) hB hB2 (rootProductFast p) hrs
    have hsplit : (splitCandidatesFast (rootProductFast p)).size ≤ B ∧
        ∀ f ∈ splitCandidatesFast (rootProductFast p), f.val.size < 2 ^ 64 := by
      by_cases hr0 : rootProductFast p = 0
      · rw [hr0, splitCandidatesFast_zero]; simp
      · refine ⟨(splitCandidatesFast_size_le hr0).trans (by omega), fun f hf ↦ ?_⟩
        have := splitCandidatesFast_natDegree_le hr0 hf
        have := val_size_le_natDegree_add_one f
        omega
    have := representedLinearFactorsOnlyC_cost P (by includes) _ hsplit.1 hsplit.2
    obtain ⟨hrs1, hrs2⟩ :=
      representedLinearFactorsOnly_props (splitCandidatesFast (rootProductFast p))
    have := rootsFromLinearFactorsC_cost P (by includes) p
      (representedLinearFactorsOnly (splitCandidatesFast (rootProductFast p))) (B := B) (F := B) hp
      (by omega)
      (fun f hf ↦ by
        have := (hrs2 f hf).2
        unfold isRepresentedLinearFactor at this
        simp only [Bool.and_eq_true, decide_eq_true_eq] at this
        omega)
    omega
  unfold rootsBound
  split_ifs
  all_goals cost_simp
  all_goals try omega
  all_goals
    have := hBig (by simpa using ‹¬(p == 0) = true›)
    omega

end

end LeanVM.Cost.Bounds.Decoder
