module

public import LeanVM.Cost.Bounds.Decoder.Rows
public import LeanVM.Cost.Extractor.PMLane
import all CompPoly.Univariate.Raw.Ops
import all CompPoly.Data.Array.Lemmas

/-!
# Bounds: polynomial arithmetic, compiled

The prices of CompPoly's raw polynomial operations as the decoder compiles them, over `K`
(`…K_cost`), in the operands' sizes, and `trimLen` over `K[X]` (`trimLenB_cost`):

* addition (`addRaw`: pad, zip; `add`: then trim), scaling (`smul`), shifting (`mulPowX`);
* the schoolbook product (`mulRaw`: for each coefficient `a_i` of `p`, `acc + X^i·(a_i·q)`;
  `mul`: then trim), `O(|p|·(|p| + |q|))` operations on coefficients.

**Honest-cost note.** `Raw.add` and `Raw.mul` compute their raw result once
(`CompPolyLib.trim_addRaw_shared`, `trim_mulRaw_shared`: the untrimmed sum or product bound by a
`let` before `trim_eq`, which names its argument three times); the bounds here charge it once.
-/

namespace LeanVM.Cost.Bounds.Decoder

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library
open LeanVM.Cost.Extractor LeanVM.Parameters CompPoly

/-! The functions compiled on demand, by their short names. -/
open LeanVM.Cost.Auto.CompPoly.CPolynomial.Raw

public section

/-! ## Sizes -/

section Sizes

variable {R : Type} [Zero R] [Add R]

theorem size_addRaw (p q : CPolynomial.Raw R) : (p.addRaw q).size = max p.size q.size := by
  simp [CPolynomial.Raw.addRaw, Array.size_zipWith, Array.size_rightpad]
  omega

theorem size_smul {R : Type} [Mul R] (r : R) (p : CPolynomial.Raw R) :
    (CPolynomial.Raw.smul r p).size = p.size := by
  simp [CPolynomial.Raw.smul]

omit [Add R] in
theorem size_mulPowX (i : ℕ) (p : CPolynomial.Raw R) :
    (CPolynomial.Raw.mulPowX i p).size = i + p.size := by
  simp [CPolynomial.Raw.mulPowX]

theorem foldl_mulRaw_size_le {R : Type} [Semiring R] (q : CPolynomial.Raw R) (B : ℕ) :
    ∀ (l : List (R × ℕ)) (acc : CPolynomial.Raw R), acc.size ≤ B + q.size →
      (∀ x ∈ l, x.2 ≤ B) →
      (l.foldl (fun acc x ↦ acc.addRaw ((CPolynomial.Raw.smul x.1 q).mulPowX x.2)) acc).size ≤
        B + q.size := by
  intro l
  induction l with
  | nil => intro acc h _; exact h
  | cons x l ih =>
    intro acc h hl
    apply ih
    · dsimp only
      rw [size_addRaw, size_mulPowX, size_smul]
      have := hl x (by simp)
      omega
    · exact fun y hy ↦ hl y (by simp [hy])

theorem size_mulRaw_le {R : Type} [Semiring R] (p q : CPolynomial.Raw R) :
    (CPolynomial.Raw.mulRaw p q).size ≤ p.size + q.size := by
  unfold CPolynomial.Raw.mulRaw
  have := foldl_mulRaw_size_le q p.size p.zipIdx.toList (CPolynomial.Raw.mk #[]) (by simp)
    (fun x hx ↦ by
      rw [Array.toList_zipIdx] at hx
      have := List.mem_zipIdx hx
      simp at this
      omega)
  rw [Array.foldl_toList] at this
  convert this using 2

end Sizes

variable (P : MachineProgram)

/-! ## Over `K` -/

/-- `Array.rightpad n a xs` (polymorphic): `8 + (n − |xs|) + max n |xs|`, word-sized lengths. -/
theorem rightpadC_cost {α : Type} [MachineEncoding α] (hP : Includes P Auto.Array.rightpad.c40.costDeps)
    (n : ℕ) (a : α) (xs : Array α) (hn : n < 2 ^ 64) (hs : xs.size < 2 ^ 64) :
    machineCost P Auto.Array.rightpad.c40.costIdx [encodeValue n, encodeValue a, encodeValue xs] ≤
      8 + (n - xs.size) + max n xs.size := by
  rw [Auto.Array.rightpad.c40.costEq P hP]
  simp only [limbs_of_lt hn, limbs_of_lt hs, Array.size_replicate]
  omega

/-- **`addRaw` over `K`**: at most `46 + 32·max(|p|, |q|)`. -/
theorem addRawK_cost (hP : Includes P addRaw.c39.costDeps) (p q : CPolynomial.Raw K)
    (hp : p.size < 2 ^ 64) (hq : q.size < 2 ^ 64) :
    machineCost P addRaw.c39.costIdx [encodeValue p, encodeValue q] ≤ 46 + 32 * max p.size q.size := by
  rw [addRaw.c39.costEq P hP]
  have hz := listZipWith_le P (by includes) (fun x y : K ↦ x + y) (.closure addRaw.c39.lam0.costIdx [])
    (fun a b ↦ RunsApp.of_spec (addRaw.c39.lam0.costSpec P (by includes) a b)) 3
    (p.rightpad q.size 0).toList (q.rightpad p.size 0).toList
    (fun a _ b _ ↦ by rw [appCost_fn, List.nil_append, addRaw.c39.lam0.costEq P (by includes)]; simp)
  have := rightpadC_cost P (by includes) q.size (0 : K) p hq hp
  have := rightpadC_cost P (by includes) p.size (0 : K) q hp hq
  simp only [Array.length_toList, Array.size_rightpad,
    List.length_zipWith] at hz ⊢
  omega

/-- **`add` over `K`** (`addRaw` and the trim): at most `53·max(|p|, |q|) + 62`. -/
theorem addK_cost (hP : Includes P add.c50.costDeps) (p q : CPolynomial.Raw K)
    (hp : p.size < 2 ^ 62) (hq : q.size < 2 ^ 62) :
    machineCost P add.c50.costIdx [encodeValue p, encodeValue q] ≤ 53 * max p.size q.size + 62 := by
  rw [add.c50.costEq P hP]
  have := addRawK_cost P (by includes) p q (by omega) (by omega)
  have := trimLen_cost P (by includes) (p.addRaw q) (p.addRaw q).size
    (by rw [size_addRaw]; omega)
  have h1 : (Array.extract (p.addRaw q) 0
      (CompPolyLib.trimLen (p.addRaw q) (p.addRaw q).size)).size ≤ (p.addRaw q).size := by
    rw [Array.size_extract]; omega
  rw [size_addRaw] at *
  omega

/-- `smul` over `K`: at most `47·|p| + 10`. -/
theorem smulK_cost (hP : Includes P smul.c29.costDeps) (r : K) (p : CPolynomial.Raw K) :
    machineCost P smul.c29.costIdx [encodeValue r, encodeValue p] ≤ 47 * p.size + 10 := by
  rw [smul.c29.costEq P hP]
  have hf := fun a ↦ RunsApp.of_spec (us := [encodeValue r]) (vs := [encodeValue a])
    (smul.c29.lam0.costSpec P (by includes) r a)
  have := listMap_le P Auto.List.map.c30.costIdx (.closure smul.c29.lam0.costIdx [encodeValue r])
    (Auto.List.map.c30.costEq_nil P (by includes) _ _ hf)
    (Auto.List.map.c30.costEq_cons P (by includes) _ _ hf) 30 p.toList
    (fun a _ ↦ by
      rw [appCost_fn, List.singleton_append, smul.c29.lam0.costEq P (by includes)]; simp)
  simp only [Array.length_toList, List.length_map] at this ⊢
  omega

/-- `mulPowX` over `K`: `2·i + |p| + 5`. -/
theorem mulPowXK_cost (hP : Includes P mulPowX.c42.costDeps) (i : ℕ) (p : CPolynomial.Raw K) :
    machineCost P mulPowX.c42.costIdx [encodeValue i, encodeValue p] = 2 * i + p.size + 5 := by
  rw [mulPowX.c42.costEq P hP]
  simp only [Array.size_replicate]
  omega

theorem mem_zipIdx_lt {α : Type} {p : Array α} {x : α × ℕ} (h : x ∈ (Array.zipIdx p).toList) :
    x.2 < p.size := by
  rw [Array.toList_zipIdx] at h
  have := List.mem_zipIdx h
  simp at this
  omega

/-- **The schoolbook product over `K`** (`mulRaw`): at most
`80·|q|·|p| + 34·|p|² + 108·|p| + 18`. -/
theorem mulRawK_cost (hP : Includes P mulRaw.c37.costDeps) (p q : CPolynomial.Raw K)
    (hp : p.size < 2 ^ 62) (hq : q.size < 2 ^ 62) :
    machineCost P mulRaw.c37.costIdx [encodeValue p, encodeValue q] ≤
      80 * (q.size * p.size) + 34 * (p.size * p.size) + 108 * p.size + 18 := by
  rw [mulRaw.c37.costEq P hP]
  have hz := zipIdx_cost P (by includes) p.toList 0 (by simp; omega)
  have hf := listFoldl_le P (by includes) _ (.closure mulRaw.c37.lam0.costIdx [encodeValue q])
    (fun acc x ↦ RunsApp.of_spec (us := [encodeValue q]) (vs := [encodeValue acc, encodeValue x])
      (mulRaw.c37.lam0.costSpec P (by includes) q acc x))
    (80 * q.size + 34 * p.size + 73) (fun acc ↦ acc.size ≤ p.size + q.size)
    (Array.zipIdx p).toList (CPolynomial.Raw.mk #[]) (by simp)
    (fun acc hacc x hx ↦ by
      have hi := mem_zipIdx_lt hx
      obtain ⟨a, i⟩ := x
      dsimp only at hi ⊢
      refine ⟨?_, ?_⟩
      · rw [size_addRaw, size_mulPowX, size_smul]; omega
      · rw [appCost_fn, List.singleton_append, List.length_singleton,
          mulRaw.c37.lam0.costEq P (by includes)]
        have := smulK_cost P (by includes) a q
        have := mulPowXK_cost P (by includes) i (CPolynomial.Raw.smul a q)
        have := addRawK_cost P (by includes) acc
          (CPolynomial.Raw.mulPowX i (CPolynomial.Raw.smul a q)) (by omega)
          (by rw [size_mulPowX, size_smul]; omega)
        rw [size_mulPowX, size_smul] at *
        dsimp only
        omega)
  have e : (80 * q.size + 34 * p.size + 73 + 11) * (Array.zipIdx p).toList.length =
      80 * (q.size * p.size) + 34 * (p.size * p.size) + 84 * p.size := by
    simp only [Array.length_toList, Array.size_zipIdx]; ring
  simp only [Array.length_toList, Array.size_zipIdx, List.length_zipIdx] at hz hf e ⊢
  omega

/-- **The product over `K`** (`mul`: `mulRaw`, the trim): at most
`80·|q|·|p| + 34·|p|² + 129·|p| + 21·|q| + 34`. -/
theorem mulK_cost (hP : Includes P mul.c36.costDeps) (p q : CPolynomial.Raw K)
    (hp : p.size < 2 ^ 61) (hq : q.size < 2 ^ 61) :
    machineCost P mul.c36.costIdx [encodeValue p, encodeValue q] ≤
      80 * (q.size * p.size) + 34 * (p.size * p.size) + 129 * p.size + 21 * q.size + 34 := by
  rw [mul.c36.costEq P hP]
  have := mulRawK_cost P (by includes) p q (by omega) (by omega)
  have hs := size_mulRaw_le p q
  have := trimLen_cost P (by includes) (p.mulRaw q) (p.mulRaw q).size (by omega)
  have h1 : (Array.extract (p.mulRaw q) 0
      (CompPolyLib.trimLen (p.mulRaw q) (p.mulRaw q).size)).size ≤ (p.mulRaw q).size := by simp
  omega

/-! ## Over `K[X]`: bivariate polynomials -/

theorem raw_trim_size_le {R : Type} [Zero R] [BEq R] (p : CPolynomial.Raw R) :
    p.trim.size ≤ p.size := by
  rw [CompPolyLib.trim_eq]; simp

theorem cpoly_add_size_le (x y : CPolynomial K) :
    (x + y).val.size ≤ max x.val.size y.val.size := by
  show (x.val.addRaw y.val).trim.size ≤ _
  have := raw_trim_size_le (x.val.addRaw y.val)
  rw [size_addRaw] at this
  exact this

theorem cpoly_mul_size_le (x y : CPolynomial K) :
    (x * y).val.size ≤ x.val.size + y.val.size := by
  show (x.val.mulRaw y.val).trim.size ≤ _
  exact (raw_trim_size_le _).trans (size_mulRaw_le _ _)

/-- Every entry of a bivariate polynomial has at most `A` coefficients. -/
@[expose] def InnerLe (p : CPolynomial.Raw (CPolynomial K)) (A : ℕ) : Prop :=
  ∀ x ∈ p, x.val.size ≤ A

/-- `trimLen` over `K[X]`: at most `(3·A + 31)·n + 5`, entries of at most `A` coefficients. -/
theorem trimLenB_cost (hP : Includes P Auto.LeanVM.Cost.CompPolyLib.trimLen.c89.costDeps)
    (p : Array (CPolynomial K)) (A : ℕ) (hA : ∀ x ∈ p, x.val.size ≤ A) :
    ∀ n : ℕ, n < 2 ^ 63 →
      machineCost P Auto.LeanVM.Cost.CompPolyLib.trimLen.c89.costIdx [encodeValue p, encodeValue n] ≤
        (3 * A + 31) * n + 5 := by
  intro n
  induction n with
  | zero => intro _; rw [Auto.LeanVM.Cost.CompPolyLib.trimLen.c89.costEq_zero P hP]; omega
  | succ k ih =>
    intro hk
    rw [Auto.LeanVM.Cost.CompPolyLib.trimLen.c89.costEq_succ P hP]
    have := ih (by omega)
    have hb := beqNilK_cost P (by includes) (↑(p.getD k 0) : Array K).toList
    have hs : (p.getD k 0).val.size ≤ A := by
      rw [Array.getD_eq_getD_getElem?]
      cases h : p[k]? with
      | none => exact Nat.zero_le _
      | some x => exact hA x (Array.mem_of_getElem? h)
    simp only [toList_zero_val, size_zero_val]
    cost_simp
    have : (3 * A + 31) * (k + 1) = (3 * A + 31) * k + 3 * A + 31 := by ring
    split_ifs <;> omega

theorem InnerLe.mono {p : CPolynomial.Raw (CPolynomial K)} {A B : ℕ} (h : InnerLe p A)
    (hAB : A ≤ B) : InnerLe p B := fun x hx ↦ (h x hx).trans hAB

/-- `X^t·p` (`shiftX`): at most `23·t + 22·|p| + 20`. -/
theorem shiftXC_cost (hP : Includes P Auto.LeanVM.Extraction.Fast.shiftX.c103.costDeps) (t : ℕ)
    (p : CPolynomial K) (h : t + p.val.size < 2 ^ 60) :
    machineCost P Auto.LeanVM.Extraction.Fast.shiftX.c103.costIdx [encodeValue t, encodeValue p] ≤
      23 * t + 22 * p.val.size + 20 := by
  rw [Auto.LeanVM.Extraction.Fast.shiftX.c103.costEq P hP]
  have := ofArray_cost P (by includes) (Array.replicate t 0 ++ p.val) (by simp; omega)
  simp only [Array.size_append, Array.size_replicate] at this ⊢
  omega

end

end LeanVM.Cost.Bounds.Decoder
