/-
  LeanVM.Protocol.EndToEnd.Front.EqKernel

  The verifier program's equality kernel `eq_kernel(point)` is CompPoly's `lagrangeBasis`, the
  first coordinate the lowest bit.
-/

module

public import LeanVM.Protocol.Whir.Complete.Tables
public import LeanVM.Protocol.ToCompPoly.Fingerprint

/-!
# The equality kernel

The verifier program (`LeanVM.Protocol.Verifier`; `crates/verifier/src/multilinear.rs` at
leanVM `40f877dc`) weighs the bus's tuple slots by `eq_kernel(alphas)` (`eqKernel`), built one
coordinate at a time, the first coordinate the lowest bit; the oracle protocol weighs them by
CompPoly's `lagrangeBasis` (`fingerprintWeights`).

* `eqKernel_snoc`: one more coordinate doubles the kernel;
* `eqKernel_getElem_prod`: the kernel's weight at `x` is `Π_j (r_j if bit j of x else 1 + r_j)`;
* `lagrangeBasis_ofFn_getD`: the kernel of a list is `lagrangeBasis` of its coordinates, in
  characteristic two.
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Protocol.Verifier CompPoly CMlPolynomialEval

@[expose] public section

/-- One more coordinate doubles the kernel: the old weights times `1 + r`, then times `r`. -/
theorem eqKernel_snoc (l : List E) (r : E) :
    eqKernel (l ++ [r]) = (eqKernel l).map (· * (1 + r)) ++ (eqKernel l).map (· * r) := by
  simp only [eqKernel, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- **The kernel's weight at `x`**: `Π_j (r_j if bit j of x else 1 + r_j)`, the first coordinate
the lowest bit. -/
theorem eqKernel_getElem_prod (l : List E) (x : ℕ) (hx : x < (eqKernel l).length) :
    (eqKernel l)[x] =
      ∏ j ∈ Finset.range l.length, (if x.testBit j then l.getD j 0 else 1 + l.getD j 0) := by
  induction l using List.reverseRecOn generalizing x with
  | nil =>
    have : x = 0 := by simpa [eqKernel] using hx
    subst this
    rfl
  | append_singleton l r ih =>
    have hlen := Whir.Complete.length_eqKernel l
    have hgetD : ∀ j < l.length, (l ++ [r]).getD j 0 = l.getD j 0 := fun j hj ↦ by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
    have hlast : (l ++ [r]).getD l.length 0 = r := by simp [List.getD_eq_getElem?_getD]
    simp only [eqKernel_snoc]
    rw [List.length_append, List.length_singleton, Finset.prod_range_succ]
    by_cases hlo : x < 2 ^ l.length
    · rw [List.getElem_append_left (by simp [hlen, hlo]), List.getElem_map,
        ih x (by rw [hlen]; exact hlo), Nat.testBit_lt_two_pow hlo, hlast]
      simp only [Bool.false_eq_true, ↓reduceIte]
      congr 1
      exact Finset.prod_congr rfl fun j hj ↦ by rw [hgetD j (Finset.mem_range.mp hj)]
    · have hx' : x < 2 ^ l.length + 2 ^ l.length := by
        simp [eqKernel_snoc, hlen] at hx
        omega
      obtain ⟨y, rfl⟩ : ∃ y, x = 2 ^ l.length + y := ⟨x - 2 ^ l.length, by omega⟩
      have hy : y < 2 ^ l.length := by omega
      rw [List.getElem_append_right (by simp [hlen]), List.getElem_map]
      simp only [List.length_map, hlen, Nat.add_sub_cancel_left]
      rw [ih y (by rw [hlen]; exact hy), Nat.testBit_two_pow_add_eq,
        Nat.testBit_lt_two_pow hy, hlast]
      simp only [Bool.not_false, ↓reduceIte]
      congr 1
      exact Finset.prod_congr rfl fun j hj ↦ by
        rw [hgetD j (Finset.mem_range.mp hj),
          Nat.testBit_two_pow_add_gt (Finset.mem_range.mp hj)]

/-- **The program's kernel is CompPoly's `lagrangeBasis`**, the first coordinate the lowest bit,
in characteristic two. -/
theorem lagrangeBasis_ofFn_getD {n : ℕ} {l : List E} (hl : l.length = n) (x : Fin (2 ^ n)) :
    (lagrangeBasis (Vector.ofFn fun i : Fin n ↦ l.getD i 0))[x] =
      (eqKernel l)[x.val]'(by rw [Whir.Complete.length_eqKernel, hl]; exact x.isLt) := by
  rw [lagrangeBasis_getElem, eqKernel_getElem_prod, hl,
    ← Fin.prod_univ_eq_prod_range (fun j ↦ if x.val.testBit j then l.getD j 0 else 1 + l.getD j 0)]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  simp only [BitVec.getLsb_eq_getElem, BitVec.getElem_ofFin, Fin.getElem_fin,
    Vector.getElem_ofFn, CharTwo.sub_eq_add]

end
end LeanVM.Protocol.EndToEnd.Front
