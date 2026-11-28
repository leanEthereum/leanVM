/-
  LeanVM.Guest.B1.VsC.VsOrcBuf

  `verify_sub`'s buffers at the honest oracle: their values, bases and own cells.
-/

module

public import LeanVM.Guest.B1.VsC.VsOrcHonest
public import LeanVM.Guest.B1.VsC.VsW0

/-!
# `verify_sub`'s buffers at the honest oracle

`vsBase cur p j`: the `j`-th `HeapBuf`'s base on the aligned bump allocator from `cur` (`vsAllocSz p`'s sizes, `p` the
stream's chunks). **`vsW_ptr`**: the honest oracle's word at the buffer's index is `ptrAt (vsBase cur p j)`;
`vsVal_fixed`: the eighteen fixed buffers' values are the oracle's words; **`vsOwn_base`**: a buffer's cells are
`verify_sub`'s own data once the body's allocations are `vsAllocSz p`. Closed forms of the bases the phases name:
`vsBase_12`, `vsBase_14`, `vsBase_wc` (`wC`'s three buffers).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd

@[expose] public section

theorem bases_length' : ∀ (b : ℕ) (ss : List ℕ), (bases b ss).length = ss.length
  | _, [] => rfl
  | b, _ :: ss => by rw [bases, List.length_cons, List.length_cons, bases_length' _ ss]

theorem bases_getD' : ∀ (b : ℕ) (ss : List ℕ) (k : ℕ), k < ss.length →
    (bases b ss).getD k 0 = b + (ss.take k).sum
  | _, [], _, hk => absurd hk (Nat.not_lt_zero _)
  | b, s :: ss, 0, _ => by simp [bases]
  | b, s :: ss, k + 1, hk => by
    simp only [bases, List.getD_cons_succ, List.take_succ_cons, List.sum_cons]
    rw [bases_getD' (b + s) ss k (by simpa using hk), Nat.add_assoc]

/-- The `j`-th buffer's base: `cur` past the buffers before it. -/
def vsBase (cur p j : ℕ) : ℕ := cur + ((vsAllocSz p).take j).sum

theorem vsAllocSz_length (p : ℕ) : (vsAllocSz p).length = 24 := rfl

theorem vsBases_getD (cur p : ℕ) {j : ℕ} (hj : j < 24) : (bases cur (vsAllocSz p)).getD j 0 = vsBase cur p j :=
  bases_getD' cur _ j (by rw [vsAllocSz_length]; exact hj)

section
variable {rd1 : Reader} {args : List E} {cur p : ℕ} {ret : ℕ → (ℕ → E) → E}

/-- **The honest oracle's buffer pointers.** -/
theorem vsW_ptr (ha : args.length = 6) (hr : CausalRule ret) {j : ℕ} (hj : j < 24) :
    vsW rd1 args cur p ret (vsAllocIdx.getD j 0) = ptrAt (vsBase cur p j) := by
  rw [vsW_alloc ha hr hj, vsBases_getD cur p hj]

end

section
variable {rd0 : Reader} {w : ℕ → E} {args : List E}

/-- **The fixed buffers' values are the oracle's words.** -/
theorem vsVal_fixed (ha : args.length = 6) {j : ℕ} (hj : 6 ≤ j ∧ j < 24) : vsVal rd0 w args (.n j) = w j := by
  have hm : Atom.hint (.alloc (.n j) (vsSz0.getD (j - 6) 0)) ∈ vsW0 := by
    obtain ⟨h1, h2⟩ := hj
    interval_cases j <;> simp [vsW0, vsW0a, vsSz0]
  exact vsW0_good (rd0 := rd0) (w := w) ha hm

end

/-- **A buffer's cells are `verify_sub`'s own data** once its allocations are the honest sizes. -/
theorem vsOwn_base {fp cur p j i : ℕ} {σ0 : Val} (hal : allocs σ0 (vsEs σ0) = vsAllocSz p) (hj : j < 24)
    (hi : i < (vsAllocSz p).getD j 0) : vsOwn fp cur σ0 (vsBase cur p j + i) := by
  unfold vsOwn
  rw [hal]
  have hl : j < ((vsAllocSz p).zip (bases cur (vsAllocSz p))).length := by
    rw [List.length_zip, bases_length', Nat.min_self, vsAllocSz_length]; exact hj
  refine Or.inl ⟨((vsAllocSz p).getD j 0, vsBase cur p j), ?_, Nat.le_add_right _ _, by dsimp only; omega⟩
  refine List.mem_iff_getElem.mpr ⟨j, hl, ?_⟩
  rw [List.getElem_zip]
  refine Prod.ext ?_ ?_
  · exact (List.getD_eq_getElem _ _ (by rw [vsAllocSz_length]; exact hj)).symm
  · show (bases cur (vsAllocSz p))[j] = vsBase cur p j
    rw [← vsBases_getD cur p hj]
    exact (List.getD_eq_getElem _ _ (by rw [bases_length', vsAllocSz_length]; exact hj)).symm

/-- The buffers' total size. -/
theorem vsAllocSz_total (p : ℕ) : (vsAllocSz p).sum = 824 + 256 * p + 158 := by
  simp only [vsAllocSz, vsSz0, List.sum_append, List.sum_cons, List.sum_nil]; omega

theorem vsBase_12 (cur p : ℕ) : vsBase cur p 6 = cur + 373 := by simp [vsBase, vsAllocSz, vsSz0]
theorem vsBase_14 (cur p : ℕ) : vsBase cur p 8 = cur + 422 := by simp [vsBase, vsAllocSz, vsSz0]
theorem vsBase_wc (cur p : ℕ) : vsBase cur p 21 = cur + (824 + 256 * p) + 14 ∧
    vsBase cur p 22 = cur + (824 + 256 * p) + 14 + 16 ∧ vsBase cur p 23 = cur + (824 + 256 * p) + 14 + 80 := by
  have h21 : (vsAllocSz p).take 21 = vsSz0 ++ [256 * p, 6, 8] := rfl
  have h22 : (vsAllocSz p).take 22 = vsSz0 ++ [256 * p, 6, 8, 16] := rfl
  have h23 : (vsAllocSz p).take 23 = vsSz0 ++ [256 * p, 6, 8, 16, 64] := rfl
  simp only [vsBase, h21, h22, h23, vsSz0, List.sum_append, List.sum_cons, List.sum_nil]
  omega

end
end LeanVM.Guest.B1.VsC
