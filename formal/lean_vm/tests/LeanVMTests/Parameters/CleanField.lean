import LeanVM.Parameters.CleanField

/-!
# Tests: Clean's field interface, and what a plain file can decide

A classic test for kernel evaluation. Guards on `instFiniteFieldK`; the check that instance
search for `Field K` still finds CompPoly's structure now that Clean's `FiniteField.toField` is
in scope; and kernel checks of `E` arithmetic that only a plain file can run.
-/

namespace LeanVMTests.Parameters

open LeanVM.Parameters

/-! ## Clean's interface -/

#guard FiniteField.val (K.ofBits 0x2a : K) = 42
#guard (FiniteField.fromNat 42 : K) = K.ofBits 0x2a

/-- The size Clean sees is `2^64`. -/
example : FiniteField.size K = 2 ^ 64 := rfl

/-- With Clean's `FiniteField.toField` in scope, instance search still finds CompPoly's field. -/
example : (inferInstance : Field K) = BF64.instField := rfl

/-- `fromNat` inverts `val`, through the interface's own lemma. -/
example (x : K) : FiniteField.fromNat (FiniteField.val x) = x := FiniteField.fromNat_val x

/-! ## Kernel reduction in a plain file -/

/-- `y^3 = y + 1` computes in the kernel to the word with limbs `(1, 1, 0)`; in a `module` the
same `decide` is stuck on CompPoly's `Ext.ofFn`. -/
example : y ^ 3 = E.ofLimbs 1 1 0 := by decide +kernel

/-- The predicates decide on words built through `ofK` and `y`. -/
example : IsInK (ofK (K.ofBits 5)) ∧ ¬ IsInK y ∧ IsCanonical128 y ∧ ¬ IsCanonical128 (y ^ 2) := by
  decide +kernel

end LeanVMTests.Parameters
