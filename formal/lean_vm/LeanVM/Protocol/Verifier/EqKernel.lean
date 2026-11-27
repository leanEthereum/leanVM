/-
  LeanVM.Protocol.Verifier.EqKernel

  The equality kernel's shape, once for every proof that reads it.
-/

module

public import Statement.Verifier.Multilinear
public import Mathlib.Tactic.Ring

/-!
# The equality kernel

`eqKernel` (`Statement/Verifier/Multilinear.lean`) doubles at each coordinate (`eqKernel_snoc`), so
it has `2^|point|` entries (`eqKernel_length`).
-/

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters

@[expose] public section

/-- One more coordinate doubles the kernel: the old weights times `1 + r`, then times `r`. -/
theorem eqKernel_snoc (l : List E) (r : E) :
    eqKernel (l ++ [r]) = (eqKernel l).map (· * (1 + r)) ++ (eqKernel l).map (· * r) := by
  simp only [eqKernel, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- `eq_kernel(point)` has `2^|point|` entries. -/
theorem eqKernel_length (pt : List E) : (eqKernel pt).length = 2 ^ pt.length := by
  induction pt using List.reverseRecOn with
  | nil => rfl
  | append_singleton pt r ih =>
    rw [eqKernel_snoc, List.length_append, List.length_map, List.length_map, ih,
      List.length_append, List.length_singleton, pow_succ]
    ring

end

end LeanVM.Protocol.Verifier
