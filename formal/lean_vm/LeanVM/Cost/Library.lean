module

public import LeanVM.Cost.Compiler

/-!
# The compiler's library

Init's functions the extractor uses, compiled once for all types (their specs quantified over the
types' encodings); each recursive one with the measure its recursion decreases.
-/

namespace LeanVM.Cost.Library

open LeanVM.Cost

-- The product in `K`, one body every product calls (`Rule.kMulCall`).
cost_compile kMulC := @Rule.kMulFn

cost_compile listZipWith measure fun _ _ _ _ as _ ↦ as.length := @List.zipWith.{0, 0, 0}

cost_measure Rewrite.ofFnFrom := fun _ n _ i ↦ n - i

cost_measure Rewrite.finRangeFrom := fun n i ↦ n - i

cost_measure Rewrite.powSq := fun _ _ _ n ↦ n

cost_measure List.merge := fun _ xs ys _ ↦ xs.length + ys.length

cost_measure List.mergeSort := fun _ xs _ ↦ xs.length

cost_compile listFoldl measure fun _ _ _ _ l ↦ l.length := @List.foldl.{0, 0}

end LeanVM.Cost.Library
