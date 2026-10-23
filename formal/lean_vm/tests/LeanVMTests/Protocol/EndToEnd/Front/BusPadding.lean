import LeanVM.Protocol.EndToEnd.Front.BusPadding
import LeanVM.Protocol.EndToEnd.Claims

/-!
# Tests: the padding weight

* **On the cube.** At every cube point of three coordinates, the verifier's `padding_weight` is
  the indicator of the rows the announced count leaves as padding, `[x ≥ n]`, for every count
  `n ≤ 8`, so it is the multilinear extension of the indicator (`paddingWeight_eq_padWeight`,
  which also covers points off the cube).
* **The last factor is load-bearing.** Without it the loop alone gives `pad_{n mod 2^m}`: at a full
  table (`n = 2^m`, no padding row) it is `1` at every cube point, where the padding weight is
  `0`. A verifier dropping the factor would charge a full table's every row as padding.
* **Inhabitants.** The theorem at a point off the cube.
-/

namespace LeanVMTests.Protocol.EndToEnd.Front.BusPadding

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front

#guard (List.range 8).all fun x ↦ (List.range 9).all fun n ↦
  decide (paddingWeight (boolPoint 3 x) n = if n ≤ x then 1 else 0)

-- An empty table: every row is padding.
#guard (List.range 8).all fun x ↦ decide (paddingWeight (boolPoint 3 x) 0 = 1)

-- Without its last factor the loop is `pad_{n mod 8}`: `1` everywhere at a full table.
#guard (List.range 8).all fun x ↦ decide (foldPad (boolPoint 3 x) 8 = 1)
#guard (List.range 8).all fun x ↦ decide (paddingWeight (boolPoint 3 x) 8 = 0)

/-- The padding weight at a point off the cube is the indicator's extension there. -/
example (r₀ r₁ : E) :
    paddingWeight [r₀, r₁] 3 = Bus.padWeight 3 (vecList [r₀, r₁]) :=
  paddingWeight_eq_padWeight _ _ (by simp)

end LeanVMTests.Protocol.EndToEnd.Front.BusPadding
