import LeanVM.Arithmetization.Completeness.Witness
import LeanVMTests.Arithmetization.Completeness.Fixture

/-!
# Tests: the prover data of the witness

`skelWitness` is never evaluated: its memory block has `2^κ` rows. Every test here is a statement
about the prover data of an image, generic in the image, through the lemmas that rewrite and never
unfold (`imageOf_imageData`). The memory log-size at most `maxLogMem` is load-bearing: the data's
`imageOf` clamps it, so a memory of `2^33` cells is named as one of `2^32`.
-/

namespace LeanVMTests.Arithmetization.Completeness.Witness

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization
open LeanVMTests.Arithmetization.Completeness.Fixture

/-- The sentinel counter of a `2^11`-slot program, as a literal term, as in `Fixture`. -/
local notation "d₀" => (gpow 2047 : K)

/-! ## The prover data of an image -/

/-- The image the data of an image names is the image, at the least memory log-size. -/
example : imageOf (imageData (badImage d₀)) = ⟨minLogMem, badImage d₀⟩ :=
  imageOf_imageData _ (by decide)

/-- The data has the `2^κ` rows of its image: it is well shaped. -/
example : WellShapedData (imageData (badImage d₀)) := imageData_wellShaped _ (by decide)

/-- A memory of `2^33` cells is named by data whose log-size is clamped to `maxLogMem`: the bound
`κ ≤ maxLogMem` of `imageOf_imageData` cannot be dropped. -/
example : (imageOf (imageData (fun _ : Fin (2 ^ 33) ↦ (0 : E)))).1 = maxLogMem := by
  show min (Nat.log 2 (memRows (imageData (fun _ : Fin (2 ^ 33) ↦ (0 : E)))).size) maxLogMem = _
  rw [memRows_imageData, Array.size_ofFn, Nat.log_pow (by norm_num)]
  decide

example : (imageOf (imageData (fun _ : Fin (2 ^ 33) ↦ (0 : E)))).1 ≠ 33 := by
  show min (Nat.log 2 (memRows (imageData (fun _ : Fin (2 ^ 33) ↦ (0 : E)))).size) maxLogMem ≠ 33
  rw [memRows_imageData, Array.size_ofFn, Nat.log_pow (by norm_num)]
  decide

end LeanVMTests.Arithmetization.Completeness.Witness
