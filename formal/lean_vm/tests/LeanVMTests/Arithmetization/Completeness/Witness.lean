import LeanVM.Arithmetization.Completeness.Witness
import LeanVMTests.Arithmetization.Completeness.Fixture

/-!
# Tests: the prover data of the witness

`skelWitness` is never evaluated: its memory block has `2^κ` rows. Clean derives the witness's
prover data from its tables (`withDerivedData`), so the `"mem"` table is the memory block's limbs,
which are the image's words (`memRows_skelWitness`). Every test here is a statement about data
whose `"mem"` table is an image's, generic in the data, through the lemmas that rewrite and never
unfold (`imageOf_of_memRows`). The memory log-size at most `maxLogMem` is load-bearing: the data's
`imageOf` clamps it, so a memory of `2^33` cells is named as one of `2^32`.
-/

namespace LeanVMTests.Arithmetization.Completeness.Witness

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization
open LeanVMTests.Arithmetization.Completeness.Fixture

/-- The sentinel counter of a `2^11`-slot program, as a literal term, as in `Fixture`. -/
local notation "d₀" => (addressOfIndex 2047 : K)

/-! ## The prover data of an image -/

/-- Data whose `"mem"` table is an image's names that image, at its memory log-size `16`. -/
example (data : ProverData K) (h : memRows data = imageRows (badImage d₀)) :
    imageOf data = ⟨16, badImage d₀⟩ :=
  imageOf_of_memRows h (by decide)

/-- Such data has the `2^κ` rows of its image: it is well shaped. -/
example (data : ProverData K) (h : memRows data = imageRows (badImage d₀)) :
    WellShapedData data :=
  wellShaped_of_memRows h (by decide)

/-- The witness of the skeletons names its image: Clean derives its `"mem"` table from the
memory block. -/
example (S : List Skel) (hrows : ∀ op, Skel.count op S ≤ 2 ^ maxLogRows) :
    imageOf (skelWitness jumpProg badInput (badImage d₀) S (by decide) hrows).data =
      ⟨16, badImage d₀⟩ :=
  imageOf_skelWitness _ _ _ _ _ _

/-- A memory of `2^33` cells is named by data whose log-size is clamped to `maxLogMem`: the bound
`κ ≤ maxLogMem` of `imageOf_of_memRows` cannot be dropped. -/
example (data : ProverData K) (h : memRows data = imageRows (fun _ : Fin (2 ^ 33) ↦ (0 : E))) :
    (imageOf data).1 = maxLogMem := by
  show min (Nat.log 2 (memRows data).size) maxLogMem = _
  rw [h, imageRows, Array.size_ofFn, Nat.log_pow (by norm_num)]
  decide

example (data : ProverData K) (h : memRows data = imageRows (fun _ : Fin (2 ^ 33) ↦ (0 : E))) :
    (imageOf data).1 ≠ 33 := by
  show min (Nat.log 2 (memRows data).size) maxLogMem ≠ 33
  rw [h, imageRows, Array.size_ofFn, Nat.log_pow (by norm_num)]
  decide

end LeanVMTests.Arithmetization.Completeness.Witness
