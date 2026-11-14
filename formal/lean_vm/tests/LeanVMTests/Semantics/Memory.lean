module

public import LeanVM.Parameters.Isa
public import LeanVM.Semantics.Lemmas
meta import Statement.LeanIsa
meta import Statement.Fast.QuadExt
meta import Statement.Fast.FieldWords

/-!
# Tests: addressing, the image, and the public input

`addressIndex?` is noncomputable, so nothing here runs it: each addressing fact is `gLog?_spec`,
`gLog?_eq_none_iff`, `gLog?_gpow_eq_none`, or a read lemma applied to a concrete address, with
the size hypothesis discharged at the two caps. Index `i` reads word `i`; `0`, a power past the
end, and a nonzero non-power read nothing; a size below the
verifier's floor still addresses correctly, since the semantics carries no cap. `PublicInput`
packs two lanes per word, one per limb; its checks are compiled
`#guard`s, since the words are field arithmetic only.
-/

namespace LeanVMTests.Semantics

open LeanVM.Parameters LeanVM.Semantics

public section

/-! ## Addressing -/

/-- `gLog?_spec` applies at the memory cap. -/
example (a : K) (i : Fin (2 ^ maxLogMem)) : addressIndex? maxLogMem a = some i ↔ a =
    addressOfIndex i :=
  gLog?_spec (by decide)

/-- `gLog?_spec` applies at the bytecode cap. -/
example (a : K) (i : Fin (2 ^ maxLogBytecode)) : addressIndex? maxLogBytecode a = some i ↔ a = addressOfIndex i :=
  gLog?_spec (by decide)

/-- Index `0` is address `1`, at the floor and in a one-cell memory. -/
example : addressIndex? minLogMem 1 = some 0 := (gLog?_spec (by decide)).mpr (pow_zero g).symm
example : addressIndex? 0 1 = some 0 := (gLog?_spec (by decide)).mpr (pow_zero g).symm

/-- `g ^ 4000` has index `4000` in a memory of `2^16` cells. -/
example : addressIndex? 16 (addressOfIndex 4000) = some ⟨4000, by decide⟩ := (gLog?_spec (by decide)).mpr rfl

/-- A one-cell memory has no second address. -/
example : addressIndex? 0 g = none := by
  have h := gLog?_gpow_eq_none (κ := 0) (j := 1) (by decide) (by decide)
  rwa [addressOfIndex, pow_one] at h

/-- One past the end of a sixteen-cell memory is no address. -/
example : addressIndex? 4 (addressOfIndex 16) = none := gLog?_gpow_eq_none (by decide) (by decide)

/-- A nonzero word that is no small power is no address: `g + 1 ≠ g ^ i` for `i < 4`. -/
example : addressIndex? 2 (g + 1) = none :=
  gLog?_eq_none_iff.mpr fun i ↦ by fin_cases i <;> decide +kernel

/-! ## The image -/

/-- Sixteen words, word `i` holding limbs `(i, 2i, 0)`. -/
def image : MemoryImage 4 := fun i ↦ E.ofLimbs (K.ofBits i) (K.ofBits (2 * i))

example : image 5 = E.ofLimbs (K.ofBits 5) (K.ofBits 10) := rfl

example : image.read 1 = some (image 0) := by simpa using MemoryImage.read_gpow (by decide) image 0
example : image.read (addressOfIndex 5) = some (image 5) := MemoryImage.read_gpow
    (by decide) image 5
example : image.read (addressOfIndex 15) = some (image 15) := MemoryImage.read_gpow
    (by decide) image 15
example : image.read (addressOfIndex 16) = none := by
  rw [MemoryImage.read, gLog?_gpow_eq_none (by decide) (by decide), Option.map_none]
example : image.read 0 = none := MemoryImage.read_zero image

/-- The read lemmas apply at the floor and at the cap. -/
example (L : MemoryImage minLogMem) (i : Fin (2 ^ minLogMem)) : L.read (addressOfIndex i) = some
    (L i) :=
  MemoryImage.read_gpow (by decide) L i

example (L : MemoryImage maxLogMem) (i : Fin (2 ^ maxLogMem)) : L.read (addressOfIndex i) = some
    (L i) :=
  MemoryImage.read_gpow (by decide) L i

/-- Reading `0` fails for every size, the cap included. -/
example (L : MemoryImage 40) : L.read 0 = none := MemoryImage.read_zero L

/-! ## The public input -/

/-- Lanes `1, 2, 3, 4`. -/
def input : PublicInput := ⟨![1, K.ofBits 2, K.ofBits 3, K.ofBits 4]⟩

example : input.word0 = E.ofLimbs 1 (K.ofBits 2) := rfl
example : input.word1 = E.ofLimbs (K.ofBits 3) (K.ofBits 4) := rfl

-- Lane `2` rides `word1`, not `word0`; a three-lane packing would move it.
#guard (PublicInput.mk ![1, K.ofBits 2, K.ofBits 5, K.ofBits 4]).word0 = input.word0
#guard (PublicInput.mk ![1, K.ofBits 2, K.ofBits 5, K.ofBits 4]).word1 ≠ input.word1
#guard (PublicInput.mk ![1, K.ofBits 5, K.ofBits 3, K.ofBits 4]).word0 ≠ input.word0

/-- Distinct inputs are distinct words: `words_injective` on a concrete pair. -/
example : (⟨![1, K.ofBits 2, K.ofBits 3, K.ofBits 4]⟩ : PublicInput) ≠ ⟨![1, K.ofBits 2, K.ofBits 3, K.ofBits 5]⟩ := by decide

end
end LeanVMTests.Semantics
