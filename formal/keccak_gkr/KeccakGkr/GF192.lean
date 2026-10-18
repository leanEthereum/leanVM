import KeccakGkr.Main
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.PrimitiveElement

/-!
# In the VM's field

`E = GF(2^192)`. An element whose minimal polynomial over `GF(2)` has degree at least `64` is a
word basis, its first `64` powers being independent over `GF(2)` (`wordBasis_of_degree`). The VM's
`x`, the generator of `GF(2^64)` inside `GF(2^192)`, has degree `64`, and a primitive element has
degree `192` (`exists_wordBasis_GF192`). So `keccak_sound` holds for every such `x` with error
`(37 κ + 902) / 2^192` (`keccak_sound_GF192`).
-/

namespace KeccakGkr

/-- `GF(2^192)`, the VM's extension field. -/
abbrev GF192 := GaloisField 2 192

noncomputable instance : Fintype GF192 := Fintype.ofFinite _
noncomputable instance : DecidableEq GF192 := Classical.decEq _
noncomputable instance : SampleableType GF192 := SampleableType.ofFintype GF192

theorem card_GF192 : Fintype.card GF192 = 2 ^ 192 := by
  rw [← Nat.card_eq_fintype_card, GaloisField.card 2 192 (by norm_num)]

theorem wordBasis_of_degree {x : GF192} (h : 64 ≤ (minpoly (ZMod 2) x).natDegree) : WordBasis x := by
  intro d hd z
  have h64 := (linearIndependent_pow (K := ZMod 2) x).comp (Fin.castLE h) (Fin.castLE_injective _)
  have hι : (ι : ZMod 2 →+* GF192) = algebraMap (ZMod 2) GF192 := RingHom.ext_zmod _ _
  exact Fintype.linearIndependent_iff.1 h64 d (by simpa [hι, Algebra.smul_def] using hd) z

theorem exists_wordBasis_GF192 : ∃ x : GF192, WordBasis x := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element (ZMod 2) GF192
  have hdeg : (minpoly (ZMod 2) α).natDegree = 192 := by
    rw [← IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral α), hα,
      IntermediateField.finrank_top', GaloisField.finrank 2 (by norm_num)]
  exact ⟨α, wordBasis_of_degree (by omega)⟩

/-- **Soundness over `GF(2^192)`.** Every `x` of degree at least `64` over `GF(2)`, the VM's
among them, makes the protocol sound with error `(37 κ + 902) / 2^192`, for every committed
column. -/
theorem keccak_sound_GF192 (x : GF192) (hx : 64 ≤ (minpoly (ZMod 2) x).natDegree) {n : ℕ}
    (Q : Column n) :
    (protocol keccak 12 Q x).Sound (fun _ => True) (Fooled keccak 12 Q x)
      ((37 * (n + 4) + 902) / 2 ^ 192) := by
  have h := keccak_sound Q x (wordBasis_of_degree hx)
  rwa [card_GF192, Nat.cast_pow, Nat.cast_ofNat] at h

end KeccakGkr
