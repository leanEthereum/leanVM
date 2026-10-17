import KeccakGkr.Main
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.PrimitiveElement

/-!
# In the VM's field

`E = GF(2^192)` holds a word basis: a primitive element's minimal polynomial has degree `192`, so
its first `64` powers are independent over `GF(2)`. So `keccak_sound` holds there with no
hypothesis left (`keccak_sound_GF192`).
-/

namespace KeccakGkr

/-- `GF(2^192)`, the VM's extension field. -/
abbrev GF192 := GaloisField 2 192

noncomputable instance : Fintype GF192 := Fintype.ofFinite _
noncomputable instance : DecidableEq GF192 := Classical.decEq _
noncomputable instance : SampleableType GF192 := SampleableType.ofFintype GF192

theorem exists_wordBasis_GF192 : ∃ x : GF192, WordBasis x := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element (ZMod 2) GF192
  have hint : IsIntegral (ZMod 2) α := Algebra.IsIntegral.isIntegral α
  have hdeg : (minpoly (ZMod 2) α).natDegree = 192 := by
    rw [← IntermediateField.adjoin.finrank hint, hα, IntermediateField.finrank_top',
      GaloisField.finrank 2 (by norm_num)]
  refine ⟨α, fun d hd z => ?_⟩
  have hli := linearIndependent_pow (K := ZMod 2) α
  rw [hdeg] at hli
  have h64 := hli.comp (Fin.castLE (by norm_num : 64 ≤ 192)) (Fin.castLE_injective _)
  have hι : (ι : ZMod 2 →+* GF192) = algebraMap (ZMod 2) GF192 := RingHom.ext_zmod _ _
  exact Fintype.linearIndependent_iff.1 h64 d (by simpa [hι, Algebra.smul_def] using hd) z

/-- **Soundness over `GF(2^192)`.** Some word basis `x` of the VM's field makes the protocol sound
with error `(37 κ + 902) / 2^192`, for every committed column. -/
theorem keccak_sound_GF192 : ∃ x : GF192, ∀ {n : ℕ} (Q : Column n),
    (protocol keccak 12 Q x).Sound (fun _ => True) (Fooled keccak 12 Q x)
      ((37 * (n + 4) + 902) / Fintype.card GF192) := by
  obtain ⟨x, hx⟩ := exists_wordBasis_GF192
  exact ⟨x, fun Q => keccak_sound Q x hx⟩

end KeccakGkr
