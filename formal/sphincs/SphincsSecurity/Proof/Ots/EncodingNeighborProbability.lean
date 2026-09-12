import SphincsSecurity.Proof.Ots.EncodingNeighbors
import SphincsSecurity.Proof.Ots.EncodingProbability
namespace SphincsSecurity.TargetSum

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ

theorem digestEncoding_of_decode_some {digest : Digest} {word : Encoding}
    (h : decodeDigest digest = some word) : digestEncoding digest = word := by
  rw [decodeDigest] at h
  split at h
  · exact Option.some.inj h
  · contradiction

noncomputable def decodingDigests (words : Finset Encoding) : Finset Digest :=
  Finset.univ.filter fun digest => ∃ word ∈ words, decodeDigest digest = some word

theorem mem_decodingDigests {words : Finset Encoding} {digest : Digest} :
    digest ∈ decodingDigests words ↔ ∃ word ∈ words, decodeDigest digest = some word := by
  simp only [decodingDigests, Finset.mem_filter, Finset.mem_univ, true_and]

theorem decodingDigests_card_le (words : Finset Encoding) : (decodingDigests words).card ≤ words.card := by
  apply Finset.card_le_card_of_injOn digestEncoding
  · intro digest hd
    obtain ⟨word, hw, hdecode⟩ := mem_decodingDigests.mp hd
    rwa [digestEncoding_of_decode_some hdecode]
  · intro left hl right hr he
    obtain ⟨leftWord, _, hleft⟩ := mem_decodingDigests.mp hl
    obtain ⟨rightWord, _, hright⟩ := mem_decodingDigests.mp hr
    have hw : leftWord = rightWord := (digestEncoding_of_decode_some hleft).symm.trans
      (he.trans (digestEncoding_of_decode_some hright))
    exact decodeDigest_some_injective (hw ▸ hleft) hright

theorem decodingDigests_uniform_le (words : Finset Encoding) :
    Pr[fun output : HashOutput => truncateHash output ∈ decodingDigests words | ($ᵗ HashOutput : ProbComp HashOutput)] ≤
      (words.card : ENNReal) / Fintype.card Digest := by
  rw [probEvent_uniform_truncateHash_mem]
  exact ENNReal.div_le_div_right (Nat.cast_le.mpr (decodingDigests_card_le words)) _

end SphincsSecurity.TargetSum
