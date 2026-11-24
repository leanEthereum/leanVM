module

public import XmssSecurity.Proof.EncodingOracleSimulation

@[expose] public section

open OracleComp ENNReal

namespace XmssSecurity

set_option maxRecDepth 100000

namespace TargetSum

def ValidDigest (digest : Digest) : Prop :=
  ∃ encoding, decodeDigest digest = some encoding

noncomputable instance : DecidablePred ValidDigest :=
  Classical.decPred _

noncomputable def validDigests : Finset Digest :=
  Finset.univ.filter ValidDigest

def exampleValidEncoding : Encoding := fun chain =>
  if chain.val < 35 then ⟨3, by decide⟩
  else if chain.val = 35 then ⟨1, by decide⟩
  else ⟨0, by decide⟩

theorem exampleValidEncoding_valid : Valid exampleValidEncoding := by
  unfold Valid sum
  rw [Finset.sum_fin_eq_sum_range]
  norm_num [exampleValidEncoding, targetSum, numChains, chainLength,
    Finset.sum_range_succ]

theorem card_digest_eq_card_encodingView :
    Fintype.card Digest = Fintype.card EncodingView := by
  simp [EncodingView]
  norm_num [zeroBits, digestBits, chainLength, winternitzBits, numChains]

theorem digestView_surjective : Function.Surjective digestView :=
  ((Fintype.bijective_iff_injective_and_card digestView).2
    ⟨digestView_injective, card_digest_eq_card_encodingView⟩).2

theorem validDigests_nonempty : validDigests.Nonempty := by
  obtain ⟨digest, hdigest⟩ := digestView_surjective (exampleValidEncoding, 0)
  refine ⟨digest, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  refine ⟨exampleValidEncoding, decodeDigest_eq_some_iff.mpr ?_⟩
  exact ⟨hdigest, exampleValidEncoding_valid⟩

theorem validDigests_card_pos : 0 < validDigests.card :=
  Finset.card_pos.mpr validDigests_nonempty

end TargetSum

end XmssSecurity
