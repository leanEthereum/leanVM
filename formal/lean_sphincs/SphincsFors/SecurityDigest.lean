import SphincsFors.ForsCoverage
import SphincsFors.Bytes
import SphincsFors.Search

/-!
The candidate's two-call message digest: the fields of the two blocks are disjoint bits of them
(the index and twelve FORS indices of the first, twelve FORS indices of the second), so two
independent uniform blocks give the uniform 266-bit digest law; and the two block inputs of a
digest call are distinct.
-/

open OracleComp OracleSpec ENNReal
set_option exponentiation.threshold 512

namespace SphincsFors.Security
open Concrete

/-- The fields of the two calls, those of call `0` first. -/
def joinDigest (blocks : BitVec 146 × BitVec 120) : MessageDigest :=
  blocks.2 ++ blocks.1

theorem joinDigest_injective : Function.Injective joinDigest := by
  intro x y h
  have h' : x.2 ++ x.1 = y.2 ++ y.1 := h
  obtain ⟨hsecond, hfirst⟩ := append_inj h'
  exact Prod.ext hfirst hsecond

theorem joinDigest_bijective : Function.Bijective joinDigest := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨joinDigest_injective, ?_⟩
  simp only [Fintype.card_prod, card_bitVec, ← pow_add]
  rfl

theorem truncateMessageDigest_eq_join (first second : HashOutput) :
    truncateMessageDigest first second = joinDigest (firstCallFields first, callIndices second) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi' : i < 266 := hi
  change ((callIndices second ++ firstCallFields first).extractLsb' 0 266).getLsbD i =
    (callIndices second ++ firstCallFields first).getLsbD i
  rw [BitVec.getLsbD_extractLsb']
  simp [hi']

/-- The two independent oracle blocks induce exactly the uniform 266-bit digest law. -/
theorem evalDist_digestBlocks_uniform :
    𝒟[(do
      let first ← ($ᵗ HashOutput : ProbComp HashOutput)
      let second ← ($ᵗ HashOutput : ProbComp HashOutput)
      pure (truncateMessageDigest first second))] =
      𝒟[($ᵗ MessageDigest : ProbComp MessageDigest)] := by
  let pairs : ProbComp (BitVec 146 × BitVec 120) := do
    let first ← ($ᵗ HashOutput : ProbComp HashOutput)
    let second ← ($ᵗ HashOutput : ProbComp HashOutput)
    pure (firstCallFields first, callIndices second)
  have hpairs : 𝒟[pairs] = 𝒟[($ᵗ (BitVec 146 × BitVec 120) :
      ProbComp (BitVec 146 × BitVec 120))] := by
    apply evalDist_ext
    intro pair
    change Pr[= pair | (do
      let first ← ($ᵗ HashOutput : ProbComp HashOutput)
      let second ← ($ᵗ HashOutput : ProbComp HashOutput)
      pure (firstCallFields first, callIndices second))] = _
    rw [probOutput_bind_bind_prod_mk_eq_mul]
    rw [evalDist_ext_iff.mp evalDist_firstCallFields_uniform pair.1,
      evalDist_ext_iff.mp evalDist_callIndices_uniform pair.2]
    simp only [probOutput_uniformSample, Fintype.card_prod, Nat.cast_mul]
    rw [ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp))]
  have hjoin : (do
      let first ← ($ᵗ HashOutput : ProbComp HashOutput)
      let second ← ($ᵗ HashOutput : ProbComp HashOutput)
      pure (truncateMessageDigest first second)) = joinDigest <$> pairs := by
    simp only [pairs, map_bind, map_pure, truncateMessageDigest_eq_join]
  rw [hjoin, evalDist_map, hpairs, ← evalDist_map]
  exact evalDist_map_bijective_uniform_cross (α := BitVec 146 × BitVec 120)
    (β := MessageDigest) joinDigest joinDigest_bijective

/-- The exact byte string queried for one block of a message digest. -/
abbrev digestInput (parameter : PublicParameter) (root : Digest) (message : Message)
    (randomness : Randomness) (call : Fin 2) : HashInput :=
  tweakableHashInput parameter (.message call) (messageDigestPayload root message randomness)

theorem digestInput_injective (parameter : PublicParameter) (root : Digest)
    (message : Message) (randomness : Randomness) :
    Function.Injective (digestInput parameter root message randomness) := by
  intro left right h
  have hfields := fieldBytes_injective
    (List.append_cancel_left (List.append_cancel_right h))
  have hposition := congrArg TweakFields.hi hfields
  apply Fin.ext
  exact ofNat_inj_of_lt (by have := left.isLt; omega) (by have := right.isLt; omega) hposition

end SphincsFors.Security
