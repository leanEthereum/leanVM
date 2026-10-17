import XmssSecurity.Proof.CappedChain.ChainHiddenTable
import XmssSecurity.Proof.CappedChain.ChainInputTrace

namespace XmssSecurity.CappedChain

open OracleSpec

noncomputable def chainSuffixValueIndices (key : ChainKey) (start : Digit) :
    List ChainValueIndex :=
  ((Finset.univ.filter fun later : Digit => start ≤ later).toList.map fun later =>
    (key, later))

@[simp]
theorem mem_chainSuffixValueIndices_iff
    (key candidateKey : ChainKey) (start candidate : Digit) :
    (candidateKey, candidate) ∈ chainSuffixValueIndices key start ↔
      candidateKey = key ∧ start ≤ candidate := by
  simp [chainSuffixValueIndices, and_comm, eq_comm]

/-- The top coordinates a returned signature of `leafIndex` sends at a chain. -/
noncomputable def topSuffixValueIndices (secretKey : SecretKey) (leafIndex : LeafIndex)
    (chain : ChainIndex) : List ChainValueIndex :=
  match secretKey.topSigned (topKeyOf leafIndex) with
  | none => []
  | some (_, topEncoding) => chainSuffixValueIndices (.inr (topKeyOf leafIndex)) (topEncoding chain)

noncomputable def returnedChainValueIndexList
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) (chain : ChainIndex) :
    List ChainValueIndex :=
  (log.flatMap fun entry =>
    match entry.2 with
    | none => []
    | some signature =>
        (match TargetSum.decodeDigest
            (Concrete.CacheView.encodingHash cache secretKey.parameter
              entry.1.leafIndex (entry.1.message, signature.randomness)) with
        | none => []
        | some encoding =>
            chainSuffixValueIndices (.inl entry.1.leafIndex) (encoding chain)) ++
          topSuffixValueIndices secretKey entry.1.leafIndex chain).dedup

set_option maxRecDepth 100000 in
@[simp]
theorem mem_returnedChainValueIndexList_iff
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) (chain : ChainIndex)
    (index : ChainValueIndex) :
    index ∈ returnedChainValueIndexList cache secretKey log chain ↔
      ReturnedChainValueIndex cache secretKey log chain index := by
  simp only [returnedChainValueIndexList, List.mem_dedup, List.mem_flatMap]
  constructor
  · rintro ⟨entry, hentry, hindex⟩
    cases hsignature : entry.2 with
    | none => simp [hsignature] at hindex
    | some signature =>
        simp only [hsignature, List.mem_append] at hindex
        rcases hindex with hindex | hindex
        · left
          cases hdecode : TargetSum.decodeDigest
              (Concrete.CacheView.encodingHash cache secretKey.parameter
                entry.1.leafIndex (entry.1.message, signature.randomness)) with
          | none => simp [hdecode] at hindex
          | some encoding =>
              simp only [hdecode] at hindex
              have hsuffix := (mem_chainSuffixValueIndices_iff
                (.inl entry.1.leafIndex) index.1 (encoding chain) index.2).1 hindex
              exact ⟨entry.1, signature, encoding,
                ⟨entry, hentry, rfl, hsignature⟩, hdecode, hsuffix.1, hsuffix.2⟩
        · right
          unfold topSuffixValueIndices at hindex
          cases htop : secretKey.topSigned (topKeyOf entry.1.leafIndex) with
          | none => simp [htop] at hindex
          | some signed =>
              obtain ⟨randomness, topEncoding⟩ := signed
              simp only [htop] at hindex
              have hsuffix := (mem_chainSuffixValueIndices_iff
                (.inr (topKeyOf entry.1.leafIndex)) index.1 (topEncoding chain) index.2).1 hindex
              exact ⟨entry.1, signature, randomness, topEncoding,
                ⟨entry, hentry, rfl, hsignature⟩, htop, hsuffix.1, hsuffix.2⟩
  · rintro (⟨request, signature, encoding,
      ⟨entry, hentry, hrequest, hsignature⟩, hdecode, hkey, hdigit⟩ |
      ⟨request, signature, randomness, topEncoding,
      ⟨entry, hentry, hrequest, hsignature⟩, htop, hkey, hdigit⟩)
    · subst request
      refine ⟨entry, hentry, ?_⟩
      simp only [hsignature, hdecode, List.mem_append]
      exact Or.inl ((mem_chainSuffixValueIndices_iff
        (.inl entry.1.leafIndex) index.1 (encoding chain) index.2).2 ⟨hkey, hdigit⟩)
    · subst request
      refine ⟨entry, hentry, ?_⟩
      simp only [hsignature, List.mem_append]
      right
      unfold topSuffixValueIndices
      rw [htop]
      exact (mem_chainSuffixValueIndices_iff
        (.inr (topKeyOf entry.1.leafIndex)) index.1 (topEncoding chain) index.2).2 ⟨hkey, hdigit⟩

theorem AttackerActionTrace.sign_mem_toSigningLog
    (trace : AttackerActionTrace) (request : SignRequest) (signature : Signature)
    (hmem : AttackerAction.sign request (some signature) ∈ trace) :
    SigningTranscript.Returned trace.toSigningLog request signature := by
  refine ⟨⟨request, some signature⟩, ?_, rfl, rfl⟩
  exact List.mem_filterMap.mpr ⟨.sign request (some signature), hmem, rfl⟩

end XmssSecurity.CappedChain
