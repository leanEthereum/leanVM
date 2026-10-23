import SphincsFors.Scheme
import SphincsBase.Proof.Base.Probability

/-! Uniform bit extraction; adapted from leanVM b7a107256. -/
namespace SphincsFors
open OracleComp OracleSpec ENNReal
theorem hashOutput_eq_of_extract {width : Nat} (hwidth : width ≤ hashOutputBits) {x y : HashOutput}
    (hlow : x.extractLsb' 0 width = y.extractLsb' 0 width)
    (hhigh : x.extractLsb' width (hashOutputBits - width)
      = y.extractLsb' width (hashOutputBits - width)) : x = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hlt : i < width
  · have := congrArg (fun b : BitVec width => b.getLsbD i) hlow
    simpa [BitVec.getLsbD_extractLsb', hlt] using this
  · have hshift : i - width < hashOutputBits - width := by omega
    have := congrArg (fun b : BitVec (hashOutputBits - width) => b.getLsbD (i - width)) hhigh
    simp only [BitVec.getLsbD_extractLsb', hshift, decide_true, Bool.true_and] at this
    rwa [show width + (i - width) = i by omega] at this

def splitHashOutput (width : Nat) (output : HashOutput) :
    BitVec width × BitVec (hashOutputBits - width) :=
  (output.extractLsb' 0 width,
    output.extractLsb' width (hashOutputBits - width))

theorem splitHashOutput_injective {width : Nat} (hwidth : width ≤ hashOutputBits) :
    Function.Injective (splitHashOutput width) := by
  intro left right heq
  apply hashOutput_eq_of_extract hwidth
  · exact congrArg Prod.fst heq
  · exact congrArg Prod.snd heq

theorem splitHashOutput_bijective {width : Nat} (hwidth : width ≤ hashOutputBits) :
    Function.Bijective (splitHashOutput width) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨splitHashOutput_injective hwidth, ?_⟩
  rw [Fintype.card_prod, Fintype.card_bitVec, Fintype.card_bitVec, Fintype.card_bitVec, ← pow_add]
  congr
  omega

noncomputable def splitHashOutputEquiv (width : Nat) (hwidth : width ≤ hashOutputBits) :
    HashOutput ≃ BitVec width × BitVec (hashOutputBits - width) :=
  Equiv.ofBijective (splitHashOutput width) (splitHashOutput_bijective hwidth)

/-- The 32-byte output whose first half is `low` and whose second half is `high`. -/
noncomputable def joinHalves (low high : Digest) : HashOutput :=
  (splitHashOutputEquiv digestBits (by decide)).symm (low, high)

theorem truncateHash_joinHalves (low high : Digest) : truncateHash (joinHalves low high) = low :=
  congrArg Prod.fst ((splitHashOutputEquiv digestBits (by decide)).apply_symm_apply (low, high))

theorem truncateHashHigh_joinHalves (low high : Digest) :
    truncateHashHigh (joinHalves low high) = high :=
  congrArg Prod.snd ((splitHashOutputEquiv digestBits (by decide)).apply_symm_apply (low, high))

theorem joinHalves_halves (output : HashOutput) :
    joinHalves (truncateHash output) (truncateHashHigh output) = output :=
  (splitHashOutputEquiv digestBits (by decide)).symm_apply_apply output

theorem evalDist_hashOutput_extract_uniform {width : Nat} (hwidth : width ≤ hashOutputBits) :
    ((fun output : HashOutput => output.extractLsb' 0 width) <$>
        ($ᵗ HashOutput : ProbComp HashOutput)) =ᵈ ($ᵗ BitVec width : ProbComp (BitVec width)) := by
  let split := splitHashOutput width
  have hmap :
      (fun output : HashOutput => output.extractLsb' 0 width) <$>
          ($ᵗ HashOutput : ProbComp HashOutput) =
        Prod.fst <$> (split <$> ($ᵗ HashOutput : ProbComp HashOutput)) := by
    simp [Functor.map_map, split, splitHashOutput]
  rw [hmap]
  have hsplit :
      (split <$> ($ᵗ HashOutput : ProbComp HashOutput)) =ᵈ ($ᵗ (BitVec width × BitVec (hashOutputBits - width)) :
          ProbComp (BitVec width × BitVec (hashOutputBits - width))) :=
    SampleableType.map_uniformSample_evalDistEq_of_bijective
      (α := HashOutput) (β := BitVec width × BitVec (hashOutputBits - width))
      (splitHashOutput_bijective hwidth)
  refine (hsplit.map Prod.fst).trans fun p => ?_
  rw [prEvent_map]
  exact SampleableType.prEvent_uniformSample_fst p

/-- A field of a hash output is uniform when some other field completes it into an injective
reading of the output and the two widths add up to the output's. -/
theorem evalDist_hashOutput_field_uniform {width rest : Nat} (hsum : width + rest = hashOutputBits)
    (field : HashOutput → BitVec width) (other : HashOutput → BitVec rest)
    (hinj : Function.Injective fun output => (field output, other output)) :
    (field <$> ($ᵗ HashOutput : ProbComp HashOutput)) =ᵈ ($ᵗ BitVec width : ProbComp (BitVec width)) := by
  have hbij : Function.Bijective fun output : HashOutput => (field output, other output) := by
    apply (Fintype.bijective_iff_injective_and_card _).2
    refine ⟨hinj, ?_⟩
    rw [Fintype.card_prod, Fintype.card_bitVec, Fintype.card_bitVec, Fintype.card_bitVec, ← pow_add, hsum]
  have hmap : field <$> ($ᵗ HashOutput : ProbComp HashOutput) =
      Prod.fst <$> ((fun output : HashOutput => (field output, other output)) <$>
        ($ᵗ HashOutput : ProbComp HashOutput)) := by
    simp [Functor.map_map]
  rw [hmap]
  refine ((SampleableType.map_uniformSample_evalDistEq_of_bijective
    (α := HashOutput) (β := BitVec width × BitVec rest) hbij).map Prod.fst).trans fun p => ?_
  rw [prEvent_map]
  exact SampleableType.prEvent_uniformSample_fst p

/-- Equal fields give equal bits. -/
theorem getLsbD_eq_of_extract_eq {n start width : Nat} {x y : BitVec n}
    (h : x.extractLsb' start width = y.extractLsb' start width) {i : Nat}
    (hlow : start ≤ i) (hhigh : i < start + width) : x.getLsbD i = y.getLsbD i := by
  have hbit := congrArg (fun b : BitVec width => b.getLsbD (i - start)) h
  simp only [BitVec.getLsbD_extractLsb', show i - start < width by omega, decide_true,
    Bool.true_and] at hbit
  rwa [show start + (i - start) = i by omega] at hbit

/-- Both parts of a concatenation are determined by it. -/
theorem append_inj {n k : Nat} {x x' : BitVec n} {y y' : BitVec k} (h : x ++ y = x' ++ y') :
    x = x' ∧ y = y' := by
  constructor
  · have := congrArg (fun b : BitVec (n + k) => b.extractLsb' k n) h
    simpa only [BitVec.extractLsb'_append_eq_left] using this
  · have := congrArg (fun b : BitVec (n + k) => b.extractLsb' 0 k) h
    simpa only [BitVec.extractLsb'_append_eq_right] using this

theorem getLsbD_callIndices (output : HashOutput) (i : Nat) :
    (callIndices output).getLsbD i =
      if i < 60 then output.getLsbD i
      else if i < 120 then output.getLsbD (64 + (i - 60)) else false := by
  unfold callIndices
  rw [BitVec.getLsbD_append]
  simp only [BitVec.getLsbD_extractLsb']
  by_cases h0 : i < 60
  · simp [h0]
  by_cases h1 : i < 120
  · simp [h0, h1, show i - 60 < 60 by omega]
  · simp [h0, h1, show ¬ i - 60 < 60 by omega]

theorem getLsbD_firstCallFields (output : HashOutput) (i : Nat) :
    (firstCallFields output).getLsbD i =
      if i < 26 then output.getLsbD (128 + i) else (callIndices output).getLsbD (i - 26) := by
  change (callIndices output ++ output.extractLsb' 128 26).getLsbD i = _
  rw [BitVec.getLsbD_append]
  by_cases h0 : i < 26
  · simp [h0]
  · simp [h0]

/-- Bit `i` of the digest's field string, in terms of the two outputs: the index, bits
`128 .. 153` of call `0`; then, for each call, the low 60 bits of its first two 64-bit words. -/
theorem getLsbD_truncateMessageDigest (first second : HashOutput) (i : Nat) :
    (truncateMessageDigest first second).getLsbD i =
      if i < 26 then first.getLsbD (128 + i)
      else if i < 86 then first.getLsbD (i - 26)
      else if i < 146 then first.getLsbD (64 + (i - 86))
      else if i < 206 then second.getLsbD (i - 146)
      else if i < 266 then second.getLsbD (64 + (i - 206))
      else false := by
  have hbit : (truncateMessageDigest first second).getLsbD i =
      (decide (i < 266) && (callIndices second ++ firstCallFields first).getLsbD i) := by
    unfold truncateMessageDigest
    rw [BitVec.getLsbD_extractLsb', Nat.zero_add]
    rfl
  rw [hbit, BitVec.getLsbD_append, getLsbD_firstCallFields, getLsbD_callIndices,
    getLsbD_callIndices]
  by_cases h0 : i < 26
  · simp only [h0, show i < 146 by omega, show i < 266 by omega, ite_true, decide_true,
      Bool.true_and]
  by_cases h1 : i < 86
  · simp only [h0, h1, show i < 146 by omega, show i < 266 by omega, show i - 26 < 60 by omega,
      ite_true, ite_false, decide_true, Bool.true_and]
  by_cases h2 : i < 146
  · simp only [h0, h1, h2, show i < 266 by omega, show ¬ i - 26 < 60 by omega,
      show i - 26 < 120 by omega, ite_true, ite_false, decide_true, Bool.true_and]
    rw [show i - 26 - 60 = i - 86 by omega]
  by_cases h3 : i < 206
  · simp only [h0, h1, h2, h3, show i < 266 by omega, show i - 146 < 60 by omega,
      ite_true, ite_false, decide_true, Bool.true_and]
  by_cases h4 : i < 266
  · simp only [h0, h1, h2, h3, h4, show ¬ i - 146 < 60 by omega, show i - 146 < 120 by omega,
      ite_true, ite_false, decide_true, Bool.true_and]
    rw [show i - 146 - 60 = i - 206 by omega]
  · simp only [h0, h1, h2, h3, h4, ite_false, decide_false, Bool.false_and]

/-- Where the FORS indices are (`digest_fields` in `crates/sphincs/src/scheme.rs`): index `kappa` is
in call `kappa / 12`, at bit `64 * ((kappa % 12) / 6) + 10 * (kappa % 6)`, so six indices lie in each
of the first two 64-bit words of a call and none across two words. -/
theorem digestLeaves_truncate (first second : HashOutput) (tree : IndexGroup) :
    Concrete.digestLeaves (truncateMessageDigest first second) tree =
      ((if tree.val < 12 then first else second).extractLsb'
        (64 * (tree.val % 12 / 6) + 10 * (tree.val % 6)) ftsTreeHeight).toFin := by
  have htree : tree.val < 24 := tree.isLt
  unfold Concrete.digestLeaves
  generalize tree.val = kappa at htree ⊢
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi' : i < 10 := hi
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb', getLsbD_truncateMessageDigest]
  congr 1
  change (if 26 + 10 * kappa + i < 26 then first.getLsbD (128 + (26 + 10 * kappa + i))
      else if 26 + 10 * kappa + i < 86 then first.getLsbD (26 + 10 * kappa + i - 26)
      else if 26 + 10 * kappa + i < 146 then first.getLsbD (64 + (26 + 10 * kappa + i - 86))
      else if 26 + 10 * kappa + i < 206 then second.getLsbD (26 + 10 * kappa + i - 146)
      else if 26 + 10 * kappa + i < 266 then second.getLsbD (64 + (26 + 10 * kappa + i - 206))
      else false) = _
  by_cases h0 : kappa < 6
  · simp only [show ¬ 26 + 10 * kappa + i < 26 by omega, show 26 + 10 * kappa + i < 86 by omega,
      show kappa < 12 by omega, ite_true, ite_false]
    rw [show 26 + 10 * kappa + i - 26 = 64 * (kappa % 12 / 6) + 10 * (kappa % 6) + i by omega]
  by_cases h1 : kappa < 12
  · simp only [show ¬ 26 + 10 * kappa + i < 26 by omega, show ¬ 26 + 10 * kappa + i < 86 by omega,
      show 26 + 10 * kappa + i < 146 by omega, h1, ite_true, ite_false]
    rw [show 64 + (26 + 10 * kappa + i - 86) =
      64 * (kappa % 12 / 6) + 10 * (kappa % 6) + i by omega]
  by_cases h2 : kappa < 18
  · simp only [show ¬ 26 + 10 * kappa + i < 26 by omega, show ¬ 26 + 10 * kappa + i < 86 by omega,
      show ¬ 26 + 10 * kappa + i < 146 by omega, show 26 + 10 * kappa + i < 206 by omega, h1,
      ite_true, ite_false]
    rw [show 26 + 10 * kappa + i - 146 = 64 * (kappa % 12 / 6) + 10 * (kappa % 6) + i by omega]
  · simp only [show ¬ 26 + 10 * kappa + i < 26 by omega, show ¬ 26 + 10 * kappa + i < 86 by omega,
      show ¬ 26 + 10 * kappa + i < 146 by omega, show ¬ 26 + 10 * kappa + i < 206 by omega,
      show 26 + 10 * kappa + i < 266 by omega, h1, ite_true, ite_false]
    rw [show 64 + (26 + 10 * kappa + i - 206) =
      64 * (kappa % 12 / 6) + 10 * (kappa % 6) + i by omega]

/-- The bits of a hash output that are not a field of digest call `0`: the top four bits of its
first two 64-bit words, and what follows the index. -/
def firstCallRest (output : HashOutput) : BitVec 110 :=
  output.extractLsb' 154 102 ++ output.extractLsb' 124 4 ++ output.extractLsb' 60 4

/-- The bits of a hash output that are not a field of digest call `1`. -/
def callIndicesRest (output : HashOutput) : BitVec 136 :=
  output.extractLsb' 124 132 ++ output.extractLsb' 60 4

/-- The bits of a hash output outside the index of digest call `0`. -/
def blockIndexRest (output : HashOutput) : BitVec 230 :=
  output.extractLsb' 154 102 ++ output.extractLsb' 0 128

theorem firstCallFields_injective :
    Function.Injective fun output : HashOutput => (firstCallFields output, firstCallRest output) := by
  intro x y h
  obtain ⟨hfields, hrest⟩ := Prod.mk.inj h
  obtain ⟨hindices, hindex⟩ := append_inj hfields
  obtain ⟨hword1, hword0⟩ := append_inj hindices
  obtain ⟨hrest, hpad0⟩ := append_inj hrest
  obtain ⟨htail, hpad1⟩ := append_inj hrest
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi' : i < 256 := hi
  by_cases h0 : i < 60
  · exact getLsbD_eq_of_extract_eq hword0 (by omega) (by omega)
  by_cases h1 : i < 64
  · exact getLsbD_eq_of_extract_eq hpad0 (by omega) (by omega)
  by_cases h2 : i < 124
  · exact getLsbD_eq_of_extract_eq hword1 (by omega) (by omega)
  by_cases h3 : i < 128
  · exact getLsbD_eq_of_extract_eq hpad1 (by omega) (by omega)
  by_cases h4 : i < 154
  · exact getLsbD_eq_of_extract_eq hindex (by omega) (by simp only [totalHeight]; omega)
  · exact getLsbD_eq_of_extract_eq htail (by omega) (by omega)

theorem callIndices_injective :
    Function.Injective fun output : HashOutput => (callIndices output, callIndicesRest output) := by
  intro x y h
  obtain ⟨hindices, hrest⟩ := Prod.mk.inj h
  obtain ⟨hword1, hword0⟩ := append_inj hindices
  obtain ⟨htail, hpad0⟩ := append_inj hrest
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi' : i < 256 := hi
  by_cases h0 : i < 60
  · exact getLsbD_eq_of_extract_eq hword0 (by omega) (by omega)
  by_cases h1 : i < 64
  · exact getLsbD_eq_of_extract_eq hpad0 (by omega) (by omega)
  by_cases h2 : i < 124
  · exact getLsbD_eq_of_extract_eq hword1 (by omega) (by omega)
  · exact getLsbD_eq_of_extract_eq htail (by omega) (by omega)

theorem blockIndexBits_injective :
    Function.Injective fun output : HashOutput =>
      (output.extractLsb' digestBits totalHeight, blockIndexRest output) := by
  intro x y h
  obtain ⟨hindex, hrest⟩ := Prod.mk.inj h
  obtain ⟨htail, hhead⟩ := append_inj hrest
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi' : i < 256 := hi
  by_cases h0 : i < 128
  · exact getLsbD_eq_of_extract_eq hhead (by omega) (by omega)
  by_cases h1 : i < 154
  · exact getLsbD_eq_of_extract_eq hindex (by simp only [digestBits]; omega)
      (by simp only [digestBits, totalHeight]; omega)
  · exact getLsbD_eq_of_extract_eq htail (by omega) (by omega)

/-- The fields of digest call `0` of a uniform output are uniform. -/
theorem evalDist_firstCallFields_uniform :
    (firstCallFields <$> ($ᵗ HashOutput : ProbComp HashOutput)) =ᵈ ($ᵗ BitVec 146 : ProbComp (BitVec 146)) :=
  evalDist_hashOutput_field_uniform (by decide) firstCallFields firstCallRest
    firstCallFields_injective

/-- The `12` FORS indices of a uniform output are uniform. -/
theorem evalDist_callIndices_uniform :
    (callIndices <$> ($ᵗ HashOutput : ProbComp HashOutput)) =ᵈ ($ᵗ BitVec 120 : ProbComp (BitVec 120)) :=
  evalDist_hashOutput_field_uniform (by decide) callIndices callIndicesRest callIndices_injective

/-- The index bits of digest call `0` of a uniform output are uniform. -/
theorem evalDist_blockIndexBits_uniform :
    ((fun output : HashOutput => output.extractLsb' digestBits totalHeight) <$>
        ($ᵗ HashOutput : ProbComp HashOutput)) =ᵈ ($ᵗ BitVec totalHeight : ProbComp (BitVec totalHeight)) :=
  evalDist_hashOutput_field_uniform (by decide) _ blockIndexRest blockIndexBits_injective

theorem evalDist_truncateHash_uniform :
    (truncateHash <$> ($ᵗ HashOutput : ProbComp HashOutput)) =ᵈ ($ᵗ Digest : ProbComp Digest) := by
  exact evalDist_hashOutput_extract_uniform (width := digestBits) (by decide)

theorem probEvent_uniform_truncateHash_eq (target : Digest) :
    Pr{let output ← ($ᵗ HashOutput : ProbComp HashOutput)}[truncateHash output = target] =
      (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  have h := evalDist_truncateHash_uniform.prEvent_eq (· = target)
  rw [prEvent_map] at h
  rw [h]
  exact SampleableType.prEvent_uniformSample_eq_singleton target

theorem probEvent_uniform_truncateHash_mem (targets : Finset Digest) :
    Pr{let output ← ($ᵗ HashOutput : ProbComp HashOutput)}[truncateHash output ∈ targets] =
      (targets.card : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞) := by
  have h := evalDist_truncateHash_uniform.prEvent_eq (· ∈ targets)
  rw [prEvent_map] at h
  rw [h, SampleableType.prEvent_uniformSample]
  rw [Finset.filter_univ_mem]

end SphincsFors
