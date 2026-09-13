import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.FewTimeProbability
import SphincsSecurity.Proof.Scheme.Guess
/-!
# Uniform few-time views

The low 166 bits of a fresh oracle answer are exactly the 26-bit index and the fourteen 10-bit
few-time leaf coordinates used by a coverage pattern. Splitting an answer into low and high bits is
bijective, as is decoding those low bits into a few-time view, so the induced view is uniform.
-/

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

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
  rw [Fintype.card_prod, card_bitVec, card_bitVec, card_bitVec, ← pow_add]
  congr
  omega

noncomputable def splitHashOutputEquiv (width : Nat) (hwidth : width ≤ hashOutputBits) :
    HashOutput ≃ BitVec width × BitVec (hashOutputBits - width) :=
  Equiv.ofBijective (splitHashOutput width) (splitHashOutput_bijective hwidth)

theorem evalDist_hashOutput_extract_uniform {width : Nat} (hwidth : width ≤ hashOutputBits) :
    𝒟[(fun output : HashOutput => output.extractLsb' 0 width) <$>
        ($ᵗ HashOutput : ProbComp HashOutput)] =
      𝒟[($ᵗ BitVec width : ProbComp (BitVec width))] := by
  let split := splitHashOutput width
  have hmap :
      (fun output : HashOutput => output.extractLsb' 0 width) <$>
          ($ᵗ HashOutput : ProbComp HashOutput) =
        Prod.fst <$> (split <$> ($ᵗ HashOutput : ProbComp HashOutput)) := by
    simp [Functor.map_map, split, splitHashOutput]
  rw [hmap]
  have hsplit :
      𝒟[split <$> ($ᵗ HashOutput : ProbComp HashOutput)] =
        𝒟[($ᵗ (BitVec width × BitVec (hashOutputBits - width)) :
          ProbComp (BitVec width × BitVec (hashOutputBits - width)))] :=
    evalDist_map_bijective_uniform_cross
      (α := HashOutput) (β := BitVec width × BitVec (hashOutputBits - width))
      split (splitHashOutput_bijective hwidth)
  rw [evalDist_map, hsplit, ← evalDist_map]
  exact evalDist_map_fst_uniformSample_prod

namespace Concrete

def hashOutputFewTimeView (output : HashOutput) : FewTimeView :=
  (digestIndex (truncateMessageDigest output),
    fun tree => digestLeaves (truncateMessageDigest output) (ftsIndexOf tree))

abbrev FullDigestView := Index × (IndexGroup → FtsLeaf)

def fullDigestView (digest : MessageDigest) : FullDigestView :=
  (digestIndex digest, digestLeaves digest)

theorem fullDigestView_injective : Function.Injective fullDigestView := by
  intro left right heq
  apply BitVec.eq_of_getLsbD_eq
  intro position hposition
  by_cases hindex : position < totalHeight
  · have hcomponent := congrArg (fun view : FullDigestView => BitVec.ofFin view.1) heq
    have hbit := congrArg (fun bits : BitVec totalHeight => bits.getLsbD position) hcomponent
    simpa [fullDigestView, digestIndex, BitVec.getLsbD_extractLsb', hindex] using hbit
  · let treeIndex := (position - totalHeight) / ftsTreeHeight
    have htreeIndex : treeIndex < ftsTrees := by
      have hposition' : position < 176 := by
        simpa [messageDigestBits, totalHeight, ftsTrees, ftsTreeHeight] using hposition
      have hindex' : 26 ≤ position := by
        simpa [totalHeight] using Nat.le_of_not_gt hindex
      simp only [treeIndex, ftsTrees, ftsTreeHeight, totalHeight]
      omega
    let tree : IndexGroup := ⟨treeIndex, htreeIndex⟩
    let within := (position - totalHeight) % ftsTreeHeight
    have hwithin : within < ftsTreeHeight := by
      simp only [within, ftsTreeHeight]
      omega
    have hoffset : totalHeight + ftsTreeHeight * tree.val + within = position := by
      have hindex' : totalHeight ≤ position := Nat.le_of_not_gt hindex
      simp only [tree, treeIndex, within]
      calc
        totalHeight + ftsTreeHeight * ((position - totalHeight) / ftsTreeHeight) +
            (position - totalHeight) % ftsTreeHeight =
            totalHeight + ((position - totalHeight) % ftsTreeHeight +
              ftsTreeHeight * ((position - totalHeight) / ftsTreeHeight)) := by omega
        _ = totalHeight + (position - totalHeight) := by rw [Nat.mod_add_div]
        _ = position := Nat.add_sub_of_le hindex'
    have hcomponent := congrArg (fun view : FullDigestView => BitVec.ofFin (view.2 tree)) heq
    change left.extractLsb' (totalHeight + ftsTreeHeight * tree.val) ftsTreeHeight =
      right.extractLsb' (totalHeight + ftsTreeHeight * tree.val) ftsTreeHeight at hcomponent
    have hbit := congrArg (fun bits : BitVec ftsTreeHeight => bits.getLsbD within) hcomponent
    simp only [BitVec.getLsbD_extractLsb', hwithin, decide_true, Bool.true_and] at hbit
    rwa [hoffset] at hbit

theorem fullDigestView_bijective : Function.Bijective fullDigestView := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨fullDigestView_injective, ?_⟩
  rw [card_bitVec, Fintype.card_prod, Fintype.card_fin, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin, ← pow_mul, ← pow_add]
  rfl

def splitFullDigestView (view : FullDigestView) : FewTimeView × FtsLeaf :=
  ((view.1, fun tree => view.2 (ftsIndexOf tree)), view.2 lastIndexGroup)

theorem splitFullDigestView_injective : Function.Injective splitFullDigestView := by
  intro left right heq
  apply Prod.ext
  · exact congrArg (fun view : FewTimeView × FtsLeaf => view.1.1) heq
  · funext tree
    rcases indexGroup_eq_ftsIndexOf_or_last tree with ⟨ftsTree, rfl⟩ | rfl
    · have hfunctions := congrArg (fun view : FewTimeView × FtsLeaf => view.1.2) heq
      exact congrFun hfunctions ftsTree
    · exact congrArg Prod.snd heq

theorem splitFullDigestView_bijective : Function.Bijective splitFullDigestView := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨splitFullDigestView_injective, ?_⟩
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_prod, fewTimeView_card, Fintype.card_fin, ← pow_mul, ← pow_add]
  norm_num [totalHeight, ftsTreeHeight, ftsTrees]

def digestCoordinates (digest : MessageDigest) : FewTimeView × FtsLeaf :=
  splitFullDigestView (fullDigestView digest)

theorem digestCoordinates_bijective : Function.Bijective digestCoordinates :=
  splitFullDigestView_bijective.comp fullDigestView_bijective

noncomputable def digestCoordinatesEquiv : MessageDigest ≃ FewTimeView × FtsLeaf :=
  Equiv.ofBijective digestCoordinates digestCoordinates_bijective

set_option maxRecDepth 100000 in
theorem evalDist_hashOutput_digestCoordinates_uniform :
    𝒟[(fun output : HashOutput => digestCoordinates (truncateMessageDigest output)) <$>
        ($ᵗ HashOutput : ProbComp HashOutput)] =
      𝒟[($ᵗ (FewTimeView × FtsLeaf) : ProbComp (FewTimeView × FtsLeaf))] := by
  calc
    𝒟[(fun output : HashOutput => digestCoordinates (truncateMessageDigest output)) <$>
        ($ᵗ HashOutput : ProbComp HashOutput)] =
        digestCoordinates <$>
          𝒟[truncateMessageDigest <$> ($ᵗ HashOutput : ProbComp HashOutput)] := by
      rw [evalDist_map, evalDist_map, Functor.map_map]
    _ = digestCoordinates <$>
          𝒟[($ᵗ MessageDigest : ProbComp MessageDigest)] := by
      rw [show truncateMessageDigest =
          (fun output : HashOutput => output.extractLsb' 0 messageDigestBits) from rfl,
        evalDist_hashOutput_extract_uniform
          (show messageDigestBits ≤ hashOutputBits by decide)]
    _ = 𝒟[digestCoordinates <$>
          ($ᵗ MessageDigest : ProbComp MessageDigest)] := by
      rw [evalDist_map]
    _ = 𝒟[($ᵗ (FewTimeView × FtsLeaf) :
          ProbComp (FewTimeView × FtsLeaf))] :=
      evalDist_map_bijective_uniform_cross
        (α := MessageDigest) (β := FewTimeView × FtsLeaf)
        digestCoordinates digestCoordinates_bijective

abbrev HashOutputCoordinates :=
  (FewTimeView × FtsLeaf) × BitVec (hashOutputBits - messageDigestBits)

noncomputable def hashOutputCoordinatesEquiv : HashOutput ≃ HashOutputCoordinates :=
  (splitHashOutputEquiv messageDigestBits
      (show messageDigestBits ≤ hashOutputBits by decide)).trans
    (Equiv.prodCongr digestCoordinatesEquiv
      (Equiv.refl (BitVec (hashOutputBits - messageDigestBits))))

theorem hashOutputCoordinatesEquiv_apply (output : HashOutput) :
    hashOutputCoordinatesEquiv output =
      ((hashOutputFewTimeView output,
          digestLeaves (truncateMessageDigest output) lastIndexGroup),
        output.extractLsb' messageDigestBits (hashOutputBits - messageDigestBits)) := rfl

set_option maxRecDepth 100000 in
theorem evalDist_uniformHashOutput_bind_coordinates {Result : Type}
    (continuation : HashOutput → ProbComp Result) :
    𝒟[($ᵗ HashOutput : ProbComp HashOutput) >>= continuation] =
      𝒟[($ᵗ HashOutputCoordinates : ProbComp HashOutputCoordinates) >>=
        fun coordinates => continuation (hashOutputCoordinatesEquiv.symm coordinates)] := by
  have hmap :
      𝒟[hashOutputCoordinatesEquiv <$> ($ᵗ HashOutput : ProbComp HashOutput)] =
        𝒟[($ᵗ HashOutputCoordinates : ProbComp HashOutputCoordinates)] :=
    evalDist_map_bijective_uniform_cross
      (α := HashOutput) (β := HashOutputCoordinates)
      hashOutputCoordinatesEquiv hashOutputCoordinatesEquiv.bijective
  have hcomputation :
      (hashOutputCoordinatesEquiv <$> ($ᵗ HashOutput : ProbComp HashOutput)) >>=
          (fun coordinates =>
            continuation (hashOutputCoordinatesEquiv.symm coordinates)) =
        ($ᵗ HashOutput : ProbComp HashOutput) >>= continuation := by
    simp [map_eq_bind_pure_comp, bind_assoc]
  rw [← hcomputation, evalDist_bind, hmap, ← evalDist_bind]

set_option maxRecDepth 100000 in
theorem evalDist_randomOracle_fresh_bind_coordinates {Result : Type}
    (input : HashInput) (cache : QueryCache HashSpec) (hcache : cache input = none)
    (continuation : HashOutput × QueryCache HashSpec → ProbComp Result) :
    𝒟[(randomOracle input).run cache >>= continuation] =
      𝒟[($ᵗ HashOutputCoordinates : ProbComp HashOutputCoordinates) >>=
        fun coordinates =>
          let output := hashOutputCoordinatesEquiv.symm coordinates
          continuation (output, cache.cacheQuery input output)] := by
  rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hcache]
  change 𝒟[((fun output : HashOutput => (output, cache.cacheQuery input output)) <$>
      ($ᵗ HashOutput : ProbComp HashOutput)) >>= continuation] = _
  have hcomputation :
      ((fun output : HashOutput => (output, cache.cacheQuery input output)) <$>
          ($ᵗ HashOutput : ProbComp HashOutput)) >>= continuation =
        ($ᵗ HashOutput : ProbComp HashOutput) >>= fun output =>
          continuation (output, cache.cacheQuery input output) := by
    simp [map_eq_bind_pure_comp, bind_assoc]
  rw [hcomputation]
  exact evalDist_uniformHashOutput_bind_coordinates fun output =>
    continuation (output, cache.cacheQuery input output)

def signAttemptResultOfOutput (output : HashOutput) :
    Option (Index × (IndexGroup → FtsLeaf)) :=
  let digest := truncateMessageDigest output
  if Admissible digest then some (digestIndex digest, digestLeaves digest) else none

theorem hashOutputCoordinatesEquiv_symm_digestCoordinates
    (coordinates : HashOutputCoordinates) :
    digestCoordinates (truncateMessageDigest (hashOutputCoordinatesEquiv.symm coordinates)) =
      coordinates.1 := by
  have heq := hashOutputCoordinatesEquiv.apply_symm_apply coordinates
  rw [hashOutputCoordinatesEquiv_apply] at heq
  exact congrArg Prod.fst heq

theorem hashOutputCoordinatesEquiv_symm_view (coordinates : HashOutputCoordinates) :
    hashOutputFewTimeView (hashOutputCoordinatesEquiv.symm coordinates) = coordinates.1.1 := by
  change (digestCoordinates
    (truncateMessageDigest (hashOutputCoordinatesEquiv.symm coordinates))).1 = coordinates.1.1
  exact congrArg Prod.fst (hashOutputCoordinatesEquiv_symm_digestCoordinates coordinates)

theorem hashOutputCoordinatesEquiv_symm_lastLeaf (coordinates : HashOutputCoordinates) :
    digestLeaves (truncateMessageDigest (hashOutputCoordinatesEquiv.symm coordinates))
        lastIndexGroup = coordinates.1.2 := by
  change (digestCoordinates
    (truncateMessageDigest (hashOutputCoordinatesEquiv.symm coordinates))).2 = coordinates.1.2
  exact congrArg Prod.snd (hashOutputCoordinatesEquiv_symm_digestCoordinates coordinates)

theorem signAttemptResultOfOutput_ne_none_iff (output : HashOutput) :
    signAttemptResultOfOutput output ≠ none ↔
      Admissible (truncateMessageDigest output) := by
  simp only [signAttemptResultOfOutput]
  split <;> simp_all

theorem signAttemptResultOfOutput_coordinates_ne_none_iff
    (coordinates : HashOutputCoordinates) :
    signAttemptResultOfOutput (hashOutputCoordinatesEquiv.symm coordinates) ≠ none ↔
      coordinates.1.2 = 0 := by
  rw [signAttemptResultOfOutput_ne_none_iff, Admissible,
    hashOutputCoordinatesEquiv_symm_lastLeaf]

theorem signAttemptResultOfOutput_coordinates_view
    (coordinates : HashOutputCoordinates) (index : Index)
    (leaves : IndexGroup → FtsLeaf)
    (hresult : signAttemptResultOfOutput (hashOutputCoordinatesEquiv.symm coordinates) =
      some (index, leaves)) :
    (index, fun tree => leaves (ftsIndexOf tree)) = coordinates.1.1 := by
  let output := hashOutputCoordinatesEquiv.symm coordinates
  simp only [signAttemptResultOfOutput] at hresult
  split at hresult
  · have hpair := Option.some.inj hresult
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
    exact hashOutputCoordinatesEquiv_symm_view coordinates
  · simp at hresult

theorem signAttemptResultOfOutput_view (output : HashOutput) (index : Index)
    (leaves : IndexGroup → FtsLeaf)
    (hresult : signAttemptResultOfOutput output = some (index, leaves)) :
    (index, fun tree => leaves (ftsIndexOf tree)) = hashOutputFewTimeView output := by
  let coordinates := hashOutputCoordinatesEquiv output
  calc
    (index, fun tree => leaves (ftsIndexOf tree)) = coordinates.1.1 := by
      apply signAttemptResultOfOutput_coordinates_view coordinates index leaves
      simpa [coordinates] using hresult
    _ = hashOutputFewTimeView output := by
      dsimp only [coordinates]
      rw [hashOutputCoordinatesEquiv_apply]

theorem simulateQ_signAttempt_run_eq (secretKey : SecretKey) (message : Message)
    (randomness : Randomness) (cache : QueryCache HashSpec) :
    (simulateQ (randomOracle : QueryImpl HashSpec _)
      (signAttempt secretKey message randomness)).run cache =
        (randomOracle (tweakableHashInput secretKey.parameter .message
          (messageDigestPayload secretKey.root message randomness))).run cache >>=
            fun result => pure (signAttemptResultOfOutput result.1, result.2) := by
  have hquery :
      simulateQ (randomOracle : QueryImpl HashSpec _)
          (oracleHash (tweakableHashInput secretKey.parameter .message
            (messageDigestPayload secretKey.root message randomness)) :
              OracleComp HashSpec HashOutput) =
        randomOracle (tweakableHashInput secretKey.parameter .message
          (messageDigestPayload secretKey.root message randomness)) := by
    change simulateQ (randomOracle : QueryImpl HashSpec _)
      (liftM (HashSpec.query (tweakableHashInput secretKey.parameter .message
        (messageDigestPayload secretKey.root message randomness)))) = _
    exact simulateQ_spec_query
      (impl := (randomOracle : QueryImpl HashSpec
        (StateT (QueryCache HashSpec) ProbComp)))
      (tweakableHashInput secretKey.parameter .message
        (messageDigestPayload secretKey.root message randomness))
  rw [signAttempt, simulateQ_bind, StateT.run_bind, messageDigest,
    simulateQ_bind, StateT.run_bind, hquery]
  simp only [signAttemptResultOfOutput, simulateQ_pure, StateT.run_pure]
  simp only [bind_assoc, pure_bind]
  apply bind_congr
  intro result
  split <;> rfl

set_option maxRecDepth 100000 in
theorem evalDist_signAttempt_fresh_bind_coordinates {Result : Type}
    (secretKey : SecretKey) (message : Message) (randomness : Randomness)
    (cache : QueryCache HashSpec)
    (hcache : cache (tweakableHashInput secretKey.parameter .message
      (messageDigestPayload secretKey.root message randomness)) = none)
    (continuation :
      Option (Index × (IndexGroup → FtsLeaf)) × QueryCache HashSpec →
        ProbComp Result) :
    𝒟[(simulateQ (randomOracle : QueryImpl HashSpec _)
        (signAttempt secretKey message randomness)).run cache >>= continuation] =
      𝒟[($ᵗ HashOutputCoordinates : ProbComp HashOutputCoordinates) >>=
        fun coordinates =>
          let output := hashOutputCoordinatesEquiv.symm coordinates
          continuation (signAttemptResultOfOutput output,
            cache.cacheQuery
              (tweakableHashInput secretKey.parameter .message
                (messageDigestPayload secretKey.root message randomness)) output)] := by
  rw [simulateQ_signAttempt_run_eq]
  simp only [bind_assoc, pure_bind]
  exact evalDist_randomOracle_fresh_bind_coordinates
    (tweakableHashInput secretKey.parameter .message
      (messageDigestPayload secretKey.root message randomness)) cache hcache
    (fun result => continuation (signAttemptResultOfOutput result.1, result.2))

end Concrete

end SphincsSecurity
