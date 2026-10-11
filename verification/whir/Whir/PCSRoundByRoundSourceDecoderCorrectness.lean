import Whir.PCSRoundByRoundSourceDecoder

/-! Kernel-checked output correctness and same-word recovery for the executable
full Root0 decoder. Common support is computed, not supplied to the algorithm. -/
namespace Whir.PCSRoundByRoundSource
open Concrete Protocol CausalGame KnowledgeExtraction SupportedCandidateExtraction
open scoped BigOperators
set_option maxHeartbeats 4000000
attribute [local irreducible] ParameterBounds.config

 theorem support_member (input : Public)
    (foldBound : input.config.folds[0]! ≤ input.config.logN)
    (laneBound : input.lanes ≤ laneCount input.config)
    (w : Witness input.config input.lanes)
    (enough : ParameterBounds.threshold input.config 0 ≤ (matchingRows input w).card) :
    w ∈ InitialCandidates.witnesses input.config input.lanes input.root := by
  classical
  have cube : laneCount input.config * width input.config = 2^input.config.logN := by
    unfold laneCount width
    rw [← Nat.pow_add, Nat.add_sub_of_le foldBound]
  have member : paddedWitness input.config input.lanes w ∈
      InitialCandidates.extensionCandidates input.config input.lanes input.root := by
    apply (CandidateFolding.arrayCandidates_mem_iff _ _ _ _ _).mpr
    refine ⟨?_, matchingRows input w, enough, ?_⟩
    · simp [paddedWitness, ArrayLayout.size_tab, cube]
    · intro lane q hq
      have matched : rowMatches input.config input.lanes
          (encodedLanes input.config (paddedWitness input.config input.lanes w))
          (q, input.root[q.val]!) = true := by
        simpa [matchingRows] using hq
      exact matches_sound _ _ _ _ matched lane
  have projected : InitialCandidates.project input.config input.lanes
      (paddedWitness input.config input.lanes w) = w := by
    funext i
    have limit : i.val < 2^input.config.logN := by
      have occupied := Nat.mul_le_mul_right (width input.config) laneBound
      rw [cube] at occupied
      exact i.isLt.trans_le occupied
    simp [InitialCandidates.project, paddedWitness, tab, getElem!_pos, limit, i.isLt, E.ofK]
  exact Finset.mem_image.mpr ⟨_, member, projected⟩

 theorem run_output_explains {m : Nat} (profile : ParameterBounds.Profile) (lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E) (root : BaseOracle)
    (w : Witness (ParameterBounds.config profile) lanes)
    (output : run profile lanes family points anchorPoint anchorValue root = some w) :
    PCSRewindSource.ExplainsOriginal (ParameterBounds.config profile) lanes root family points anchorPoint anchorValue w := by
  unfold run runForConfig at output
  split at output
  · obtain ⟨prepared, _, output⟩ := Option.bind_eq_some_iff.mp output
    obtain ⟨decoded, _, output⟩ := Option.bind_eq_some_iff.mp output
    dsimp only at output
    split at output
    · rename_i checked
      have same := Option.some.inj output
      subst decoded
      have original := (OriginalClaimsChecker.check_iff prepared w).mp checked.2
      refine ⟨support_member ⟨ParameterBounds.config profile, lanes, root, #[]⟩
        (InitialCandidates.production_initial_facts profile).2.1
        prepared.guards.2.2.2.1 w ?_, original.1, original.2⟩
      simpa only [countedSupport_value] using checked.1
    · contradiction
  · contradiction

 theorem decodeRoot_recovers (input : Public)
    (noWrap : input.config.logN - input.config.folds[0]! + input.config.rates[0]! ≤ 64)
    (redundancy : width input.config < blockLength input.config)
    (w : Witness input.config input.lanes)
    (radius : ∀ lane : Fin input.lanes,
      2 * hammingDist
        (Vector.mk (Array.ofFn (receivedLane input lane)) (by simp) :
          Vector E (ConcreteRowExtraction.domain
            (input.config.logN - input.config.folds[0]! + input.config.rates[0]!) noWrap).n).get
        (fun i => (encode (input.config.logN - input.config.folds[0]!) input.config.rates[0]!
          ((PCSRewindExtraction.witnessLane input w lane).map E.ofK))[i.val]!) ≤
        blockLength input.config - width input.config) :
    (decodeRoot input noWrap).1 = some w := by
  apply PCSRewindExtraction.assembleWitness_recovers
  intro lane
  simp only [Array.getElem_ofFn]
  exact (ConcreteRowExtraction.countedExtractRow_recovers _ _ noWrap redundancy
    (PCSRewindExtraction.witnessLane input w lane) (by simp [PCSRewindExtraction.witnessLane])
    _ (radius lane)).1

 theorem receivedLane_distance (input : Public)
    (foldBound : input.config.folds[0]! ≤ input.config.logN)
    (laneBound : input.lanes ≤ laneCount input.config)
    (w : Witness input.config input.lanes) (lane : Fin input.lanes) :
    hammingDist (receivedLane input lane)
      (fun q => (encode (input.config.logN - input.config.folds[0]!) input.config.rates[0]!
        ((PCSRewindExtraction.witnessLane input w lane).map E.ofK))[q.val]!) ≤
      blockLength input.config - (matchingRows input w).card := by
  classical
  let target := fun q : Fin (blockLength input.config) =>
    (encode (input.config.logN - input.config.folds[0]!) input.config.rates[0]!
      ((PCSRewindExtraction.witnessLane input w lane).map E.ofK))[q.val]!
  have subset : matchingRows input w ⊆ UniqueRadiusSampling.agreement
      (input.config.logN - input.config.folds[0]! + input.config.rates[0]!)
      (receivedLane input lane) target := by
    intro q member
    simp only [UniqueRadiusSampling.agreement, Finset.mem_filter, Finset.mem_univ, true_and]
    apply SupportedCandidateRecovery.live_agrees_of_rowMatches input foldBound laneBound w q _ lane
    simpa [matchingRows] using member
  have card := Finset.card_le_card subset
  have partition := UniqueRadiusSampling.agreement_add_distance
    (input.config.logN - input.config.folds[0]! + input.config.rates[0]!)
    (receivedLane input lane) target
  change _ + hammingDist (receivedLane input lane) target = blockLength input.config at partition
  change hammingDist (receivedLane input lane) target ≤ _
  omega

private theorem hammingDist_index_cast {M N : Nat} (same : M = N) (received target : Fin N → E) :
    hammingDist (fun q => received (Fin.cast same q)) (fun q => target (Fin.cast same q)) =
      hammingDist received target := by
  subst N
  rfl

 theorem decodeRoot_recovers_heavy (profile : ParameterBounds.Profile) (lanes : Nat) (root : BaseOracle)
    (laneBound : lanes ≤ laneCount (ParameterBounds.config profile))
    (w : Witness (ParameterBounds.config profile) lanes)
    (heavy : StrongRootSupport profile lanes root w) :
    (decodeRoot ⟨ParameterBounds.config profile, lanes, root, #[]⟩
      (InitialCandidates.production_initial_facts profile).2.2.1).1 = some w := by
  let input : Public := ⟨ParameterBounds.config profile, lanes, root, #[]⟩
  have gao : PCSRewindExtractor.gaoAgreementCap profile < (matchingRows input w).card :=
    (Nat.le_max_left _ _).trans_lt heavy
  have redundancy := (PCSRewindExtractor.production_heavy_static profile).2.1
  have card : (matchingRows input w).card ≤ blockLength input.config := by
    exact (Finset.card_le_univ _).trans_eq (by simp)
  have enough : 2 * (blockLength input.config - (matchingRows input w).card) ≤
      blockLength input.config - width input.config := by
    unfold PCSRewindExtractor.gaoAgreementCap at gao
    change (blockLength input.config + width input.config - 1) / 2 < _ at gao
    change width input.config < blockLength input.config at redundancy
    omega
  apply decodeRoot_recovers input _ redundancy w
  intro lane
  have distance := receivedLane_distance input (InitialCandidates.production_initial_facts profile).2.1
    laneBound w lane
  have size : (ConcreteRowExtraction.domain
      (input.config.logN - input.config.folds[0]! + input.config.rates[0]!)
      (InitialCandidates.production_initial_facts profile).2.2.1).n = blockLength input.config :=
    ConcreteRowExtraction.domain_size _ _
  have receivedEqual : (Vector.mk (Array.ofFn (receivedLane input lane)) (by simp) :
      Vector E (ConcreteRowExtraction.domain
        (input.config.logN - input.config.folds[0]! + input.config.rates[0]!)
        (InitialCandidates.production_initial_facts profile).2.2.1).n).get =
      fun q => receivedLane input lane (Fin.cast size q) := by
    funext q
    simp [Vector.get, Fin.cast]
  rw [receivedEqual]
  change 2 * hammingDist (fun q => receivedLane input lane (Fin.cast size q))
    (fun q => (encode (input.config.logN - input.config.folds[0]!) input.config.rates[0]!
      ((PCSRewindExtraction.witnessLane input w lane).map E.ofK))[(Fin.cast size q).val]!) ≤ _
  rw [hammingDist_index_cast size (receivedLane input lane)
    (fun q => (encode (input.config.logN - input.config.folds[0]!) input.config.rates[0]!
      ((PCSRewindExtraction.witnessLane input w lane).map E.ofK))[q.val]!)]
  exact (Nat.mul_le_mul_left 2 distance).trans enough

 theorem run_recovers_heavy {m : Nat} (profile : ParameterBounds.Profile) (lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E) (root : BaseOracle)
    (prepared : OriginalClaimsChecker.Prepared (ParameterBounds.config profile) lanes m family points anchorPoint anchorValue)
    (familyCap : m ≤ 2^64) (pointCap : points.size ≤ 2^64)
    (full : FullRoot (ParameterBounds.config profile) lanes root)
    (w : Witness (ParameterBounds.config profile) lanes)
    (heavy : StrongRootSupport profile lanes root w)
    (original : RingPCSGame.Honest (ParameterBounds.config profile) lanes family points w)
    (anchor : CommitmentAnchor.value (ParameterBounds.config profile) lanes w anchorPoint = anchorValue) :
    run profile lanes family points anchorPoint anchorValue root = some w := by
  have recovered := decodeRoot_recovers_heavy profile lanes root prepared.guards.2.2.2.1 w heavy
  have threshold := (PCSRewindExtractor.production_heavy_static profile).2.2
  have enough : ParameterBounds.threshold (ParameterBounds.config profile) 0 ≤
      (matchingRows ⟨ParameterBounds.config profile, lanes, root, #[]⟩ w).card := by
    unfold StrongRootSupport at heavy
    omega
  unfold run runForConfig
  rw [ite_eq_left ⟨familyCap, pointCap, full⟩]
  cases hp : OriginalClaimsChecker.prepare (ParameterBounds.config profile) lanes family points anchorPoint anchorValue with
  | none =>
    have valid := (OriginalClaimsChecker.prepare_some_iff _ _ family points anchorPoint anchorValue).mpr prepared.guards
    simp [hp] at valid
  | some cached =>
    simp only [Option.bind_some, recovered]
    rw [ite_eq_left ⟨by simpa only [countedSupport_value] using enough,
      (OriginalClaimsChecker.check_iff cached w).mpr ⟨original, anchor⟩⟩]

#print axioms run_output_explains
#print axioms decodeRoot_recovers_heavy
#print axioms run_recovers_heavy
end Whir.PCSRoundByRoundSource
