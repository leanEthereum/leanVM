import Whir.SupportedCandidateProtocolRows

/-! One actual initial witness explains all claims and every heavy authenticated
Root0 coordinate. Non-heavy authenticated rows are not asserted honest. -/
namespace Whir.SupportedCandidateProtocol
open Concrete Protocol CausalGame CausalExecution CausalProbability ExecutionShapes
open CandidateFolding SupportedCandidateExtraction ParameterBounds InitialKnowledgeSchedule
set_option maxRecDepth 100000
set_option maxHeartbeats 400000
attribute [local irreducible] ParameterBounds.config

/-- Production SAME-w bridge. The set H is any common support derived from
safe accepted full resets; only its actual cardinality and scalar-hit projection
are consumed. Raw MCA and guarded round events instantiate the six causal
steps internally. No abstract safe-fold-schedule premise occurs. -/
theorem same_w_on_support (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (strategy : Strategy) (t : Tape (config p))
    (valid : oracleValid (liftRoot root) (length (config p) 0) lanes = true)
    (laneBound : lanes ≤ 2 ^ (config p).folds[0]!)
    (mca : ∀ j : Fin (config p).folds[0]!,
      ¬ RawMCA (Input p lanes root claims) strategy (initialLevel p) j t)
    (guard : ∀ j : Fin (config p).folds[0]!,
      ¬ ClaimEscape (Input p lanes root claims) strategy (initialLevel p) j t)
    (batchSafe : t.1 ∉ InitialBatching.candidateEscape
      (InitialCandidates.extensionCandidates (config p) lanes root) claims)
    (cancelSafe : ¬ initialRowCancellation (Input p lanes root claims) (t.2.1 (initialLevel p)).1)
    (target : Array E) (size : target.size = width (config p))
    (truth : dot target (CausalBoundary.boundary (Input p lanes root claims) strategy t (initialLevel p)).state.weight =
      (CausalBoundary.boundary (Input p lanes root claims) strategy t (initialLevel p)).state.claim)
    (H : Finset (Fin (blockLength (config p)))) (enough : threshold (config p) 0 ≤ H.card)
    (agree : ∀ q ∈ H,
      (encode ((config p).logN-(config p).folds[0]!) (config p).rates[0]! target)[q.val]! =
      QueryBatchSoundness.oldWord ((config p).logN-(config p).folds[0]!) (config p).rates[0]!
        (liftRoot root) true (challenges (config p) t).levels[0]!.folds q) :
    ∃ w : Witness (config p) lanes,
      KnowledgeExtraction.Explains (Input p lanes root claims) w ∧
      ∀ q ∈ H, rowMatches (config p) lanes
        (encodedLanes (config p) (paddedWitness (config p) lanes w)) (q, root[q.val]!) = true := by
  have dims := (InitialCandidates.production_initial_facts p).1
  have targetMember : target ∈ foldCandidates (Input p lanes root claims) strategy t 0 (config p).folds[0]! := by
    let lift : Fin (blockLength (config p)) ↪ Fin (length (config p) 0) :=
      { toFun := fun q => ⟨q.val, by simpa only [length, dims] using q.isLt⟩
        inj' := by
          intro a b equality
          apply Fin.ext
          exact congrArg (fun q : Fin (length (config p) 0) => q.val) equality }
    let support := H.map lift
    apply target_member_of_agreement p lanes root claims strategy t valid laneBound target
      (by simpa only [dims, width] using size) support
    · simpa only [support, Finset.card_map] using enough
    · intro q hq
      change q ∈ H.map lift at hq
      obtain ⟨original, inside, equality⟩ := Finset.mem_map.mp hq
      subst q
      have scalar := agree original inside
      change (encode (remaining (config p) 0) (config p).rates[0]! target)[original.val]! =
        dot ((liftRoot root)[original.val]!.reverse) (eqTable (challenges (config p) t).levels[0]!.folds)
      simpa only [dims, QueryBatchSoundness.oldWord, ↓reduceIte] using scalar
  obtain ⟨w, explains, folded⟩ := initial_same_target p lanes root claims strategy t valid laneBound
    mca guard batchSafe target targetMember truth
  refine ⟨w, explains, ?_⟩
  intro q hq
  have qs : q.val < length (config p) 0 := by simpa only [length, dims] using q.isLt
  have rowSize := OracleReplay.oracleValid_row _ _ _ valid q.val qs
  have rs : q.val < root.size := by
    have shape := valid
    simp only [oracleValid, Bool.and_eq_true, beq_iff_eq, liftRoot, Array.size_map] at shape
    exact qs.trans_eq shape.1.symm
  have shape : root[q.val]!.size = lanes := by simpa [liftRoot, getElem!_pos, rs] using rowSize
  apply rowMatches_of_folded_equality (Input p lanes root claims) (t.2.1 (initialLevel p)).1
    cancelSafe w explains.1 q shape
  have seed : Array.ofFn (t.2.1 (initialLevel p)).1 =
      (challenges (config p) t).levels[0]!.folds := by
    simp [challenges, initialLevel, _root_.getElem!_pos, (production_config_valid p).2.1]
  rw [seed, committed_folded_word p lanes root claims t valid laneBound q]
  have encoded := witness_folded_encode p lanes root claims t w q
  rw [folded] at encoded
  exact (agree q hq).symm.trans encoded

#print axioms same_w_on_support
end Whir.SupportedCandidateProtocol
