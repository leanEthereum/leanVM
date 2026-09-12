import SphincsSecurity.Proof.Forced.FtsGuessCachedSigning
namespace SphincsSecurity.Concrete.FtsGuessHash

open _root_.OracleComp OracleSpec UniformTableCompletion
open FtsGuessSigning (Coordinate)
open FtsProbeSimulation (retainedGameRestComputation signingTraceComputation liftOracleWorldLeft)
open SecretGuessObservation (State lazyRun forcedRun environment)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs canonicalGraphGameInputs instFintypePosition
  publicDigestLoop canonicalGraphRoot canonicalGraphInput instSampleableTypePublicParameter hashInputs

/-! ### Hash inputs of continuations -/

theorem hashInputs_bind_of_mem_support {A B : Type} (first : OracleComp OracleWorld A)
    (next : A → OracleComp OracleWorld B) (value : A) (hvalue : value ∈ support first) :
    hashInputs (next value) ⊆ hashInputs (first >>= next) := by
  induction first using OracleComp.inductionOn generalizing next with
  | pure x =>
      rw [support_pure, Set.mem_singleton_iff] at hvalue
      subst hvalue
      rw [pure_bind]
  | query_bind input tail ih =>
      rw [mem_support_bind_iff] at hvalue
      obtain ⟨answer, _, hvalue⟩ := hvalue
      rw [bind_assoc]
      exact (ih answer next hvalue).trans (hashInputs_next_subset input (fun answer => tail answer >>= next) answer)

theorem hashInputs_liftHash_bind_subset {A B : Type} (computation : OracleComp HashSpec A)
    (next : A → OracleComp OracleWorld B) (value : A) (hvalue : value ∈ support computation) :
    hashInputs (next value) ⊆ hashInputs ((liftM computation : OracleComp OracleWorld A) >>= next) := by
  induction computation using OracleComp.inductionOn generalizing next with
  | pure x =>
      rw [support_pure, Set.mem_singleton_iff] at hvalue
      subst hvalue
      rw [liftM_pure, pure_bind]
  | query_bind input tail ih =>
      rw [mem_support_bind_iff] at hvalue
      obtain ⟨answer, _, hvalue⟩ := hvalue
      rw [liftM_bind, bind_assoc]
      change hashInputs (next value) ⊆
        hashInputs (liftM (OracleWorld.query (.inr input)) >>= fun answer => (liftM (tail answer) : OracleComp OracleWorld A) >>= next)
      exact (ih answer next hvalue).trans
        (hashInputs_next_subset (.inr input) (fun answer => (liftM (tail answer) : OracleComp OracleWorld A) >>= next) answer)

theorem hashInputs_liftProb_bind_subset {A B : Type} (computation : ProbComp A)
    (next : A → OracleComp OracleWorld B) (value : A) (hvalue : value ∈ support computation) :
    hashInputs (next value) ⊆ hashInputs ((liftM computation : OracleComp OracleWorld A) >>= next) := by
  induction computation using OracleComp.inductionOn generalizing next with
  | pure x =>
      rw [support_pure, Set.mem_singleton_iff] at hvalue
      subst hvalue
      rw [liftM_pure, pure_bind]
  | query_bind input tail ih =>
      rw [mem_support_bind_iff] at hvalue
      obtain ⟨answer, _, hvalue⟩ := hvalue
      rw [liftM_bind, bind_assoc]
      change hashInputs (next value) ⊆
        hashInputs (liftM (OracleWorld.query (.inl input)) >>= fun answer => (liftM (tail answer) : OracleComp OracleWorld A) >>= next)
      exact (ih answer next hvalue).trans
        (hashInputs_next_subset (.inl input) (fun answer => (liftM (tail answer) : OracleComp OracleWorld A) >>= next) answer)

/-- Evaluating a hash-only computation against a total answer function lands in its support. -/
theorem evalWithAnswerFn_mem_support {A : Type} (f : QueryImpl HashSpec Id) (computation : OracleComp HashSpec A) :
    evalWithAnswerFn f computation ∈ support computation := by
  have hagrees : (∅ : QueryCache HashSpec).AgreesWithFn f := by
    intro input output houtput
    simp at houtput
  obtain ⟨cache, hcache⟩ := (exists_agreesWithFn_evalWithAnswerFn_eq_iff_mem_support computation ∅
    (evalWithAnswerFn f computation)).mp ⟨f, hagrees, rfl⟩
  have h : evalWithAnswerFn f computation ∈ support ((simulateQ (randomOracle : QueryImpl HashSpec _) computation).run' ∅) := by
    rw [StateT.run'_eq, support_map]
    exact ⟨_, hcache, rfl⟩
  exact support_simulateQ_run'_subset _ computation ∅ h

theorem evalWithAnswerFn_tweakableHash (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (domain : HashDomain)
    (payload : HashInput) :
    evalWithAnswerFn f (tweakableHash parameter domain payload : OracleComp HashSpec Digest) =
      truncateHash (f (tweakableHashInput parameter domain payload)) := by
  simp [tweakableHash, oracleHash, evalWithAnswerFn]
  rfl

/-- Every digest is a possible tree root. -/
theorem mem_support_treeRoot (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → Digest) (hheight : 0 < layerHeight lay) (root : Digest) :
    root ∈ support (treeRoot parameter lay tree secret : OracleComp HashSpec Digest) := by
  obtain ⟨level, hlevel⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hheight)
  have hroot : root = evalWithAnswerFn ((fun _ => OtsProbeSimulation.hashOutputOfDigest root) : QueryImpl HashSpec Id)
      (treeRoot parameter lay tree secret : OracleComp HashSpec Digest) := by
    rw [treeRoot, hlevel, treeNode_succ_eq, evalWithAnswerFn_bind, evalWithAnswerFn_bind, evalWithAnswerFn_tweakableHash,
      OtsProbeSimulation.truncateHash_hashOutputOfDigest]
  rw [hroot]
  exact evalWithAnswerFn_mem_support _ _

/-! ### Covered inputs of the adversary's remaining computation -/

theorem hashInputs_bind_congr {A B C : Type} (first : OracleComp OracleWorld A) (left : A → OracleComp OracleWorld B)
    (right : A → OracleComp OracleWorld C) (hnext : ∀ value, hashInputs (left value) = hashInputs (right value)) :
    hashInputs (first >>= left) = hashInputs (first >>= right) := by
  induction first using OracleComp.inductionOn with
  | pure value => simpa only [pure_bind] using hnext value
  | query_bind input tail ih =>
      simp only [bind_assoc, hashInputs_query_bind, ih]
      cases input <;> rfl

theorem signingTrace_bind_fst {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Forgery)
    (next : Forgery → OracleComp (OracleWorld + SigningSpec) Result) :
    (signingTraceComputation computation >>= fun result => next result.1) = computation >>= next := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [FtsProbeSimulation.signingTraceComputation, OracleComp.construct_pure, pure_bind]
  | query_bind input tail ih =>
      simp only [FtsProbeSimulation.signingTraceComputation_query_bind, bind_assoc, bind_map_left, ih]

theorem logged_eq_signingTrace {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result) :
    OtsPrefix.logged computation = signingTraceComputation computation := by
  rw [OtsPrefix.logged, FtsProbeSimulation.simulateQ_withTraceAppend_run_eq_signingTraceComputation, simulateQ_id']

noncomputable def coveredInputs (key : SecretKey) (computation : OracleComp (OracleWorld + SigningSpec) Forgery) : Finset HashInput :=
  hashInputs (simulateQ (expandedAdversaryImpl key) (computation >>= fun forgery =>
    liftOracleWorldLeft (scheme.verify ⟨key.root, key.parameter⟩ forgery.message forgery.signature)))

theorem coveredInputs_main_eq_gameRest (adversary : Adversary) (key : SecretKey) :
    coveredInputs key (adversary.main ⟨key.root, key.parameter⟩) =
      hashInputs (gameRest scheme adversary ⟨key.root, key.parameter⟩ key) := by
  have hretained : OtsProbeSimulation.retainedGameRestComputation adversary ⟨key.root, key.parameter⟩ =
      retainedGameRestComputation adversary ⟨key.root, key.parameter⟩ := by
    unfold OtsProbeSimulation.retainedGameRestComputation retainedGameRestComputation
    rfl
  have htail : retainedGameRestComputation adversary ⟨key.root, key.parameter⟩ =
      signingTraceComputation (adversary.main ⟨key.root, key.parameter⟩) >>= fun result =>
        liftOracleWorldLeft (scheme.verify ⟨key.root, key.parameter⟩ result.1.message result.1.signature) >>= fun verified =>
          pure (result, verified) := by
    unfold retainedGameRestComputation
    apply congrArg (_ >>= ·)
    funext result
    rcases result with ⟨forgery, log⟩
    rfl
  have hdrop : hashInputs (simulateQ (expandedAdversaryImpl key) (signingTraceComputation (adversary.main ⟨key.root, key.parameter⟩)) >>=
      fun result => simulateQ (expandedAdversaryImpl key)
        (liftOracleWorldLeft (scheme.verify ⟨key.root, key.parameter⟩ result.1.message result.1.signature) >>= fun verified =>
          pure (result, verified))) =
      hashInputs (simulateQ (expandedAdversaryImpl key) (signingTraceComputation (adversary.main ⟨key.root, key.parameter⟩)) >>=
        fun result => simulateQ (expandedAdversaryImpl key)
          (liftOracleWorldLeft (scheme.verify ⟨key.root, key.parameter⟩ result.1.message result.1.signature))) := by
    refine hashInputs_bind_congr (simulateQ (expandedAdversaryImpl key) (signingTraceComputation (adversary.main ⟨key.root, key.parameter⟩)))
      (fun result => simulateQ (expandedAdversaryImpl key)
        (liftOracleWorldLeft (scheme.verify ⟨key.root, key.parameter⟩ result.1.message result.1.signature) >>= fun verified =>
          pure (result, verified)))
      (fun result => simulateQ (expandedAdversaryImpl key)
        (liftOracleWorldLeft (scheme.verify ⟨key.root, key.parameter⟩ result.1.message result.1.signature))) (fun result => ?_)
    rw [simulateQ_bind]
    exact ResidualByteFrontend.hashInputs_bind_pure_next _ _ (fun verified => ⟨_, by rw [simulateQ_pure]⟩)
  have hfst : (signingTraceComputation (adversary.main ⟨key.root, key.parameter⟩) >>= fun result =>
      liftOracleWorldLeft (scheme.verify ⟨key.root, key.parameter⟩ result.1.message result.1.signature)) =
      adversary.main ⟨key.root, key.parameter⟩ >>= fun forgery =>
        liftOracleWorldLeft (scheme.verify ⟨key.root, key.parameter⟩ forgery.message forgery.signature) :=
    signingTrace_bind_fst _ (fun forgery => liftOracleWorldLeft (scheme.verify ⟨key.root, key.parameter⟩ forgery.message forgery.signature))
  rw [OtsProbeSimulation.gameRest_eq_map_retained, ResidualByteFrontend.hashInputs_map, hretained, htail, simulateQ_bind, hdrop,
    ← simulateQ_bind, hfst, coveredInputs]

theorem hashInputs_gameRest_subset_gameAfterSecrets (adversary : Adversary) (parameter : PublicParameter) (root : Digest)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    hashInputs (gameRest scheme adversary ⟨root, parameter⟩ ⟨parameter, root, otsSecret, ftsSecret⟩) ⊆
      hashInputs (gameAfterSecrets adversary parameter otsSecret ftsSecret) := by
  rw [gameAfterSecrets]
  have hheight : 0 < layerHeight topLayer := by
    rw [show layerHeight topLayer = maxLayerHeight from rfl]
    decide
  exact hashInputs_liftHash_bind_subset (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree))
    (fun root => gameRest scheme adversary ⟨root, parameter⟩ ⟨parameter, root, otsSecret, ftsSecret⟩) root
    (mem_support_treeRoot parameter topLayer rootTree _ hheight root)

theorem hashInputs_gameAfterSecrets_subset_boundaryGameCore (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    hashInputs (gameAfterSecrets adversary parameter otsSecret ftsSecret) ⊆ hashInputs (boundaryGameCore adversary) := by
  rw [boundaryGameCore, ← ResidualByteFrontend.hashInputs_boundary parameter (gameAfterSecrets adversary parameter otsSecret ftsSecret)]
  refine (hashInputs_liftProb_bind_subset sampleFtsSecrets
    (fun ftsSecret => boundaryComputation parameter (gameAfterSecrets adversary parameter otsSecret ftsSecret)) ftsSecret
    (by simp only [sampleFtsSecrets, support_uniformSample, Set.mem_univ])).trans ?_
  refine (hashInputs_liftProb_bind_subset sampleOtsSecrets
    (fun otsSecret => (liftM sampleFtsSecrets : OracleComp OracleWorld _) >>= fun ftsSecret =>
      boundaryComputation parameter (gameAfterSecrets adversary parameter otsSecret ftsSecret)) otsSecret
    (by simp only [sampleOtsSecrets, support_uniformSample, Set.mem_univ])).trans ?_
  exact hashInputs_liftProb_bind_subset sampleParameter
    (fun parameter => (liftM sampleOtsSecrets : OracleComp OracleWorld _) >>= fun otsSecret =>
      (liftM sampleFtsSecrets : OracleComp OracleWorld _) >>= fun ftsSecret =>
        boundaryComputation parameter (gameAfterSecrets adversary parameter otsSecret ftsSecret)) parameter
    (by unfold sampleParameter; exact @mem_support_uniformSample PublicParameter instSampleableTypePublicParameter parameter)

theorem hashInputs_gameRest_subset_boundaryGameCore (adversary : Adversary) (key : SecretKey) :
    hashInputs (gameRest scheme adversary ⟨key.root, key.parameter⟩ key) ⊆ hashInputs (boundaryGameCore adversary) :=
  (hashInputs_gameRest_subset_gameAfterSecrets adversary key.parameter key.root key.otsSecret key.ftsSecret).trans
    (hashInputs_gameAfterSecrets_subset_boundaryGameCore adversary key.parameter key.otsSecret key.ftsSecret)

theorem coveredInputs_main_subset (adversary : Adversary) (key : SecretKey) :
    coveredInputs key (adversary.main ⟨key.root, key.parameter⟩) ⊆ canonicalGraphGameInputs adversary := by
  rw [coveredInputs_main_eq_gameRest]
  exact (hashInputs_gameRest_subset_boundaryGameCore adversary key).trans (hashInputs_subset_canonicalGraphGameInputs adversary)

theorem expandedAdversaryImpl_inl (key : SecretKey) (input : OracleWorld.Domain) :
    expandedAdversaryImpl key (.inl input) = liftM (OracleWorld.query input) := rfl

theorem expandedAdversaryImpl_inr (key : SecretKey) (message : Message) :
    expandedAdversaryImpl key (.inr message) = sign key message := rfl

theorem coveredInputs_query_bind (key : SecretKey) (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) Forgery) :
    coveredInputs key (liftM ((OracleWorld + SigningSpec).query input) >>= next) =
      hashInputs (expandedAdversaryImpl key input >>= fun answer => simulateQ (expandedAdversaryImpl key) (next answer >>= fun forgery =>
        liftOracleWorldLeft (scheme.verify ⟨key.root, key.parameter⟩ forgery.message forgery.signature))) := by
  unfold coveredInputs
  rw [bind_assoc, simulateQ_bind, simulateQ_spec_query]

theorem coveredInputs_world (key : SecretKey) (input : HashInput)
    (next : HashOutput → OracleComp (OracleWorld + SigningSpec) Forgery) :
    input ∈ coveredInputs key (liftM ((OracleWorld + SigningSpec).query (.inl (.inr input))) >>= next) := by
  rw [coveredInputs_query_bind, expandedAdversaryImpl_inl]
  exact mem_hashInputs_hash_bind input _

theorem coveredInputs_world_next (key : SecretKey) (input : OracleWorld.Domain)
    (next : OracleWorld.Range input → OracleComp (OracleWorld + SigningSpec) Forgery) (answer : OracleWorld.Range input) :
    coveredInputs key (next answer) ⊆ coveredInputs key (liftM ((OracleWorld + SigningSpec).query (.inl input)) >>= next) := by
  rw [coveredInputs_query_bind, expandedAdversaryImpl_inl]
  exact hashInputs_next_subset input (fun answer => simulateQ (expandedAdversaryImpl key) (next answer >>= fun forgery =>
    liftOracleWorldLeft (scheme.verify ⟨key.root, key.parameter⟩ forgery.message forgery.signature))) answer

theorem coveredInputs_sign (key : SecretKey) (message : Message)
    (next : Option Signature → OracleComp (OracleWorld + SigningSpec) Forgery) :
    hashInputs (signDigestLoop digestAttemptLimit key message) ⊆
      coveredInputs key (liftM ((OracleWorld + SigningSpec).query (.inr message)) >>= next) := by
  rw [coveredInputs_query_bind, expandedAdversaryImpl_inr]
  refine Finset.Subset.trans ?_ (ResidualByteFrontend.hashInputs_left_subset _ _)
  rw [sign_eq_digestLoop_afterDigest]
  exact ResidualByteFrontend.hashInputs_left_subset _ _

theorem coveredInputs_sign_next (key : SecretKey) (message : Message)
    (next : Option Signature → OracleComp (OracleWorld + SigningSpec) Forgery)
    (signature : Option Signature) (hsignature : signature ∈ support (sign key message)) :
    coveredInputs key (next signature) ⊆ coveredInputs key (liftM ((OracleWorld + SigningSpec).query (.inr message)) >>= next) := by
  rw [coveredInputs_query_bind, expandedAdversaryImpl_inr]
  exact hashInputs_bind_of_mem_support (sign key message)
    (fun answer => simulateQ (expandedAdversaryImpl key) (next answer >>= fun forgery =>
      liftOracleWorldLeft (scheme.verify ⟨key.root, key.parameter⟩ forgery.message forgery.signature))) signature hsignature

theorem simulateQ_expanded_liftOracleWorldLeft {Result : Type} (key : SecretKey) (computation : OracleComp OracleWorld Result) :
    simulateQ (expandedAdversaryImpl key) (liftOracleWorldLeft computation) = computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      rw [FtsProbeSimulation.liftOracleWorldLeft_query_bind, simulateQ_bind, simulateQ_spec_query]
      simp only [ih]
      rfl

theorem coveredInputs_pure (key : SecretKey) (forgery : Forgery) :
    coveredInputs key (pure forgery) = hashInputs (scheme.verify ⟨key.root, key.parameter⟩ forgery.message forgery.signature) := by
  rw [coveredInputs, pure_bind, simulateQ_expanded_liftOracleWorldLeft]

/-! ### Candidate sets only shrink -/

variable (parameter : PublicParameter) (root : Digest)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (labels : CanonicalGraphLabels)
  (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs parameter ⊆ inputs)
  (selections : ReferenceFamily) (rows : CanonicalEncodingRows) (dummy : OtsReferenceWords) (slot : Nat)

theorem cachedForcedRun_allowed_subset {Result : Type} (computation : OracleComp World Result)
    (cache : QueryCache HashSpec) (state : State Coordinate Digest PUnit) (result : Result × CachedState)
    (hr : cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot computation (cache, state) result ≠ 0) :
    ∀ coordinate, result.2.2.allowed coordinate ⊆ state.allowed coordinate := by
  obtain ⟨seed, _, hforced⟩ := cachedForcedRun_fixed_seed parameter root otsSecret labels inputs hencoding selections rows dummy slot
    computation cache state result hr
  have hlazy := SecretGuessObservation.forcedRun_nonzero _ slot _ _ _ hforced
  apply SecretGuessObservation.lazyRun_preserves _ (fun current : State Coordinate Digest PUnit =>
    ∀ coordinate, current.allowed coordinate ⊆ state.allowed coordinate) _ computation state (fun _ => Finset.Subset.refl _) _ hlazy
  intro current hcurrent input step hstep coordinate
  cases input with
  | inl input =>
      simp only [SecretGuessObservation.lazyImpl, StateT.run_mk, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero,
        Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hstep
      obtain ⟨answer, _, rfl⟩ := hstep
      exact hcurrent coordinate
  | inr input =>
      cases input with
      | inl probe =>
          rcases probe with ⟨probed, candidate⟩
          simp only [SecretGuessObservation.lazyImpl, StateT.run_mk, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero,
            Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hstep
          obtain ⟨hit, _, rfl⟩ := hstep
          exact (SecretGuessObservation.restrict_subset current.allowed probed candidate hit coordinate).trans (hcurrent coordinate)
      | inr disclosed =>
          simp only [SecretGuessObservation.lazyImpl, StateT.run_mk, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero,
            Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hstep
          obtain ⟨value, hvalue, rfl⟩ := hstep
          have hvalue' : cell (Value := Digest) (current.allowed disclosed) value ≠ 0 := hvalue
          have hmem : (value : Digest) ∈ current.allowed disclosed := by
            rw [cell_apply] at hvalue'
            by_contra hnot
            exact hvalue' (if_neg hnot)
          show Function.update current.allowed disclosed ({(value : Digest)} : Finset Digest) coordinate ⊆ state.allowed coordinate
          by_cases heq : coordinate = disclosed
          · subst heq
            rw [Function.update_self]
            exact (Finset.singleton_subset_iff.mpr hmem).trans (hcurrent coordinate)
          · rw [Function.update_of_ne heq]
            exact hcurrent coordinate

/-! ### Signatures of the cached forced law are possible signer outputs -/

theorem support_simulateQ_fixedHashWorld_subset {Result : Type} (f : QueryImpl HashSpec Id)
    (computation : OracleComp OracleWorld Result) :
    support (simulateQ (fixedHashWorld f) computation) ⊆ support computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query]
      intro value hvalue
      rw [mem_support_bind_iff] at hvalue
      obtain ⟨answer, _, hvalue⟩ := hvalue
      rw [mem_support_bind_iff]
      exact ⟨answer, mem_support_query input answer, ih answer hvalue⟩

theorem mem_support_of_fixedBoundaryRun {Result : Type} (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (computation : OracleComp OracleWorld Result) (result : Result × SigningBoundaryTrace)
    (hresult : result ∈ support (fixedBoundaryRun parameter f computation)) : result.1 ∈ support computation := by
  rw [fixedBoundaryRun_eq_boundaryComputation] at hresult
  have h := support_simulateQ_fixedHashWorld_subset f _ hresult
  have hfst : result.1 ∈ support (Prod.fst <$> boundaryComputation parameter computation) := by
    rw [support_map]
    exact ⟨result, h, rfl⟩
  rwa [boundaryComputation_fst] at hfst

theorem lazyRun_auxiliary_bind {Result : Type} (auxiliary : QueryImpl Auxiliary ProbComp) (input : Auxiliary.Domain)
    (next : Auxiliary.Range input → OracleComp World Result) (state : State Coordinate Digest PUnit) :
    lazyRun (environment auxiliary) (liftM (World.query (.inl input)) >>= next) state =
      (𝒟[auxiliary input] >>= fun answer => lazyRun (environment auxiliary) (next answer) state) := by
  rw [lazyRun, SecretGuessObservation.runWith_query_bind]
  simp only [SecretGuessObservation.lazyImpl, environment, StateT.run_mk, evalDist_map, Functor.map_map, bind_map_left]
  rfl

theorem foldl_disclosure_allowed_of_notMem (auxiliary : QueryImpl Auxiliary ProbComp) (secrets : Coordinate → Digest)
    (entries : List Coordinate) (state : State Coordinate Digest PUnit) (coordinate : Coordinate) (hnot : coordinate ∉ entries) :
    (entries.foldl (fun state coordinate => SecretGuessObservation.afterDisclosure (environment auxiliary) state coordinate (secrets coordinate))
      state).allowed coordinate = state.allowed coordinate := by
  induction entries generalizing state with
  | nil => rfl
  | cons entry entries ih =>
      rw [List.foldl_cons, ih _ (fun h => hnot (List.mem_cons_of_mem _ h))]
      have hne : coordinate ≠ entry := fun h => hnot (h ▸ List.mem_cons_self ..)
      simp only [SecretGuessObservation.afterDisclosure, discloseTableValue, Function.update_of_ne hne]

theorem foldl_disclosure_allowed_of_mem (auxiliary : QueryImpl Auxiliary ProbComp) (secrets : Coordinate → Digest)
    (entries : List Coordinate) (state : State Coordinate Digest PUnit) (coordinate : Coordinate) (hmem : coordinate ∈ entries) :
    (entries.foldl (fun state coordinate => SecretGuessObservation.afterDisclosure (environment auxiliary) state coordinate (secrets coordinate))
      state).allowed coordinate = {secrets coordinate} := by
  induction entries generalizing state with
  | nil => cases hmem
  | cons entry entries ih =>
      rw [List.foldl_cons]
      by_cases hin : coordinate ∈ entries
      · exact ih _ hin
      · have heq : coordinate = entry := by
          rcases List.mem_cons.mp hmem with h | h
          · exact h
          · exact absurd h hin
        subst heq
        rw [foldl_disclosure_allowed_of_notMem auxiliary secrets entries _ coordinate hin]
        simp only [SecretGuessObservation.afterDisclosure, discloseTableValue, Function.update_self]

theorem completedState_allowed_disclosed (auxiliary : QueryImpl Auxiliary ProbComp) (secrets : Coordinate → Digest)
    (plan : PublicSigningPlan) (view : FewTimeView) (trace : SigningBoundaryTrace) (state : State Coordinate Digest PUnit)
    (tree : FtsTree) :
    (FtsGuessSigning.completedState (environment auxiliary) secrets ((some plan, some view), trace) state).allowed
      (view.1, tree, view.2 tree) = {secrets (view.1, tree, view.2 tree)} := by
  simp only [FtsGuessSigning.completedState, SecretGuessObservation.disclosureSequenceState]
  apply foldl_disclosure_allowed_of_mem
  rw [List.mem_ofFn]
  exact ⟨tree, rfl⟩

theorem completePublicSigningRecord_congr (first second : Index → FtsTree → FtsLeaf → Digest) (record : PublicSigningRecord)
    (hagree : ∀ (plan : PublicSigningPlan) (view : FewTimeView), record.1 = (some plan, some view) →
      ∀ tree, first view.1 tree (view.2 tree) = second view.1 tree (view.2 tree)) :
    completePublicSigningRecord first record = completePublicSigningRecord second record := by
  obtain ⟨⟨plan, view⟩, trace⟩ := record
  cases plan with
  | none => cases view <;> rfl
  | some plan =>
      cases view with
      | none => rfl
      | some view =>
          simp only [completePublicSigningRecord, Option.map_some]
          congr 4
          funext tree
          exact hagree plan view rfl tree

theorem complete_ne_zero_of_mem (allowed : Coordinate → Finset Digest) (secrets : Coordinate → Digest)
    (hmem : ∀ coordinate, secrets coordinate ∈ allowed coordinate) : complete allowed secrets ≠ 0 := by
  rw [complete_apply, if_pos hmem]
  apply ENNReal.inv_ne_zero.mpr
  exact ENNReal.natCast_ne_top _

theorem mem_of_complete_ne_zero (allowed : Coordinate → Finset Digest) (secrets : Coordinate → Digest)
    (hsecrets : complete allowed secrets ≠ 0) : ∀ coordinate, secrets coordinate ∈ allowed coordinate := by
  rw [complete_apply] at hsecrets
  by_contra hnot
  exact hsecrets (if_neg hnot)

/-- A supported signing outcome of the cached forced law is a possible output of the actual signer, for every secret table compatible with the disclosed coordinates. -/
theorem cachedSigning_mem_support_sign (message : Message) (cache : QueryCache HashSpec)
    (state : State Coordinate Digest PUnit) (ha : ∀ coordinate, (state.allowed coordinate).Nonempty)
    (hauxiliary : ∀ seed : inputs → HashOutput, (⟨selections, rows, seed⟩ : ReferenceAuxiliary inputs) ∈ (referenceAuxiliarySample inputs).support)
    (result : ((Option Signature × Option FewTimeView) × SigningBoundaryTrace) × CachedState)
    (hr : cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot (signingProgram message) (cache, state) result ≠ 0)
    (secrets : Coordinate → Digest) (hsecrets : complete result.2.2.allowed secrets ≠ 0) :
    result.1.1.1 ∈ support (sign ⟨parameter, root, otsSecret, FtsGuessSigning.secretTable.symm secrets⟩ message) := by
  obtain ⟨seed, _, hforced⟩ := cachedForcedRun_fixed_seed parameter root otsSecret labels inputs hencoding selections rows dummy slot
    (signingProgram message) cache state result hr
  have hlazy := SecretGuessObservation.forcedRun_nonzero _ slot _ _ _ hforced
  have hsigning : lazyRun (environment (referenceAnswers parameter root otsSecret labels inputs hencoding ⟨selections, rows, seed⟩ dummy))
      (signingProgram message) state =
      FtsGuessSigning.lazySigningRun (environment (referenceAnswers parameter root otsSecret labels inputs hencoding ⟨selections, rows, seed⟩ dummy))
        state parameter root (finiteHashAnswer ∅ inputs (knownReferenceResidual parameter inputs hencoding (known otsSecret labels) rows seed))
        (known otsSecret labels) (referenceFamilyWords selections dummy) selections message := by
    rw [signingProgram, lazyRun_auxiliary_bind]
    rfl
  rw [hsigning, ← FtsGuessSigning.signingRun_erasure _ _ ha, RetainedObservation.bind_nonzero] at hlazy
  obtain ⟨table, _, hnative⟩ := hlazy
  simp only [FtsGuessSigning.nativeRun, FtsGuessSigning.fixedRun_completeRecord, RetainedObservation.bind_nonzero,
    ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hnative
  obtain ⟨record, hrecord, heq⟩ := hnative
  have hstate : result.2.2 = FtsGuessSigning.completedState
      (environment (referenceAnswers parameter root otsSecret labels inputs hencoding ⟨selections, rows, seed⟩ dummy)) table record state :=
    congrArg Prod.snd heq
  have hsignature : result.1 = completePublicSigningRecord (fun index tree leaf => table (index, tree, leaf)) record := congrArg Prod.fst heq
  have hagree : completePublicSigningRecord (fun index tree leaf => secrets (index, tree, leaf)) record =
      completePublicSigningRecord (fun index tree leaf => table (index, tree, leaf)) record := by
    apply completePublicSigningRecord_congr
    intro plan view hrecord tree
    have hmem := mem_of_complete_ne_zero _ _ hsecrets (view.1, tree, view.2 tree)
    have hrec : record = ((some plan, some view), record.2) := Prod.ext hrecord rfl
    rw [hstate, hrec, completedState_allowed_disclosed, Finset.mem_singleton] at hmem
    exact hmem
  have hfixed := FtsGuessSigning.nativeRun_original
    (environment (referenceAnswers parameter root otsSecret labels inputs hencoding ⟨selections, rows, seed⟩ dummy)) state
    ⟨parameter, root, otsSecret, FtsGuessSigning.secretTable.symm secrets⟩ inputs hencoding labels ⟨selections, rows, seed⟩ (hauxiliary seed)
    dummy (fun _ _ _ => False) (known otsSecret labels) (known_agrees otsSecret _ labels _) message
  dsimp only at hfixed
  have hnonzero : (Prod.fst <$> FtsGuessSigning.nativeRun
      (environment (referenceAnswers parameter root otsSecret labels inputs hencoding ⟨selections, rows, seed⟩ dummy))
      (fun coordinate => FtsGuessSigning.secretTable.symm secrets coordinate.1 coordinate.2.1 coordinate.2.2) state parameter root
      (finiteHashAnswer ∅ inputs (knownReferenceResidual parameter inputs hencoding (known otsSecret labels) rows seed))
      (known otsSecret labels) (referenceFamilyWords selections dummy) selections message) result.1 ≠ 0 := by
    rw [FtsGuessSigning.nativeRun_erasure, evalDist_map, hsignature, ← hagree]
    exact map_nonzero_of _ _ record hrecord
  rw [hfixed] at hnonzero
  have hmem := (mem_support_iff_evalDist_apply_ne_zero _ _).mpr hnonzero
  have hview := mem_support_of_fixedBoundaryRun _ _ _ _ hmem
  have hsign : result.1.1.1 ∈ support (Prod.fst <$> signWithView ⟨parameter, root, otsSecret, FtsGuessSigning.secretTable.symm secrets⟩ message) := by
    rw [support_map]
    exact ⟨_, hview, rfl⟩
  rwa [signWithView_fst] at hsign

end SphincsSecurity.Concrete.FtsGuessHash
