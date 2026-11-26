module

public import XmssSecurity.State
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.Stateless

/-!
# The statement's SUF-CMA game is EthLib's

An adversary of the statement's game queries coins, leanVM's `π` and `π⁻¹`, and the signing oracle
with the statement's requests. With its queries answered by EthLib's oracles at the same lanes and
requests (`leanVmOracles`), the adversary is one of EthLib's game (`toEthLibAdversary`). The
statement's game equals EthLib's game against the stateless signer, its oracles answered by
leanVM's (`forgeryGame_eq`), with no probability argument. A bound on the adversary's permutation
calls or signing requests in the statement's game bounds them in EthLib's
(`isQueryBoundP_toEthLibAdversary_hash`, `isQueryBoundP_toEthLibAdversary_request`).
-/

@[expose] public section

open OracleComp OracleSpec PFunctor.FreeM ENNReal Common Common.SufCma
open EthLib.Cryptography
open EthLib.Cryptography.LazyPermutation (PermSpec)
open EthLib.Cryptography.Hash.Keccak (State)

/-- EthLib's game's oracles: coins, `π` and `π⁻¹`, and the signing oracle. -/
abbrev EthLibGameSpec :=
  (unifSpec + PermSpec State) +
    EthLib.Cryptography.SufCma.SigningSpec Xmss.Unforgeability.SignRequest Xmss.Signature

namespace XmssSecurity

/-- A bound on a `0/1` cost is a bound on the number of queries it counts. -/
theorem isQueryBoundP_of_queryCostAtMost {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    (p : ι → Prop) [DecidablePred p] (w : ι → ℕ) (hw : ∀ t, w t = if p t then 1 else 0)
    {oa : OracleComp spec α} {n : ℕ} (h : QueryCostAtMost oa w n) : IsQueryBoundP oa p n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure x => trivial
  | query_bind t k ih =>
    have h' := (isQueryBound_query_bind_iff t k n _ _).1 h
    rw [isQueryBoundP_query_bind_iff]
    have hk := fun u ↦ ih u (h'.2 u)
    rw [hw t] at h' hk
    by_cases hp : p t
    · simp only [hp, ite_true] at h' hk ⊢
      exact ⟨Or.inr (by omega), hk⟩
    · simp only [hp, ite_false, Nat.sub_zero, not_false_eq_true, true_or, true_and] at h' hk ⊢
      exact hk

/-- A query of the statement's adversary that is a call of `π` or `π⁻¹`. -/
abbrev IsPermutationQuery :=
  SignatureAlg.IsHashQuery (hs := permutationOracleSpec LeanVM.Semantics.KeccakState)
    (M := LeanXmss.SigningRequest) (S := Option Xmss.Signature)

/-- A query of the statement's adversary that is a signing request. -/
abbrev IsRequestQuery :=
  SignatureAlg.IsSignQuery (hs := permutationOracleSpec LeanVM.Semantics.KeccakState)
    (M := LeanXmss.SigningRequest) (S := Option Xmss.Signature)


/-- The statement's adversary's oracles answered by EthLib's: a coin by a coin, `π` and `π⁻¹` at a
state by EthLib's at the same lanes, a signing request by EthLib's of the same leaf index and
message. -/
def leanVmOracles :
    QueryImpl (RandomPermutationOracles + LeanXmss.SigningOracleSpec)
      (OracleComp EthLibGameSpec)
  | .inl (.inl n) => liftM (EthLibGameSpec.query (.inl (.inl n)))
  | .inl (.inr (.forward x)) => stateEquiv.symm <$> liftM (EthLibGameSpec.query
        (.inl (.inr (.inl (stateEquiv x)))))
  | .inl (.inr (.inverse y)) => stateEquiv.symm <$> liftM (EthLibGameSpec.query
        (.inl (.inr (.inr (stateEquiv y)))))
  | .inr request => liftM (EthLibGameSpec.query (.inr ⟨request.leafIndex, request.message⟩))

/-- EthLib's sponge over `π`, answered by leanVM's oracles, is leanVM's leanXMSS hash. -/
theorem simulateQ_ethLibOracles_keccak256LanesWith (input : Array UInt64) :
    simulateQ ethLibOracles
      (Hash.Keccak.keccak256LanesWith (LazyPermutation.forward (A := State)) input) =
      LeanXmss.xmssHash queryPermutation input := by
  rw [Hash.Keccak.simulateQ_keccak256LanesWith]
  unfold LeanXmss.xmssHash
  congr 1

/-- EthLib's key generation over `π`, answered by leanVM's oracles, is the statement's. -/
theorem simulateQ_ethLibOracles_keyGenWith (seed : Xmss.Seed) :
    simulateQ ethLibOracles (Xmss.keyGenWith
      (Hash.Keccak.keccak256LanesWith (LazyPermutation.forward (A := State))) seed) =
      Xmss.keyGenWith (LeanXmss.xmssHash queryPermutation) seed := by
  rw [Xmss.keyGenWith_map_monad (fun x => simulateQ ethLibOracles x)
    (fun b => simulateQ_pure _ b) (fun x f => simulateQ_bind _ x f),
    funext simulateQ_ethLibOracles_keccak256LanesWith]

/-- EthLib's signer over `π`, answered by leanVM's oracles, is the statement's. -/
theorem simulateQ_ethLibOracles_signWith (sk : Xmss.SecretKey) (idx : Xmss.LeafIndex)
    (msg : Xmss.Message) :
    simulateQ ethLibOracles (Xmss.signWith
      (Hash.Keccak.keccak256LanesWith (LazyPermutation.forward (A := State))) sk idx msg) =
      Xmss.signWith (LeanXmss.xmssHash queryPermutation) sk idx msg := by
  rw [Xmss.signWith_map_monad (fun x => simulateQ ethLibOracles x)
    (fun b => simulateQ_pure _ b) (fun x f => simulateQ_bind _ x f),
    funext simulateQ_ethLibOracles_keccak256LanesWith]

/-- EthLib's verifier over `π`, answered by leanVM's oracles, is the statement's. -/
theorem simulateQ_ethLibOracles_verifyWith (pk : Xmss.PublicKey) (msg : Xmss.Message)
    (sig : Xmss.Signature) :
    simulateQ ethLibOracles (Xmss.verifyWith
      (Hash.Keccak.keccak256LanesWith (LazyPermutation.forward (A := State))) pk msg sig) =
      Xmss.verifyWith (LeanXmss.xmssHash queryPermutation) pk msg sig := by
  rw [Xmss.verifyWith_map_monad (fun x => simulateQ ethLibOracles x)
    (fun b => simulateQ_pure _ b) (fun x f => simulateQ_bind _ x f),
    funext simulateQ_ethLibOracles_keccak256LanesWith]

/-- A request of the statement as EthLib's. -/
def relabelRequest (request : LeanXmss.SigningRequest) : Xmss.Unforgeability.SignRequest :=
  ⟨request.leafIndex, request.message⟩

/-- A signing transcript of the statement as EthLib's. -/
def relabelLog (log : QueryLog LeanXmss.SigningOracleSpec) :
    QueryLog (SufCma.SigningSpec Xmss.Unforgeability.SignRequest Xmss.Signature) :=
  log.map fun entry => ⟨relabelRequest entry.1, entry.2⟩

/-- The adversary's oracles in EthLib's game after key generation, the signer stateless. -/
noncomputable def phaseOraclesEthLib (sk : Xmss.SecretKey) :
    QueryImpl EthLibGameSpec
      (WriterT (QueryLog (SufCma.SigningSpec Xmss.Unforgeability.SignRequest Xmss.Signature))
        (OracleComp (unifSpec + PermSpec State))) :=
  QueryImpl.ofLift (unifSpec + PermSpec State)
    (WriterT (QueryLog (SufCma.SigningSpec Xmss.Unforgeability.SignRequest Xmss.Signature))
      (OracleComp (unifSpec + PermSpec State))) +
    QueryImpl.withLogging fun (request : Xmss.Unforgeability.SignRequest) =>
      (fun (result : Except Xmss.XmssError Xmss.Signature × Xmss.SecretKey) =>
        result.1.toOption) <$>
        Xmss.signWith (Hash.Keccak.keccak256LanesWith (LazyPermutation.forward (A := State)))
          sk request.leafIndex request.message

/-- The adversary's oracles in the statement's game after key generation. -/
noncomputable def phaseOraclesStatement (sk : Xmss.SecretKey) :
    QueryImpl (RandomPermutationOracles + LeanXmss.SigningOracleSpec)
      (WriterT (QueryLog LeanXmss.SigningOracleSpec) (OracleComp RandomPermutationOracles)) :=
  QueryImpl.ofLift RandomPermutationOracles
    (WriterT (QueryLog LeanXmss.SigningOracleSpec) (OracleComp RandomPermutationOracles)) +
    QueryImpl.withLogging (spec := LeanXmss.SigningOracleSpec)
      (LeanXmss.RandomPermutationModel.sufCmaScheme.sign sk)

/-- EthLib's adversary phase answers a coin or a permutation call, logging nothing. -/
theorem run_phaseOraclesEthLib_inl (sk : Xmss.SecretKey)
    (q : (unifSpec + PermSpec State).Domain) :
    (phaseOraclesEthLib sk (.inl q)).run =
      (fun x => (x, ∅)) <$> (liftM ((unifSpec + PermSpec State).query q) :
        OracleComp (unifSpec + PermSpec State) _) := rfl

/-- The statement's adversary phase answers a coin or a permutation call, logging nothing. -/
theorem run_phaseOraclesStatement_inl (sk : Xmss.SecretKey)
    (q : RandomPermutationOracles.Domain) :
    (phaseOraclesStatement sk (.inl q)).run =
      (fun x => (x, ∅)) <$> (liftM (RandomPermutationOracles.query q) :
        OracleComp RandomPermutationOracles _) := rfl

/-- EthLib's adversary phase answers a request with the stateless signer, and logs it. -/
theorem run_phaseOraclesEthLib_inr (sk : Xmss.SecretKey)
    (request : Xmss.Unforgeability.SignRequest) :
    (phaseOraclesEthLib sk (.inr request)).run =
      (fun u => (u, [⟨request, u⟩])) <$> ((fun result => result.1.toOption) <$>
        Xmss.signWith (Hash.Keccak.keccak256LanesWith (LazyPermutation.forward (A := State)))
          sk request.leafIndex request.message) := by
  simp [phaseOraclesEthLib, QueryImpl.withLogging_apply]

/-- The statement's adversary phase answers a request with its signer, and logs it. -/
theorem run_phaseOraclesStatement_inr (sk : Xmss.SecretKey)
    (request : LeanXmss.SigningRequest) :
    (phaseOraclesStatement sk (.inr request)).run =
      (fun u => (u, [⟨request, u⟩])) <$> ((fun result => result.1.toOption) <$>
        Xmss.signWith (LeanXmss.xmssHash queryPermutation) sk request.leafIndex
          request.message) := by
  simp [phaseOraclesStatement, QueryImpl.withLogging_apply,
    LeanXmss.RandomPermutationModel.sufCmaScheme]

/-- One query of the statement's adversary, answered by EthLib's oracles then leanVM's. -/
theorem simulateQ_ethLibOracles_query (sk : Xmss.SecretKey)
    (t : (RandomPermutationOracles + LeanXmss.SigningOracleSpec).Domain) :
    simulateQ ethLibOracles
        (simulateQ (phaseOraclesEthLib sk) (leanVmOracles t)).run =
      (fun x => (x.1, relabelLog x.2)) <$> (phaseOraclesStatement sk t).run := by
  rcases t with (n | x | y) | request
  · simp only [leanVmOracles, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      LawfulFunctor.id_map]
    rw [run_phaseOraclesEthLib_inl, run_phaseOraclesStatement_inl]
    simp [relabelLog, ethLibOracles]
  · simp only [leanVmOracles, simulateQ_map, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, LawfulFunctor.id_map]
    rw [WriterT.run_map, run_phaseOraclesEthLib_inl, run_phaseOraclesStatement_inl]
    simp [relabelLog, ethLibOracles]
    rw [Equiv.symm_apply_apply]
  · simp only [leanVmOracles, simulateQ_map, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, LawfulFunctor.id_map]
    rw [WriterT.run_map, run_phaseOraclesEthLib_inl, run_phaseOraclesStatement_inl]
    simp [relabelLog, ethLibOracles]
    rw [Equiv.symm_apply_apply]
  · simp only [leanVmOracles, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      LawfulFunctor.id_map]
    rw [run_phaseOraclesEthLib_inr, run_phaseOraclesStatement_inr]
    simp [simulateQ_ethLibOracles_signWith, relabelLog, relabelRequest]

/-- The adversary's phase of the statement's game is that of EthLib's, its transcript relabelled. -/
theorem simulateQ_ethLibOracles_phase (sk : Xmss.SecretKey) {α : Type}
    (oa : OracleComp (RandomPermutationOracles + LeanXmss.SigningOracleSpec) α) :
    simulateQ ethLibOracles
        (simulateQ (phaseOraclesEthLib sk) (simulateQ leanVmOracles oa)).run =
      (fun x => (x.1, relabelLog x.2)) <$> (simulateQ (phaseOraclesStatement sk) oa).run := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp [relabelLog]
  | query_bind t k ih =>
    simp only [simulateQ_bind, OracleQuery.input_query,
      OracleQuery.cont_query, simulateQ_query, WriterT.run_bind', simulateQ_map,
      ih, Functor.map_map, bind_map_left]
    rw [simulateQ_ethLibOracles_query sk t]
    simp [bind_map_left, Functor.map_map, Prod.map, relabelLog, List.map_append]

/-- **The statement's adversary as EthLib's**: its queries answered by EthLib's oracles, its
forgery the same message and signature. -/
def toEthLibAdversary
    (adversary : Xmss.PublicKey →
      OracleComp (RandomPermutationOracles + LeanXmss.SigningOracleSpec) LeanXmss.Forgery) :
    EthLib.Cryptography.SufCma.Adversary (PermSpec State) Xmss.Unforgeability.SignRequest
      Xmss.Message Xmss.PublicKey Xmss.Signature :=
  ⟨fun pk ↦ (fun forgery ↦ ⟨forgery.message, forgery.signature⟩) <$>
    simulateQ leanVmOracles (adversary pk)⟩

/-- The two seed samplers are one term. -/
theorem sampleSeed_eq :
    LeanXmss.RandomPermutationModel.sampleSeed = Xmss.Unforgeability.sampleSeed := rfl

/-- Coins pass through leanVM's answers to EthLib's oracles. -/
theorem simulateQ_ethLibOracles_liftM {α : Type} (oa : ProbComp α) :
    simulateQ ethLibOracles (liftM oa : OracleComp (unifSpec + PermSpec State) α) =
      (liftM oa : OracleComp RandomPermutationOracles α) := by
  rw [QueryImpl.simulateQ_liftM_eq_of_query _ (fun t => liftM (unifSpec.query t)) fun _ => rfl]
  rfl

/-- EthLib's key generation with the stateless signer, answered by leanVM's, is the statement's. -/
theorem simulateQ_ethLibOracles_keyGen :
    simulateQ ethLibOracles Xmss.Unforgeability.schemeRpmStateless.keyGen =
      (liftM LeanXmss.RandomPermutationModel.sampleSeed : OracleComp RandomPermutationOracles _) >>=
        fun seed => Xmss.keyGenWith (LeanXmss.xmssHash queryPermutation) seed := by
  change simulateQ ethLibOracles (liftM Xmss.Unforgeability.sampleSeed >>= fun seed =>
    Xmss.keyGenWith (Hash.Keccak.keccak256LanesWith (LazyPermutation.forward (A := State)))
      seed) = _
  rw [simulateQ_bind, simulateQ_ethLibOracles_liftM, ← sampleSeed_eq]
  exact bind_congr fun seed => simulateQ_ethLibOracles_keyGenWith seed

/-- The statement's game is EthLib's, as computations over the model's oracles. -/
theorem forgeryGame_eq
    (adversary : Xmss.PublicKey →
      OracleComp (RandomPermutationOracles + LeanXmss.SigningOracleSpec) LeanXmss.Forgery) :
    forgeryGame LeanXmss.RandomPermutationModel.sufCmaScheme adversary =
      simulateQ ethLibOracles
        (EthLib.Cryptography.SufCma.game Xmss.Unforgeability.schemeRpmStateless
          (toEthLibAdversary adversary)) := by
  unfold SufCma.game
  rw [simulateQ_bind, simulateQ_ethLibOracles_keyGen]
  unfold forgeryGame
  rw [bind_assoc]
  refine bind_congr fun seed => ?_
  refine bind_congr fun keys => ?_
  obtain ⟨pk, sk⟩ := keys
  dsimp only
  rw [Xmss.Unforgeability.gameAfterKeys_schemeRpmStateless, simulateQ_bind]
  change (simulateQ (phaseOraclesStatement sk) (adversary pk)).run >>= _ = _
  change _ = simulateQ ethLibOracles (simulateQ (phaseOraclesEthLib sk) _).run >>= _
  have hmain : (toEthLibAdversary adversary).main pk =
      (fun forgery ↦ (⟨forgery.message, forgery.signature⟩ :
        EthLib.Cryptography.SufCma.Forgery Xmss.Message Xmss.Signature)) <$>
        simulateQ leanVmOracles (adversary pk) := rfl
  rw [hmain, simulateQ_map, WriterT.run_map, simulateQ_map, simulateQ_ethLibOracles_phase,
    Functor.map_map, bind_map_left]
  refine bind_congr fun x => ?_
  obtain ⟨forgery, log⟩ := x
  dsimp only
  unfold SufCma.checkForgery
  rw [simulateQ_bind, show simulateQ ethLibOracles
      (Xmss.Unforgeability.schemeRpmStateless.verify pk forgery.message forgery.signature) =
      LeanXmss.RandomPermutationModel.sufCmaScheme.verify pk forgery from
    simulateQ_ethLibOracles_verifyWith pk forgery.message forgery.signature]
  refine bind_congr fun verified => ?_
  rw [simulateQ_pure]
  refine congrArg pure (congrArg (· && verified) (decide_eq_decide.mpr ?_))
  simp [relabelLog, relabelRequest, Xmss.Unforgeability.schemeRpmStateless,
    Xmss.Unforgeability.schemeRpm, Xmss.Unforgeability.scheme, Xmss.Unforgeability.Valid,
    SufCma.Returned, SignerReturnedForgery, LeanXmss.SigningTranscript.NoLeafIndexReused,
    Function.comp_def]

/-- **The statement's game is EthLib's**, run in leanVM's model: the statement's adversary against
the statement's leanXMSS, and the adversary as EthLib's against EthLib's leanXMSS with the stateless
signer, its oracles answered by leanVM's, win with one law. -/
theorem evalDist_runWithRandomPermutation_forgeryGame
    (adversary : Xmss.PublicKey →
      OracleComp (RandomPermutationOracles + LeanXmss.SigningOracleSpec) LeanXmss.Forgery) :
    evalDist (runWithRandomPermutation
        (forgeryGame LeanXmss.RandomPermutationModel.sufCmaScheme adversary)) =
      evalDist (runWithRandomPermutation (simulateQ ethLibOracles
        (EthLib.Cryptography.SufCma.game Xmss.Unforgeability.schemeRpmStateless
          (toEthLibAdversary adversary)))) :=
  congrArg (fun c => evalDist (runWithRandomPermutation c)) (forgeryGame_eq adversary)

/-- **The adversary's permutation calls**: bounded in the statement's game, so in EthLib's. -/
theorem isQueryBoundP_toEthLibAdversary_hash
    {adversary : Xmss.PublicKey →
      OracleComp (RandomPermutationOracles + LeanXmss.SigningOracleSpec) LeanXmss.Forgery}
    {pk : Xmss.PublicKey} {q : ℕ}
    (h : QueryCostAtMost (adversary pk) adversaryPermutationCost q) :
    IsQueryBoundP ((toEthLibAdversary adversary).main pk)
      (EthLib.Cryptography.SufCma.IsAdversaryHash (PermSpec State)
        Xmss.Unforgeability.SignRequest Xmss.Signature) q := by
  refine (isQueryBoundP_map_iff _ _ _).2 (IsQueryBoundP.simulateQ_of_step
    (p := IsPermutationQuery) (isQueryBoundP_of_queryCostAtMost _ adversaryPermutationCost ?_ h)
    ?_ ?_)
  · rintro ((n | (x | y)) | r) <;> rfl
  · rintro ((n | (x | y)) | r) hp <;> simp_all [leanVmOracles, IsPermutationQuery,
      SignatureAlg.IsHashQuery]
  · rintro ((n | (x | y)) | r) hp <;> simp_all [leanVmOracles, IsPermutationQuery,
      SignatureAlg.IsHashQuery]

/-- **The adversary's signing requests**: bounded in the statement's game, so in EthLib's. -/
theorem isQueryBoundP_toEthLibAdversary_request
    {adversary : Xmss.PublicKey →
      OracleComp (RandomPermutationOracles + LeanXmss.SigningOracleSpec) LeanXmss.Forgery}
    {pk : Xmss.PublicKey} {n : ℕ} (h : QueryCostAtMost (adversary pk) signingRequestCost n) :
    IsQueryBoundP ((toEthLibAdversary adversary).main pk)
      (EthLib.Cryptography.SufCma.IsAdversaryRequest (PermSpec State)
        Xmss.Unforgeability.SignRequest Xmss.Signature) n := by
  refine (isQueryBoundP_map_iff _ _ _).2 (IsQueryBoundP.simulateQ_of_step
    (p := IsRequestQuery) (isQueryBoundP_of_queryCostAtMost _ signingRequestCost ?_ h) ?_ ?_)
  · rintro ((n | (x | y)) | r) <;> rfl
  · rintro ((n | (x | y)) | r) hp <;> simp_all [leanVmOracles, IsRequestQuery,
      SignatureAlg.IsSignQuery]
  · rintro ((n | (x | y)) | r) hp <;> simp_all [leanVmOracles, IsRequestQuery,
      SignatureAlg.IsSignQuery]

end XmssSecurity

end
