module

public import XmssSecurity.Proof.EvalDistEq
public import XmssSecurity.Proof.Bridge.TopBase
public import XmssSecurity.Proof.Bridge.Honest
public import XmssSecurity.Proof.Deterministic.TrialSampling

@[expose] public section

/-!
# The prepared key is the model's key

Over a uniform derivation table, the parameter, the chain starts of both layers and the top bases are
uniform and independent, and the model key built from the run equals the model's key generation.
-/

open OracleComp OracleSpec

namespace XmssSecurity.Bridge

open Seeded DeterministicSigning

set_option backward.isDefEq.respectTransparency false

/-! ## Chain starts from pair derivations -/

/-- The two halves of a derivation start chains `2t` and `2t + 1`. -/
def pairEquiv (K : Type) : (K × ChainPair → HashOutput) ≃ (K → ChainIndex → Digest) where
  toFun outputs key chain := hashHalf chain.val (outputs (key, chainPair chain))
  invFun starts pos := Rom.hashOutputEquivDigestPair.symm
    (starts pos.1 ⟨2 * pos.2.val + 1, by have := pos.2.isLt; simp [numChains] at *; omega⟩,
     starts pos.1 ⟨2 * pos.2.val, by have := pos.2.isLt; simp [numChains] at *; omega⟩)
  left_inv outputs := by
    funext pos
    obtain ⟨key, t⟩ := pos
    have h1 : ∀ h, chainPair (⟨2 * t.val + 1, h⟩ : ChainIndex) = t := fun h =>
      Fin.ext (by simp only [chainPair]; omega)
    have h0 : ∀ h, chainPair (⟨2 * t.val, h⟩ : ChainIndex) = t := fun h =>
      Fin.ext (by simp only [chainPair]; omega)
    simp only [hashHalf, h1, h0, show (2 * t.val + 1) % 2 ≠ 0 by omega, show 2 * t.val % 2 = 0 by omega,
      ite_true, ite_false]
    exact Rom.hashOutputEquivDigestPair.symm_apply_apply (outputs (key, t))
  right_inv starts := by
    funext key chain
    simp only [hashHalf]
    have hc := chain.isLt
    rcases Nat.mod_two_eq_zero_or_one chain.val with h | h
    · rw [ite_eq_left h]
      have := congrArg Prod.snd (Rom.hashOutputEquivDigestPair.apply_symm_apply
        (starts key ⟨2 * (chainPair chain).val + 1, by simp [chainPair, numChains] at *; omega⟩,
         starts key ⟨2 * (chainPair chain).val, by simp [chainPair, numChains] at *; omega⟩))
      refine this.trans (congrArg _ (Fin.ext ?_))
      simp only [chainPair]
      omega
    · rw [ite_eq_right (by omega)]
      have := congrArg Prod.fst (Rom.hashOutputEquivDigestPair.apply_symm_apply
        (starts key ⟨2 * (chainPair chain).val + 1, by simp [chainPair, numChains] at *; omega⟩,
         starts key ⟨2 * (chainPair chain).val, by simp [chainPair, numChains] at *; omega⟩))
      refine this.trans (congrArg _ (Fin.ext ?_))
      simp only [chainPair]
      omega

theorem secret_eq (d : Derivations) : d.secret = pairEquiv LeafIndex d.bottom := rfl

theorem topSecret_eq (d : Derivations) : d.topSecret = pairEquiv TopIndex d.top := rfl

/-! ## Samplers -/

theorem evalDist_bind_of_map {α β γ : Type} {s : ProbComp α} {t : ProbComp β} (f : α → β)
    (h : (f <$> s) =ᵈ t) (F : β → ProbComp γ) :
    (t >>= F) =ᵈ (s >>= fun a => F (f a)) :=
  (h.symm.bind_left F).trans (.of_eq (bind_map_left _ _ _))

theorem evalDist_samplePublicParameter : (Concrete.samplePublicParameter) =ᵈ ($ᵗ Digest) := by
  unfold Concrete.samplePublicParameter
  exact EvalDistEq.of_forall_prEvent_eq fun p =>
    SampleableType.prEvent_uniformSample_inst_irrel (α := Digest) _ _ p

theorem evalDist_samplePublicParameter_bind {γ : Type} (F : PublicParameter → ProbComp γ) :
    (Concrete.samplePublicParameter >>= F) =ᵈ (($ᵗ HashOutput : ProbComp HashOutput) >>= fun x => F (truncateHash x)) :=
  evalDist_bind_of_map truncateHash
    (Rom.evalDist_truncate_uniformHashOutput.trans evalDist_samplePublicParameter.symm) F

theorem evalDist_sampleSecret_bind {γ : Type} (F : (LeafIndex → ChainIndex → Digest) → ProbComp γ) :
    (Concrete.sampleSecret >>= F) =ᵈ (sampleBottom >>= fun b => F (pairEquiv LeafIndex b)) := by
  refine evalDist_bind_of_map (pairEquiv LeafIndex) ?_ F
  let := bottomSampleable
  let : SampleableType (LeafIndex → ChainIndex → Digest) := SampleableType.ofFintype _
  rw [show sampleBottom = $ᵗ (BottomPos → HashOutput) from rfl]
  refine (SampleableType.map_uniformSample_evalDistEq_of_bijective
    (pairEquiv LeafIndex).bijective).trans ?_
  unfold Concrete.sampleSecret
  exact EvalDistEq.of_forall_prEvent_eq fun p =>
    SampleableType.prEvent_uniformSample_inst_irrel (α := LeafIndex → ChainIndex → Digest) _ _ p

theorem evalDist_sampleTopSecret_bind {γ : Type} (F : (TopIndex → ChainIndex → Digest) → ProbComp γ) :
    (Concrete.sampleTopSecret >>= F) =ᵈ (sampleTopOts >>= fun b => F (pairEquiv TopIndex b)) := by
  refine evalDist_bind_of_map (pairEquiv TopIndex) ?_ F
  let := topOtsSampleable
  let : SampleableType (TopIndex → ChainIndex → Digest) := SampleableType.ofFintype _
  rw [show sampleTopOts = $ᵗ (TopOtsPos → HashOutput) from rfl]
  refine (SampleableType.map_uniformSample_evalDistEq_of_bijective
    (pairEquiv TopIndex).bijective).trans ?_
  unfold Concrete.sampleTopSecret
  exact EvalDistEq.of_forall_prEvent_eq fun p =>
    SampleableType.prEvent_uniformSample_inst_irrel (α := TopIndex → ChainIndex → Digest) _ _ p

theorem evalDist_drop_randomizers {γ : Type} (X : ProbComp γ) :
    (sampleRandomizerOutputs >>= fun _ => X) =ᵈ (X) :=
  OracleComp.EvalDistEq.bind_const _ _

/-! ## Logged runs from the empty cache -/

theorem evalDist_logged {α β : Type} (c : OracleComp HashSpec α)
    (G : α → QueryCache HashSpec → QueryCache HashSpec → ProbComp β) :
    ((simulateQ randomOracle c.withQueryLog).run ∅ >>= fun p => G p.1.1 (hashCacheOfLog p.1.2) p.2) =ᵈ
      ((simulateQ randomOracle c).run ∅ >>= fun p => G p.1 p.2 p.2) := by
  rw [← withQueryLog_run_forget c ∅, bind_map_left]
  apply OracleComp.EvalDistEq.bind_congr_of_support
  intro p hp
  have hfinal := withQueryLog_finalCache c ∅ p hp
  rw [hashCacheOfLog, ← hfinal]

theorem run_lift_sample_bind {α β : Type} (c : ProbComp α) (next : α → OracleComp OracleWorld β)
    (cache : QueryCache HashSpec) :
    (simulateQ romImpl ((liftM c : OracleComp OracleWorld α) >>= next)).run cache =
      c >>= fun a => (simulateQ romImpl (next a)).run cache := by
  rw [simulateQ_bind, StateT.run_bind]
  have h : simulateQ romImpl (liftM c : OracleComp OracleWorld α) = simulateQ (unifFwdImpl HashSpec) c :=
    QueryImpl.simulateQ_add_liftM_left _ _ c
  rw [h, unifFwdImpl.simulateQ_run, bind_map_left]

theorem run_lift_hash_bind {α β : Type} (c : OracleComp HashSpec α) (next : α → OracleComp OracleWorld β)
    (cache : QueryCache HashSpec) :
    (simulateQ romImpl ((liftM c : OracleComp OracleWorld α) >>= next)).run cache =
      (simulateQ randomOracle c).run cache >>= fun r => (simulateQ romImpl (next r.1)).run r.2 := by
  rw [simulateQ_bind, StateT.run_bind]
  have h : simulateQ romImpl (liftM c : OracleComp OracleWorld α) = simulateQ randomOracle c :=
    QueryImpl.simulateQ_add_liftM_right _ _ c
  rw [h]

/-! ## The key distribution -/

/-- The game after key generation, on the model key a run of key generation gives. -/
noncomputable def keyCont {β : Type} (H : PublicKey → XmssSecurity.SecretKey → QueryCache HashSpec → ProbComp β)
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (topSecret : TopIndex → ChainIndex → Digest)
    (p : (Digest × (TopIndex → Option (Randomness × Encoding))) × QueryCache HashSpec) : ProbComp β :=
  H ⟨p.1.1, parameter⟩ (Concrete.precomputedSecretKey parameter secret topSecret p.1.2 p.2) p.2

/-- The prepared model key over a uniform table has the model's key distribution. -/
theorem evalDist_keygen {β : Type} (H : PublicKey → XmssSecurity.SecretKey → QueryCache HashSpec → ProbComp β) :
    (drawDerivations >>= fun d => (simulateQ randomOracle (honestRun d).withQueryLog).run ∅ >>= fun p =>
        H (modelPublicKey d p.1) (modelSecretKey d p.1) p.2) =ᵈ
      ((simulateQ romImpl Concrete.precomputedKeygen).run ∅ >>= fun k => H k.1.1 k.1.2 k.2) := by
  have hleft : ∀ d : Derivations, ((simulateQ randomOracle (honestRun d).withQueryLog).run ∅ >>= fun p =>
      H (modelPublicKey d p.1) (modelSecretKey d p.1) p.2) =ᵈ
        ((simulateQ randomOracle (honestRun d)).run ∅ >>= keyCont H d.parameter d.secret d.topSecret) :=
    fun d => evalDist_logged (honestRun d) fun (res : Digest × (TopIndex → Option (Randomness × Encoding)))
      cacheOfLog cache =>
      H ⟨res.1, d.parameter⟩ (Concrete.precomputedSecretKey d.parameter d.secret d.topSecret res.2 cacheOfLog) cache
  refine (EvalDistEq.bind_right _ hleft).trans ?_
  unfold Concrete.precomputedKeygen
  simp only [run_lift_sample_bind, run_lift_hash_bind, bind_assoc, simulateQ_pure, StateT.run_pure, pure_bind]
  have hright : ∀ (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
      (topSecret : TopIndex → ChainIndex → Digest) (topBase : TopIndex → Randomness),
      ((simulateQ randomOracle (Concrete.honestKeygen parameter secret topSecret
          fun key _ => (pure (topBase key) : OracleComp HashSpec Randomness)).withQueryLog).run ∅ >>= fun r =>
        H ⟨r.1.1.1, parameter⟩ (Concrete.precomputedSecretKey parameter secret topSecret r.1.1.2
          (hashCacheOfLog r.1.2)) r.2) =ᵈ
      ((simulateQ randomOracle (Concrete.honestKeygen parameter secret topSecret
          fun key _ => (pure (topBase key) : OracleComp HashSpec Randomness))).run ∅ >>=
        keyCont H parameter secret topSecret) :=
    fun parameter secret topSecret topBase => evalDist_logged _
      fun (res : Digest × (TopIndex → Option (Randomness × Encoding))) cacheOfLog cache =>
      H ⟨res.1, parameter⟩ (Concrete.precomputedSecretKey parameter secret topSecret res.2 cacheOfLog) cache
  refine EvalDistEq.trans ?_ (evalDist_samplePublicParameter_bind _).symm
  unfold drawDerivations
  simp only [bind_assoc, pure_bind]
  apply EvalDistEq.bind_right
  intro param
  refine EvalDistEq.trans ?_ (evalDist_sampleSecret_bind _).symm
  apply EvalDistEq.bind_right
  intro bottom
  refine EvalDistEq.trans ?_ (evalDist_sampleTopSecret_bind _).symm
  apply EvalDistEq.bind_right
  intro top
  simp only [honestRun, Derivations.parameter, Derivations.topBase, secret_eq, topSecret_eq]
  refine (evalDist_drop_randomizers _).trans ((evalDist_topBase _ _ _ _).trans ?_)
  apply EvalDistEq.bind_right
  intro topBase
  exact (hright _ _ _ topBase).symm

end XmssSecurity.Bridge
