module

public import XmssSecurity.Proof.ConsistentQueryBound

@[expose] public section

/-!
# The adversary's own budget

The pieces for bounding the forgery probability by the adversary's own hash calls rather than by
the whole game's: a static bound on a computation's hash queries (`IsQueryBoundP`) bounds its calls
in the random-oracle simulation (`hashQueryBound_of_isQueryBoundP`), and the verifier makes at most
`verifyHashCalls` of them (`verify_hashQueryBound`).
-/

open OracleComp OracleSpec

namespace XmssSecurity

/-- A hash query of the game's world. -/
def IsWorldHashQuery : OracleWorld.Domain → Prop := fun input => input matches .inr _

instance : DecidablePred IsWorldHashQuery := fun input => by
  unfold IsWorldHashQuery; infer_instance

/-- A static bound on a computation's hash queries bounds its calls from every cache. -/
theorem hashQueryBound_of_isQueryBoundP {α : Type} (computation : OracleComp OracleWorld α)
    (n : Nat) (hbound : IsQueryBoundP computation IsWorldHashQuery n) (cache : QueryCache HashSpec) :
    HashQueryBound computation cache n := by
  rw [hashQueryBound_iff_run]
  induction computation using OracleComp.inductionOn generalizing cache n with
  | pure value =>
      intro result hresult
      simp [countHashQueries_pure] at hresult
      rw [hresult]; exact Nat.zero_le _
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at hbound
      obtain ⟨hcan, hnext⟩ := hbound
      intro result hresult
      rw [countHashQueries_query_bind, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hresult
      obtain ⟨step, hstep, hrest⟩ := hresult
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
      obtain ⟨inner, hinner, hlast⟩ := hrest
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hlast
      subst hlast
      have hcount := ih step.1 (if IsWorldHashQuery input then n - 1 else n) (hnext step.1) step.2
        inner hinner
      cases input with
      | inl _ => simpa [IsWorldHashQuery] using hcount
      | inr _ =>
          simp only [IsWorldHashQuery] at hcount hcan ⊢
          simp at hcan hcount ⊢
          omega

/-- A model adversary's own hash query: uniform samples and signing requests are free. -/
def IsAdvHashAction : (OracleWorld + SigningSpec).Domain → Prop := fun input => input matches .inl (.inr _)

instance : DecidablePred IsAdvHashAction := fun input => by
  unfold IsAdvHashAction; infer_instance

/-- A model adversary's own hash queries are at most `q` on every path. -/
def OwnHashBound (adversary : Adversary) (q : Nat) : Prop :=
  ∀ publicKey, IsQueryBoundP (adversary.main publicKey) IsAdvHashAction q

/-! ## The verifier's hash calls -/

section VerifyBound

open Concrete

local notation "HC" => OracleComp HashSpec

theorem total_pure {α : Type} (value : α) (n : Nat) : IsTotalQueryBound (pure value : HC α) n :=
  isQueryBound_pure _ _ _ _

theorem total_oracleHash (input : HashInput) :
    IsTotalQueryBound (Concrete.oracleHash input : HC HashOutput) 1 := by
  rw [Concrete.oracleHash, HasQuery.instOfMonadLift_query, ← bind_pure (liftM _),
    isTotalQueryBound_query_bind_iff]
  exact ⟨Nat.one_pos, fun _ => total_pure _ _⟩

theorem total_tweakableHash (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    IsTotalQueryBound (Concrete.tweakableHash parameter domain payload : HC Digest) 1 := by
  unfold Concrete.tweakableHash
  exact isTotalQueryBound_bind (total_oracleHash _) fun _ => total_pure _ 0

theorem total_chainWalk (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex) :
    ∀ (position steps : Nat) (value : Digest),
      IsTotalQueryBound (Concrete.chainWalk parameter leafIndex chain position steps value : HC Digest) steps
  | _, 0, _ => total_pure _ _
  | position, steps + 1, value => by
      rw [Concrete.chainWalk]
      refine isTotalQueryBound_bind (total_chainWalk parameter leafIndex chain position steps value)
        fun previous => ?_
      split
      · exact total_tweakableHash _ _ _
      · exact total_pure _ _

theorem total_topChainWalk (parameter : PublicParameter) (key : TopIndex) (chain : ChainIndex) :
    ∀ (position steps : Nat) (value : Digest),
      IsTotalQueryBound (Concrete.topChainWalk parameter key chain position steps value : HC Digest) steps
  | _, 0, _ => total_pure _ _
  | position, steps + 1, value => by
      rw [Concrete.topChainWalk]
      refine isTotalQueryBound_bind (total_topChainWalk parameter key chain position steps value)
        fun previous => ?_
      split
      · exact total_tweakableHash _ _ _
      · exact total_pure _ _

theorem total_sequenceFin {α : Type} (b : Nat) :
    ∀ {n : Nat} (computation : Fin n → HC α), (∀ index, IsTotalQueryBound (computation index) b) →
      IsTotalQueryBound (Concrete.sequenceFin computation) (n * b)
  | 0, _, _ => total_pure _ _
  | n + 1, computation, h => by
      rw [Concrete.sequenceFin]
      have hrest := total_sequenceFin b (fun index : Fin n => computation index.succ) fun index => h _
      have hmul : (n + 1) * b = b + (n * b + 0) := by ring
      rw [hmul]
      exact isTotalQueryBound_bind (h 0) fun _ => isTotalQueryBound_bind hrest fun _ => total_pure _ 0

theorem total_authenticationRoot (parameter : PublicParameter) (leafIndex : LeafIndex)
    (signature : Signature) :
    ∀ (levels : Nat) (leaf : Digest),
      IsTotalQueryBound (Concrete.authenticationRoot parameter leafIndex signature levels leaf : HC Digest)
        levels
  | 0, _ => total_pure _ _
  | levels + 1, leaf => by
      rw [Concrete.authenticationRoot]
      refine isTotalQueryBound_bind (total_authenticationRoot parameter leafIndex signature levels leaf)
        fun current => ?_
      unfold Concrete.authenticationNodeHash
      split
      · split
        · exact total_tweakableHash _ _ _
        · exact total_tweakableHash _ _ _
      · exact (total_pure _ 0).mono (Nat.zero_le _)

theorem total_topAuthenticationRoot (parameter : PublicParameter) (key : TopIndex)
    (path : Fin treeHeight → Digest) :
    ∀ (levels : Nat) (leaf : Digest),
      IsTotalQueryBound (Concrete.topAuthenticationRoot parameter key path levels leaf : HC Digest) levels
  | 0, _ => total_pure _ _
  | levels + 1, leaf => by
      rw [Concrete.topAuthenticationRoot]
      refine isTotalQueryBound_bind (total_topAuthenticationRoot parameter key path levels leaf)
        fun current => ?_
      split
      · split
        · exact total_tweakableHash _ _ _
        · exact total_tweakableHash _ _ _
      · exact (total_pure _ 0).mono (Nat.zero_le _)

theorem total_topAuthenticationRoot_tree (parameter : PublicParameter) (key : TopIndex)
    (path : Fin treeHeight → Digest) (leaf : Digest) :
    IsTotalQueryBound (Concrete.topAuthenticationRoot parameter key path treeHeight leaf : HC Digest)
      treeHeight := by
  have h := total_topAuthenticationRoot parameter key path
  exact h _ _

theorem total_authenticationRoot_tree (parameter : PublicParameter) (leafIndex : LeafIndex)
    (signature : Signature) (leaf : Digest) :
    IsTotalQueryBound (Concrete.authenticationRoot parameter leafIndex signature treeHeight leaf : HC Digest)
      treeHeight := by
  have h := total_authenticationRoot parameter leafIndex signature
  exact h _ _

/-- One layer's hash calls: the digest, the chains' remaining steps, the leaf and the path. -/
def layerVerifyHashCalls : Nat := 1 + (numChains * (chainLength - 1) + (1 + treeHeight))

/-- The verifier's hash calls: two layers. -/
def verifyHashCalls : Nat := layerVerifyHashCalls + layerVerifyHashCalls

theorem total_bind_le {α β : Type} {first : HC α} {next : α → HC β} {a b n : Nat}
    (h1 : IsTotalQueryBound first a) (h2 : ∀ value, IsTotalQueryBound (next value) b) (h : a + b ≤ n) :
    IsTotalQueryBound (first >>= next) n :=
  (isTotalQueryBound_bind h1 h2).mono h

theorem total_bind_pure {α β : Type} {first : HC α} {a : Nat} (f : α → β) (h : IsTotalQueryBound first a) :
    IsTotalQueryBound (first >>= fun value => pure (f value)) a :=
  (isTotalQueryBound_bind h fun _ => total_pure _ 0).mono (Nat.le_of_eq (Nat.add_zero _))

/- The tree's height and the chain count, unfolded to literals, unroll the verifier under `whnf`. -/
attribute [local irreducible] treeHeight numChains in
theorem total_verifyTop (publicKey : PublicKey) (key : TopIndex) (root : Digest) (part : LayerSignature) :
    IsTotalQueryBound (Concrete.verifyTop publicKey key root part : HC Bool) layerVerifyHashCalls := by
  unfold Concrete.verifyTop
  refine total_bind_le (by unfold Concrete.topEncodingHash; exact total_tweakableHash _ _ _)
    (b := numChains * (chainLength - 1) + (1 + treeHeight)) (fun digest => ?_) (by simp [layerVerifyHashCalls])
  split
  · refine total_bind_le (total_sequenceFin (chainLength - 1) _ fun chain =>
      (total_topChainWalk _ _ _ _ _ _).mono (Nat.sub_le _ _)) (b := 1 + treeHeight) (fun _ => ?_) (Nat.le_refl _)
    refine total_bind_le (by unfold Concrete.topLeafHash; exact total_tweakableHash _ _ _)
      (b := treeHeight) (fun _ => ?_) (Nat.le_refl _)
    exact total_bind_pure _ (total_topAuthenticationRoot_tree _ _ _ _)
  · exact total_pure _ _

attribute [local irreducible] treeHeight numChains in
theorem total_verify (publicKey : PublicKey) (leafIndex : LeafIndex) (message : Message)
    (signature : Signature) :
    IsTotalQueryBound (Concrete.verify publicKey leafIndex message signature : HC Bool) verifyHashCalls := by
  unfold Concrete.verify
  refine total_bind_le (by unfold Concrete.encodingHash; exact total_tweakableHash _ _ _)
    (b := numChains * (chainLength - 1) + (1 + (treeHeight + layerVerifyHashCalls))) (fun digest => ?_)
    (by simp [verifyHashCalls, layerVerifyHashCalls]; omega)
  split
  · refine total_bind_le (total_sequenceFin (chainLength - 1) _ fun chain =>
      (total_chainWalk _ _ _ _ _ _).mono (Nat.sub_le _ _)) (b := 1 + (treeHeight + layerVerifyHashCalls))
        (fun _ => ?_) (Nat.le_refl _)
    refine total_bind_le (by unfold Concrete.leafHash; exact total_tweakableHash _ _ _)
      (b := treeHeight + layerVerifyHashCalls) (fun _ => ?_) (Nat.le_refl _)
    unfold Concrete.verifyAfterLeaf
    exact total_bind_le (total_authenticationRoot_tree _ _ _ _) (fun _ => total_verifyTop _ _ _ _) (Nat.le_refl _)
  · exact total_pure _ _

/-- A hash-only computation's queries, lifted into the game's world, are all hash queries. -/
theorem isQueryBoundP_liftM_of_total {α : Type} (computation : HC α) (n : Nat)
    (h : IsTotalQueryBound computation n) :
    IsQueryBoundP (liftM computation : OracleComp OracleWorld α) IsWorldHashQuery n := by
  have hall : IsQueryBoundP computation (fun _ => True) n :=
    (isQueryBound_congr (fun _ _ => by simp) (fun _ _ => by simp)).mp h
  exact IsQueryBoundP.liftComp_subSpec (q := IsWorldHashQuery) (fun _ => iff_of_true trivial (by rfl)) hall

theorem verify_hashQueryBound (publicKey : PublicKey) (leafIndex : LeafIndex) (message : Message)
    (signature : Signature) (cache : QueryCache HashSpec) :
    HashQueryBound (Concrete.scheme.verify publicKey leafIndex message signature) cache verifyHashCalls :=
  hashQueryBound_of_isQueryBoundP _ _
    (isQueryBoundP_liftM_of_total _ _ (total_verify publicKey leafIndex message signature)) cache

end VerifyBound

end XmssSecurity
