module

public import Qrom.Sphincs.Domain

@[expose] public section

/-!
# The number of hash calls of the verifier

The leanSPHINCS verifier makes at most `verifyQueries` hash calls on every run
(`Qrom.Sphincs.isTotalQueryBound_verify`): the digest calls, `a + 1` per FORS tree, the FORS public
key, and per layer the encoding, at most three steps per chain, the leaf and the path.
-/

open OracleComp OracleSpec FORS Concrete

noncomputable section

set_option linter.unusedSectionVars false

namespace Qrom.Sphincs

variable [Params]

abbrev HComp := OracleComp HashSpec

theorem bound_query (t : HashInput) : IsTotalQueryBound (liftM (HashSpec.query t) : HComp _) 1 := by
  rw [show (liftM (HashSpec.query t) : HComp _) = liftM (HashSpec.query t) >>= pure from
    (bind_pure _).symm, isTotalQueryBound_query_bind_iff]
  exact ⟨Nat.one_pos, fun _ ↦ trivial⟩

theorem bound_pure {α : Type} (a : α) (n : ℕ) : IsTotalQueryBound (pure a : HComp α) n :=
  trivial

theorem bound_tweakableHash (parameter : PublicParameter) (domain : HashDomain)
    (payload : HashInput) : IsTotalQueryBound (tweakableHash parameter domain payload : HComp _) 1 :=
  (isTotalQueryBound_bind (bound_query _) fun _ ↦ bound_pure _ 0).mono (by omega)

theorem bound_sequenceFin {α : Type} {n b : ℕ} (c : Fin n → HComp α)
    (h : ∀ i, IsTotalQueryBound (c i) b) : IsTotalQueryBound (sequenceFin c) (n * b) := by
  induction n with
  | zero => exact bound_pure _ _
  | succ n ih =>
    rw [sequenceFin]
    refine (isTotalQueryBound_bind (h 0) fun _ ↦ isTotalQueryBound_bind
      (ih (fun i ↦ c i.succ) fun i ↦ h _) fun _ ↦ bound_pure _ 0).mono ?_
    rw [Nat.succ_mul]
    omega

theorem bound_chainWalk (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chainIdx : ChainIndex) (start : ℕ) :
    ∀ steps value, IsTotalQueryBound
      (chainWalk parameter lay tree leaf chainIdx start steps value : HComp _) steps
  | 0, _ => bound_pure _ _
  | steps + 1, value => by
    rw [chainWalk]
    refine isTotalQueryBound_bind (bound_chainWalk parameter lay tree leaf chainIdx start steps value)
      fun _ ↦ ?_
    split
    · exact bound_tweakableHash _ _ _
    · exact bound_pure _ _

theorem bound_recoverChain (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chainIdx : ChainIndex) (digit : Digit) (value : Digest) :
    IsTotalQueryBound (recoverChain parameter lay tree leaf chainIdx digit value : HComp _)
      (chainLength - 1) :=
  (bound_chainWalk _ _ _ _ _ _ _ _).mono (Nat.sub_le _ _)

theorem bound_encode (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (message : HashInput) (counter : Counter) :
    IsTotalQueryBound (encode parameter lay tree leaf message counter : HComp _) 1 :=
  (isTotalQueryBound_bind (bound_tweakableHash _ _ _) fun _ ↦ bound_pure _ 0).mono (by omega)

/-- The calls of a one-time leaf: the encoding, the chains and the leaf. -/
def otsQueries : ℕ := 1 + numChains * (chainLength - 1) + 1

theorem bound_otsLeaf (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (message : HashInput) (counter : Counter) (values : ChainIndex → Digest) :
    IsTotalQueryBound (otsLeaf parameter lay tree leaf message counter values : HComp _)
      otsQueries := by
  rw [otsLeaf]
  refine (isTotalQueryBound_bind (n₂ := numChains * (chainLength - 1) + 1)
    (bound_encode _ _ _ _ _ _) fun e ↦ ?_).mono (by unfold otsQueries; omega)
  rcases e with _ | e
  · exact bound_pure _ _
  · refine (isTotalQueryBound_bind (bound_sequenceFin _ fun i ↦ bound_recoverChain _ _ _ _ i _ _)
      fun _ ↦ isTotalQueryBound_bind (bound_tweakableHash _ _ _) fun _ ↦ bound_pure _ 0).mono ?_
    simp [numChains]

theorem bound_treeFold (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (path : ℕ → Digest) :
    ∀ levels value, IsTotalQueryBound
      (treeFold parameter lay tree leaf path levels value : HComp _) levels
  | 0, _ => bound_pure _ _
  | levels + 1, value => by
    rw [treeFold]
    refine isTotalQueryBound_bind (bound_treeFold parameter lay tree leaf path levels value)
      fun _ ↦ ?_
    split
    · exact bound_tweakableHash _ _ _
    · exact bound_tweakableHash _ _ _

theorem bound_forsFold (parameter : PublicParameter) (index : Index) (κ : FTree) (leaf : FLeaf)
    (path : Fin forsHeight → Digest) :
    ∀ levels value, IsTotalQueryBound
      (forsFold parameter index κ leaf path levels value : HComp _) levels
  | 0, _ => bound_pure _ _
  | levels + 1, value => by
    rw [forsFold]
    refine isTotalQueryBound_bind (bound_forsFold parameter index κ leaf path levels value)
      fun _ ↦ ?_
    split
    · split
      · exact bound_tweakableHash _ _ _
      · exact bound_tweakableHash _ _ _
    · exact bound_pure _ _

theorem bound_treeRecover (parameter : PublicParameter) (index : Index) (κ : FTree) (leaf : FLeaf)
    (opening : TreeOpening) :
    IsTotalQueryBound (treeRecover parameter index κ leaf opening : HComp _) (1 + forsHeight) := by
  unfold treeRecover forsLeafHash
  exact isTotalQueryBound_bind (bound_tweakableHash _ _ _) fun _ ↦ bound_forsFold _ _ _ _ _ _ _

theorem bound_forsRecover (parameter : PublicParameter) (index : Index) (leaves : FTree → FLeaf)
    (opening : FTree → TreeOpening) :
    IsTotalQueryBound (forsRecover parameter index leaves opening : HComp _)
      (forsTrees * (1 + forsHeight)) := by
  unfold forsRecover
  exact bound_sequenceFin _ fun _ ↦ bound_treeRecover _ _ _ _ _

theorem bound_messageDigest (parameter : PublicParameter) (root : Digest) (message : Message)
    (randomness : Randomness) :
    IsTotalQueryBound (messageDigest parameter root message randomness : HComp _) digestCalls := by
  unfold messageDigest messageDigestCall
  have h := isTotalQueryBound_bind (ob := fun outputs ↦ (pure (truncateMessageDigest outputs) : HComp _))
    (bound_sequenceFin (n := digestCalls) (b := 1)
      (fun call : DigestCall ↦ (oracleHash (messageDigestInput parameter root message randomness call) :
        HComp HashOutput)) fun _ ↦ bound_query _) fun _ ↦ bound_pure _ 0
  rw [Nat.mul_one, Nat.add_zero] at h
  exact h

/-- The calls of one layer: its one-time leaf and its path. -/
def layerQueries : ℕ := otsQueries + maxLayerHeight

theorem bound_verifyLayers (parameter : PublicParameter) (index : Index) (signature : Signature) :
    ∀ remaining message, IsTotalQueryBound
      (verifyLayers parameter index signature remaining message : HComp _)
      (remaining * layerQueries)
  | 0, _ => bound_pure _ _
  | remaining + 1, message => by
    rw [verifyLayers]
    split
    · refine (isTotalQueryBound_bind (n₂ := maxLayerHeight + remaining * layerQueries)
        (bound_otsLeaf _ _ _ _ _ _ _) fun v ↦ ?_).mono (by unfold layerQueries; rw [Nat.succ_mul]; omega)
      rcases v with _ | v
      · exact bound_pure _ _
      · refine isTotalQueryBound_bind ((bound_treeFold _ _ _ _ _ _ _).mono
          (layerHeight_le _)) fun _ ↦ ?_
        split
        · exact bound_pure _ _
        · exact bound_verifyLayers parameter index signature remaining _
    · exact bound_pure _ _

/-- The calls of the verifier. -/
def verifyQueries : ℕ :=
  digestCalls + forsTrees * (1 + forsHeight) + 1 + numLayers * layerQueries

theorem bound_verify (pk : PublicKey) (message : Message) (signature : Signature) :
    IsTotalQueryBound (verify pk message signature : HComp Bool) verifyQueries := by
  rw [verify]
  refine (isTotalQueryBound_bind (n₂ := forsTrees * (1 + forsHeight) + (1 + numLayers * layerQueries))
    (bound_messageDigest _ _ _ _) fun _ ↦ ?_).mono (by unfold verifyQueries; omega)
  refine isTotalQueryBound_bind (bound_forsRecover _ _ _ _) fun _ ↦ ?_
  refine isTotalQueryBound_bind (bound_tweakableHash _ _ _) fun _ ↦ ?_
  refine (isTotalQueryBound_bind (n₂ := 0) (bound_verifyLayers _ _ _ _ _) fun r ↦ ?_).mono
    (by omega)
  rcases r with _ | r <;> exact bound_pure _ _

theorem bound_liftH {α : Type} {oa : HComp α} {n : ℕ} (h : IsTotalQueryBound oa n) :
    IsTotalQueryBound (liftH oa) n :=
  IsTotalQueryBound.simulateQ_of_step h fun t ↦ by
    unfold liftImpl
    split
    · rw [show (liftM ((Input →ₒ HashOutput).query _) : OracleComp (Input →ₒ HashOutput) _) =
        liftM ((Input →ₒ HashOutput).query _) >>= pure from (bind_pure _).symm,
        isTotalQueryBound_query_bind_iff]
      exact ⟨Nat.one_pos, fun _ ↦ trivial⟩
    · trivial

theorem bound_traced {α : Type} {oa : HComp α} {n : ℕ} (h : IsTotalQueryBound oa n) :
    IsTotalQueryBound (traced oa) n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => trivial
  | query_bind t k ih =>
    rw [isTotalQueryBound_query_bind_iff] at h
    rw [traced, construct_query_bind]
    refine (isTotalQueryBound_bind (bound_query t) fun u ↦ isTotalQueryBound_bind
      (ih u (h.2 u)) fun _ ↦ bound_pure _ 0).mono (by omega)

theorem length_queriedInputs_le (f : QueryImpl HashSpec Id) {α : Type} {oa : HComp α} {n : ℕ}
    (h : IsTotalQueryBound oa n) : (Security.queriedInputs f oa).length ≤ n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => simp
  | query_bind t k ih =>
    rw [isTotalQueryBound_query_bind_iff] at h
    rw [Security.queriedInputs_query_bind, List.length_cons]
    have := ih (f t) (h.2 (f t))
    omega

end Qrom.Sphincs
