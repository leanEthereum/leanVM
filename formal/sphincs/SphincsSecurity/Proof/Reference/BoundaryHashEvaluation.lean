import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Reference.BoundaryHashCost

/-! ## AuthenticationQueryCost -/

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

def authenticationHashCost (lay : Layer) : Nat :=
  ∑ level : Fin maxLayerHeight, if level.val < layerHeight lay then 296 * 2 ^ level.val - 1 else 0

def layerMessageHashCost (lay : Layer) : Nat :=
  if hbelow : lay.val + 1 < numLayers then
    296 * 2 ^ layerHeight ⟨lay.val + 1, hbelow⟩ - 1
  else 28659

end SphincsSecurity.Concrete

/-! ## FtsSigningReserve -/

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

theorem tweakableHashInput_tag_eq (parameter : PublicParameter) (first second : HashDomain)
    (firstPayload secondPayload : HashInput)
    (heq : tweakableHashInput parameter first firstPayload = tweakableHashInput parameter second secondPayload) :
    (hashDomainFields first).tag = (hashDomainFields second).tag := by
  simp only [tweakableHashInput] at heq
  obtain ⟨hprefix, _⟩ := List.append_inj heq (by simp [tweakBytes_length, bytesLE_length])
  obtain ⟨htweak, _⟩ := List.append_inj' hprefix (by simp [bytesLE_length])
  exact congrArg TweakFields.tag (tweakBytes_eq_iff.mp htweak)

end SphincsSecurity.Concrete.FtsProbeSimulation

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

theorem SigningBoundaryTrace.hashCalls_pow_none (cost : Nat) :
    SigningBoundaryTrace.hashCalls ((FreeMonoid.of none : SigningBoundaryTrace) ^ cost) = cost := by
  induction cost with
  | zero => rfl
  | succ cost ih =>
      rw [pow_succ, SigningBoundaryTrace.hashCalls_mul, ih]
      rfl

theorem SigningBoundaryTrace.messageCalls_pow_none (cost : Nat) :
    SigningBoundaryTrace.messageCalls ((FreeMonoid.of none : SigningBoundaryTrace) ^ cost) = [] := by
  induction cost with
  | zero => rfl
  | succ cost ih =>
      rw [pow_succ, SigningBoundaryTrace.messageCalls_mul, ih]
      rfl

noncomputable def boundaryEval {α : Type} (parameter : PublicParameter)
    (f : QueryImpl HashSpec Id) (computation : OracleComp HashSpec α) : α × SigningBoundaryTrace :=
  (simulateQ (f.withTrace (fun input output => signingBoundaryTrace parameter (.inr input) output))
    computation).run

@[simp] theorem boundaryEval_pure {α : Type} (parameter : PublicParameter)
    (f : QueryImpl HashSpec Id) (value : α) : boundaryEval parameter f (pure value) = (value, 1) := rfl

theorem boundaryEval_fst {α : Type} (parameter : PublicParameter)
    (f : QueryImpl HashSpec Id) (computation : OracleComp HashSpec α) :
    (boundaryEval parameter f computation).1 = evalWithAnswerFn f computation := by
  exact QueryImpl.fst_map_run_withTrace f
    (fun input output => signingBoundaryTrace parameter (.inr input) output) computation

theorem boundaryEval_bind {α β : Type} (parameter : PublicParameter)
    (f : QueryImpl HashSpec Id) (first : OracleComp HashSpec α) (next : α → OracleComp HashSpec β) :
    boundaryEval parameter f (first >>= next) =
      ((boundaryEval parameter f (next (evalWithAnswerFn f first))).1,
        (boundaryEval parameter f first).2 *
          (boundaryEval parameter f (next (evalWithAnswerFn f first))).2) := by
  simp only [boundaryEval, simulateQ_bind, WriterT.run_bind]
  rw [← boundaryEval_fst parameter f first]
  rfl

theorem boundaryEval_tweakableHash (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (domain : HashDomain) (payload : HashInput) (hmessage : (hashDomainFields domain).tag ≠ 9#8) :
    boundaryEval parameter f (tweakableHash parameter domain payload) =
      (truncateHash (f (tweakableHashInput parameter domain payload)), FreeMonoid.of none) := by
  have hn : ¬ FtsProbeSimulation.MessageHashInput parameter (tweakableHashInput parameter domain payload) := by
    rintro ⟨otherPayload, heq⟩
    exact hmessage (FtsProbeSimulation.tweakableHashInput_tag_eq parameter domain .message
      payload otherPayload heq.symm)
  simp [boundaryEval, tweakableHash, oracleHash, QueryImpl.withTrace_apply,
    signingBoundaryTrace_nonmessage _ _ _ hn]
  rfl

theorem boundaryEval_eq_of_snd {α : Type} (parameter : PublicParameter)
    (f : QueryImpl HashSpec Id) (computation : OracleComp HashSpec α) (trace : SigningBoundaryTrace)
    (htrace : (boundaryEval parameter f computation).2 = trace) :
    boundaryEval parameter f computation = (evalWithAnswerFn f computation, trace) := by
  exact Prod.ext (boundaryEval_fst _ _ _) htrace

theorem boundaryEval_sequenceFin {α : Type} {n : Nat} (parameter : PublicParameter)
    (f : QueryImpl HashSpec Id) (computation : Fin n → OracleComp HashSpec α) (cost : Fin n → Nat)
    (hcost : ∀ i, (boundaryEval parameter f (computation i)).2 = (FreeMonoid.of none) ^ cost i) :
    boundaryEval parameter f (sequenceFin computation) =
      (fun i => evalWithAnswerFn f (computation i), (FreeMonoid.of none) ^ (∑ i, cost i)) := by
  rw [← evalWithAnswerFn_sequenceFin]
  apply boundaryEval_eq_of_snd
  induction n with
  | zero => simp [sequenceFin]
  | succ n ih =>
      rw [sequenceFin, boundaryEval_bind]
      have ht := ih (fun i => computation i.succ) (fun i => cost i.succ) (fun i => hcost i.succ)
      simp only [boundaryEval_bind, boundaryEval_pure, mul_one, hcost, ht,
        Fin.sum_univ_succ, pow_add]

theorem boundaryEval_chainWalk (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chainIdx : ChainIndex)
    (start steps : Nat) (value : Digest) (hsteps : start + steps ≤ chainLength - 1) :
    boundaryEval parameter f (chainWalk parameter lay tree leaf chainIdx start steps value) =
      (evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx start steps value),
        (FreeMonoid.of none) ^ steps) := by
  apply boundaryEval_eq_of_snd
  induction steps with
  | zero => simp [chainWalk]
  | succ steps ih =>
      have hstep : start + steps < chainLength - 1 := by omega
      rw [chainWalk, boundaryEval_bind, dif_pos hstep,
        boundaryEval_tweakableHash _ _ _ _ (by simp [hashDomainFields]), ih (by omega), pow_succ]

theorem boundaryEval_oneTimePublicKey (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (secret : ChainIndex → Digest) :
    boundaryEval parameter f (oneTimePublicKey parameter lay tree leaf secret) =
      (evalWithAnswerFn f (oneTimePublicKey parameter lay tree leaf secret), (FreeMonoid.of none) ^ 294) := by
  rw [oneTimePublicKey]
  have h := boundaryEval_sequenceFin parameter f
    (fun chainIdx => chainWalk parameter lay tree leaf chainIdx 0 (chainLength - 1) (secret chainIdx))
    (fun _ => chainLength - 1)
    (fun chainIdx => congrArg Prod.snd (boundaryEval_chainWalk _ _ _ _ _ _ _ _ _ (by omega)))
  simpa only [evalWithAnswerFn_sequenceFin, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, show numChains * (chainLength - 1) = 294 from rfl] using h

theorem boundaryEval_treeNode (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (secret : LeafIndex → ChainIndex → Digest) (level nodeIdx : Nat) :
    boundaryEval parameter f (treeNode parameter lay tree secret level nodeIdx) =
      (evalWithAnswerFn f (treeNode parameter lay tree secret level nodeIdx),
        (FreeMonoid.of none) ^ (296 * 2 ^ level - 1)) := by
  apply boundaryEval_eq_of_snd
  induction level generalizing nodeIdx with
  | zero =>
      rw [treeNode_zero_eq, boundaryEval_bind, boundaryEval_oneTimePublicKey]
      simp only [leafHash, boundaryEval_tweakableHash parameter f (.leaf lay tree (leafOfNat nodeIdx)) _
        (by simp [hashDomainFields])]
      rw [← pow_succ]
      congr 1
  | succ level ih =>
      rw [treeNode_succ_eq, boundaryEval_bind]
      simp only [boundaryEval_bind, ih, boundaryEval_tweakableHash parameter f (.node lay tree (level + 1) nodeIdx) _
        (by simp [hashDomainFields])]
      rw [← pow_succ, ← pow_add]
      congr 1
      have hp : 0 < 2 ^ level := by positivity
      rw [pow_succ]
      omega

theorem boundaryEval_treePath (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (secret : LeafIndex → ChainIndex → Digest) (leaf : LeafIndex) :
    boundaryEval parameter f (treePath parameter lay tree secret leaf) =
      (evalWithAnswerFn f (treePath parameter lay tree secret leaf),
        (FreeMonoid.of none) ^ authenticationHashCost lay) := by
  unfold treePath authenticationHashCost
  rw [evalWithAnswerFn_sequenceFin]
  apply boundaryEval_sequenceFin
  intro level
  split_ifs
  · exact congrArg Prod.snd (boundaryEval_treeNode _ _ _ _ _ _ _)
  · simp

theorem boundaryEval_ftsNode (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (index : Index) (tree : FtsTree) (secret : FtsLeaf → Digest) (level nodeIdx : Nat) :
    boundaryEval parameter f (ftsNode parameter index tree secret level nodeIdx) =
      (evalWithAnswerFn f (ftsNode parameter index tree secret level nodeIdx),
        (FreeMonoid.of none) ^ (2 ^ (level + 1) - 1)) := by
  apply boundaryEval_eq_of_snd
  induction level generalizing nodeIdx with
  | zero =>
      rw [ftsNode_zero_eq, ftsLeafHash, boundaryEval_tweakableHash _ _ _ _ (by simp [hashDomainFields])]
      simp
  | succ level ih =>
      rw [ftsNode_succ_eq, boundaryEval_bind]
      simp only [boundaryEval_bind, ih,
        boundaryEval_tweakableHash parameter f (.ftsNode index tree (level + 1) nodeIdx) _
          (by simp [hashDomainFields])]
      rw [← pow_succ, ← pow_add]
      congr 1
      have hp : 0 < 2 ^ (level + 1) := by positivity
      rw [pow_succ]
      omega

theorem boundaryEval_ftsKey (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (index : Index) (secret : FtsTree → FtsLeaf → Digest) :
    boundaryEval parameter f (ftsKey parameter index secret) =
      (evalWithAnswerFn f (ftsKey parameter index secret), (FreeMonoid.of none) ^ 28659) := by
  have hroots := boundaryEval_sequenceFin parameter f
    (fun tree => ftsNode parameter index tree (secret tree) ftsTreeHeight 0)
    (fun _ => 2 ^ (ftsTreeHeight + 1) - 1)
    (fun tree => by rw [boundaryEval_ftsNode])
  have hcost : (∑ _tree : FtsTree, (2 ^ (ftsTreeHeight + 1) - 1)) = 28658 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    rfl
  apply boundaryEval_eq_of_snd
  rw [ftsKey, boundaryEval_bind, hroots, hcost,
    boundaryEval_tweakableHash _ _ _ _ (by simp [hashDomainFields]), ← pow_succ]

theorem boundaryEval_ftsOpen (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (index : Index) (leaves : IndexGroup → FtsLeaf) (secret : FtsTree → FtsLeaf → Digest) :
    boundaryEval parameter f (ftsOpen parameter index leaves secret) =
      (evalWithAnswerFn f (ftsOpen parameter index leaves secret), (FreeMonoid.of none) ^ 28504) := by
  apply boundaryEval_eq_of_snd
  unfold ftsOpen
  have hcost : (∑ _tree : FtsTree, ∑ level : Fin ftsTreeHeight, (2 ^ (level.val + 1) - 1)) = 28504 := by decide
  rw [← hcost]
  apply congrArg Prod.snd (boundaryEval_sequenceFin parameter f _ _ ?_)
  intro tree
  apply congrArg Prod.snd (boundaryEval_sequenceFin parameter f _ _ ?_)
  intro level
  exact congrArg Prod.snd (boundaryEval_ftsNode _ _ _ _ _ _ _)

theorem boundaryEval_layerMessage (key : SecretKey) (f : QueryImpl HashSpec Id) (index : Index) (lay : Layer) :
    boundaryEval key.parameter f (layerMessage key index lay) =
      (evalWithAnswerFn f (layerMessage key index lay), (FreeMonoid.of none) ^ layerMessageHashCost lay) := by
  rw [layerMessage, layerMessageHashCost]
  split_ifs
  · rw [treeRoot]
    exact boundaryEval_treeNode _ _ _ _ _ _ _
  · exact boundaryEval_ftsKey _ _ _ _

theorem boundaryEval_hash_query (parameter : PublicParameter) (f : QueryImpl HashSpec Id) (input : HashInput) :
    boundaryEval parameter f (liftM (HashSpec.query input)) =
      (f input, signingBoundaryTrace parameter (.inr input) (f input)) := rfl

end SphincsSecurity.Concrete
