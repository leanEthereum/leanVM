module

public import FORS.Scheme
public import VCVio.OracleComp.QueryTracking.QueryBound

@[expose] public section

/-! The verifier's hash calls: `Concrete.verify` makes at most `verifyCalls` calls of `H` on every
path, rejecting paths included. -/

open OracleComp OracleSpec

namespace FORS.Concrete

variable [Params]

/-- The verifier's call budget: the digest calls, `k (a + 1)` FORS calls and `T_k`, and per layer the
encoding, the chains, the leaf and the path. -/
def verifyCalls : Nat :=
  digestCalls + forsTrees * (forsHeight + 1) + 1 + numLayers * (numChains * (chainLength - 1) + 2 + maxLayerHeight)

/-- `IsQueryBoundP` counting every call. -/
abbrev CallsAtMost {α : Type} (oa : OracleComp HashSpec α) (n : Nat) : Prop :=
  oa.IsQueryBoundP (fun _ => True) n

theorem callsAtMost_bind {α β : Type} {oa : OracleComp HashSpec α} {ob : α → OracleComp HashSpec β}
    {n m : Nat} (h : CallsAtMost oa n) (h' : ∀ x, CallsAtMost (ob x) m) : CallsAtMost (oa >>= ob) (n + m) :=
  isQueryBoundP_bind h fun x _ => h' x

theorem callsAtMost_pure {α : Type} (x : α) (n : Nat) : CallsAtMost (pure x : OracleComp HashSpec α) n :=
  trivial

theorem oracleHash_calls (input : HashInput) : CallsAtMost (oracleHash input : OracleComp HashSpec HashOutput) 1 :=
  (isQueryBoundP_query_iff (spec := HashSpec) _ input 1).2 fun _ => Nat.one_pos

theorem tweakableHash_calls (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    CallsAtMost (tweakableHash parameter domain payload : OracleComp HashSpec Digest) 1 :=
  callsAtMost_bind (oracleHash_calls _) fun _ => callsAtMost_pure _ 0

theorem sequenceFin_calls {α : Type} (b : Nat) :
    ∀ {n : Nat} (computation : Fin n → OracleComp HashSpec α),
      (∀ i, CallsAtMost (computation i) b) → CallsAtMost (sequenceFin computation) (n * b)
  | 0, _, _ => trivial
  | n + 1, computation, h => by
      unfold sequenceFin
      refine (callsAtMost_bind (h 0) fun _ => callsAtMost_bind
        (sequenceFin_calls b (fun i : Fin n => computation i.succ) fun i => h i.succ)
        fun _ => callsAtMost_pure _ 0).mono ?_
      rw [Nat.succ_mul]
      omega

theorem chainWalk_calls (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (chainIdx : ChainIndex) (start : Nat) :
    ∀ steps value, CallsAtMost (chainWalk parameter lay tree leaf chainIdx start steps value :
      OracleComp HashSpec Digest) steps
  | 0, _ => trivial
  | steps + 1, value => by
      unfold chainWalk
      refine callsAtMost_bind (chainWalk_calls parameter lay tree leaf chainIdx start steps value) fun _ => ?_
      split
      · exact tweakableHash_calls _ _ _
      · exact callsAtMost_pure _ 1

theorem otsLeaf_calls (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : HashInput) (counter : Counter) (values : ChainIndex → Digest) :
    CallsAtMost (otsLeaf parameter lay tree leaf message counter values : OracleComp HashSpec (Option Digest))
      (1 + (numChains * (chainLength - 1) + 1)) := by
  unfold otsLeaf
  refine callsAtMost_bind (callsAtMost_bind (tweakableHash_calls _ _ _) fun _ => callsAtMost_pure _ 0) fun r => ?_
  rcases r with _ | encoding
  · exact callsAtMost_pure _ _
  · refine callsAtMost_bind (sequenceFin_calls (chainLength - 1) _ fun chainIdx =>
      (chainWalk_calls _ _ _ _ _ _ _ _).mono (by omega)) fun _ => ?_
    exact callsAtMost_bind (tweakableHash_calls _ _ _) fun _ => callsAtMost_pure _ 0

theorem treeFold_calls (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (path : Nat → Digest) :
    ∀ levels value, CallsAtMost (treeFold parameter lay tree leaf path levels value : OracleComp HashSpec Digest)
      levels
  | 0, _ => trivial
  | levels + 1, value => by
      unfold treeFold
      refine callsAtMost_bind (treeFold_calls parameter lay tree leaf path levels value) fun _ => ?_
      split
      · exact tweakableHash_calls _ _ _
      · exact tweakableHash_calls _ _ _

theorem forsFold_calls (parameter : PublicParameter) (index : Index) (κ : FTree) (leaf : FLeaf)
    (path : Fin forsHeight → Digest) :
    ∀ levels value, CallsAtMost (forsFold parameter index κ leaf path levels value : OracleComp HashSpec Digest)
      levels
  | 0, _ => trivial
  | levels + 1, value => by
      unfold forsFold
      refine callsAtMost_bind (forsFold_calls parameter index κ leaf path levels value) fun _ => ?_
      split
      · split
        · exact tweakableHash_calls _ _ _
        · exact tweakableHash_calls _ _ _
      · exact callsAtMost_pure _ 1

theorem forsRecover_calls (parameter : PublicParameter) (index : Index) (leaves : FTree → FLeaf)
    (opening : FTree → TreeOpening) :
    CallsAtMost (forsRecover parameter index leaves opening : OracleComp HashSpec ForsKey)
      (forsTrees * (forsHeight + 1)) := by
  unfold forsRecover
  refine (sequenceFin_calls (1 + forsHeight) _ fun κ => ?_).mono (by rw [Nat.add_comm])
  exact callsAtMost_bind (tweakableHash_calls _ _ _) fun _ => forsFold_calls _ _ _ _ _ _ _

theorem verifyLayers_calls (parameter : PublicParameter) (index : Index) (signature : Signature) :
    ∀ n message, CallsAtMost (verifyLayers parameter index signature n message : OracleComp HashSpec (Option Digest))
      (n * (numChains * (chainLength - 1) + 2 + maxLayerHeight))
  | 0, _ => trivial
  | n + 1, message => by
      unfold verifyLayers
      split
      · refine (callsAtMost_bind (otsLeaf_calls _ _ _ _ _ _ _) fun r => ?_).mono (le_of_eq (by
          rw [Nat.succ_mul]; omega) : 1 + (numChains * (chainLength - 1) + 1) +
            (maxLayerHeight + n * (numChains * (chainLength - 1) + 2 + maxLayerHeight)) ≤ _)
        rcases r with _ | value
        · exact callsAtMost_pure _ _
        · refine callsAtMost_bind ((treeFold_calls _ _ _ _ _ _ _).mono (layerHeight_le _)) fun _ => ?_
          split
          · exact callsAtMost_pure _ _
          · exact verifyLayers_calls parameter index signature n _
      · exact callsAtMost_pure _ _

theorem messageDigest_calls (parameter : PublicParameter) (root : Digest) (message : Message)
    (randomness : Randomness) :
    CallsAtMost (messageDigest parameter root message randomness : OracleComp HashSpec MessageDigest) digestCalls :=
  (callsAtMost_bind (sequenceFin_calls 1 _ fun _ => oracleHash_calls _) fun _ => callsAtMost_pure _ 0).mono
    (by simp)

/-- **The verifier makes at most `verifyCalls` calls of `H`**, on every path. -/
theorem verify_calls (publicKey : PublicKey) (message : Message) (signature : Signature) :
    CallsAtMost (verify publicKey message signature : OracleComp HashSpec Bool) verifyCalls := by
  unfold verify
  refine (callsAtMost_bind (n := digestCalls) (messageDigest_calls _ _ _ _) fun _ =>
    callsAtMost_bind (n := forsTrees * (forsHeight + 1)) (forsRecover_calls _ _ _ _) fun _ =>
    callsAtMost_bind (n := 1) (tweakableHash_calls _ _ _) fun _ =>
    callsAtMost_bind (m := 0) (verifyLayers_calls _ _ _ _ _) fun r => ?_).mono (by unfold verifyCalls; omega)
  rcases r with _ | root
  · exact callsAtMost_pure _ 0
  · exact callsAtMost_pure _ 0

end FORS.Concrete
