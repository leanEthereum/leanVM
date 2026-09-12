import XmssSecurity.Proof.ExactQueryCount
import XmssSecurity.Proof.CacheReplayEval
import XmssSecurity.Proof.DetailedExecution
import XmssSecurity.Proof.CappedChain.EncodingQueryBound
import XmssSecurity.Proof.QueryBoundSupport
import XmssSecurity.Statement
import XmssSecurity.Proof.StatementLemmas
import VCVio.OracleComp.QueryTracking.SubSpec

open OracleComp OracleSpec
open scoped BigOperators

namespace XmssSecurity

def treeHashQueryCount : Nat → Nat
  | 0 => numChains * (chainLength - 1) + 1
  | levels + 1 => 2 * treeHashQueryCount levels + 1

namespace ExactQueryCount

theorem oneTimePublicKey (parameter : PublicParameter)
    (secret : Epoch → ChainIndex → Digest) (epoch : Epoch) :
    ExactQueryCount
      (Concrete.oneTimePublicKey (m := OracleComp HashSpec) parameter secret epoch)
      (numChains * (chainLength - 1)) := by
  unfold Concrete.oneTimePublicKey
  have hexact := sequenceFin
    (fun chain : ChainIndex =>
      Concrete.chainWalk (m := OracleComp HashSpec) parameter epoch chain 0
        (chainLength - 1) (secret epoch chain))
    (fun _ : ChainIndex => chainLength - 1)
    (fun chain => chainWalk parameter epoch chain 0 (chainLength - 1)
      (secret epoch chain) (by omega))
  simpa using hexact

theorem leafAt (parameter : PublicParameter)
    (secret : Epoch → ChainIndex → Digest) (epoch : Epoch) :
    ExactQueryCount
      (Concrete.leafAt (m := OracleComp HashSpec) parameter secret epoch)
      (numChains * (chainLength - 1) + 1) := by
  unfold Concrete.leafAt
  exact (oneTimePublicKey parameter secret epoch).bind
    (fun endpoints => Concrete.leafHash parameter epoch endpoints) 1
    (fun endpoints => tweakableHash parameter (.leaf epoch)
      (Concrete.leafPayload endpoints))

theorem treeNode (parameter : PublicParameter)
    (secret : Epoch → ChainIndex → Digest) (levels : Nat) (node : MerkleNode)
    (hlevels : levels ≤ treeHeight) :
    ExactQueryCount
      (Concrete.treeNode (m := OracleComp HashSpec) parameter secret levels node)
      (treeHashQueryCount levels) := by
  induction levels generalizing node with
  | zero =>
      rw [Concrete.treeNode_zero_eq]
      exact leafAt parameter secret node
  | succ levels ih =>
      have hlevel : levels < treeHeight := Nat.lt_of_succ_le hlevels
      rw [Concrete.treeNode_succ_eq]
      have hleft := ih (Concrete.childNode node false) (Nat.le_of_succ_le hlevels)
      have hright := ih (Concrete.childNode node true) (Nat.le_of_succ_le hlevels)
      have hcontinuation (left : Digest) :
          ExactQueryCount (do
            let right ← Concrete.treeNode (m := OracleComp HashSpec) parameter secret levels
              (Concrete.childNode node true)
            Concrete.nodeHash parameter ⟨levels, hlevel⟩ node left right)
            (treeHashQueryCount levels + 1) :=
        hright.bind
          (fun right => Concrete.nodeHash parameter ⟨levels, hlevel⟩ node left right) 1
          (fun right => tweakableHash parameter (.merkle ⟨levels, hlevel⟩ node)
            (Concrete.nodePayload left right))
      simpa [hlevel, treeHashQueryCount, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm, Nat.two_mul] using
        hleft.bind
          (fun left => do
            let right ← Concrete.treeNode (m := OracleComp HashSpec) parameter secret levels
              (Concrete.childNode node true)
            Concrete.nodeHash parameter ⟨levels, hlevel⟩ node left right)
          (treeHashQueryCount levels + 1) hcontinuation

theorem rootTree (parameter : PublicParameter)
    (secret : Epoch → ChainIndex → Digest) :
    ExactQueryCount
      (Concrete.treeNode (m := OracleComp HashSpec) parameter secret treeHeight
        Concrete.rootNode)
      (treeHashQueryCount treeHeight) :=
  treeNode parameter secret treeHeight Concrete.rootNode le_rfl

end ExactQueryCount

theorem treeHashQueryCount_base_le (levels : Nat) :
    numChains * (chainLength - 1) + 1 ≤ treeHashQueryCount levels := by
  induction levels with
  | zero => rfl
  | succ levels ih =>
      simp only [treeHashQueryCount]
      omega

def IsHashQuery : OracleWorld.Domain → Prop := fun input => input matches .inr _

instance : DecidablePred IsHashQuery := by
  intro input
  cases input <;> unfold IsHashQuery <;> exact inferInstance

namespace ExactQueryCount.ExactPredicateQueryCount

theorem liftProbComp_hashCount_zero (computation : ProbComp α) :
    ExactPredicateQueryCount IsHashQuery
      (liftM computation : OracleComp OracleWorld α) 0 := by
  apply ExactQueryCount.ExactPredicateQueryCount.of_isQueryBoundP_zero
  exact OracleComp.IsQueryBoundP.liftComp_subSpec
    (p := fun _ : unifSpec.Domain => False) (q := IsHashQuery)
    (fun input => by simp [IsHashQuery])
    (OracleComp.isQueryBoundP_false computation 0)

theorem rootTreeWithLog_hashCount
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest) :
    ExactPredicateQueryCount IsHashQuery
      (liftM
        (Concrete.treeNode (m := OracleComp HashSpec) parameter secret treeHeight
          Concrete.rootNode).withQueryLog :
        OracleComp OracleWorld (Digest × QueryLog HashSpec))
      (treeHashQueryCount treeHeight) := by
  exact ExactQueryCount.liftComp_predicate
    (ExactQueryCount.withQueryLog (ExactQueryCount.rootTree parameter secret))
    IsHashQuery (fun input => by
      change IsHashQuery (Sum.inr input)
      simp [IsHashQuery])

theorem precomputedKeygen_hashCount :
    ExactPredicateQueryCount IsHashQuery Concrete.precomputedKeygen
      (treeHashQueryCount treeHeight) := by
  unfold Concrete.precomputedKeygen
  exact ExactQueryCount.ExactPredicateQueryCount.bind
    (liftProbComp_hashCount_zero Concrete.samplePublicParameter)
    (fun parameter => do
      let secret ← liftM Concrete.sampleSecret
      let result ← liftM
        (Concrete.treeNode (m := OracleComp HashSpec) parameter secret treeHeight
          Concrete.rootNode).withQueryLog
      let cache := hashCacheOfLog result.2
      return (PublicKey.mk result.1 parameter,
        Concrete.precomputedSecretKey parameter secret cache))
    (treeHashQueryCount treeHeight) (fun parameter =>
      ExactQueryCount.ExactPredicateQueryCount.bind
        (liftProbComp_hashCount_zero Concrete.sampleSecret)
        (fun secret => do
          let result ← liftM
            (Concrete.treeNode (m := OracleComp HashSpec) parameter secret treeHeight
              Concrete.rootNode).withQueryLog
          let cache := hashCacheOfLog result.2
          return (PublicKey.mk result.1 parameter,
            Concrete.precomputedSecretKey parameter secret cache))
        (treeHashQueryCount treeHeight) (fun secret =>
          ExactQueryCount.ExactPredicateQueryCount.bind
            (rootTreeWithLog_hashCount parameter secret)
            (fun result =>
              let cache := hashCacheOfLog result.2
              (Pure.pure (PublicKey.mk result.1 parameter,
                Concrete.precomputedSecretKey parameter secret cache) :
                OracleComp OracleWorld (PublicKey × SecretKey)))
            0 (fun result => ExactPredicateQueryCount.pure _)))

end ExactQueryCount.ExactPredicateQueryCount

theorem countHashQueries_of_exact {α : Type} {computation : OracleComp OracleWorld α} {count : Nat}
    (hexact : ExactPredicateQueryCount IsHashQuery computation count) :
    countHashQueries computation = (fun value => (value, count)) <$> computation := by
  induction hexact with
  | pure value => simp only [countHashQueries_pure, map_pure]
  | query input next count hnext ih =>
      simp only [countHashQueries_query_bind, ih, map_bind, bind_pure_comp, Functor.map_map]
      cases input <;> simp [IsHashQuery, Nat.add_comm]

theorem keygen_hashQueryBound_split (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound Concrete.scheme adversary q)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅)) :
    treeHashQueryCount treeHeight ≤ q ∧
      HashQueryBound (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2)
        keyResult.2 (q - treeHashQueryCount treeHeight) := by
  have hdetailed := (hasHashQueryBound_iff_detailedGameCore Concrete.scheme adversary q).mp hbound
  apply hashQueryBound_bind Concrete.scheme.keygen
    (fun key => detailedGameAfterKeygen Concrete.scheme adversary key.1 key.2) ∅ q hdetailed
    ((keyResult.1, treeHashQueryCount treeHeight), keyResult.2)
  have hcount : countHashQueries Concrete.scheme.keygen =
      (fun key => (key, treeHashQueryCount treeHeight)) <$> Concrete.scheme.keygen :=
    countHashQueries_of_exact ExactQueryCount.ExactPredicateQueryCount.precomputedKeygen_hashCount
  rw [hcount, simulateQ_map, StateT.run_map, support_map]
  exact ⟨keyResult, hkeyResult, rfl⟩

theorem keygen_hashQueryCount_le (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound Concrete.scheme adversary q) : treeHashQueryCount treeHeight ≤ q := by
  obtain ⟨keyResult, hkeyResult⟩ := probComp_support_nonempty ((simulateQ romImpl Concrete.scheme.keygen).run ∅)
  exact (keygen_hashQueryBound_split adversary q hbound keyResult hkeyResult).1

namespace CappedChain

theorem sourceUnloggedDetailedGameAfterKeygen_hashQueryBound_sub_keygen
    (q : Nat) (adversary : Adversary) (hbound : HasHashQueryBound Concrete.scheme adversary q)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅)) :
    HashQueryBound (sourceUnloggedDetailedGameAfterKeygen adversary keyResult.1.1 keyResult.1.2)
      keyResult.2 (q - treeHashQueryCount treeHeight) :=
  (hashQueryBound_iff_of_map_eq
    (detailedGameAfterKeygen_unlogged_projection adversary keyResult.1.1 keyResult.1.2) _ _).mp
      (keygen_hashQueryBound_split adversary q hbound keyResult hkeyResult).2

end CappedChain

end XmssSecurity
