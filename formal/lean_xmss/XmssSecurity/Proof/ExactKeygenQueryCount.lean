import XmssSecurity.Proof.ExactQueryCount
import XmssSecurity.Proof.CacheReplayEval
import XmssSecurity.Proof.DetailedExecution
import XmssSecurity.Proof.CappedChain.EncodingQueryBound
import XmssSecurity.Proof.QueryBoundSupport
import XmssSecurity.Proof.IdealStatement
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
    (secret : LeafIndex → ChainIndex → Digest) (leafIndex : LeafIndex) :
    ExactQueryCount
      (Concrete.oneTimePublicKey (m := OracleComp HashSpec) parameter secret leafIndex)
      (numChains * (chainLength - 1)) := by
  unfold Concrete.oneTimePublicKey
  have hexact := sequenceFin
    (fun chain : ChainIndex =>
      Concrete.chainWalk (m := OracleComp HashSpec) parameter leafIndex chain 0
        (chainLength - 1) (secret leafIndex chain))
    (fun _ : ChainIndex => chainLength - 1)
    (fun chain => chainWalk parameter leafIndex chain 0 (chainLength - 1)
      (secret leafIndex chain) (by omega))
  simpa using hexact

theorem leafAt (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest) (leafIndex : LeafIndex) :
    ExactQueryCount
      (Concrete.leafAt (m := OracleComp HashSpec) parameter secret leafIndex)
      (numChains * (chainLength - 1) + 1) := by
  unfold Concrete.leafAt
  exact (oneTimePublicKey parameter secret leafIndex).bind
    (fun endpoints => Concrete.leafHash parameter leafIndex endpoints) 1
    (fun endpoints => tweakableHash parameter (.leaf leafIndex)
      (Concrete.leafPayload endpoints))

theorem treeNode (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest) (levels : Nat) (node : MerkleNode)
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

end ExactQueryCount.ExactPredicateQueryCount

theorem countHashQueries_of_exact {α : Type} {computation : OracleComp OracleWorld α} {count : Nat}
    (hexact : ExactPredicateQueryCount IsHashQuery computation count) :
    countHashQueries computation = (fun value => (value, count)) <$> computation := by
  induction hexact with
  | pure value => simp only [countHashQueries_pure, map_pure]
  | query input next count hnext ih =>
      simp only [countHashQueries_query_bind, ih, map_bind, bind_pure_comp, Functor.map_map]
      cases input <;> simp [IsHashQuery, Nat.add_comm]

/-- The after-key-generation budget bounds every run after key generation. -/
theorem afterKeygen_hashQueryBound (adversary : Adversary) (q : Nat)
    (hbound : HasAfterKeygenHashQueryBound Concrete.scheme adversary q)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅)) :
    HashQueryBound (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2)
      keyResult.2 q := by
  have hrest : HashQueryBound
      (Seeded.gameRest Concrete.scheme adversary keyResult.1.1 keyResult.1.2) keyResult.2 q := by
    simp only [HashQueryBound, simulateQ_countHashQueries]
    exact hbound keyResult hkeyResult
  have hmap : GameOutcome.won <$>
      detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2 =
        Seeded.gameRest Concrete.scheme adversary keyResult.1.1 keyResult.1.2 := by
    classical
    simp [Seeded.gameRest, detailedGameAfterKeygen, GameOutcome.won]
  exact (hashQueryBound_iff_of_map_eq hmap _ _).mpr hrest

namespace CappedChain

theorem sourceUnloggedDetailedGameAfterKeygen_hashQueryBound_sub_keygen
    (q : Nat) (adversary : Adversary) (hbound : HasAfterKeygenHashQueryBound Concrete.scheme adversary q)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅)) :
    HashQueryBound (sourceUnloggedDetailedGameAfterKeygen adversary keyResult.1.1 keyResult.1.2)
      keyResult.2 q :=
  (hashQueryBound_iff_of_map_eq
    (detailedGameAfterKeygen_unlogged_projection adversary keyResult.1.1 keyResult.1.2) _ _).mp
      (afterKeygen_hashQueryBound adversary q hbound keyResult hkeyResult)

end CappedChain

end XmssSecurity
