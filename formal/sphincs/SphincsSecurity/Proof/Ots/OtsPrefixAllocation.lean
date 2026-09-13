import SphincsSecurity.Proof.Reference.CausalFrontierAllocation
import SphincsSecurity.Proof.Ots.OtsPrefixFrontier
namespace SphincsSecurity.Concrete.OtsPrefix

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] frontierSigningRun boundaryEval frontierRoot

abbrev ChainAddress := Layer × TreeIndex × LeafIndex × ChainIndex

abbrev atAddress (parameter : PublicParameter) (words : OtsReferenceWords) (address : ChainAddress) : OtsPrefix :=
  ⟨parameter, address.1, address.2.1, address.2.2.1, address.2.2.2,
    words address.1 address.2.1 address.2.2.1 address.2.2.2⟩

def Selects (segment : OtsPrefix) : OracleWorld.Domain → Prop
  | .inl _ => False
  | .inr input => segment.parse input ≠ none

noncomputable instance (segment : OtsPrefix) : DecidablePred segment.Selects := Classical.decPred _

theorem atAddress_selects_unique (parameter : PublicParameter) (words : OtsReferenceWords)
    (left right : ChainAddress) (input : OracleWorld.Domain)
    (hleft : (atAddress parameter words left).Selects input)
    (hright : (atAddress parameter words right).Selects input) : left = right := by
  cases input with
  | inl input => exact False.elim hleft
  | inr input =>
      obtain ⟨query, hquery⟩ := Option.ne_none_iff_exists'.mp hleft
      have hinput := ((atAddress parameter words left).parse_some_iff input query).mp hquery
      by_contra hne
      have hother : ¬(atAddress parameter words right).SameChain left.1 left.2.1 left.2.2.1 left.2.2.2 := by
        intro h
        exact hne (Prod.ext h.1 (Prod.ext h.2.1 (Prod.ext h.2.2.1 h.2.2.2)))
      have hnone := (atAddress parameter words right).parse_other_chain left.1 left.2.1 left.2.2.1 left.2.2.2
        hother ((atAddress parameter words left).step query.1) query.2
      exact hright (hinput ▸ hnone)

theorem allocation_step_le (parameter : PublicParameter) (words : OtsReferenceWords) (addresses : Finset ChainAddress)
    (input : OracleWorld.Domain) :
    (∑ address ∈ addresses, if (atAddress parameter words address).Selects input then 1 else 0) ≤
      if CausalFrontierProgram.IsHash input then 1 else 0 := by
  classical
  cases input with
  | inl input => simp [Selects, CausalFrontierProgram.IsHash]
  | inr input =>
      change (∑ address ∈ addresses, if (atAddress parameter words address).Selects (.inr input) then 1 else 0) ≤ 1
      apply Finset.sum_le_one_iff.mpr
      intro left right _ _ hleft hright
      have hl : (atAddress parameter words left).Selects (.inr input) := by simpa using hleft
      have hr : (atAddress parameter words right).Selects (.inr input) := by simpa using hright
      exact ⟨atAddress_selects_unique parameter words left right _ hl hr, if_pos hl⟩

theorem allocation_le (parameter : PublicParameter) (words : OtsReferenceWords) (addresses : Finset ChainAddress)
    (inputs : List OracleWorld.Domain) :
    (∑ address ∈ addresses, QueryCap.calls (atAddress parameter words address).Selects inputs) ≤
      QueryCap.calls CausalFrontierProgram.IsHash inputs :=
  QueryCap.calls_sum_le addresses _ _ (allocation_step_le parameter words addresses) inputs

theorem worldImpl_counted (segment : OtsPrefix) (tables : Fin segment.digit.val → Digest → Digest)
    (high : segment.Query → High) (outside : QueryImpl HashSpec Id) (input : OracleWorld.Domain) :
    simulateQ (segment.fixedImpl tables) (QueryCap.counted PartialChainEndpoint.IsPrefixQuery
      (segment.worldImpl high outside input)) =
      (fun answer => (answer, if segment.Selects input then 1 else 0)) <$>
        fixedHashWorld (segment.answer tables high outside) input := by
  cases input with
  | inl input =>
      simp only [worldImpl, QueryCap.counted_query, simulateQ_map, simulateQ_spec_query]
      simp only [PartialChainEndpoint.IsPrefixQuery, Selects, if_false]
      rfl
  | inr bytes =>
      cases hparse : segment.parse bytes with
      | none => simp [worldImpl, hashImpl, hparse, QueryCap.counted_pure, Selects, fixedHashWorld, answer]
      | some query =>
          simp [worldImpl, hashImpl, hparse, QueryCap.counted_map, QueryCap.counted_query,
            Selects, fixedHashWorld, answer, PartialChainEndpoint.IsPrefixQuery, fixedImpl]

theorem program_mask_answer (segment : OtsPrefix) (tables : Fin segment.digit.val → Digest → Digest)
    (high : segment.Query → High) (outside : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords)
    (hword : segment.digit.val ≤ (words segment.lay segment.tree segment.leaf segment.chainIdx).val)
    (frontier : OtsFrontierValues) (adversary : Adversary) :
    CausalFrontierProgram.game segment.parameter (segment.answer tables high outside) ftsSecret words frontier adversary =
      CausalFrontierProgram.game segment.parameter outside ftsSecret words frontier adversary := by
  have himpl (root : Digest) : CausalFrontierProgram.adversaryImpl segment.parameter root
      (segment.answer tables high outside) ftsSecret words frontier =
      CausalFrontierProgram.adversaryImpl segment.parameter root outside ftsSecret words frontier := by
    funext input
    cases input with
    | inl input => rfl
    | inr message =>
        rw [CausalFrontierProgram.adversaryImpl_signing, CausalFrontierProgram.adversaryImpl_signing,
          segment.mask_answer words hword tables high outside]
  simp only [CausalFrontierProgram.game, CausalFrontierProgram.gameRest, CausalFrontierProgram.adversaryRun,
    segment.mask_answer words hword tables high outside, himpl]

theorem game_counted_source (segment : OtsPrefix) (tables : Fin segment.digit.val → Digest → Digest)
    (high : segment.Query → High) (outside : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords)
    (hword : segment.digit.val ≤ (words segment.lay segment.tree segment.leaf segment.chainIdx).val)
    (frontier : OtsFrontierValues) (adversary : Adversary) :
    simulateQ (segment.fixedImpl tables) (QueryCap.counted PartialChainEndpoint.IsPrefixQuery
        (segment.game high outside ftsSecret words frontier adversary)) =
      simulateQ (fixedHashWorld (segment.answer tables high outside)) (QueryCap.counted segment.Selects
        (CausalFrontierProgram.game segment.parameter (segment.answer tables high outside) ftsSecret words frontier adversary)) := by
  rw [← CausalFrontierProgram.prefix_game, segment.program_mask_answer tables high outside ftsSecret words hword frontier adversary]
  exact QueryCap.simulate_counted segment.Selects PartialChainEndpoint.IsPrefixQuery _ _ _
    (segment.worldImpl_counted tables high outside) _

end SphincsSecurity.Concrete.OtsPrefix
