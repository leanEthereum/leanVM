import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Hypertree.CanonicalProbeCache
import SphincsSecurity.Proof.Fts.PublicSigningRecord
namespace SphincsSecurity.Concrete.InterleavedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

structure Routing where
  disclosed : Index → FtsTree → FtsLeaf → Prop
  known : Labels

abbrev SigningRecord := (Option Signature × Option FewTimeView) × SigningBoundaryTrace

noncomputable def Routing.disclose (routing : Routing) (view : FewTimeView) (secrets : FtsTree → Digest) : Routing where
  disclosed index tree leaf := routing.disclosed index tree leaf ∨ index = view.1 ∧ leaf = view.2 tree
  known coordinate := match coordinate with
    | .ftsStart index tree leaf => if index = view.1 ∧ leaf = view.2 tree then secrets tree else routing.known coordinate
    | _ => routing.known coordinate

noncomputable def Routing.afterSigning (routing : Routing) (record : SigningRecord) : Routing :=
  match record.1.1, record.1.2 with
  | some signature, some view => routing.disclose view signature.ftsSecret
  | _, _ => routing

theorem Routing.afterSigning_mono (routing : Routing) (record : SigningRecord)
    (index : Index) (tree : FtsTree) (leaf : FtsLeaf) :
    routing.disclosed index tree leaf → (routing.afterSigning record).disclosed index tree leaf := by
  rcases record with ⟨⟨signature, view⟩, trace⟩
  cases signature <;> cases view <;> first | exact id | exact Or.inl

theorem hidden_graph_disclosed (words : OtsReferenceWords)
    (before after : Index → FtsTree → FtsLeaf → Prop) (position : Position) :
    CanonicalCoordinate.Hidden words before (.graph position) = CanonicalCoordinate.Hidden words after (.graph position) := by
  cases position <;> rfl

theorem Routing.disclose_agreement (routing : Routing) (words : OtsReferenceWords) (actual : Labels)
    (hagrees : PublicAgreement words routing.disclosed routing.known actual)
    (view : FewTimeView) (secrets : FtsTree → Digest)
    (hsecrets : ∀ tree, secrets tree = actual (.ftsStart view.1 tree (view.2 tree))) :
    PublicAgreement words (routing.disclose view secrets).disclosed (routing.disclose view secrets).known actual := by
  intro coordinate hpublic
  cases coordinate with
  | otsStart lay tree leaf chain => exact hagrees _ hpublic
  | graph position =>
      apply hagrees
      rw [hidden_graph_disclosed words routing.disclosed (routing.disclose view secrets).disclosed position]
      exact hpublic
  | ftsStart index tree leaf =>
      change ¬¬(routing.disclosed index tree leaf ∨ index = view.1 ∧ leaf = view.2 tree) at hpublic
      change (if index = view.1 ∧ leaf = view.2 tree then secrets tree else routing.known (.ftsStart index tree leaf)) = _
      split
      · rename_i h
        rcases h with ⟨rfl, rfl⟩
        exact hsecrets tree
      · rename_i h
        exact hagrees _ (not_not.mpr ((not_not.mp hpublic).resolve_right h))

theorem Routing.afterSigning_graph (routing : Routing) (record : SigningRecord) (position : Position) :
    (routing.afterSigning record).known (.graph position) = routing.known (.graph position) := by
  rcases record with ⟨⟨signature, view⟩, trace⟩
  cases signature <;> cases view <;> rfl

theorem Routing.afterSigning_cacheClean (routing : Routing) (record : SigningRecord)
    (parameter : PublicParameter) (words : OtsReferenceWords) (actual : Labels) (cache : ExternalCache)
    (hclean : CacheClean parameter words routing.disclosed actual cache) :
    CacheClean parameter words (routing.afterSigning record).disclosed actual cache :=
  cacheClean_disclose parameter words routing.disclosed (routing.afterSigning record).disclosed
    (routing.afterSigning_mono record) actual cache hclean

theorem Routing.afterSigning_completed_agreement (routing : Routing) (words : OtsReferenceWords) (actual : Labels)
    (hagrees : PublicAgreement words routing.disclosed routing.known actual) (record : PublicSigningRecord) :
    let completed := completePublicSigningRecord (fun index tree leaf => actual (.ftsStart index tree leaf)) record
    PublicAgreement words (routing.afterSigning completed).disclosed (routing.afterSigning completed).known actual := by
  rcases record with ⟨⟨plan, view⟩, trace⟩
  cases plan <;> cases view <;> simp only [completePublicSigningRecord, Option.map_none, Option.map_some, Routing.afterSigning]
  all_goals first
    | exact hagrees
    | exact routing.disclose_agreement words actual hagrees _ _ (fun _ => rfl)

end SphincsSecurity.Concrete.InterleavedResidual
