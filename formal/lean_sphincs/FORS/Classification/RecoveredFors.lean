module

public import FORS.Classification.Accepted

@[expose] public section

/-! The FORS part of the classification that keeps the recovered FORS roots
(`accepted_recovered_classification`, `Classification/Accepted.lean`), refined tree by tree. Roots
compressing to the canonical FORS key either are non-canonical (a roots match, a first-order hit at
the `T_k` input), or have a node match at a hashed level (a first-order hit), or, in every tree, the
canonical path and a secret that is canonical or a leaf match. It is `Fors.tree_classification`
(`Classification/Fors.lean`) with the canonical path kept in the leaf branch, where only the secret
differs. -/

open OracleComp OracleSpec

namespace FORS.Security.Fors

variable [Params]
open Concrete

section Refined

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (index : Index) (κ : FTree)
  (seed : MasterSeed)

/-- One tree reaching the canonical root, keeping the path: the path is canonical and the secret is
canonical or a leaf match, or a node query hits a canonical value. -/
theorem tree_refined (leaf : FLeaf) (secret : Digest) (path : Fin forsHeight → Digest)
    (hroot : recoveredRoot f parameter index κ leaf secret path = Completeness.rootValue f parameter index seed κ) :
    (path = canonicalPath f parameter index κ seed leaf ∧
      (secret = Completeness.forsSecretValue f parameter index κ seed leaf ∨
        LeafMatch f parameter index κ seed leaf secret)) ∨
    ∃ level, level < forsHeight ∧ NodeMatch f parameter index κ seed leaf secret path level := by
  have hfold : merkleValue f parameter (forsDomain index κ) leaf.val (extendPath path)
      (leafValue f parameter index κ leaf secret) forsHeight =
    merkleValue f parameter (forsDomain index κ) leaf.val
      (extendPath (canonicalPath f parameter index κ seed leaf))
      (leafValue f parameter index κ leaf (Completeness.forsSecretValue f parameter index κ seed leaf))
      forsHeight := by
    simp only [merkleValue, merkleFold_forsFold _ _ _ _ _ _ le_rfl]
    exact hroot.trans (canonical_root f parameter index κ seed leaf).symm
  rcases merkleFold_same_index f parameter _ leaf.val _ _ _ _ forsHeight hfold with
    ⟨hleaf, hpath⟩ | hmatch
  · refine Or.inl ⟨?_, ?_⟩
    · funext level
      simpa only [extendPath, dite_eq_left level.isLt] using hpath level.val level.isLt
    · by_cases hsecret : secret = Completeness.forsSecretValue f parameter index κ seed leaf
      · exact Or.inl hsecret
      · exact Or.inr ⟨hsecret, hleaf⟩
  · exact Or.inr hmatch

end Refined

section Key

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (index : Index) (seed : MasterSeed)

/-- The node branch of a recovered key that is a first-order hit: a node match at a hashed level.
The leaf match is left in the refined classification, since it is a contact at a hidden secret; the
roots match is the other first-order branch. -/
def NodeException (leaves : FTree → FLeaf) (opening : FTree → TreeOpening) : Prop :=
  ∃ κ level, level < forsHeight ∧
    NodeMatch f parameter index κ seed (leaves κ) (opening κ).secret (opening κ).path level

/-- **Tree-by-tree classification of recovered roots with the canonical FORS key.** -/
theorem recovered_classification (leaves : FTree → FLeaf) (opening : FTree → TreeOpening)
    (hrecover : evalWithAnswerFn f (forsPublicKey parameter index
        (evalWithAnswerFn f (forsRecover parameter index leaves opening : OracleComp HashSpec ForsKey))
        : OracleComp HashSpec Digest) =
      evalWithAnswerFn f (Seeded.forsKey parameter index seed : OracleComp HashSpec Digest)) :
    NodeException f parameter index seed leaves opening ∨
    RootsMatch f parameter index seed (roots f parameter index leaves opening) ∨
    ∀ κ, (opening κ).path = canonicalPath f parameter index κ seed (leaves κ) ∧
      ((opening κ).secret = Completeness.forsSecretValue f parameter index κ seed (leaves κ) ∨
        LeafMatch f parameter index κ seed (leaves κ) (opening κ).secret) := by
  classical
  by_cases hroots : roots f parameter index leaves opening = fun κ => Completeness.rootValue f parameter index seed κ
  · by_cases hN : NodeException f parameter index seed leaves opening
    · exact Or.inl hN
    refine Or.inr (Or.inr fun κ => ?_)
    rcases tree_refined f parameter index κ seed (leaves κ) (opening κ).secret (opening κ).path
      (congrFun hroots κ) with h | ⟨level, hlevel, hnode⟩
    · exact h
    · exact absurd ⟨κ, level, hlevel, hnode⟩ hN
  · refine Or.inr (Or.inl ⟨hroots, ?_⟩)
    rw [← eval_forsRecover, hrecover, Completeness.forsKey_eq]

end Key

end FORS.Security.Fors


namespace FORS.Security.SignatureWitness

variable [Params]
open Concrete

attribute [local irreducible] messageDigest forsRecover otsLeaf treeFold
  Seeded.forsKey Seeded.treeRoot Seeded.treePath chainWalk encode


/-- A recovered opening whose FORS part is the canonical opening is a canonical opening. -/
theorem RecoveredOpening.canonical {f : QueryImpl HashSpec Id} {pk : PublicKey} {seed : MasterSeed}
    {message : Message} {signature : Signature} {counter : Layer → Counter}
    (h : RecoveredOpening f pk seed message signature counter)
    (hopening : Fors.Opening f pk.parameter (index f pk message signature) seed
      (digestLeaves (verificationDigest f pk message signature)) signature.fors) :
    CanonicalOpening f pk seed message signature counter
      (chosenWord f pk.parameter seed (index f pk message signature)) :=
  ⟨h.1, h.2.1, hopening⟩

/-- **The refined FORS case.** -/
theorem RecoveredOpening.fors_classification {f : QueryImpl HashSpec Id} {pk : PublicKey}
    {seed : MasterSeed} {message : Message} {signature : Signature} {counter : Layer → Counter}
    (h : RecoveredOpening f pk seed message signature counter) :
    Fors.NodeException f pk.parameter (index f pk message signature) seed
        (digestLeaves (verificationDigest f pk message signature)) signature.fors ∨
    Fors.RootsMatch f pk.parameter (index f pk message signature) seed
        (Fors.roots f pk.parameter (index f pk message signature)
          (digestLeaves (verificationDigest f pk message signature)) signature.fors) ∨
    ∀ κ, (signature.fors κ).path = Fors.canonicalPath f pk.parameter (index f pk message signature) κ seed
        (digestLeaves (verificationDigest f pk message signature) κ) ∧
      ((signature.fors κ).secret = Completeness.forsSecretValue f pk.parameter
          (index f pk message signature) κ seed
          (digestLeaves (verificationDigest f pk message signature) κ) ∨
        Fors.LeafMatch f pk.parameter (index f pk message signature) κ seed
          (digestLeaves (verificationDigest f pk message signature) κ) (signature.fors κ).secret) :=
  Fors.recovered_classification f pk.parameter (index f pk message signature) seed
    (digestLeaves (verificationDigest f pk message signature)) signature.fors
    (h.2.2.trans (Completeness.forsKey_eq f pk.parameter (index f pk message signature) seed).symm)

end FORS.Security.SignatureWitness
