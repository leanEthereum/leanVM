import Sphincs.SecurityVerifier
import Sphincs.SecurityWotsWitness
import Sphincs.SecurityForestWitness
import Sphincs.RandomizedCorrectness

/-!
The interface of deterministic extraction from an accepted candidate signature: its index and
verifier trace, the canonical forest key, reference certificates for the WOTS counter and word at a
leaf, canonical openings, and the explicit exceptional branches (`ForestException`, `Exception`).
`BridgeClassify` proves the classification of accepted signatures.
-/

open OracleComp OracleSpec

namespace Sphincs.Security.SignatureWitness

open Concrete

attribute [local irreducible] messageDigest forestRecover otsLeaf treeFold
  Seeded.forestKey Seeded.treeRoot Seeded.treePath chainWalk encode

def index (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) : Index := digestIndex (verificationDigest f pk message signature)

def trace (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) : List HashInput :=
  queriedInputs f (Concrete.verify pk message signature : OracleComp HashSpec Bool)

def canonicalForest (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (leaf : Index) : Digest :=
  evalWithAnswerFn f (Seeded.forestKey parameter leaf seed : OracleComp HashSpec Digest)

/-- A concrete reference counter certifies the canonical forest key's valid WOTS encoding. -/
def ReferenceCertificate (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (leaf : Index) (counter : Counter) (word : Encoding) : Prop :=
  evalWithAnswerFn f (encode parameter topLayer rootTree leaf
    (canonicalForest f parameter seed leaf) counter : OracleComp HashSpec (Option Encoding)) = some word

/-- The forest recovery is always part of the complete verifier's actual execution. -/
theorem verification_forest_run (f : QueryImpl HashSpec Id) (pk : PublicKey)
    (message : Message) (signature : Signature) :
    ContainsRun f (trace f pk message signature)
      (forestRecover pk.parameter (index f pk message signature)
        (digestMarks (verificationDigest f pk message signature)) signature.forest) := by
  have hrun : ContainsRun f
      (queriedInputs f (Concrete.verify pk message signature : OracleComp HashSpec Bool))
      (Concrete.verify pk message signature : OracleComp HashSpec Bool) := fun _ hi => hi
  rw [verify_eq_single_layer] at hrun
  simpa only [← verify_eq_single_layer, trace, index, verificationDigest] using hrun.bind_right.bind_left

theorem canonical_wots_leaf (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (leaf : LeafIndex) :
    Completeness.node f parameter topLayer rootTree seed 0 leaf.val =
      Wots.canonicalLeaf f parameter topLayer rootTree leaf
        (Completeness.otsSecret f parameter topLayer rootTree leaf seed) := by
  rw [Completeness.node_zero]
  rfl

variable [Params]

/-- A successful honest WOTS layer supplies its reference certificate and exact published values.
The counter is the counter actually returned by the signer, rather than an arbitrary valid one. -/
theorem reference_of_signLayer (f : QueryImpl HashSpec Id) (sk : Seeded.SecretKey) (leaf : Index)
    (part : LayerSignature topLayer)
    (hsign : evalWithAnswerFn f (Seeded.signLayer sk leaf topLayer :
      OracleComp HashSpec (Option (LayerSignature topLayer))) = some part) :
    ∃ word, ReferenceCertificate f sk.parameter sk.seed leaf part.counter word ∧
      part.chainValues = Wots.frontier f sk.parameter topLayer rootTree leaf word
        (Completeness.otsSecret f sk.parameter topLayer rootTree leaf sk.seed) ∧
      part.path = evalWithAnswerFn f (Seeded.treePath sk.parameter topLayer rootTree sk.seed leaf :
        OracleComp HashSpec (Fin (layerHeight topLayer) → Digest)) := by
  obtain ⟨hots, hpath⟩ := Completeness.signLayer_spec f sk leaf topLayer hsign
  simp only [Completeness.treeIndexAt_eq, Completeness.leafIndexAt_eq] at hots hpath
  obtain ⟨word, hencode, hvalues⟩ := Completeness.otsSignFrom_spec f sk.parameter topLayer rootTree
    leaf sk.seed (Completeness.layerMessageValue f sk leaf topLayer) encodingAttemptLimit 0 hots
  exact ⟨word, hencode, funext hvalues, hpath⟩

/-- Exact retained-leaf components of a canonical signature. The message and randomizer are
unrestricted; they select the index and the forest marks through the actual message digest. -/
def CanonicalOpening (f : QueryImpl HashSpec Id) (pk : PublicKey) (seed : MasterSeed)
    (message : Message) (signature : Signature) (referenceCounter : Counter)
    (referenceWord : Encoding) : Prop :=
  let leaf := index f pk message signature
  Landed pk.parameter leaf ∧
    (signature.layers topLayer).counter = referenceCounter ∧
    (signature.layers topLayer).chainValues = Wots.frontier f pk.parameter topLayer rootTree leaf
      referenceWord (Completeness.otsSecret f pk.parameter topLayer rootTree leaf seed) ∧
    (signature.layers topLayer).path = evalWithAnswerFn f
      (Seeded.treePath pk.parameter topLayer rootTree seed leaf :
        OracleComp HashSpec (Fin (layerHeight topLayer) → Digest)) ∧
    Forest.Opening f pk.parameter leaf seed (digestMarks (verificationDigest f pk message signature))
      signature.forest

/-- All canonical signature components are fixed by the message, randomizer, reference counter
and reference word. This is equality of the complete signature structure. -/
theorem canonicalOpening_unique (f : QueryImpl HashSpec Id) (pk : PublicKey) (seed : MasterSeed)
    (message : Message) (left right : Signature) (counter : Counter) (word : Encoding)
    (hleft : CanonicalOpening f pk seed message left counter word)
    (hright : CanonicalOpening f pk seed message right counter word)
    (hrandomness : left.randomness = right.randomness) : left = right := by
  have hdigest : verificationDigest f pk message left = verificationDigest f pk message right := by
    simp only [verificationDigest, hrandomness]
  have hindex : index f pk message left = index f pk message right := congrArg digestIndex hdigest
  obtain ⟨_, hcounterL, hvaluesL, hpathL, hforsL⟩ := hleft
  obtain ⟨_, hcounterR, hvaluesR, hpathR, hforsR⟩ := hright
  have hcounter : (left.layers topLayer).counter = (right.layers topLayer).counter :=
    hcounterL.trans hcounterR.symm
  have hvalues : (left.layers topLayer).chainValues = (right.layers topLayer).chainValues := by
    rw [hvaluesL, hvaluesR, hindex]
  have hpath : (left.layers topLayer).path = (right.layers topLayer).path := by
    rw [hpathL, hpathR, hindex]
  have hlayers : left.layers = right.layers := by
    funext lay
    rw [Completeness.only_layer lay]
    change LayerSignature.mk (left.layers topLayer).counter (left.layers topLayer).chainValues
      (left.layers topLayer).path =
        LayerSignature.mk (right.layers topLayer).counter (right.layers topLayer).chainValues
          (right.layers topLayer).path
    rw [hcounter, hvalues, hpath]
  have hforest : left.forest = right.forest := by
    funext c
    obtain ⟨hvL, hpL, htL⟩ := hforsL c
    obtain ⟨hvR, hpR, htR⟩ := hforsR c
    rw [hindex, hdigest] at hvL hpL htL
    have hsub : (left.forest c).sub = (right.forest c).sub := by
      funext j
      have hv : ((left.forest c).sub j).values = ((right.forest c).sub j).values :=
        funext fun i => (hvL j i).trans (hvR j i).symm
      have hp : ((left.forest c).sub j).path = ((right.forest c).sub j).path := (hpL j).trans (hpR j).symm
      rcases hl : (left.forest c).sub j with ⟨vl, pl⟩
      rcases hr : (right.forest c).sub j with ⟨vr, pr⟩
      rw [hl, hr] at hv hp
      simp only at hv hp
      subst hv hp
      rfl
    have htop : (left.forest c).top = (right.forest c).top := htL.trans htR.symm
    rcases hl : left.forest c with ⟨sl, tl⟩
    rcases hr : right.forest c with ⟨sr, tr⟩
    rw [hl, hr] at hsub htop
    simp only at hsub htop
    subst hsub htop
    rfl
  cases left
  cases right
  cases hrandomness
  cases hforest
  cases hlayers
  rfl

attribute [local irreducible] Seeded.signLayer Seeded.forestOpen sequenceFin

/-- Honest assembly preserves its selected randomizer exactly. -/
theorem finishSign_randomness (f : QueryImpl HashSpec Id) (sk : Seeded.SecretKey)
    (message : Message) (randomness : Randomness) (signature : Signature)
    (hsign : evalWithAnswerFn f (Randomized.finishSign sk message randomness) = some signature) :
    signature.randomness = randomness := by
  rw [Randomized.finishSign, evalWithAnswerFn_bind, evalWithAnswerFn_bind,
    evalWithAnswerFn_bind] at hsign
  split at hsign
  next =>
    simp only [evalWithAnswerFn_pure, Option.some.injEq] at hsign
    subst signature
    rfl
  next => simp at hsign

/-- A successful honest assembly supplies a canonical opening and its concrete reference
certificate. Only the randomizer's actual landing condition is required. -/
theorem canonical_of_finishSign (f : QueryImpl HashSpec Id) (sk : Seeded.SecretKey)
    (message : Message) (randomness : Randomness) (signature : Signature)
    (hland : Landed sk.parameter (digestIndex (Completeness.digestValue f sk message randomness)))
    (hsign : evalWithAnswerFn f (Randomized.finishSign sk message randomness) = some signature) :
    ∃ word,
      ReferenceCertificate f sk.parameter sk.seed
        (index f ⟨sk.root, sk.parameter⟩ message signature) (signature.layers topLayer).counter word ∧
      CanonicalOpening f ⟨sk.root, sk.parameter⟩ sk.seed message signature
        (signature.layers topLayer).counter word := by
  obtain ⟨hland, hforest, hlayers⟩ := Completeness.finishSign_spec f sk message randomness hland hsign
  obtain ⟨word, href, hvalues, hpath⟩ := reference_of_signLayer f sk _ _ (hlayers topLayer)
  refine ⟨word, href, hland, rfl, hvalues, hpath, ?_⟩
  intro c
  have hc := congrFun hforest c
  simp only [Seeded.forestOpen, Completeness.eval_sequenceFin, Completeness.eval_coordOpen] at hc
  refine ⟨fun j i => ?_, fun j => ?_, ?_⟩
  · rw [hc]; rfl
  · rw [hc]; rfl
  · rw [hc]; rfl

/-- The detailed forest exception also supplies a distinct-input match in the complete verifier. -/
def ForestException (f : QueryImpl HashSpec Id) (pk : PublicKey) (seed : MasterSeed)
    (message : Message) (signature : Signature) : Prop :=
  Forest.Exception f pk.parameter (index f pk message signature) seed
    (digestMarks (verificationDigest f pk message signature)) signature.forest ∧
  ∃ input canonicalInput, input ∈ trace f pk message signature ∧ input ≠ canonicalInput ∧
    truncateHash (f input) = truncateHash (f canonicalInput)

/-- Structural outside-subtree events and all explicit WOTS/forest exceptional cases. -/
def Exception (f : QueryImpl HashSpec Id) (pk : PublicKey) (seed : MasterSeed)
    (message : Message) (signature : Signature) (referenceCounter : Counter)
    (referenceWord : Encoding) : Prop :=
  let leaf := index f pk message signature
  let inputs := trace f pk message signature
  (∃ value, TreeException f pk.parameter seed leaf (signaturePath signature topLayer) value) ∨
  Wots.EncodingOutputMatch f pk.parameter topLayer rootTree leaf
    (canonicalForest f pk.parameter seed leaf) referenceCounter inputs ∨
  Wots.LeafOutputMatch f pk.parameter topLayer rootTree leaf
    (Completeness.otsSecret f pk.parameter topLayer rootTree leaf seed) inputs ∨
  Wots.ChainException f pk.parameter topLayer rootTree leaf referenceWord
    (Completeness.otsSecret f pk.parameter topLayer rootTree leaf seed) inputs ∨
  ForestException f pk seed message signature

end Sphincs.Security.SignatureWitness
