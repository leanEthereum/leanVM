import SphincsFors.SecurityVerifier
import SphincsFors.SecurityWotsWitness
import SphincsFors.SecurityForsWitness
import SphincsFors.RandomizedCorrectness

/-!
The interface of deterministic extraction from an accepted candidate signature: its index and
verifier trace, the canonical FORS tops, reference certificates for the WOTS counter and word at a
leaf, canonical openings, and the explicit exceptional branches (`ForsException`, `Exception`).
`BridgeClassify` proves the classification of accepted signatures.
-/

open OracleComp OracleSpec

namespace SphincsFors.Security.SignatureWitness

open Concrete

attribute [local irreducible] messageDigest ftsRecover otsLeaf treeFold
  Seeded.ftsKey Seeded.treeRoot Seeded.treePath chainWalk encode

def index (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) : Index := digestIndex (verificationDigest f pk message signature)

def trace (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) : List HashInput :=
  queriedInputs f (Concrete.verify pk message signature : OracleComp HashSpec Bool)

def canonicalFors (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (leaf : Index) : FtsTops :=
  evalWithAnswerFn f (Seeded.ftsKey parameter leaf seed : OracleComp HashSpec FtsTops)

/-- A concrete reference counter certifies the canonical FORS tops' valid WOTS encoding. -/
def ReferenceCertificate (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (leaf : Index) (counter : Counter) (word : Encoding) : Prop :=
  evalWithAnswerFn f (encode parameter topLayer rootTree leaf
    (canonicalFors f parameter seed leaf) counter : OracleComp HashSpec (Option Encoding)) = some word

/-- The FORS recovery is always part of the complete verifier's actual execution. -/
theorem verification_fors_run (f : QueryImpl HashSpec Id) (pk : PublicKey)
    (message : Message) (signature : Signature) :
    ContainsRun f (trace f pk message signature)
      (ftsRecover pk.parameter (index f pk message signature)
        (digestLeaves (verificationDigest f pk message signature)) signature.ftsSecret signature.ftsPath) := by
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
unrestricted; they select the index and the 24 FORS leaves through the actual message digest. -/
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
    Fors.Opening f pk.parameter leaf seed (digestLeaves (verificationDigest f pk message signature))
      signature.ftsSecret signature.ftsPath

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
  have hsecrets : left.ftsSecret = right.ftsSecret := by
    funext tree
    rw [(hforsL tree).1, (hforsR tree).1, hindex, hdigest]
  have hpaths : left.ftsPath = right.ftsPath := by
    funext tree
    rw [(hforsL tree).2, (hforsR tree).2, hindex, hdigest]
  cases left
  cases right
  cases hrandomness
  cases hsecrets
  cases hpaths
  cases hlayers
  rfl

attribute [local irreducible] Seeded.signLayer Seeded.ftsOpen sequenceFin

/-- Honest assembly preserves its selected randomizer exactly. -/
theorem finishSign_randomness (f : QueryImpl HashSpec Id) (sk : Seeded.SecretKey)
    (message : Message) (randomness : Randomness) (signature : Signature)
    (hsign : evalWithAnswerFn f (Randomized.finishSign sk message randomness) = some signature) :
    signature.randomness = randomness := by
  rw [Randomized.finishSign, evalWithAnswerFn_bind, evalWithAnswerFn_bind,
    evalWithAnswerFn_bind, evalWithAnswerFn_bind] at hsign
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
  obtain ⟨hland, hsecrets, hpaths, hlayers⟩ := Completeness.finishSign_spec f sk message randomness hland hsign
  obtain ⟨word, href, hvalues, hpath⟩ := reference_of_signLayer f sk _ _ (hlayers topLayer)
  refine ⟨word, href, hland, rfl, hvalues, hpath, ?_⟩
  intro tree
  constructor
  · simpa only [ftsIndexOf, index, verificationDigest, Completeness.digestValue]
      using congrFun hsecrets tree
  · funext level
    rw [hpaths, Completeness.eval_ftsOpen]
    rfl

/-- The detailed FORS exception also supplies a distinct-input match in the complete verifier. -/
def ForsException (f : QueryImpl HashSpec Id) (pk : PublicKey) (seed : MasterSeed)
    (message : Message) (signature : Signature) : Prop :=
  Fors.Exception f pk.parameter (index f pk message signature) seed
    (digestLeaves (verificationDigest f pk message signature)) signature.ftsSecret signature.ftsPath ∧
  ∃ input canonicalInput, input ∈ trace f pk message signature ∧ input ≠ canonicalInput ∧
    truncateHash (f input) = truncateHash (f canonicalInput)

/-- Structural outside-subtree events and all explicit WOTS/FORS exceptional cases. -/
def Exception (f : QueryImpl HashSpec Id) (pk : PublicKey) (seed : MasterSeed)
    (message : Message) (signature : Signature) (referenceCounter : Counter)
    (referenceWord : Encoding) : Prop :=
  let leaf := index f pk message signature
  let inputs := trace f pk message signature
  (∃ value, TreeException f pk.parameter seed leaf (signaturePath signature topLayer) value) ∨
  Wots.EncodingOutputMatch f pk.parameter topLayer rootTree leaf
    (canonicalFors f pk.parameter seed leaf) referenceCounter inputs ∨
  Wots.LeafOutputMatch f pk.parameter topLayer rootTree leaf
    (Completeness.otsSecret f pk.parameter topLayer rootTree leaf seed) inputs ∨
  Wots.ChainException f pk.parameter topLayer rootTree leaf referenceWord
    (Completeness.otsSecret f pk.parameter topLayer rootTree leaf seed) inputs ∨
  ForsException f pk seed message signature

end SphincsFors.Security.SignatureWitness
