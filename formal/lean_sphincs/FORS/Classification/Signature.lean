import FORS.Classification.Verifier
import FORS.Classification.Wots
import FORS.Classification.Fors

/-!
The interface of deterministic extraction from an accepted candidate signature: its index and
verifier trace, the canonical FORS key and the canonical message of every layer's WOTS+C key on
the index's path (the root of the honest tree below it, the FORS key at the bottom), reference
certificates for the counter and word of each key, canonical openings, and the explicit exceptional
branches (`ForsException`, `Exception`). `Classification/Accepted` proves the
classification of accepted signatures.
-/

open OracleComp OracleSpec

namespace FORS.Security.SignatureWitness

variable [Params]

open Concrete

attribute [local irreducible] messageDigest forsRecover otsLeaf treeFold
  Seeded.forsKey Seeded.treeRoot Seeded.treePath chainWalk encode

def index (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) : Index := digestIndex (verificationDigest f pk message signature)

def trace (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) : List HashInput :=
  queriedInputs f (Concrete.verify pk message signature : OracleComp HashSpec Bool)

def canonicalFors (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (leaf : Index) : ForsKey :=
  evalWithAnswerFn f (Seeded.forsKey parameter leaf seed : OracleComp HashSpec ForsKey)

/-- The canonical message of a WOTS+C key: the root of the honest tree below it, or the FORS key
of its instance at the bottom layer. -/
def keyMessageValue (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (seed : MasterSeed)
    (key : OtsKey) : HashInput :=
  evalWithAnswerFn f (Seeded.keyMessage parameter seed key.1 key.2.1 key.2.2 : OracleComp HashSpec HashInput)

/-- The canonical message of the WOTS+C key of layer `lay` on the path of `leaf`. -/
def canonicalMessage (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (leaf : Index) (lay : Layer) : HashInput :=
  keyMessageValue f parameter seed (keyAt leaf lay)

theorem canonicalMessage_eq (f : QueryImpl HashSpec Id) (sk : Seeded.SecretKey) (leaf : Index)
    (lay : Layer) :
    canonicalMessage f sk.parameter sk.seed leaf lay = Completeness.layerMessageValue f sk leaf lay := rfl

/-- The bottom key signs the FORS key. -/
theorem canonicalMessage_bottom (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (leaf : Index) :
    canonicalMessage f parameter seed leaf (layerUp 0) = rootsPayload (canonicalFors f parameter seed leaf) := by
  have h := Completeness.layerMessageValue_bottom f ⟨seed, parameter, 0⟩ leaf
  exact h

/-- A key above the bottom signs the root of the tree below on the path. -/
theorem canonicalMessage_succ (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (leaf : Index) (j : Nat) (hj : j + 1 < numLayers) :
    canonicalMessage f parameter seed leaf (layerUp (j + 1)) =
      rootPayload (evalWithAnswerFn f (Seeded.treeRoot parameter (layerUp j)
        (treeIndexAt leaf (layerUp j)) seed : OracleComp HashSpec Digest)) := by
  have hbelow : (layerUp (j + 1)).val + 1 < numLayers := by simp only [layerUp]; omega
  have hlay : (⟨(layerUp (j + 1)).val + 1, hbelow⟩ : Layer) = layerUp j := by
    apply Fin.ext; simp only [layerUp]; omega
  have h := Completeness.layerMessageValue_above f ⟨seed, parameter, 0⟩ leaf (layerUp (j + 1)) hbelow
  rw [hlay] at h
  exact h

/-- The key of layer `lay` on the path of `leaf`, at the canonical message. -/
abbrev keyTree (leaf : Index) (lay : Layer) : TreeIndex := treeIndexAt leaf lay
abbrev keyLeaf (leaf : Index) (lay : Layer) : LeafIndex := leafIndexAt leaf lay

/-- A concrete reference counter certifies the valid WOTS encoding of the canonical message of the
key of layer `lay` on the path of `leaf`. -/
def ReferenceCertificate (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (leaf : Index) (lay : Layer) (counter : Counter) (word : Encoding) : Prop :=
  evalWithAnswerFn f (encode parameter lay (keyTree leaf lay) (keyLeaf leaf lay)
    (canonicalMessage f parameter seed leaf lay) counter : OracleComp HashSpec (Option Encoding)) = some word

/-- The FORS recovery is always part of the complete verifier's actual execution. -/
theorem verification_fors_run (f : QueryImpl HashSpec Id) (pk : PublicKey)
    (message : Message) (signature : Signature) :
    ContainsRun f (trace f pk message signature)
      (forsRecover pk.parameter (index f pk message signature)
        (digestLeaves (verificationDigest f pk message signature)) signature.fors) := by
  have hrun : ContainsRun f
      (queriedInputs f (Concrete.verify pk message signature : OracleComp HashSpec Bool))
      (Concrete.verify pk message signature : OracleComp HashSpec Bool) := fun _ hi => hi
  rw [verify_eq_layers] at hrun
  simpa only [← verify_eq_layers, trace, index, verificationDigest] using hrun.bind_right.bind_left

theorem canonical_wots_leaf (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) :
    Completeness.node f parameter lay tree seed 0 leaf.val =
      Wots.canonicalLeaf f parameter lay tree leaf
        (Completeness.otsSecret f parameter lay tree leaf seed) := by
  rw [Completeness.node_zero]
  rfl

/-- A successful honest WOTS layer supplies its reference certificate and exact published values.
The counter is the counter actually returned by the signer, rather than an arbitrary valid one. -/
theorem reference_of_signLayer (f : QueryImpl HashSpec Id) (sk : Seeded.SecretKey) (leaf : Index)
    (lay : Layer) (part : LayerSignature lay)
    (hsign : evalWithAnswerFn f (Seeded.signLayer sk leaf lay :
      OracleComp HashSpec (Option (LayerSignature lay))) = some part) :
    ∃ word, ReferenceCertificate f sk.parameter sk.seed leaf lay part.counter word ∧
      part.chainValues = Wots.frontier f sk.parameter lay (keyTree leaf lay) (keyLeaf leaf lay) word
        (Completeness.otsSecret f sk.parameter lay (keyTree leaf lay) (keyLeaf leaf lay) sk.seed) ∧
      part.path = evalWithAnswerFn f (Seeded.treePath sk.parameter lay (keyTree leaf lay) sk.seed
        (keyLeaf leaf lay) : OracleComp HashSpec (Fin (layerHeight lay) → Digest)) := by
  obtain ⟨hots, hpath⟩ := Completeness.signLayer_spec f sk leaf lay hsign
  obtain ⟨word, hencode, hvalues⟩ := Completeness.otsSignFrom_spec f sk.parameter lay
    (treeIndexAt leaf lay) (leafIndexAt leaf lay) sk.seed
    (Completeness.layerMessageValue f sk leaf lay) encodingAttemptLimit 0 hots
  refine ⟨word, ?_, funext hvalues, hpath⟩
  unfold ReferenceCertificate
  rw [canonicalMessage_eq]
  exact hencode

/-- Exact canonical components of one layer of a signature: its counter, the chain values of the
reference word and the honest path of its key on the index's path. -/
def CanonicalLayer (f : QueryImpl HashSpec Id) (pk : PublicKey) (seed : MasterSeed) (leaf : Index)
    (signature : Signature) (lay : Layer) (referenceCounter : Counter) (referenceWord : Encoding) : Prop :=
  (signature.layers lay).counter = referenceCounter ∧
    (signature.layers lay).chainValues = Wots.frontier f pk.parameter lay (keyTree leaf lay)
      (keyLeaf leaf lay) referenceWord
      (Completeness.otsSecret f pk.parameter lay (keyTree leaf lay) (keyLeaf leaf lay) seed) ∧
    (signature.layers lay).path = evalWithAnswerFn f
      (Seeded.treePath pk.parameter lay (keyTree leaf lay) seed (keyLeaf leaf lay) :
        OracleComp HashSpec (Fin (layerHeight lay) → Digest))

/-- Exact retained-leaf components of a canonical signature. The message and randomizer are
unrestricted; they select the index and the FORS leaves through the actual message digest. -/
def CanonicalOpening (f : QueryImpl HashSpec Id) (pk : PublicKey) (seed : MasterSeed)
    (message : Message) (signature : Signature) (referenceCounter : Layer → Counter)
    (referenceWord : Layer → Encoding) : Prop :=
  let leaf := index f pk message signature
  Landed pk.parameter leaf ∧
    (∀ lay, CanonicalLayer f pk seed leaf signature lay (referenceCounter lay) (referenceWord lay)) ∧
    Fors.Opening f pk.parameter leaf seed (digestLeaves (verificationDigest f pk message signature))
      signature.fors

/-- All canonical signature components are fixed by the message, randomizer, reference counters
and reference words. This is equality of the complete signature structure. -/
theorem canonicalOpening_unique (f : QueryImpl HashSpec Id) (pk : PublicKey) (seed : MasterSeed)
    (message : Message) (left right : Signature) (counter : Layer → Counter) (word : Layer → Encoding)
    (hleft : CanonicalOpening f pk seed message left counter word)
    (hright : CanonicalOpening f pk seed message right counter word)
    (hrandomness : left.randomness = right.randomness) : left = right := by
  have hdigest : verificationDigest f pk message left = verificationDigest f pk message right := by
    simp only [verificationDigest, hrandomness]
  have hindex : index f pk message left = index f pk message right := congrArg digestIndex hdigest
  obtain ⟨_, hlayersL, hforsL⟩ := hleft
  obtain ⟨_, hlayersR, hforsR⟩ := hright
  have hlayers : left.layers = right.layers := by
    funext lay
    obtain ⟨hcounterL, hvaluesL, hpathL⟩ := hlayersL lay
    obtain ⟨hcounterR, hvaluesR, hpathR⟩ := hlayersR lay
    have hcounter : (left.layers lay).counter = (right.layers lay).counter :=
      hcounterL.trans hcounterR.symm
    have hvalues : (left.layers lay).chainValues = (right.layers lay).chainValues := by
      rw [hvaluesL, hvaluesR, hindex]
    have hpath : (left.layers lay).path = (right.layers lay).path := by
      rw [hpathL, hpathR, hindex]
    rcases hl : left.layers lay with ⟨cl, vl, pl⟩
    rcases hr : right.layers lay with ⟨cr, vr, pr⟩
    rw [hl, hr] at hcounter hvalues hpath
    simp only at hcounter hvalues hpath
    subst hcounter hvalues hpath
    rfl
  have hfors : left.fors = right.fors := by
    funext κ
    obtain ⟨hsL, hpL⟩ := hforsL κ
    obtain ⟨hsR, hpR⟩ := hforsR κ
    rw [hindex, hdigest] at hsL hpL
    rcases hl : left.fors κ with ⟨sl, pl⟩
    rcases hr : right.fors κ with ⟨sr, pr⟩
    rw [hl] at hsL hpL
    rw [hr] at hsR hpR
    simp only at hsL hpL hsR hpR
    rw [hsL, hsR, hpL, hpR]
  cases left
  cases right
  cases hrandomness
  cases hfors
  cases hlayers
  rfl

attribute [local irreducible] Seeded.signLayer Seeded.forsOpen sequenceFin

/-- Honest assembly preserves its selected randomizer exactly. -/
theorem finishSign_randomness (f : QueryImpl HashSpec Id) (sk : Seeded.SecretKey)
    (message : Message) (randomness : Randomness) (signature : Signature)
    (hsign : evalWithAnswerFn f (Seeded.finishSign sk message randomness) = some signature) :
    signature.randomness = randomness := by
  rw [Seeded.finishSign, evalWithAnswerFn_bind, evalWithAnswerFn_bind,
    evalWithAnswerFn_bind] at hsign
  split at hsign
  next =>
    simp only [evalWithAnswerFn_pure, Option.some.injEq] at hsign
    subst signature
    rfl
  next => simp at hsign

/-- A successful honest assembly supplies a canonical opening and its concrete reference
certificates. Only the randomizer's actual landing condition is required. -/
theorem canonical_of_finishSign (f : QueryImpl HashSpec Id) (sk : Seeded.SecretKey)
    (message : Message) (randomness : Randomness) (signature : Signature)
    (hland : Landed sk.parameter (digestIndex (Completeness.digestValue f sk message randomness)))
    (hsign : evalWithAnswerFn f (Seeded.finishSign sk message randomness) = some signature) :
    ∃ word : Layer → Encoding,
      (∀ lay, ReferenceCertificate f sk.parameter sk.seed
        (index f ⟨sk.root, sk.parameter⟩ message signature) lay (signature.layers lay).counter (word lay)) ∧
      CanonicalOpening f ⟨sk.root, sk.parameter⟩ sk.seed message signature
        (fun lay => (signature.layers lay).counter) word := by
  obtain ⟨hland, hfors, hlayers⟩ := Completeness.finishSign_spec f sk message randomness hland hsign
  choose word href hvalues hpath using fun lay => reference_of_signLayer f sk _ lay _ (hlayers lay)
  refine ⟨word, href, hland, fun lay => ⟨rfl, hvalues lay, hpath lay⟩, ?_⟩
  intro κ
  have hκ := congrFun hfors κ
  simp only [Seeded.forsOpen, Completeness.eval_sequenceFin, Completeness.eval_treeOpen] at hκ
  refine ⟨?_, ?_⟩
  · rw [hκ]; rfl
  · rw [hκ]; rfl

/-- The detailed FORS exception also supplies a distinct-input match in the complete verifier. -/
def ForsException (f : QueryImpl HashSpec Id) (pk : PublicKey) (seed : MasterSeed)
    (message : Message) (signature : Signature) : Prop :=
  Fors.Exception f pk.parameter (index f pk message signature) seed
    (digestLeaves (verificationDigest f pk message signature)) signature.fors ∧
  ∃ input canonicalInput, input ∈ trace f pk message signature ∧ input ≠ canonicalInput ∧
    truncateHash (f input) = truncateHash (f canonicalInput)

end FORS.Security.SignatureWitness
