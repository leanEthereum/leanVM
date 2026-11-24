module

public import FORS.GraphView.Signer
public import FORS.GraphView.Secrets
public import FORS.GraphView.HashCalls
public import FORS.LazyRun.Cost

@[expose] public section

section

/-! The source oracle of the graph-reveal signer on a fixed answer function and coordinate
table: private draws are uniform, and hash and reveal queries are answered by the fixed view. -/

open OracleComp OracleSpec

namespace FORS.Security.GraphView

variable [Params]
open Concrete Completeness Prefix HiddenGraph
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Seeded.finishSign digestAttemptLimit
set_option backward.isDefEq.respectTransparency false

noncomputable def fixedSource (f : QueryImpl HashSpec Id) (table : HiddenGraph.Table) :
    QueryImpl HiddenGraph.SourceSpec PMF :=
  (fun input => Cslib.Probability.PMF.uniformOfFintype (unifSpec.Range input) : QueryImpl unifSpec PMF) +
    (fixedView f table).liftTarget PMF

end FORS.Security.GraphView

end

section

/-! Exact original honest hash costs for the graph-reveal signer. The simulation retains
ordinary message/encoding queries and represents the remaining internal work by explicit
natural-number ticks, including work performed before a failed WOTS search. -/

open OracleComp OracleSpec

namespace FORS.Security.GraphView

variable [Params]
open Concrete Completeness Prefix PrunedGraph
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] firstEncoding ReferenceChoice.search encodingAttemptLimit
  Seeded.forsKey Seeded.forsOpen Seeded.treePath Seeded.otsSignFrom Seeded.signLayer
  chainWalk sequenceFin encode Seeded.treeRoot Seeded.forsNode

/-- The cost of opening one tree: the opened secret, then the sibling node at every level. -/
def treeOpenCost : Nat :=
  1 + ∑ level : Fin forsHeight, (3 * 2 ^ level.val - 1)

/-- The published values of a WOTS+C signature cost `64 + 128 = 192` calls: the 64 seed derivations
of the chain starts and the 128 chain steps of a codeword. -/
theorem hashCalls_published_values (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (seed : MasterSeed) (word : Encoding)
    (hword : TargetSum.Valid word) :
    hashCalls f (do
      let secrets ← (Seeded.otsSecrets parameter lay tree leaf seed : OracleComp HashSpec (ChainIndex → Digest))
      sequenceFin fun chain => chainWalk parameter lay tree leaf chain 0 (word chain).val (secrets chain)) = 192 := by
  simp only [hashCalls_sequenceFin, hashCalls_bind, hashCalls_otsSecrets]
  have hwalk (chain : ChainIndex) (value : Digest) :
      hashCalls f (chainWalk parameter lay tree leaf chain 0 (word chain).val value :
        OracleComp HashSpec Digest) = (word chain).val :=
    hashCalls_chainWalk f parameter lay tree leaf chain 0 (word chain).val value
      (by have := (word chain).isLt; omega)
  simp only [hwalk]
  change 64 + TargetSum.sum word = 192
  rw [show TargetSum.sum word = targetSum from hword]
  rfl

theorem hashCalls_otsSignFrom_search (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (seed : MasterSeed) (message : HashInput)
    (attempts start : Nat) :
    hashCalls f (Seeded.otsSignFrom parameter lay tree leaf seed message attempts start :
      OracleComp HashSpec (Option (Counter × (ChainIndex → Digest)))) =
      hashCalls f (ReferenceChoice.search parameter lay tree leaf message attempts start) +
        if (firstEncoding f parameter lay tree leaf message attempts start).isSome then 192 else 0 := by
  induction attempts generalizing start with
  | zero => simp only [Seeded.otsSignFrom, ReferenceChoice.search, firstEncoding, hashCalls_pure,
      Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
  | succ attempts ih =>
      cases he : evalWithAnswerFn f (encode parameter lay tree leaf message
          (BitVec.ofNat counterBits start) : OracleComp HashSpec (Option Encoding)) with
      | none =>
          simp only [Seeded.otsSignFrom, ReferenceChoice.search, firstEncoding,
            hashCalls_bind, hashCalls_encode, he, ih]
          omega
      | some word =>
          have hvalid := EncodingCode.decode_valid (Wots.decode_of_encode f parameter lay tree leaf
            message (BitVec.ofNat counterBits start) word he)
          have hpub := hashCalls_published_values f parameter lay tree leaf seed word hvalid
          rw [hashCalls_bind] at hpub
          simp only [Seeded.otsSignFrom, ReferenceChoice.search, firstEncoding,
            hashCalls_bind, hashCalls_encode, he, hashCalls_pure, hpub,
            Option.isSome_some, ↓reduceIte, Nat.add_zero]

/-- The cost of the authentication path of a layer: kept nodes below `keptHeight`, one derivation
per surrogate above. -/
def treePathCost (lay : Layer) : Nat :=
  ∑ level : Fin (layerHeight lay), if level.val < keptHeight lay then 258 * 2 ^ level.val - 1 else 1

theorem hashCalls_treePath_exact (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (seed : MasterSeed) :
    hashCalls f (Seeded.treePath parameter lay tree seed leaf :
      OracleComp HashSpec (Fin (layerHeight lay) → Digest)) = treePathCost lay := by
  simp only [Seeded.treePath, hashCalls_sequenceFin, treePathCost]
  apply Finset.sum_congr rfl
  intro level _
  split
  · exact hashCalls_treeNode f parameter lay tree seed _ _
  · have hlevel : level.val < maxLayerHeight := level.isLt.trans_le (layerHeight_le lay)
    simp only [Seeded.surrogate, dite_eq_left hlevel, hashCalls_deriveKey]

/-- Folding a leaf up `levels` levels costs one call per level. -/
theorem hashCalls_treeFold (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (lay : Layer)
    (tree : TreeIndex) (leaf : LeafIndex) (path : Nat → Digest) :
    ∀ levels value, hashCalls f (treeFold parameter lay tree leaf path levels value :
      OracleComp HashSpec Digest) = levels
  | 0, _ => hashCalls_pure f _
  | levels + 1, value => by
      rw [treeFold, hashCalls_bind, hashCalls_treeFold f parameter lay tree leaf path levels value]
      dsimp only
      split <;> simp only [hashCalls_tweakableHash]

/-- The cost of recovering the FORS public key from an opening: each tree's leaf and its `a` path
nodes, then `T_k`. -/
def forsRecoverCost : Nat := forsTrees * (1 + forsHeight) + 1

/-- Recovering a one-time leaf at a counter that encodes costs the encoding, the chains from the
revealed values to their ends, and the leaf hash: `1 + (64 * 3 - 128) + 1 = 66`. -/
theorem hashCalls_otsLeaf_of_encode (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (message : HashInput) (counter : Counter)
    (values : ChainIndex → Digest) (word : Encoding)
    (hencode : evalWithAnswerFn f (encode parameter lay tree leaf message counter :
      OracleComp HashSpec (Option Encoding)) = some word) :
    hashCalls f (otsLeaf parameter lay tree leaf message counter values :
      OracleComp HashSpec (Option Digest)) = 66 := by
  have hvalid := EncodingCode.decode_valid (Wots.decode_of_encode f parameter lay tree leaf
    message counter word hencode)
  have hwalk (chain : ChainIndex) (value : Digest) :
      hashCalls f (recoverChain parameter lay tree leaf chain (word chain) value :
        OracleComp HashSpec Digest) = chainLength - 1 - (word chain).val :=
    hashCalls_chainWalk f parameter lay tree leaf chain _ _ value
      (by have := (word chain).isLt; omega)
  simp only [otsLeaf, hashCalls_bind, hashCalls_encode, hencode,
    hashCalls_sequenceFin, hwalk, Completeness.verification_chain_steps word hvalid,
    leafHash, hashCalls_tweakableHash, hashCalls_pure]

/-- The cost of recovering a layer's root below the top layer, which the layer above signs: the
one-time leaf and the fold up the layer's tree. The top layer's root is never recomputed. -/
def recoverCost (lay : Layer) : Nat := if lay.val = 0 then 0 else 66 + layerHeight lay

end FORS.Security.GraphView

end
