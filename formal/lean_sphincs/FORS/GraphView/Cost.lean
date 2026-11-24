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

/-- The cost of the authentication path of a layer: kept nodes below `keptHeight`, one derivation
per surrogate above. -/
def treePathCost (lay : Layer) : Nat :=
  ∑ level : Fin (layerHeight lay), if level.val < keptHeight lay then 258 * 2 ^ level.val - 1 else 1

/-- The cost of recovering the FORS public key from an opening: each tree's leaf and its `a` path
nodes, then `T_k`. -/
def forsRecoverCost : Nat := forsTrees * (1 + forsHeight) + 1

/-- The cost of recovering a layer's root below the top layer, which the layer above signs: the
one-time leaf and the fold up the layer's tree. The top layer's root is never recomputed. -/
def recoverCost (lay : Layer) : Nat := if lay.val = 0 then 0 else 66 + layerHeight lay

end FORS.Security.GraphView

end
