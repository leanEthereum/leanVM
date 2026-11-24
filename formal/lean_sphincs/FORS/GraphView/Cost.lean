module

public import FORS.GraphView.Signer
public import FORS.GraphView.HashCalls
public import FORS.LazyRun.Cost

@[expose] public section

/-! The source oracle of the graph-reveal signer on a fixed answer function and coordinate table
(private draws are uniform, hash and reveal queries are answered by the fixed view), and the honest
hash costs of the signer's parts, which the counted game charges. -/

open OracleComp OracleSpec

namespace FORS.Security.GraphView

variable [Params]

noncomputable def fixedSource (f : QueryImpl HashSpec Id) (table : HiddenGraph.Table) :
    QueryImpl HiddenGraph.SourceSpec PMF :=
  (fun input => Cslib.Probability.PMF.uniformOfFintype (unifSpec.Range input) : QueryImpl unifSpec PMF) +
    (fixedView f table).liftTarget PMF

/-- The cost of opening one tree: the opened secret, then the sibling node at every level. -/
def treeOpenCost : Nat :=
  1 + ∑ level : Fin forsHeight, (3 * 2 ^ level.val - 1)

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
