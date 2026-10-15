import Sphincs.SecurityGraphView
import Sphincs.SecurityPrefixFullSign

/-! The source oracle of the graph-reveal signer on a fixed answer function and coordinate
table: private draws are uniform, and hash and reveal queries are answered by the fixed view. -/

open OracleComp OracleSpec

namespace Sphincs.Security.GraphView
open Concrete Completeness Prefix HiddenGraph
attribute [local instance] Classical.propDecidable
attribute [local irreducible] finishSource Randomized.finishSign digestAttemptLimit
set_option backward.isDefEq.respectTransparency false

noncomputable def fixedSource (f : QueryImpl HashSpec Id) (table : HiddenGraph.Table) :
    QueryImpl HiddenGraph.SourceSpec PMF :=
  (fun input => PMF.uniformOfFintype (unifSpec.Range input) : QueryImpl unifSpec PMF) +
    (fixedView f table).liftTarget PMF

end Sphincs.Security.GraphView
