import SphincsFors.SecurityGraphView
import SphincsFors.SecurityPrefixFullSign

/-! The source oracle of the graph-reveal signer on a fixed answer function and coordinate
table: private draws are uniform, and hash and reveal queries are answered by the fixed view. -/

open OracleComp OracleSpec

namespace SphincsFors.Security.GraphView
open Concrete Completeness Prefix HiddenGraph
attribute [local instance] Classical.propDecidable
attribute [local irreducible] finishSource Randomized.finishSign digestAttemptLimit
set_option backward.isDefEq.respectTransparency false

noncomputable def fixedSource (f : QueryImpl HashSpec Id) (table : HiddenGraph.Table) :
    QueryImpl HiddenGraph.SourceSpec PMF :=
  (fun input => PMF.uniformOfFintype (unifSpec.Range input) : QueryImpl unifSpec PMF) +
    (fixedView f table).liftTarget PMF

end SphincsFors.Security.GraphView
