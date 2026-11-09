module

public import LeanVM.Cost.Decoder.Readers
public import LeanVM.Guest.B1.Main.Aggregate
import all LeanVM.Guest.B1.Main.Aggregate

/-!
# The guest decoder's compiled chain: the batching's hints

`aggregate_claims`' hints off its valuation and the memory (`aggHints`: the sumcheck's rounds at
`bc_sumcheck_msgs`, the bytecode's value `bc_star_hint`).
-/

namespace LeanVM.Cost.Decoder

open LeanVM.Cost LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Main
open LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

cost_compile digestMemAtC := LeanVM.Guest.B1.Digest.memAt
cost_compile aggRoundsC := aggRounds
cost_compile aggHintsC := aggHints

end

end LeanVM.Cost.Decoder
