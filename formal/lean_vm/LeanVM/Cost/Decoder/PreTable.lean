module

public import LeanVM.Cost.Decoder.PreTest

/-!
# The guest decoder's compiled chain: the functions' preconditions, a literal

`preTableC`: `Guest.Fast.preTable` (`Fast/PreTable.lean`, the functions' preconditions
`fnPreOf (glob.sig j)` the kernel wrote out), compiled as a function of no argument, its body the
table's constructors: a literal of the decoder's program. The decoder's top level calls it once
and passes the table to `preTestAtC` (`PreTest.lean`). Its size is measured in
`Cost/Decoder/PreTableSize.lean`.
-/

namespace LeanVM.Cost.Decoder

open LeanVM.Cost LeanVM.Guest.Fast

@[expose] public section

-- The spec's `simp` (`preTableC.costSpec`) unfolds the 1536 entries of the literal table, above
-- the default heartbeats (profiled with `tools/profile.py`).
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
cost_compile preTableC := preTable

end

end LeanVM.Cost.Decoder
