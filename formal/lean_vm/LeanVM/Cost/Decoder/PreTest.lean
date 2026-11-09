module

public import LeanVM.Cost.Decoder.Ends
public import LeanVM.Guest.Fast.PreTest

/-!
# The guest decoder's compiled chain: the precondition's test

`Guest.Fast.preTestAt D T Pw rd j fp`, function `j`'s precondition at the frame `fp` read off the
table `T` of the functions' preconditions (`FnPre`, by its constructor; a frame cell's known word
`Sym`, by its constructors), the logarithm's baby-step tables `D` given, compiled bottom-up: the
logarithm's bound (`powBelowAt`, the logarithm passed in as a value, `powBelow`), each check of one
entry (`envOne`, `bndOne`, `memOne`) and the entry's test (`fnPreTest`). The three
tables are parameters: the decoder's top level builds them once and passes them (`D`:
`Extraction.Fast.discreteLogTables`, about `7.8·10^7`; `T`: `preTableC`,
`Cost/Decoder/PreTable.lean`, the literal `Guest.Fast.preTable`; `Pw`: `genPowsC`, the powers
`gen^(2^j)`, `j < 34`, by `34` squarings). `Guest.Fast.preTestWith_eq_preTable`:
`preTestWith discreteLog = preTestAt discreteLogTables preTable genPows`.
-/

namespace LeanVM.Cost.Decoder

open LeanVM.Cost LeanVM.Parameters LeanVM.Guest.Fast

@[expose] public section

cost_enc LeanVM.Guest.Exec.Sym
cost_enc LeanVM.Guest.Fast.FnPre

cost_compile powBelowAtC := powBelowAt
cost_compile twoPowScanC measure fun _ _ m ↦ m := twoPowScan
cost_compile powBelowLogC := powBelowLog
cost_compile powBelowC := powBelow
cost_compile readPowBelowC := readPowBelow
cost_compile readIsC := readIs
cost_compile gpowAtC := gpowAt
cost_compile symValAtC := symValAt
cost_compile wordAtC := wordAt
cost_compile envOneC := envOne
cost_compile bndOneC := bndOne
cost_compile memAtC := memAt
cost_compile memCellC := memCell
cost_compile memOneC := memOne
cost_compile squaresFromC measure fun _ n ↦ n := squaresFrom
cost_compile powsFromC measure fun _ n ↦ n := powsFrom
cost_compile genPowsC := genPows
cost_compile fnPreTestC := fnPreTest
cost_compile preTestAtC := preTestAt

end

end LeanVM.Cost.Decoder
