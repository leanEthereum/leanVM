module

public import LeanVM.Cost.Decoder.Signatures
public import LeanVM.Guest.Fast.Xmss

/-!
# The guest decoder's compiled chain: a leanXMSS signature

The reader of a leanXMSS signature off `__loop2`'s iteration frame, off arrays
(`Guest/Fast/Xmss.lean`: `xmssSigOfA`): the windows' and the dispatches' exponents off the lanes
of `g^k` (`logGTWith`), each read once, the chain starts off the tables `XmssTabs` (`lxFold`,
`lxRest`, `lxTail` as arrays), built once by the decoder's top level (`readerTabsC`,
`Frames.lean`) and passed. The compiled name stays the reader's (`xmssSigOfNC`).
-/

namespace LeanVM.Cost.Decoder

open LeanVM.Cost LeanVM.Parameters LeanVM.Guest.B1 LeanVM.Guest.Fast

@[expose] public section

cost_enc LeanVM.Guest.Fast.XmssTabs

cost_compile lxFoldC := lxFold
cost_compile lxRestC := lxRest
cost_compile lxTailC := lxTail
cost_compile xmssTabsC := xmssTabs

cost_compile lxRhoCellC := lxRhoCell
cost_compile lxDigitBaseC := lxDigitBase
cost_compile lxGroupBaseC := lxGroupBase
cost_compile lxGroupTabC := lxGroupTab
cost_compile lxArmsTakenC := lxArmsTaken
cost_compile lxChainCellC := lxChainCell
cost_compile lxWinBaseC := lxWinBase
cost_compile lxArmBaseC := lxArmBase
cost_compile lxSibAtC := lxSibAt
cost_compile xPartNC := xPartA
cost_compile lxLeafOfC := lxLeafOf
cost_compile xmssSigOfNC := xmssSigOfA

end

end LeanVM.Cost.Decoder
