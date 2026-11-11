module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvssplit_344_3558 : blockR (kvslookJ 344) (kvsomLookJ 344) false [(.n 151, 1), (.n 152, 22), (.n 196, 54), (.n 312, 1), (.n 313, 9), (.n 367, 44), (.n 480, 1), (.n 481, 6), (.n 535, 28), (.n 647, 1), (.n 648, 4), (.n 702, 21), (.n 814, 1), (.n 815, 3), (.n 869, 17), (.n 945, 1), (.n 946, 3), (.n 993, 15), (.n 1722, 0), (.n 1723, 13), (.n 2519, 0), (.n 2520, 5), (.n 3037, 0), (.n 3038, 3), (.n 3459, 0), (.n 3460, 2), (.n 3861, 0), (.n 3862, 2)] Data.core344.params Data.core344.name (Data.core344.body.drop 3558)
    ([(.n 3460, 2), (.n 3459, 0), (.n 3038, 3), (.n 3037, 0), (.n 2520, 5), (.n 2519, 0), (.n 1723, 13), (.n 1722, 0), (.n 993, 15), (.n 946, 3), (.n 945, 1), (.n 869, 17), (.n 815, 3), (.n 814, 1), (.n 702, 21), (.n 648, 4), (.n 647, 1), (.n 535, 28), (.n 481, 6), (.n 480, 1), (.n 367, 44), (.n 313, 9), (.n 312, 1), (.n 196, 54), (.n 152, 22), (.n 151, 1)], []) = some (⟨20, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_345 : kvsStaticRange 345 2 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_347 : kvsStaticRange 347 1 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
