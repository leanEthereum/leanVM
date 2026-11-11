module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_314 : kvjStaticRange 314 1 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjsplit_315_0 : blockR (kvjlookJ 315) (kvjomLookJ 315) false [] Data.core315.params Data.core315.name (Data.core315.body.drop 0)
    ([], []) = some (⟨15304, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kvjsplit_316_0 : blockR (kvjlookJ 316) (kvjomLookJ 316) false [] Data.core316.params Data.core316.name (Data.core316.body.drop 0)
    ([], []) = some (⟨15490, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_317 : kvjStaticRange 317 21 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_338 : kvjStaticRange 338 22 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_360 : kvjStaticRange 360 23 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
