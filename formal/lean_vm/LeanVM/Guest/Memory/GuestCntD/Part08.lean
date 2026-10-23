module

public import LeanVM.Guest.Memory.GuestCntD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwdsplit_17_512 : noTopRet ((Data.core17.body.drop 512).take 1) = true ∧
    blockR (kwdlookJ 17) (kwdomLookJ 17) false [] Data.core17.params Data.core17.name ((Data.core17.body.drop 512).take 1) ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwdsplit_17_513 : noTopRet ((Data.core17.body.drop 513).take 264) = true ∧
    blockR (kwdlookJ 17) (kwdomLookJ 17) false [] Data.core17.params Data.core17.name ((Data.core17.body.drop 513).take 264) ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwdsplit_17_777 : blockR (kwdlookJ 17) (kwdomLookJ 17) false [] Data.core17.params Data.core17.name (Data.core17.body.drop 777) ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwdstaticRange_18 : kwdStaticRange 18 30 := by
  unfold kwdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwdstaticRange_48 : kwdStaticRange 48 30 := by
  unfold kwdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwdstaticRange_78 : kwdStaticRange 78 30 := by
  unfold kwdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwdstaticRange_108 : kwdStaticRange 108 30 := by
  unfold kwdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwdstaticRange_138 : kwdStaticRange 138 30 := by
  unfold kwdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwdstaticRange_168 : kwdStaticRange 168 30 := by
  unfold kwdStaticRange; decide +kernel

end
end LeanVM.Guest
