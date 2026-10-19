module

public import LeanVM.Guest.Memory.GuestCntB.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwbsplit_17_512 : noTopRet ((Data.core17.body.drop 512).take 1) = true ∧
    blockR (kwblookJ 17) (kwbomLookJ 17) false [] Data.core17.params Data.core17.name ((Data.core17.body.drop 512).take 1) ([], []) = some (⟨7, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwbsplit_17_513 : noTopRet ((Data.core17.body.drop 513).take 264) = true ∧
    blockR (kwblookJ 17) (kwbomLookJ 17) false [] Data.core17.params Data.core17.name ((Data.core17.body.drop 513).take 264) ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwbsplit_17_777 : blockR (kwblookJ 17) (kwbomLookJ 17) false [] Data.core17.params Data.core17.name (Data.core17.body.drop 777) ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwbstaticRange_18 : kwbStaticRange 18 30 := by
  unfold kwbStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwbstaticRange_48 : kwbStaticRange 48 30 := by
  unfold kwbStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwbstaticRange_78 : kwbStaticRange 78 30 := by
  unfold kwbStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwbstaticRange_108 : kwbStaticRange 108 30 := by
  unfold kwbStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwbstaticRange_138 : kwbStaticRange 138 30 := by
  unfold kwbStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwbstaticRange_168 : kwbStaticRange 168 30 := by
  unfold kwbStaticRange; decide +kernel

end
end LeanVM.Guest
