module

public import LeanVM.Guest.Memory.GuestCntOM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwomstaticRange_188 : kwomStaticRange 188 1 := by
  unfold kwomStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwomstaticRange_189 : kwomStaticRange 189 1 := by
  unfold kwomStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwomstaticRange_190 : kwomStaticRange 190 1 := by
  unfold kwomStaticRange; decide +kernel

end
end LeanVM.Guest
