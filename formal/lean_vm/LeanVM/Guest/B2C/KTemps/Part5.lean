module

public import LeanVM.Guest.B2C.KTempsBase

namespace LeanVM.Guest.B2C

@[expose] public section

set_option maxRecDepth 100000 in
theorem tmpsRange_1009 : TmpsRange 1009 15 := by
  unfold TmpsRange; decide +kernel

set_option maxRecDepth 100000 in
theorem tmpsRange_1024 : TmpsRange 1024 14 := by
  unfold TmpsRange; decide +kernel

set_option maxRecDepth 100000 in
theorem tmpsRange_1038 : TmpsRange 1038 5 := by
  unfold TmpsRange; decide +kernel

end
end LeanVM.Guest.B2C
