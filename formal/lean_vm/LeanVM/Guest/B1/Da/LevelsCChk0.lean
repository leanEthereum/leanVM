module

public import LeanVM.Guest.B1.Da.LevelsCDefs

namespace LeanVM.Guest.B1.Da

@[expose] public section

set_option maxRecDepth 100000 in
theorem dlc_ok0 : dlCEntryOk 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem dlc_ok1 : dlCEntryOk 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem dlc_ok2 : dlCEntryOk 2 = true := by decide +kernel

end
end LeanVM.Guest.B1.Da
