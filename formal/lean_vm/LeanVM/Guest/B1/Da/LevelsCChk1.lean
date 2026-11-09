module

public import LeanVM.Guest.B1.Da.LevelsCDefs

namespace LeanVM.Guest.B1.Da

@[expose] public section

set_option maxRecDepth 100000 in
theorem dlc_ok3 : dlCEntryOk 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem dlc_ok4 : dlCEntryOk 4 = true := by decide +kernel

end
end LeanVM.Guest.B1.Da
