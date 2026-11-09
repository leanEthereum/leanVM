module

public import LeanVM.Guest.B1.Da.LevelsCDefs

namespace LeanVM.Guest.B1.Da

@[expose] public section

set_option maxRecDepth 100000 in
theorem dlc_ok10 : dlCEntryOk 10 = true := by decide +kernel

end
end LeanVM.Guest.B1.Da
