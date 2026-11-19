module

public import Native.QM

/-!
# Phase 7: ring switching and the stacked opening

The code of `phase7M` (`ringSwitch`, `verifyStackedOpening`); contract `Phase7Ok` (`NativeVm.Code.Contracts`). Not written yet: it fails, so `body` rejects.
-/

@[expose] public section

namespace NativeVm.Code

open Native

/-- **Phase 7**: ring switching and the stacked opening. -/
def phase7 : Stmt := .fail

end NativeVm.Code
