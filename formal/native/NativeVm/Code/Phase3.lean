module

public import Native.QM

/-!
# Phase 3: the bus

The code of `Model.verifyBusBalance`; contract `Phase3Ok` (`NativeVm.Code.Contracts`). Not written yet: it fails, so `body` rejects.
-/

@[expose] public section

namespace NativeVm.Code

open Native

/-- **Phase 3**: the bus. -/
def phase3 : Stmt := .fail

end NativeVm.Code
