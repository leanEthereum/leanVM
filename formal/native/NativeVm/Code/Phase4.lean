module

public import Native.QM

/-!
# Phase 4: the table sumcheck

The code of `Model.tablePhase`; contract `Phase4Ok` (`NativeVm.Code.Contracts`). Not written yet: it fails, so `body` rejects.
-/

@[expose] public section

namespace NativeVm.Code

open Native

/-- **Phase 4**: the table sumcheck. -/
def phase4 : Stmt := .fail

end NativeVm.Code
