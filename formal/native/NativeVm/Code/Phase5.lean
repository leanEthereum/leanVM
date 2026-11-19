module

public import Native.QM

/-!
# Phase 5: the public input

The code of `Model.publicInputPhase`; contract `Phase5Ok` (`NativeVm.Code.Contracts`). Not written yet: it fails, so `body` rejects.
-/

@[expose] public section

namespace NativeVm.Code

open Native

/-- **Phase 5**: the public input. -/
def phase5 : Stmt := .fail

end NativeVm.Code
