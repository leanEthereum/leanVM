module

public import Native.QM

/-!
# Phase 2: the stack's commitment and its out-of-domain claim

The code of `phase2M` (`commitStack`, `readOod`); contract `Phase2Ok` (`NativeVm.Code.Contracts`). Not written yet: it fails, so `body` rejects.
-/

@[expose] public section

namespace NativeVm.Code

open Native

/-- **Phase 2**: the stack's commitment and its out-of-domain claim. -/
def phase2 : Stmt := .fail

end NativeVm.Code
