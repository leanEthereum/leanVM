module

public import Native.QM

/-!
# Phase 1: the announced sizes and the layout

The code of `Model.readAnnouncedSizes`; contract `Phase1Ok` (`NativeVm.Code.Contracts`). Not written yet: it fails, so `body` rejects.
-/

@[expose] public section

namespace NativeVm.Code

open Native

/-- **Phase 1**: the announced sizes and the layout. -/
def phase1 : Stmt := .fail

end NativeVm.Code
