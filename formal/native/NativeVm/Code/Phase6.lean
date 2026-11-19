module

public import Native.QM

/-!
# Phase 6: `KECCAK`'s validity by GKR

The code of `Model.keccakPhase`; contract `Phase6Ok` (`NativeVm.Code.Contracts`). Not written yet: it fails, so `body` rejects.
-/

@[expose] public section

namespace NativeVm.Code

open Native

/-- **Phase 6**: `KECCAK`'s validity by GKR. -/
def phase6 : Stmt := .fail

end NativeVm.Code
