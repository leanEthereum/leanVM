module

public import NativeVm.Transcript.Layout
public import NativeVm.Model.Verify
public import NativeVm.Wire.Layout

/-!
# The Rust entry's fixed memory sizes
-/

@[expose] public section

namespace NativeVm.Entry

/-- The context words read by `leanvm_verify`. -/
def ctxWords : Nat := 12

/-- `WORK_WORDS` in `rustc/vm/src/lib.rs`. -/
def workWords : Nat := 61944

end NativeVm.Entry
