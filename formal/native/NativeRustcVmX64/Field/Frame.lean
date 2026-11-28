module

public import NativeRustcX64.Sym

/-!
# A function's frame as a symbolic region (x86-64)

Region 0 is the `F` bytes below the entry's RSP and the return address at RSP. `frameS F`: the
symbolic state at a function's entry, RSP at the region's offset `F`; `midS F`: between the
prologue and the epilogue of a function whose `F` bytes end in its pushes above the 8-byte slot
its calls push their return address in, RSP at the region's offset `8`.
-/

namespace NativeRustcVmX64.Field

open NativeRustcX64 NativeRustcX64.Sym

/-- At a function's entry: the `F` bytes below RSP and the return address (region 0), RSP at
offset `F`. -/
@[expose] public def frameS (F : Nat) : SState := init [F + 8] [(.rsp, .ptr 0 F)]

/-- Between the prologue and the epilogue: RSP at offset `8` of the region. -/
@[expose] public def midS (F : Nat) : SState := init [F + 8] [(.rsp, .ptr 0 8)]

end NativeRustcVmX64.Field
