module

public import NativeRustcArm.Sym

/-!
# A function's frame as a symbolic region

`frameS F`: the symbolic state at the entry of a function that works in the `F` bytes below SP,
region 0 those bytes, SP their end; `epiS F` at its epilogue, SP their start; `regS` for blocks
without memory accesses.
-/

namespace NativeRustcVmArm.Field

open NativeRustcArm.Sym

/-- At a function's entry: its `F`-byte frame below SP (region 0, 16-byte aligned), SP its end. -/
@[expose] public def frameS (F : Nat) : SState := init [(F, true)] (.ptr 0 F)

/-- At a function's epilogue: its `F`-byte frame from SP (region 0). -/
@[expose] public def epiS (F : Nat) : SState := init [(F, true)] (.ptr 0 0)

/-- Registers only: a block without memory accesses. -/
@[expose] public def regS : SState := init [] .sp

end NativeRustcVmArm.Field
