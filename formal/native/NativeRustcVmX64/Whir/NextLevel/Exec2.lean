module

public import NativeRustcVmX64.Whir.NextLevel.Exec

/-!
# `next_level`: one more fact of a block run (x86-64)

`b23` (after `each_row`, RSP back at `72`) keeps the frame.
-/

namespace NativeRustcVmX64.Whir.Levels.NL

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.NextLevel NativeRustcVmX64.Transcript

set_option Elab.async false

public theorem mid_b23 : MidOk 8176 72 slots (after b23 s56S) = true := by decide +kernel

end NativeRustcVmX64.Whir.Levels.NL
