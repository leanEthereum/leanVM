module

public import NativeRustcVmArm.Whir.Common
public import NativeRustcVmArm.Code.Vm.QueryBits
public meta import NativeRustcVmArm.Code.Vm.QueryBits
public meta import NativeRustcVmArm.Whir.Common

/-!
# `query_bits`'s blocks, run by the symbolic executor

No region: every block from the entry's registers (`entryS`), along the four paths: `shift = 0`
(`b0`, `b3`), `0 < shift < 64` (`b0`, `b1`, `b2`, `b3`), `64 ≤ shift < 128` (`b0`, `b1`, `b4`,
`b5`), `128 ≤ shift` (`b0`, `b1`, `b4`, `b6`).
-/

namespace NativeRustcVmArm.Whir.QueryBits

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.QueryBits

@[expose] public section

/-- At the entry: no region, every register its atom. -/
def entryS : SState := init [] .sp

/-- After `b0`'s test. -/
def s1 : SState := after b0 entryS
/-- After `b1`'s test. -/
def s2 : SState := after b1 s1
/-- After `b4`'s test. -/
def s4 : SState := after b4 s2

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 s1
sym_block run_b2 := exec b2 s2
sym_block run_b3z := exec b3 s1
sym_block run_b3 := exec b3 (after b2 s2)
sym_block run_b4 := exec b4 s2
sym_block run_b5 := exec b5 s4
sym_block run_b6 := exec b6 s4

end NativeRustcVmArm.Whir.QueryBits
