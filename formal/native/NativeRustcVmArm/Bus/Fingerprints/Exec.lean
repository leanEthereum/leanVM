module

public import NativeRustcArm.Sym
public import NativeRustcVmArm.Code.Vm.Fingerprints
public meta import NativeRustcVmArm.Code.Vm.Fingerprints

/-!
# `fingerprints`' blocks, run by the symbolic executor

Region 0 the 320-byte frame (at the entry with the 48 bytes of stack arguments above it). Block
`k` runs from `s<k>`: `b3` reads the memory's two elements (region 1, X28), `b7` writes the three
fingerprints (region 1, X20).
-/

namespace NativeRustcVmArm.Bus.Fingerprints

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.Fingerprints

@[expose] public section

/-- At the entry: the frame and the stack arguments (region 0), SP 320 bytes in. -/
def s0 : SState := init [(368, true)] (.ptr 0 320)
/-- In the frame, SP at its base. -/
def sF : SState := init [(320, true)] (.ptr 0 0)
/-- In the frame, the memory's elements at X28 (region 1). -/
def s3 : SState := init [(320, true), (32, false)] (.ptr 0 0) [(.X28, .ptr 1 0)]
/-- In the frame, the output at X20 (region 1). -/
def s7 : SState := init [(320, true), (48, false)] (.ptr 0 0) [(.X20, .ptr 1 0)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 s0
sym_block run_b1 := exec b1 sF
sym_block run_b2 := exec b2 sF
sym_block run_b3 := exec b3 s3
sym_block run_b4 := exec b4 sF
sym_block run_b5 := exec b5 sF
sym_block run_b6 := exec b6 sF
sym_block run_b7 := exec b7 s7

end NativeRustcVmArm.Bus.Fingerprints
