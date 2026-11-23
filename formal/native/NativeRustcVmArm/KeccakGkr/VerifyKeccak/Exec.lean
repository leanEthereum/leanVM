module

public import NativeRustcArm.Sym
public import NativeRustcVmArm.Code.Vm.VerifyKeccak
public meta import NativeRustcVmArm.Code.Vm.VerifyKeccak

/-!
# `verify_keccak`'s blocks, run by the symbolic executor

Region 0 the 3360-byte frame: below SP at the entry (`entryS`, `b0`), from SP between the calls
(`midS`). `rowS` (`b44`): region 1 the slot rows' first element less 1024 bytes, X28 its base.
`outS` (`b66`): region 1 the `KeccakOutW`, its address the frame's word at 72.
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyKeccak

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.VerifyKeccak

@[expose] public section

/-- At the entry: the frame below SP. -/
def entryS : SState := init [(3360, true)] (.ptr 0 3360)
/-- Between the calls: the frame from SP. -/
def midS : SState := init [(3360, true)] (.ptr 0 0)
/-- At the check of the committed outputs' opening: X28 region 1's base. -/
def rowS : SState := init [(3360, true), (1040, false)] (.ptr 0 0) [(.X28, .ptr 1 0)]
/-- At the output point's reset: the `KeccakOutW` region 1, its address at frame offset 72. -/
def outS : SState := init [(3360, true), (1608, false)] (.ptr 0 0) [] [] [] [(.load 0 72 8, 1, 0)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 midS
sym_block run_b2 := exec b2 midS
sym_block run_b3 := exec b3 midS
sym_block run_b4 := exec b4 midS
sym_block run_b5 := exec b5 midS
sym_block run_b6 := exec b6 midS
sym_block run_b7 := exec b7 midS
sym_block run_b8 := exec b8 midS
sym_block run_b9 := exec b9 midS
sym_block run_b10 := exec b10 midS
sym_block run_b11 := exec b11 midS
sym_block run_b12 := exec b12 midS
sym_block run_b13 := exec b13 midS
sym_block run_b14 := exec b14 midS
sym_block run_b15 := exec b15 midS
sym_block run_b16 := exec b16 midS
sym_block run_b17 := exec b17 midS
sym_block run_b18 := exec b18 midS
sym_block run_b19 := exec b19 midS
sym_block run_b20 := exec b20 midS
sym_block run_b21 := exec b21 midS
sym_block run_b22 := exec b22 midS
sym_block run_b23 := exec b23 midS
sym_block run_b24 := exec b24 midS
sym_block run_b25 := exec b25 midS
sym_block run_b26 := exec b26 midS
sym_block run_b27 := exec b27 midS
sym_block run_b28 := exec b28 midS
sym_block run_b29 := exec b29 midS
sym_block run_b30 := exec b30 midS
sym_block run_b31 := exec b31 midS
sym_block run_b32 := exec b32 midS
sym_block run_b33 := exec b33 midS
sym_block run_b34 := exec b34 midS
sym_block run_b35 := exec b35 midS
sym_block run_b36 := exec b36 midS
sym_block run_b37 := exec b37 midS
sym_block run_b38 := exec b38 midS
sym_block run_b39 := exec b39 midS
sym_block run_b40 := exec b40 midS
sym_block run_b41 := exec b41 midS
sym_block run_b42 := exec b42 midS
sym_block run_b43 := exec b43 midS
sym_block run_b44 := exec b44 rowS
sym_block run_b45 := exec b45 midS
sym_block run_b46 := exec b46 midS
sym_block run_b47 := exec b47 midS
sym_block run_b48 := exec b48 midS
sym_block run_b49 := exec b49 midS
sym_block run_b50 := exec b50 midS
sym_block run_b51 := exec b51 midS
sym_block run_b52 := exec b52 midS
sym_block run_b53 := exec b53 midS
sym_block run_b54 := exec b54 midS
sym_block run_b55 := exec b55 midS
sym_block run_b56 := exec b56 midS
sym_block run_b57 := exec b57 midS
sym_block run_b58 := exec b58 midS
sym_block run_b59 := exec b59 midS
sym_block run_b60 := exec b60 midS
sym_block run_b61 := exec b61 midS
sym_block run_b62 := exec b62 midS
sym_block run_b63 := exec b63 midS
sym_block run_b64 := exec b64 midS
sym_block run_b65 := exec b65 midS
sym_block run_b66 := exec b66 outS
sym_block run_b67 := exec b67 midS
sym_block run_b68 := exec b68 midS
sym_block run_b69 := exec b69 midS
sym_block run_b70 := exec b70 midS
sym_block run_b71 := exec b71 midS
sym_block run_b72 := exec b72 midS
sym_block run_b73 := exec b73 midS

end NativeRustcVmArm.KeccakGkr.VerifyKeccak
