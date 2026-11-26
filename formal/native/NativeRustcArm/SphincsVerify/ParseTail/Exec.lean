module

public import NativeRustcArm.SphincsVerify.ParseTail.Loop
public meta import NativeRustcArm.Code.Sphincs.SphincsVerify
public meta import NativeRustcArm.SphincsVerify.ParseTail.Glue

/-!
# The parse's tail: its blocks run by the executor

Each block of `b7 .. b35` from its start state (`fs known`, or `loopS D` for the copy loops), its
summary as a kernel-checked literal (`run_b<k>`).
-/

namespace NativeRustcArm.SphincsVerifyProof.ParseTail

open NativeRustcArm.Sym NativeRustcArm.Sphincs.SphincsVerify

set_option Elab.async false

public section

sym_block run_b7 := exec b7 (fs [])
sym_block run_b8 := exec b8 (fs [(.X19, .ptr 1 0)])
sym_block run_b9 := exec b9 (loopS .X10)
sym_block run_b10 := exec b10 (fs [])
sym_block run_b11 := exec b11 (fs [(.X19, .ptr 1 0)])
sym_block run_b12 := exec b12 (fs [])
sym_block run_b13 := exec b13 (fs [])
sym_block run_b14 := exec b14 (fs [])
sym_block run_b15 := exec b15 (fs [])
sym_block run_b16 := exec b16 (fs [(.X19, .ptr 1 0)])
sym_block run_b17 := exec b17 (loopS .X26)
sym_block run_b18 := exec b18 (fs [])
sym_block run_b19 := exec b19 (fs [(.X19, .ptr 1 0), (.X25, .ptr 0 8224)])
sym_block run_b20 := exec b20 (fs [])
sym_block run_b21 := exec b21 (fs [])
sym_block run_b22 := exec b22 (fs [])
sym_block run_b23 := exec b23 (fs [])
sym_block run_b24 := exec b24 (fs [(.X19, .ptr 1 0)])
sym_block run_b25 := exec b25 (loopS .X28)
sym_block run_b26 := exec b26 (fs [])
sym_block run_b27 := exec b27 (fs [(.X19, .ptr 1 0)])
sym_block run_b28 := exec b28 (fs [])
sym_block run_b29 := exec b29 (fs [])
sym_block run_b30 := exec b30 (fs [])
sym_block run_b31 := exec b31 (fs [(.X22, .ptr 0 484)])
sym_block run_b32 := exec b32 (fs [(.X25, .ptr 0 484)])
sym_block run_b33 := exec b33 (fs [(.X25, .ptr 0 484)])
sym_block run_b34 := exec b34 (fs [(.X25, .ptr 0 484)])
sym_block run_b35 := exec b35 (fs [(.X25, .ptr 0 484), (.X22, .lit 4224)])

end

end NativeRustcArm.SphincsVerifyProof.ParseTail
