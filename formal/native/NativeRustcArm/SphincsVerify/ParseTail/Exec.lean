module

public import NativeRustcArm.SphincsVerify.ParseTail.Loop
public meta import NativeRustcArm.Code.Sphincs.SphincsVerify
public meta import NativeRustcArm.SphincsVerify.ParseTail.Glue

/-!
# The parse's tail: its blocks run by the executor

Each block of `b16 .. b44` from its start state (`fs known`, or `loopS D` for the copy loops), its
summary as a kernel-checked literal (`run_b<k>`).
-/

namespace NativeRustcArm.SphincsVerifyProof.ParseTail

open NativeRustcArm.Sym NativeRustcArm.Sphincs.SphincsVerify

set_option Elab.async false

public section

sym_block run_b16 := exec b16 (fs [])
sym_block run_b17 := exec b17 (fs [])
sym_block run_b18 := exec b18 (loopS .X10)
sym_block run_b19 := exec b19 (fs [])
sym_block run_b20 := exec b20 (fs [])
sym_block run_b21 := exec b21 (fs [])
sym_block run_b22 := exec b22 (fs [])
sym_block run_b23 := exec b23 (fs [])
sym_block run_b24 := exec b24 (fs [])
sym_block run_b25 := exec b25 (fs [(.X25, .ptr 0 468)])
sym_block run_b26 := exec b26 (loopS .X24)
sym_block run_b27 := exec b27 (fs [])
sym_block run_b28 := exec b28 (fs [(.X20, .ptr 0 468), (.X23, .ptr 0 15984)])
sym_block run_b29 := exec b29 (fs [])
sym_block run_b30 := exec b30 (fs [])
sym_block run_b31 := exec b31 (fs [])
sym_block run_b32 := exec b32 (fs [])
sym_block run_b33 := exec b33 (fs [])
sym_block run_b34 := exec b34 (loopS .X25)
sym_block run_b35 := exec b35 (fs [])
sym_block run_b36 := exec b36 (fs [])
sym_block run_b37 := exec b37 (fs [])
sym_block run_b38 := exec b38 (fs [])
sym_block run_b39 := exec b39 (fs [])
sym_block run_b40 := exec b40 (fs [(.X20, .ptr 0 468)])
sym_block run_b41 := exec b41 (fs [(.X23, .ptr 0 8244)])
sym_block run_b42 := exec b42 (fs [(.X23, .ptr 0 8244)])
sym_block run_b43 := exec b43 (fs [(.X23, .ptr 0 8244)])
sym_block run_b44 := exec b44 (fs [(.X23, .ptr 0 8244), (.X20, .lit 4224)])

end

end NativeRustcArm.SphincsVerifyProof.ParseTail
