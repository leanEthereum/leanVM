module

public import NativeRustcArm.Code.Common.Memcpy
public import NativeRustcArm.Code.Common.Memset
public import NativeRustcArm.Code.Sphincs.SphincsVerify
public import NativeRustcArm.Code.Common.KeccakF
public import NativeRustcArm.Code.Common.Update
public import NativeRustcArm.Code.Common.Finalize
public meta import RustcIngest.Arm

ingest_arm "NativeRustcArm" "NativeRustcArm/Code/Sphincs.lean"
