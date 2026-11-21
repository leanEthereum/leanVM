module

import NativeArm.Emit
import Native.Xmss.Code
import Native.Sphincs.Code

/-!
# `emit-arm`

`lake exe emit-arm xmss FILE.S` (or `sphincs`) writes a verifier's AArch64 machine code,
`NativeArm.Compile.program body onFail`, as an assembly file exporting `xmss_verify` (or
`sphincs_verify`), `uint64_t verify(uint64_t *ctx)` in AAPCS64 (`NativeArm.emit`).
-/

open Native

public def main (args : List String) : IO UInt32 := do
  match args with
  | ["xmss", path] =>
    IO.FS.writeFile path <|
      NativeArm.emit "xmss_verify" XmssVerifier.body XmssVerifier.onFail
    return 0
  | ["sphincs", path] =>
    IO.FS.writeFile path <|
      NativeArm.emit "sphincs_verify" SphincsVerifier.body SphincsVerifier.onFail
    return 0
  | _ =>
    IO.eprintln "usage: emit-arm xmss|sphincs FILE.S"
    return 2
