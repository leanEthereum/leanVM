module

public import NativeRustcArm.SphincsVerify.Parse.Glue
public meta import NativeRustcArm.Code.Sphincs.SphincsVerify

/-!
# The parse: the openings' blocks run by the executor (`b3 .. b6`)

A turn `c` of the openings' loop runs with region 0 the frame from its byte 480 (16-byte aligned;
SP its byte `-480`) and region 1 the raw opening `c`, 176 bytes at `r.sigPtr + 16 + 176 c`
(`openS`, `open4S`: X28 = X23 + X24 points 4144 bytes below it); `b5` and `b6` touch no memory
(`regsS'`).
-/

namespace NativeRustcArm.SphincsVerifyProof.Parse

open NativeRustcArm.Sym NativeRustcArm.Sphincs.SphincsVerify

@[expose] public section

/-- `b3`: the frame from 480, the raw opening; X27 the frame's 19008, X23 + X24 the opening's
address less 4144. -/
def openS : SState := init [(21136, true), (176, false)] (.ptr 0 (-480)) [(.X27, .ptr 0 18528)]
  [] [] [(.bin .add .W64 (.reg .X23) (.reg .X24), 1, -4144)]

/-- `b4`: as `b3`, X22 the frame's 484, X28 the opening's address less 4144. -/
def open4S : SState := init [(21136, true), (176, false)] (.ptr 0 (-480)) [(.X22, .ptr 0 4)]
  [] [] [(.reg .X28, 1, -4144)]

/-- No memory, SP an atom. -/
def regsS' : SState := init []

end

set_option Elab.async false

sym_block run_b3 := exec b3 openS
sym_block run_b4 := exec b4 open4S
sym_block run_b5 := exec b5 regsS'
sym_block run_b6 := exec b6 regsS'

end NativeRustcArm.SphincsVerifyProof.Parse
