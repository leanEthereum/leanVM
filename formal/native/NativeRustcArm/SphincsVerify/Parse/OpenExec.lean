module

public import NativeRustcArm.SphincsVerify.Parse.Glue
public meta import NativeRustcArm.Code.Sphincs.SphincsVerify

/-!
# The parse, part 6: the openings' blocks run by the executor (`b12 .. b15`)

A turn `c` of the openings' loop runs with region 0 the frame from its byte 8240 (16-byte
aligned; SP its byte `-8240`) and region 1 the raw opening `c`, 176 bytes at the frame's byte
`484 + 176 c` (`openS`, `open13S`: X27 = X23 + X24 points 4144 bytes below it); `b14` and `b15`
touch no memory (`regsS'`).
-/

namespace NativeRustcArm.SphincsVerifyProof.Parse

open NativeRustcArm.Sym NativeRustcArm.Sphincs.SphincsVerify

@[expose] public section

/-- `b12`: the frame from 8240, the raw opening; X21 the frame's 26768, X23 + X24 the opening's
address less 4144. -/
def openS : SState := init [(21136, true), (176, false)] (.ptr 0 (-8240)) [(.X21, .ptr 0 18528)]
  [] [] [(.bin .add .W64 (.reg .X23) (.reg .X24), 1, -4144)]

/-- `b13`: as `b12`, X22 the frame's 8244, X27 the opening's address less 4144. -/
def open13S : SState := init [(21136, true), (176, false)] (.ptr 0 (-8240)) [(.X22, .ptr 0 4)]
  [] [] [(.reg .X27, 1, -4144)]

/-- No memory, SP an atom. -/
def regsS' : SState := init []

end

set_option Elab.async false

sym_block run_b12 := exec b12 openS
sym_block run_b13 := exec b13 open13S
sym_block run_b14 := exec b14 regsS'
sym_block run_b15 := exec b15 regsS'

end NativeRustcArm.SphincsVerifyProof.Parse
