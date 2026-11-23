module

public import NativeRustcArm.SphincsVerify.Parse.Glue
public meta import NativeRustcArm.Code.Sphincs.SphincsVerify

/-!
# The parse, part 2: the words' blocks run by the executor (`b3 .. b11`)

The loops copy 32 bytes a turn, each turn run from a state whose region 0 is the turn's 32
destination bytes in the frame and region 1 its 4 source words:
- `b4` (`loop4S`): X9 the counter, the source `X8 + X9 - 4200`, the destination `X20 + X9 - 4224`;
- `b6`, `b10` (`loopPS`): X8 the source's end (`ptr 1 24`), the destination `X11 + X10`;
- `b8` (`loop8S`): X8 the counter, the source `X9 + X8 - 24`, the destination `X10 + X8 + 5400`.
The blocks between them (`b5`, `b7`, `b9`, `b11`, `straightS`) run with region 0 the frame (SP its
base) and region 1 the input (X19 1024 below it). `b3` (`regsS`) touches no memory.
-/

namespace NativeRustcArm.SphincsVerifyProof.Parse

open NativeRustcArm.Sym NativeRustcArm.Sphincs.SphincsVerify

@[expose] public section

/-- No memory. -/
def regsS : SState := init []

/-- `b4`'s turn. -/
def loop4S : SState := init [(32, false), (32, false)] .sp [] [] []
  [(.bin .add .W64 (.reg .X20) (.reg .X9), 0, -4224), (.bin .add .W64 (.reg .X8) (.reg .X9), 1, -4200)]

/-- `b6`'s and `b10`'s turn. -/
def loopPS : SState := init [(32, false), (32, false)] .sp [(.X8, .ptr 1 24)] [] []
  [(.bin .add .W64 (.reg .X11) (.reg .X10), 0, 0)]

/-- `b8`'s turn. -/
def loop8S : SState := init [(32, false), (32, false)] .sp [] [] []
  [(.bin .add .W64 (.reg .X10) (.reg .X8), 0, -5400), (.bin .add .W64 (.reg .X9) (.reg .X8), 1, 24)]

/-- `b5`, `b7`, `b9`, `b11`: the frame and the input. -/
def straightS : SState :=
  init [(29376, true), (7816, false)] (.ptr 0 0)
    [(.X19, .ptr 1 (-1024)), (.X20, .ptr 0 468), (.X25, .ptr 0 4564), (.X29, .ptr 0 29280)]

end

set_option Elab.async false

sym_block run_b3 := exec b3 regsS
sym_block run_b4 := exec b4 loop4S
sym_block run_b5 := exec b5 straightS
sym_block run_b6 := exec b6 loopPS
sym_block run_b7 := exec b7 straightS
sym_block run_b8 := exec b8 loop8S
sym_block run_b9 := exec b9 straightS
sym_block run_b10 := exec b10 loopPS
sym_block run_b11 := exec b11 straightS

end NativeRustcArm.SphincsVerifyProof.Parse
