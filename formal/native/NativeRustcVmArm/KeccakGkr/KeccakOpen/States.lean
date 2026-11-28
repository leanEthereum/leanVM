module

public import NativeRustcArm.Sym

/-!
# `keccak_open`'s symbolic states

The states its blocks run from. The prologue's stores (`frS`) with the 2224-byte frame below SP
as region 0; the blocks reading the stack arguments (`argS`) with the frame and the 32 bytes of
arguments from SP. The blocks around the fold (`pS known`): region 0 the frame, region 1 the slot
point (96 bytes), region 2 the rows, the frame's word `40` (the slot's address) an alias of
region 1, the registers `known` (`P` the rows, `A0`/`B0` the frame's two row buffers, `V0`/`V1`
the round's challenge, variables `0`, `1`; a looped round's row `i` and `1024 i`, variables `2`,
`3`; the lists `k…`, by the block they start). An inner loop's loads (`loS`) with the two buffer
elements as regions 0 and 1; its stores (`dstS`, `lstS`) with the row's element as region 0; the
last round's (`lo5S`, `st5S`). The result's stores (`outS`, `resS`) and the epilogue (`epiS`).
-/

namespace NativeRustcVmArm.KeccakGkr.KeccakOpen

open NativeRustcArm NativeRustcArm.Sym

@[expose] public section

/-- The rows. -/
def P : Sym := .ptr 2 0
/-- The first row buffer. -/
def A0 : Sym := .ptr 0 80
/-- The second row buffer. -/
def B0 : Sym := .ptr 0 1104
/-- The challenge's low limb. -/
def V0 : Sym := .var 0
/-- The challenge's high limb. -/
def V1 : Sym := .var 1
/-- The slot point. -/
def SL : Sym := .ptr 1 0

/-- The prologue's stores: region 0 the frame below SP. -/
def frS : SState := init [(2224, true)] (.ptr 0 2224)
/-- The stack arguments: region 0 the frame from SP and the 32 bytes above it. -/
def argS : SState := init [(2256, true)] (.ptr 0 0)
/-- No regions. -/
def regsS : SState := init [] .sp
/-- `b4`: the frame, the slot point, the rows; X28 the slot, X29 the rows. -/
def b4S : SState :=
  init [(2224, true), (96, false), (65536, false)] (.ptr 0 0) [(.X28, SL), (.X29, P)]
/-- Around the fold: the frame, the slot point, the rows, `known` registers. -/
def pS (known : List (XReg × Sym)) : SState :=
  init [(2224, true), (96, false), (65536, false)] (.ptr 0 0) known [] [] [(.load 0 40 8, 1, 0)]
/-- The loads of an inner loop: the elements at `A + CT` and `B + CT`. -/
def loS (A B CT : XReg) : SState :=
  init [(16, false), (16, false)] .sp [] [] []
    [(.bin .add .W64 (.reg A) (.reg CT), 0, 0), (.bin .add .W64 (.reg B) (.reg CT), 1, 0)]
/-- The stores of an unrolled round's inner loop: from X21, `C + 16` bytes. -/
def dstS (C : Nat) : SState := init [(C + 16, false)] .sp [] [] [] [(.reg .X21, 0, 0)]
/-- The stores of a looped round's inner loop: the element at X24 + `OC`. -/
def lstS (OC : XReg) : SState :=
  init [(16, false)] .sp [] [] []
    [(.bin .add .W64 (.reg .X24) (.un (.memExtend ⟨.UXTX, .E0⟩) .W64 (.reg OC)), 0, 0),
      (.bin .add .W64 (.reg .X24) (.reg OC), 0, 0)]
/-- The last round's loads: the elements at X25 - 8 and X24 - 8. -/
def lo5S : SState :=
  init [(16, false), (16, false)] .sp [] [] [] [(.reg .X25, 0, 8), (.reg .X24, 1, 8)]
/-- The last round's stores: the element at X21 - 8. -/
def st5S : SState := init [(16, false)] .sp [] [] [] [(.reg .X21, 0, 8)]
/-- The result's value: the frame, the result (24 bytes) at the frame's word `32`. -/
def outS : SState := init [(2224, true), (24, false)] (.ptr 0 0) [] [] [] [(.load 0 32 8, 1, 0)]
/-- The result's tag: the result at X19. -/
def resS : SState := init [(24, false)] .sp [(.X19, .ptr 0 0)]
/-- The epilogue: the frame. -/
def epiS : SState := init [(2224, true)] (.ptr 0 0)

/-! ## Known registers, by the block they start -/

/-- A looped round's head: the row `i` (variable `2`), `1024 i` (variable `3`). -/
def kO : List (XReg × Sym) :=
  [(.X29, P), (.X27, A0), (.X28, B0), (.X22, V0), (.X23, V1), (.X26, .var 2), (.X25, .var 3)]
/-- A looped round's source rows. -/
def src0 : Sym := .bin .add .W64 P (.un (.shift .LSL 11) .W64 (.var 2))
/-- A looped round's head, the source rows' address in X24. -/
def kM : List (XReg × Sym) :=
  [(.X22, V0), (.X23, V1), (.X24, src0), (.X25, .var 3), (.X26, .var 2), (.X27, A0), (.X28, B0),
    (.X29, P)]
/-- After a looped round's inner loop. -/
def kOE : List (XReg × Sym) :=
  [(.X27, A0), (.X28, B0), (.X22, V0), (.X23, V1), (.X26, .var 2), (.X25, .var 3)]
/-- The rows alone. -/
def kP : List (XReg × Sym) := [(.X29, P)]
def k19 : List (XReg × Sym) := [(.X22, V0), (.X23, V1), (.X24, A0), (.X29, P)]
def k20 : List (XReg × Sym) := [(.X22, V0), (.X23, V1), (.X24, A0), (.X25, B0), (.X29, P)]
def k29 : List (XReg × Sym) := [(.X22, V0), (.X23, V1), (.X24, A0), (.X25, A0), (.X29, P)]
def k30 : List (XReg × Sym) :=
  [(.X22, V0), (.X23, V1), (.X24, .lit 5120), (.X25, A0), (.X26, B0), (.X29, P)]
def k34 : List (XReg × Sym) :=
  [(.X22, V0), (.X23, V1), (.X24, .lit 5120), (.X25, A0), (.X26, B0), (.X27, A0), (.X29, P)]
def k35 : List (XReg × Sym) :=
  [(.X22, V0), (.X23, V1), (.X24, .lit 5120), (.X25, A0), (.X26, .lit 7168), (.X27, A0),
    (.X28, B0), (.X29, P)]
def k38 : List (XReg × Sym) :=
  [(.X22, V0), (.X23, V1), (.X24, .lit 5120), (.X25, P), (.X26, .lit 7168), (.X27, A0),
    (.X28, B0)]
/-- Round 3's start: `k38` without the challenge. -/
def k58 : List (XReg × Sym) :=
  [(.X24, .lit 5120), (.X25, P), (.X26, .lit 7168), (.X27, A0), (.X28, B0)]
def k70 : List (XReg × Sym) :=
  [(.X22, V0), (.X23, V1), (.X24, B0), (.X25, P), (.X26, .lit 7168), (.X27, A0), (.X28, B0)]
def k73 : List (XReg × Sym) :=
  [(.X22, V0), (.X23, V1), (.X24, B0), (.X25, P), (.X26, .lit 7168), (.X27, A0), (.X29, P)]
def k74 : List (XReg × Sym) :=
  [(.X22, V0), (.X23, V1), (.X24, A0), (.X25, P), (.X26, .lit 7168), (.X27, A0), (.X29, P)]
def k75 : List (XReg × Sym) :=
  [(.X22, V0), (.X23, V1), (.X24, A0), (.X25, B0), (.X26, .lit 7168), (.X27, A0), (.X29, P)]
/-- Round 4's start: after round 3 without the challenge. -/
def k78 : List (XReg × Sym) := [(.X24, A0), (.X25, B0), (.X27, A0), (.X29, P)]
def k79 : List (XReg × Sym) :=
  [(.X22, V0), (.X23, V1), (.X24, A0), (.X25, B0), (.X27, SL), (.X29, P)]
/-- Round 5's start: after round 4 without the challenge. -/
def k88 : List (XReg × Sym) := [(.X24, A0), (.X25, B0), (.X27, SL), (.X29, P)]
def k89 : List (XReg × Sym) :=
  [(.X19, A0), (.X20, V1), (.X22, V0), (.X23, .lit 1024), (.X24, A0), (.X25, B0), (.X27, SL),
    (.X29, P)]
def k90 : List (XReg × Sym) :=
  [(.X19, A0), (.X20, V1), (.X22, V0), (.X23, .lit 1024), (.X24, B0), (.X25, B0), (.X27, SL),
    (.X29, P)]

end

end NativeRustcVmArm.KeccakGkr.KeccakOpen
