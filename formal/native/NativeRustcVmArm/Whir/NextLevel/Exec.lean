module

public import NativeRustcVmArm.Transcript.FrameRun
public import NativeRustcVmArm.Code.Vm.NextLevel
public meta import NativeRustcVmArm.Code.Vm.NextLevel
public meta import NativeRustcVmArm.Transcript.FrameRun

/-!
# `next_level`'s blocks, run by the symbolic executor

Region 0 the 8192-byte frame (X29, X30, X28 to X19 at `8096` to `8192`). Its words: `64`, `72` the
challenge `λ` (`c1`, `c0`); `80` the out-of-domain value's `c0` (`c1` in X25); `88` `μ`; `96`
to `192` the high part (`read_scalars`' output); `192` the out-of-domain point (`Buf<EW, 30>`,
filled by `sample_challenges` at `200`); `680` `read_scalar`'s output, then the query weights
(`Buf<EW, 230>`, items from `688`, `powers`' output); `4368` a zeroed scratch (`b17`'s loop,
`memcpy`'d over the weights), then `query_openings`' `Option<Rows>`, then `each_row`'s closure
(48 bytes); `8048` the rows (32 bytes); `8080` `batched`; `0` to `48` `glue_level`'s stack
arguments.

`entryS` at `b0` (region 1 the level); `fS` the frame alone; `levelS` with the level at X28; `bufS`
with `WhirW` at X19 (X28 its query buffer); `zeroS` the zeroing loop's 64 bytes at `X10 + X9`;
`rowsS` with `WhirW` at X19 (X24 at `57344`).
-/

namespace NativeRustcVmArm.Whir.NextLevel

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.NextLevel NativeRustcVmArm.Transcript

@[expose] public section

/-- The frame's slots. -/
def slots : Slots := [(8096, .X29), (8104, .X30), (8112, .X28), (8120, .X27), (8128, .X26),
  (8136, .X25), (8144, .X24), (8152, .X23), (8160, .X22), (8168, .X21), (8176, .X20),
  (8184, .X19)]

/-- At the entry: the frame (region 0), the level (region 1, X2). -/
def entryS : SState := init [(8192, true), (24, false)] (.ptr 0 8192) [(.X2, .ptr 1 0)]
/-- A block in the frame alone. -/
def fS : SState := init [(8192, true)] (.ptr 0 0)
/-- The frame and the level (X28). -/
def levelS : SState := init [(8192, true), (24, false)] (.ptr 0 0) [(.X28, .ptr 1 0)]
/-- The frame and `WhirW` (X19), X28 its queries' buffer. -/
def bufS : SState := init [(8192, true), (63200, false)] (.ptr 0 0) [(.X19, .ptr 1 0)]
  (aliases := [(.reg .X28, (1, 61352))])
/-- The zeroing loop's body: the 64 bytes at `X10 + X9`. -/
def zeroS : SState :=
  init [(64, false)] .sp (aliases := [(.bin .add .W64 (.reg .X10) (.reg .X9), (0, 0))])
/-- The frame and `WhirW` (X19, X24 at `57344`). -/
def rowsS : SState := init [(8192, true), (63200, false)] (.ptr 0 0) [(.X19, .ptr 1 0)]
  (aliases := [(.reg .X24, (1, 57344))])

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 fS
sym_block run_b2 := exec b2 levelS
sym_block run_b3 := exec b3 fS
sym_block run_b4 := exec b4 fS
sym_block run_b5 := exec b5 fS
sym_block run_b6 := exec b6 fS
sym_block run_b7 := exec b7 fS
sym_block run_b8 := exec b8 fS
sym_block run_b9 := exec b9 fS
sym_block run_b10 := exec b10 fS
sym_block run_b11 := exec b11 fS
sym_block run_b12 := exec b12 fS
sym_block run_b13 := exec b13 levelS
sym_block run_b14 := exec b14 fS
sym_block run_b15 := exec b15 fS
sym_block run_b16 := exec b16 bufS
sym_block run_b17 := exec b17 zeroS
sym_block run_b18 := exec b18 fS
sym_block run_b19 := exec b19 fS
sym_block run_b20 := exec b20 fS
sym_block run_b21 := exec b21 fS
sym_block run_b22 := exec b22 rowsS
sym_block run_b23 := exec b23 fS
sym_block run_b24 := exec b24 fS
sym_block run_b25 := exec b25 fS
sym_block run_b26 := exec b26 fS
sym_block run_b27 := exec b27 fS


end NativeRustcVmArm.Whir.NextLevel
