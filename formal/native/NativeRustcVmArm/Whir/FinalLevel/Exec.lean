module

public import NativeRustcVmArm.Whir.Common
public import NativeRustcVmArm.Code.Vm.FinalLevel
public meta import NativeRustcVmArm.Code.Vm.FinalLevel
public meta import NativeRustcVmArm.Whir.Common

/-!
# `final_level`'s blocks, run by the symbolic executor

Region 0 is the 2672-byte frame below the entry's SP throughout (X29, X30, X28 to X19 at `2576`
to `2672`). Its bytes: `0` `each_row`'s stack argument (the folded scalars' count); `24` the
sumcheck's claim; `40` the folded scalars (`[EW; 64]`); `1064` the rows; `1096` the sumcheck's
tail (`[EW; 30]`); `1576` the point (`Buf<EW, 30>`); `2064` `query_openings`' then the sumcheck's
output, then the rotated point (`Buf<EW, 30>`); `2552` `BasisW::eval`'s and `glued_eval`'s
`Option<EW>`.
- `entryS` (`b0`): SP at the frame's top, the level region 1 (X2).
- `levelS` (`b1`): the level region 1 (X2); `lev26S` (`b8`): the level region 1 (X26).
- `fS`: the frame alone.
- `qS` (`b10`): the queries' count region 1 (X26).
- `rS` (`b12`): `WhirW` region 1 (X27, X29 at `57344`).
- `wS n` (`b15`, `b17`, `b27`): the state's first `n` bytes region 1 (X27).
- `gS` (`b29`): a glued claim's first 24 bytes region 1 (X24).
-/

namespace NativeRustcVmArm.Whir.FinalLevel

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.FinalLevel

@[expose] public section

/-- At the entry. -/
def entryS : SState := init [(2672, true), (24, false)] (.ptr 0 2672) [(.X2, .ptr 1 0)]
/-- The level at X2. -/
def levelS : SState := init [(2672, true), (24, false)] (.ptr 0 0) [(.X2, .ptr 1 0)]
/-- The level at X26. -/
def lev26S : SState := init [(2672, true), (24, false)] (.ptr 0 0) [(.X26, .ptr 1 0)]
/-- The frame alone. -/
def fS : SState := init [(2672, true)] (.ptr 0 0)
/-- The queries' count at X26. -/
def qS : SState := init [(2672, true), (8, false)] (.ptr 0 0) [(.X26, .ptr 1 0)]
/-- `WhirW` at X27, X29 at its byte `57344`. -/
def rS : SState := init [(2672, true), (63200, false)] (.ptr 0 0) [(.X27, .ptr 1 0)]
  (aliases := [(.reg .X29, (1, 57344))])
/-- The state's first `n` bytes at X27. -/
def wS (n : Nat) : SState := init [(2672, true), (n, false)] (.ptr 0 0) [(.X27, .ptr 1 0)]
/-- A glued claim's first 24 bytes at X24. -/
def gS : SState := init [(2672, true), (24, false)] (.ptr 0 0) [(.X24, .ptr 1 0)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1e := exec b1 (after b0 entryS)
sym_block run_b4e := exec b4 (after b1 (after b0 entryS))
sym_block run_b1 := exec b1 levelS
sym_block run_b2 := exec b2 fS
sym_block run_b3 := exec b3 fS
sym_block run_b3z := exec b3 (after b2 fS)
sym_block run_b4 := exec b4 fS
sym_block run_b5 := exec b5 fS
sym_block run_b6 := exec b6 fS
sym_block run_b7 := exec b7 fS
sym_block run_b8 := exec b8 lev26S
sym_block run_b9 := exec b9 fS
sym_block run_b10 := exec b10 qS
sym_block run_b11 := exec b11 fS
sym_block run_b12 := exec b12 rS
sym_block run_b13 := exec b13 fS
sym_block run_b14 := exec b14 fS
sym_block run_b15 := exec b15 (wS 16)
sym_block run_b16 := exec b16 fS
sym_block run_b17 := exec b17 (wS 24)
sym_block run_b18 := exec b18 fS
sym_block run_b19 := exec b19 fS
sym_block run_b20 := exec b20 fS
sym_block run_b21 := exec b21 fS
sym_block run_b22 := exec b22 fS
sym_block run_b23 := exec b23 fS
sym_block run_b24 := exec b24 fS
sym_block run_b25 := exec b25 fS
sym_block run_b26 := exec b26 fS
sym_block run_b27 := exec b27 (wS 512)
sym_block run_b28 := exec b28 fS
sym_block run_b29 := exec b29 gS
sym_block run_b30 := exec b30 fS
sym_block run_b31 := exec b31 fS
sym_block run_b32 := exec b32 fS
sym_block run_b33 := exec b33 fS
sym_block run_b34 := exec b34 fS
sym_block run_b35 := exec b35 fS

end NativeRustcVmArm.Whir.FinalLevel
