module

public import NativeRustcArm.Sym
public import NativeRustcVmArm.Code.Vm.OpenPhase
public meta import NativeRustcVmArm.Code.Vm.OpenPhase

/-!
# `open_phase`'s blocks, run by the symbolic executor

Region 0 the 176-byte frame below the entry's SP:
- `entryS`, at the entry (`b0`): region 1 the phase's three counts (X6);
- `frS`, in the frame (SP its base): the tests and the loops' heads;
- `posS`, at `b8`: region 1 position `j` (X4), region 2 opening `j`'s leaf index (X9);
- `rootS`, at `b12`: region 1 the root (X1);
- `opS`, at `b15`: region 1 the 32 bytes from X20 (opening `j`'s leaf index at `24`);
- `outS`, at `b21`, `b22`: region 1 the output (X19).
-/

namespace NativeRustcVmArm.Sumcheck.OpenPhase

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.OpenPhase

@[expose] public section

/-- The state `exec ds S` ends in (`S` where it fails). -/
def after (ds : List Directive) (S : SState) : SState :=
  match exec ds S with
  | some (S', _) => S'
  | none => S

theorem after_eq {ds : List Directive} {S S₁ : SState} {x : Exit} (h : exec ds S = some (S₁, x)) :
    after ds S = S₁ := by
  rw [after, h]

def entryS : SState := init [(176, true), (24, false)] (.ptr 0 176) [(.X6, .ptr 1 0)]
def frS : SState := init [(176, true)] (.ptr 0 0)
def posS : SState :=
  init [(176, true), (8, false), (8, false)] (.ptr 0 0) [(.X4, .ptr 1 0), (.X9, .ptr 2 0)]
def rootS : SState := init [(176, true), (32, false)] (.ptr 0 0) [(.X1, .ptr 1 0)]
def opS : SState := init [(176, true), (32, false)] (.ptr 0 0) [(.X20, .ptr 1 0)]
def outS : SState := init [(176, true), (32, false)] (.ptr 0 0) [(.X19, .ptr 1 0)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 frS
sym_block run_b2 := exec b2 frS
sym_block run_b3 := exec b3 frS
sym_block run_b4 := exec b4 frS
sym_block run_b5 := exec b5 frS
sym_block run_b6 := exec b6 frS
sym_block run_b7 := exec b7 frS
sym_block run_b8 := exec b8 posS
sym_block run_b9 := exec b9 frS
sym_block run_b10 := exec b10 frS
sym_block run_b11 := exec b11 frS
sym_block run_b12 := exec b12 rootS
sym_block run_b13 := exec b13 frS
sym_block run_b14 := exec b14 frS
sym_block run_b15 := exec b15 opS
sym_block run_b16 := exec b16 frS
sym_block run_b17 := exec b17 frS
sym_block run_b18 := exec b18 frS
sym_block run_b19 := exec b19 frS
sym_block run_b20 := exec b20 frS
sym_block run_b21 := exec b21 outS
sym_block run_b22 := exec b22 outS
sym_block run_b23a := exec b23 (after b21 outS)
sym_block run_b23b := exec b23 (after b22 outS)

end NativeRustcVmArm.Sumcheck.OpenPhase
