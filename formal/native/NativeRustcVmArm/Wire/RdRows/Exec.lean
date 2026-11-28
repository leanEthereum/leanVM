module

public import NativeRustcArm.Sym
public import NativeRustcVmArm.Code.Vm.RdRows
public meta import NativeRustcVmArm.Code.Vm.RdRows

/-!
# `rd_rows`' blocks, run by the symbolic executor

Region 0 is the 112-byte frame below SP throughout.

- `entryS`: SP at the frame's end: the prologue and the width check (`b0`).
- `frS`: SP at the frame: everything else but the stores and the row's first word.
- `rowS`: region 1 the row's first word (X26): its check (`b13`).
- `vecS`, `vecS'`: region 1 the 32 bytes before X9 (X10) plus 16: four zeros (`b8`, `b19`).
- `sclS`, `sclS'`: region 1 the word at X8 (X9): one zero (`b10`, `b21`).
-/

namespace NativeRustcVmArm.Wire.RdRows

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.RdRows

@[expose] public section

/-- The state `exec ds S` ends in (`S` where it fails). -/
def after (ds : List Directive) (S : SState) : SState :=
  match exec ds S with
  | some (S', _) => S'
  | none => S

/-- At the entry: the frame (region 0), SP at its end. -/
def entryS : SState := init [(112, true)] (.ptr 0 112)

/-- In the frame (region 0, SP). -/
def frS : SState := init [(112, true)] (.ptr 0 0)

/-- The row's first word (region 1, X26). -/
def rowS : SState := init [(112, true), (8, false)] (.ptr 0 0) [] [] [] [(.reg .X26, 1, 0)]

/-- Four words (region 1) from X9 minus 16. -/
def vecS : SState := init [(112, true), (32, false)] (.ptr 0 0) [] [] [] [(.reg .X9, 1, 16)]

/-- Four words (region 1) from X10 minus 16. -/
def vecS' : SState := init [(112, true), (32, false)] (.ptr 0 0) [] [] [] [(.reg .X10, 1, 16)]

/-- The word at X8 (region 1). -/
def sclS : SState := init [(112, true), (8, false)] (.ptr 0 0) [] [] [] [(.reg .X8, 1, 0)]

/-- The word at X9 (region 1). -/
def sclS' : SState := init [(112, true), (8, false)] (.ptr 0 0) [] [] [] [(.reg .X9, 1, 0)]

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
sym_block run_b8 := exec b8 vecS
sym_block run_b9 := exec b9 frS
sym_block run_b10 := exec b10 sclS
sym_block run_b11 := exec b11 frS
sym_block run_b12 := exec b12 frS
sym_block run_b13 := exec b13 rowS
sym_block run_b14 := exec b14 frS
sym_block run_b15 := exec b15 frS
sym_block run_b16 := exec b16 frS
sym_block run_b17 := exec b17 frS
sym_block run_b18 := exec b18 frS
sym_block run_b19 := exec b19 vecS'
sym_block run_b20 := exec b20 frS
sym_block run_b21 := exec b21 sclS'
sym_block run_b22 := exec b22 frS
sym_block run_b23 := exec b23 frS
sym_block run_b24 := exec b24 frS
sym_block run_b25 := exec b25 frS

end NativeRustcVmArm.Wire.RdRows
