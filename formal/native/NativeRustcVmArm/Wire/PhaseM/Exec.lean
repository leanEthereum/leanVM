module

public import NativeRustcArm.Sym
public import NativeRustcVmArm.Code.Vm.PhaseM
public meta import NativeRustcVmArm.Code.Vm.PhaseM

/-!
# `phase_m`'s blocks, run by the symbolic executor

Region 0 is the 192-byte frame below SP throughout; SP at its end at the entry (`entryS`, the
prologue `b0`), at its base after (`frS`). The blocks that reach into the working area take
region 1 there, at an alias: the query stored (`b6`, X24), the query loaded (`b15`, X19 plus X23),
the last position (`b23`), the position loaded (`b27`, X23), the node stored (`b28`, 40 bytes from
X25 minus 8), the level's count stored (`b34`, X23).
-/

namespace NativeRustcVmArm.Wire.PhaseM

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.PhaseM

@[expose] public section

/-- At the entry: the frame (region 0), SP at its end. -/
def entryS : SState := init [(192, true)] (.ptr 0 192)

/-- In the frame (region 0, SP). -/
def frS : SState := init [(192, true)] (.ptr 0 0)

/-- In the frame, region 1 the `n` bytes at `a` minus `o`. -/
def alS (a : Sym) (n : Nat) (o : Int) : SState :=
  init [(192, true), (n, false)] (.ptr 0 0) [] [] [] [(a, 1, o)]

/-- Query X23's address: X19 plus X23 bytes. -/
def qAddr : Sym := .bin .add .W64 (.reg .X19) (.un (.memExtend ⟨.UXTX, .E0⟩) .W64 (.reg .X23))

/-- The address past the last position: X19 plus 2048 plus X26 words. -/
def lastAddr : Sym :=
  .bin .add .W64 (.bin .add .W64 (.reg .X19) (.lit 2048)) (.un (.shift .LSL 3) .W64 (.reg .X26))

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 frS
sym_block run_b2 := exec b2 frS
sym_block run_b3 := exec b3 frS
sym_block run_b4 := exec b4 frS
sym_block run_b5 := exec b5 frS
sym_block run_b6 := exec b6 (alS (.reg .X24) 8 0)
sym_block run_b7 := exec b7 frS
sym_block run_b8 := exec b8 frS
sym_block run_b9 := exec b9 frS
sym_block run_b10 := exec b10 frS
sym_block run_b11 := exec b11 frS
sym_block run_b12 := exec b12 frS
sym_block run_b13 := exec b13 frS
sym_block run_b14 := exec b14 frS
sym_block run_b15 := exec b15 (alS qAddr 8 0)
sym_block run_b16 := exec b16 frS
sym_block run_b17 := exec b17 frS
sym_block run_b18 := exec b18 frS
sym_block run_b19 := exec b19 frS
sym_block run_b20 := exec b20 frS
sym_block run_b21 := exec b21 frS
sym_block run_b22 := exec b22 frS
sym_block run_b23 := exec b23 (alS lastAddr 8 8)
sym_block run_b24 := exec b24 frS
sym_block run_b25 := exec b25 frS
sym_block run_b26 := exec b26 frS
sym_block run_b27 := exec b27 (alS (.reg .X23) 8 0)
sym_block run_b28 := exec b28 (alS (.reg .X25) 40 8)
sym_block run_b29 := exec b29 frS
sym_block run_b30 := exec b30 frS
sym_block run_b31 := exec b31 frS
sym_block run_b32 := exec b32 frS
sym_block run_b33 := exec b33 frS
sym_block run_b34 := exec b34 (alS (.reg .X23) 8 0)
sym_block run_b35 := exec b35 frS
sym_block run_b36 := exec b36 frS
sym_block run_b37 := exec b37 frS

end NativeRustcVmArm.Wire.PhaseM
