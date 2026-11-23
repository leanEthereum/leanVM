module

public import NativeRustcVmArm.Layout.PlacementsOf.Exec
public meta import NativeRustcVmArm.Layout.PlacementsOf.Exec

/-!
# `placements_of`'s `b22` in two parts

`b22` loads a byte of `KECCAK_SLOT` and a log-size, which need not be apart: its first two
directives (`b22a`, the byte, from `byteS .X23 .X9`) and the rest (`b22b`, the log-size and the
test, from `kapS`: region 0 `kappas[c]`) run one after the other.
-/

namespace NativeRustcVmArm.Layout.PlacementsOf

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.PlacementsOf NativeRustcVmArm.Arrays

@[expose] public section

/-- `b22`'s byte load. -/
def b22a : List Directive := b22.take 2
/-- `b22`'s log-size load and test. -/
def b22b : List Directive := b22.drop 2
/-- Region 0 `kappas[c]`, at `[x19, x9, lsl #3]`. -/
def kapS : SState := init [(8, false)] .sp [] [] [] [(idx .X19 .X9, 0, 0)]

end

set_option Elab.async false

sym_block run_b22a := exec b22a (byteS .X23 .X9)
sym_block run_b22b := exec b22b kapS

public theorem b22a_keep : keepsAll (byteS .X23 .X9) (after b22a (byteS .X23 .X9)) keptRegs =
    true := by
  decide +kernel
public theorem b22b_keep : keepsAll kapS (after b22b kapS) keptRegs = true := by decide +kernel

public theorem b22a_in_code : b22a.IsInfixAt code b22Offset :=
  (List.take_prefix 2 b22).trans b22_in_code

public theorem b22b_in_code : b22b.IsInfixAt code (b22Offset + 2) := by
  obtain ⟨t, ht⟩ := b22_in_code
  refine ⟨t, ?_⟩
  rw [show code.drop (b22Offset + 2) = (code.drop b22Offset).drop 2 by rw [List.drop_drop]]
  rw [← ht, List.drop_append_of_le_length (by decide)]
  rfl

end NativeRustcVmArm.Layout.PlacementsOf
