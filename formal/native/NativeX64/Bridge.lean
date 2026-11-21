module

public import NativeX64.Bridge.Basic
public import NativeX64.Bridge.Instr

/-!
# The bridge from QM to Kraken's x86-64

`QInstr.toInstr_correct`: each QM instruction does on Kraken's machine what
`QInstr.step` says; `Cond.toInstr_correct`: each condition's `cmp` or `test` sets the flags so that
its condition code holds exactly when the condition does. Both are generic in the label map and
hold for every value Kraken leaves undefined.
-/
