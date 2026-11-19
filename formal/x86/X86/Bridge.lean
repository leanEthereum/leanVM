module

public import X86.Bridge.Basic
public import X86.Bridge.Instr

/-!
# The bridge from the subset to Kraken's x86-64

`QInstr.toInstr_correct`: each instruction of the subset does on Kraken's machine what
`QInstr.step` says; `Cond.toInstr_correct`: each condition's `cmp` or `test` sets the flags so that
its condition code holds exactly when the condition does. Both are generic in the label map and
hold for every value Kraken leaves undefined.
-/
