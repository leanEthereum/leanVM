module

public import NativeArm.Bridge.Instr
public import NativeArm.Bridge.Cond

/-!
# The bridge from QM to Kraken's AArch64

`QInstr.toArm_correct`: each QM instruction's code does on Kraken's machine what `QInstr.step`
says, changing no reserved register nor SP; `Cond.toArm_correct`: each condition's code sets the
flags so that `Cond.armCC` holds exactly when the condition does. Both are generic in the label map.
-/
