module

public import Statement.CostMachine

/-!
# The cost machine

The machine (`MachineValue`, `PrimitiveOperation`, `Term`, `MachineProgram`, `evaluateTerm`, `run`, `outputWithin`, `MachineProgram.size`) is
the statement's, `Statement/CostMachine.lean`, where `LeanVM.extractorComputedBy` runs a program; its
specification by rules is `Cost/Spec.lean`.
-/
