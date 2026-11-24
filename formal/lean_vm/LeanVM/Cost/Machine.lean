module

public import Statement.CostMachine
public import Statement.LeanVmExtractor
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# The cost machine

The machine (`MachineValue`, `PrimitiveOperation`, `Term`, `MachineProgram`, `evaluateTerm`, `run`, `outputWithin`, `MachineProgram.size`) is
the statement's, `Statement/CostMachine.lean`, on which `LeanVM.extractorComputedBy`
(`Statement/LeanVmExtractor.lean`) runs a program; its
specification by rules is `Cost/Spec.lean`.
-/
