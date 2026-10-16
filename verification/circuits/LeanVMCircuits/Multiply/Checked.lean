module

public import LeanVMCircuits.Multiply.Gates

@[expose] public section

/-!
The multiplier's plan, checked once per width by reduction in Lean's kernel: every step's bits and carries are what
`LeanVMCircuits.Multiply.Replay` requires.
-/

namespace LeanVMCircuits.Multiply

theorem check64 : check 64 = true := by decide +kernel

theorem check128 : check 128 = true := by decide +kernel

theorem steps64 : (plan 64).1.length = 64 := by decide +kernel

theorem steps128 : (plan 128).1.length = 64 := by decide +kernel

end LeanVMCircuits.Multiply
