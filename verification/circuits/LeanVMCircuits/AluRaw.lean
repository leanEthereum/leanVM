module

public import LeanVMCircuits.AluArithmetic
public import LeanVMCircuits.AluBranch
public import LeanVMCircuits.AluEquality
public import LeanVMCircuits.AluIndirect
public import LeanVMCircuits.AluSelector
public import LeanVMCircuits.AluSemantics

@[expose] public section

namespace LeanVMCircuits.Alu

def rawCarry (input : Input Bit) : Bit :=
  (((Adder.value input.v1 + Adder.value (AluArithmetic.flip (operand input) input.flags[0]) +
    input.flags[0].val) / 2 ^ 64 : ℕ) : Bit)

theorem rawCarry_correct (input : Input Bit) (output : Adder.Output 64 Bit)
    (h : AluArithmetic.Spec { x := input.v1, y := operand input, sub := input.flags[0] } output) :
    output.carry = rawCarry input := by
  have hsum := Adder.value_lt output.sum
  have hc : output.carry.val =
      (Adder.value input.v1 + Adder.value (AluArithmetic.flip (operand input) input.flags[0]) +
        input.flags[0].val) / 2 ^ 64 := by
    dsimp [AluArithmetic.Spec] at h
    omega
  unfold rawCarry
  rw [← hc, ZMod.natCast_zmod_val]

def afterArithmetic (input : Input Bit) (arithmetic : Adder.Output 64 Bit) : Output Bit :=
  let b := operand input
  let ltu := 1 + arithmetic.carry
  let lt := ltu + input.v1[63] + b[63]
  let ne := if input.v1 ≠ b then (1 : Bit) else 0
  let selected := AluSelector.selected {
    x := input.v1
    y := b
    sum := arithmetic.sum
    difference := AluEquality.difference input.v1 b
    flags := input.flags
    lt
    ltu
  }
  let value := if input.flags[7] = 1 then input.pc4 else selected
  let offset := AluIndirect.offset input.dt selected value
  let taken := AluBranch.selected { flags := input.flags, ne, lt, ltu }
  { value, jump := if taken = 1 then offset else Vector.replicate 64 0 }

def rawReference (input : Input Bit) : Output Bit :=
  afterArithmetic input { sum := sum input, carry := rawCarry input }

theorem afterArithmetic_correct (input : Input Bit) (arithmetic : Adder.Output 64 Bit)
    (h : AluArithmetic.Spec { x := input.v1, y := operand input, sub := input.flags[0] } arithmetic) :
    afterArithmetic input arithmetic = rawReference input := by
  have hs := AluArithmetic.sum_correct
    { x := input.v1, y := operand input, sub := input.flags[0] } arithmetic h
  change arithmetic.sum = sum input at hs
  have hc := rawCarry_correct input arithmetic h
  rcases arithmetic with ⟨s, c⟩
  dsimp only at hs hc
  subst s
  subst c
  rfl

end LeanVMCircuits.Alu
