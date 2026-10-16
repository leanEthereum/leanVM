module

public import LeanVMCircuits.AluWords
public import LeanVMCircuits.WordMode

@[expose] public section

namespace LeanVMCircuits.Alu

structure Input (F : Type) where
  v1 : Vector F 64
  v2 : Vector F 64
  imm : Vector F 64
  flags : Vector F 15
  dt : Vector F 64
  pc4 : Vector F 64
  deriving ProvableStruct

structure Output (F : Type) where
  value : Vector F 64
  jump : Vector F 64
  deriving ProvableStruct

def legalFlags : List ℕ := [0, 1, 2, 3, 5, 9, 16, 32, 64, 16512, 257, 513, 1025, 2049, 4097, 8193, 16384]

def Legal (flags : Vector Bit 15) : Prop := Adder.value flags ∈ legalFlags

theorem legal_cases {flags : Vector Bit 15} (h : Legal flags) :
    flags ∈ legalFlags.map (Words.ofNat 15) := by
  rw [← Words.ofNat_value flags]
  exact List.mem_map_of_mem h

def operand {α : Type} [Add α] (input : Input α) : Vector α 64 :=
  Vector.zipWith (· + ·) input.v2 input.imm

def sum (input : Input Bit) : Vector Bit 64 :=
  Words.ofNat 64 (if input.flags[0] = 1 then
    Adder.value input.v1 + 2 ^ 64 - Adder.value (operand input)
  else Adder.value input.v1 + Adder.value (operand input))

def unsignedLess (input : Input Bit) : Prop := Adder.value input.v1 < Adder.value (operand input)

def signedLess (input : Input Bit) : Prop := AluWord.signed input.v1 < AluWord.signed (operand input)

instance (input : Input Bit) : Decidable (unsignedLess input) := inferInstanceAs (Decidable (Adder.value input.v1 < Adder.value (operand input)))
instance (input : Input Bit) : Decidable (signedLess input) := inferInstanceAs (Decidable (AluWord.signed input.v1 < AluWord.signed (operand input)))

def value (input : Input Bit) : Vector Bit 64 :=
  if input.flags[2] = 1 then Words.ofNat 64 (if signedLess input then 1 else 0)
  else if input.flags[3] = 1 then Words.ofNat 64 (if unsignedLess input then 1 else 0)
  else if input.flags[4] = 1 then Vector.mapFinRange 64 fun i => input.v1[i] * (operand input)[i]
  else if input.flags[5] = 1 then Vector.mapFinRange 64 fun i =>
    input.v1[i] + (operand input)[i] + input.v1[i] * (operand input)[i]
  else if input.flags[6] = 1 then Vector.mapFinRange 64 fun i => input.v1[i] + (operand input)[i]
  else if input.flags[7] = 1 then input.pc4
  else if input.flags[1] = 1 then Words.high (sum input)[31] (sum input)
  else sum input

def Taken (input : Input Bit) : Prop :=
  input.flags[14] = 1 ∨
  (input.flags[8] = 1 ∧ input.v1 = operand input) ∨
  (input.flags[9] = 1 ∧ input.v1 ≠ operand input) ∨
  (input.flags[10] = 1 ∧ signedLess input) ∨
  (input.flags[11] = 1 ∧ ¬ signedLess input) ∨
  (input.flags[12] = 1 ∧ unsignedLess input) ∨
  (input.flags[13] = 1 ∧ ¬ unsignedLess input)

instance (input : Input Bit) : Decidable (Taken input) := inferInstanceAs (Decidable (
  input.flags[14] = 1 ∨
  (input.flags[8] = 1 ∧ input.v1 = operand input) ∨
  (input.flags[9] = 1 ∧ input.v1 ≠ operand input) ∨
  (input.flags[10] = 1 ∧ signedLess input) ∨
  (input.flags[11] = 1 ∧ ¬ signedLess input) ∨
  (input.flags[12] = 1 ∧ unsignedLess input) ∨
  (input.flags[13] = 1 ∧ ¬ unsignedLess input)))

def jump (input : Input Bit) : Vector Bit 64 :=
  if Taken input then
    let target := Words.ofNat 64 (Adder.value input.v1 + Adder.value (operand input))
    Vector.mapFinRange 64 fun i => input.dt[i] +
      if input.flags[7] = 1 ∧ i.val ≠ 0 then target[i] + input.pc4[i] else 0
  else Vector.replicate 64 0

def reference (input : Input Bit) : Output Bit := ⟨value input, jump input⟩

end LeanVMCircuits.Alu
