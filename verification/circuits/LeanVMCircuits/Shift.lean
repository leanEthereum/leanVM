module

public import LeanVMCircuits.DirectedShift

@[expose] public section

namespace LeanVMCircuits.Shift

structure Input (F : Type) where
  v1 : Vector F 64
  v2 : Vector F 64
  imm : Vector F 64
  right : F
  arith : F
  word : F
  deriving ProvableStruct

def preparation {F : Type} (input : Input F) : ShiftPreparation.Input F :=
  { v1 := input.v1, v2 := input.v2, imm := input.imm, arith := input.arith, word := input.word }

def Assumptions (input : Input Bit) : Prop := input.arith = 1 → input.right = 1

def flags (input : Input Bit) : ℕ := input.right.val + 2 * input.arith.val + 4 * input.word.val

/-- The semantic domain is exactly the six flag words accepted by the RV instruction class. -/
theorem assumptions_iff_legal_flags (input : Input Bit) :
    Assumptions input ↔ flags input ∈ [0, 1, 3, 4, 5, 7] := by
  have hr := ZMod.val_lt input.right
  have ha := ZMod.val_lt input.arith
  have hw := ZMod.val_lt input.word
  have er : input.right = (input.right.val : Bit) := (ZMod.natCast_zmod_val _).symm
  have ea : input.arith = (input.arith.val : Bit) := (ZMod.natCast_zmod_val _).symm
  have ew : input.word = (input.word.val : Bit) := (ZMod.natCast_zmod_val _).symm
  interval_cases hrr : input.right.val <;> interval_cases haa : input.arith.val <;>
    interval_cases hww : input.word.val <;> simp_all [Assumptions, flags]

def shifted (input : Input Bit) : Vector Bit 64 :=
  let prepared := preparation input
  let operand := ShiftPreparation.operand prepared
  let amount := Adder.value (ShiftPreparation.amountBits prepared)
  if input.right = 1 then Words.right amount (if input.arith = 1 then operand[63] else 0) operand
    else Words.left amount 0 operand

def Spec (input : Input Bit) (output : Vector Bit 64) : Prop :=
  output = if input.word = 1 then Words.high (shifted input)[31] (shifted input) else shifted input

def main (barrel : BarrelShift.Certified 6) (input : Var Input Bit) : Circuit Bit (Var (fields 64) Bit) := do
  let prepared ← ShiftPreparation.circuit (preparation input)
  let shifted ← DirectedShift.build barrel { amount := prepared.amount, fill := prepared.fill, right := input.right, word := prepared.word }
  WordMode.circuit { selector := input.word, fill := shifted[31], word := shifted }

instance elaborated (barrel : BarrelShift.Certified 6) : ElaboratedCircuit Bit Input (fields 64) (main barrel) := by
  elaborate_circuit

def build (barrel : BarrelShift.Certified 6) : FormalCircuit Bit Input (fields 64) where
  main := main barrel
  elaborated := elaborated barrel
  Assumptions
  Spec
  soundness := by
    circuit_proof_start [main, preparation, Assumptions, Spec, DirectedShift.build, ShiftPreparation.Spec]
    rcases h_holds with ⟨hp, hd, ho⟩
    rcases hp with ⟨hamount, hword, hfill⟩
    have hguard : input_right = 1 ∨
        (if input_arith = 1 then (ShiftPreparation.operand (preparation {
          v1 := input_v1, v2 := input_v2, imm := input_imm,
          right := input_right, arith := input_arith, word := input_word }))[63] else 0) = 0 := by
      by_cases ha : input_arith = 1
      · exact Or.inl (h_assumptions ha)
      · exact Or.inr (by simp [ha])
    simp only [DirectedShift.Assumptions, DirectedShift.Spec] at hd
    simp only [hamount, hword, hfill] at hd
    have hshift := hd hguard
    have hsign := congrArg (fun v : Vector Bit 64 => v[31]) hshift
    simp only [Vector.getElem_map] at hsign
    rw [hsign, hshift] at ho
    simpa only [shifted, preparation] using ho
  completeness := by
    circuit_proof_start [main, preparation, DirectedShift.build, Assumptions, ShiftPreparation.Spec]
    simp only [DirectedShift.Assumptions]
    have hfill := h_env.1.2.2
    rw [hfill]
    by_cases ha : input_arith = 1
    · exact Or.inl (h_assumptions ha)
    · exact Or.inr (by simp [ha])

def circuit := build (BarrelShift.certified 6)

@[circuit_norm] theorem circuit_assumptions : circuit.Assumptions = Assumptions := rfl
@[circuit_norm] theorem circuit_spec : circuit.Spec = Spec := rfl

end LeanVMCircuits.Shift
