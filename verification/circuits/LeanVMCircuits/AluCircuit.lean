module

public import LeanVMCircuits.AluRaw

@[expose] public section

namespace LeanVMCircuits.Alu

set_option maxRecDepth 65536

def arithmeticInput {α : Type} [Add α] (input : Input α) : AluArithmetic.Input α :=
  { x := input.v1, y := operand input, sub := input.flags[0] }
@[circuit_norm]
private theorem eval_arithmetic_output (env : Environment Bit)
    (output : Adder.Output 64 (Expression Bit)) :
    ProvableStruct.eval env output =
      ({ sum := output.sum.map (Expression.eval env),
         carry := Expression.eval env output.carry } : Adder.Output 64 Bit) := by
  rcases output with ⟨sum, carry⟩
  simp only [circuit_norm]

@[circuit_norm]
private theorem eval_indirect_output (env : Environment Bit)
    (output : AluIndirect.Output (Expression Bit)) :
    ProvableStruct.eval env output =
      ({ value := output.value.map (Expression.eval env),
         offset := output.offset.map (Expression.eval env) } : AluIndirect.Output Bit) := by
  rcases output with ⟨value, offset⟩
  simp only [circuit_norm]


def main (input : Var Input Bit) : Circuit Bit (Var Output Bit) := do
  let b := operand input
  let arithmetic ← AluArithmetic.circuit (arithmeticInput input)
  let ltu := 1 + arithmetic.carry
  let lt := ltu + input.v1[63] + b[63]
  let ne ← AluEquality.circuit { x := input.v1, y := b }
  let selected ← AluSelector.circuit {
    x := input.v1
    y := b
    sum := arithmetic.sum
    difference := AluEquality.difference input.v1 b
    flags := input.flags
    lt
    ltu
  }
  let indirect ← AluIndirect.circuit {
    indirect := input.flags[7], value := selected, pc4 := input.pc4, dt := input.dt }
  let taken ← AluBranch.circuit { flags := input.flags, ne, lt, ltu }
  let jump ← WordScale.circuit 64 { selector := taken, word := indirect.offset }
  return { value := indirect.value, jump }

instance elaborated : ElaboratedCircuit Bit Input Output main := by elaborate_circuit

def Spec (input : Input Bit) (output : Output Bit) : Prop :=
  ∃ arithmetic : Adder.Output 64 Bit,
    AluArithmetic.Spec (arithmeticInput input) arithmetic ∧ output = afterArithmetic input arithmetic

theorem spec_raw (input : Input Bit) (output : Output Bit) (h : Spec input output) :
    output = rawReference input := by
  rcases h with ⟨arithmetic, ha, rfl⟩
  exact afterArithmetic_correct input arithmetic ha

def circuit : FormalCircuit Bit Input Output where
  main
  elaborated
  Spec
  soundness := by
    circuit_proof_start_core
    rw [← elaborated.output_eq input_var i₀]
    dsimp +instances only [main] at h_holds
    dsimp only [field, id_eq, CircuitType.var_of_provableType,
      CircuitType.value_of_provableType] at *
    provable_struct_simp
    simp +instances only [circuit_norm] at h_input
    simp only [Circuit.bind_operations_eq, Circuit.pure_operations_eq, subcircuit,
      Circuit.operations, Circuit.output, Circuit.localLength,
      Operations.localLength, FormalCircuit.toSubcircuit_localLength,
      AluArithmetic.circuit_length, AluEquality.circuit_length,
      AluSelector.circuit_length, AluIndirect.circuit_length,
      AluBranch.circuit_length, WordScale.circuit_length,
      ConstraintsHold.Soundness, Operations.forAllNoOffset_append,
      Operations.forAllNoOffset, FormalCircuit.toSubcircuit_assumptions,
      FormalCircuit.toSubcircuit_soundness,
      AluArithmetic.circuit_assumptions, AluEquality.circuit_assumptions,
      AluSelector.circuit_assumptions, AluIndirect.circuit_assumptions,
      AluBranch.circuit_assumptions, WordScale.circuit_assumptions,
      AluArithmetic.circuit_spec, AluEquality.circuit_spec,
      AluSelector.circuit_spec, AluIndirect.circuit_spec,
      AluBranch.circuit_spec, WordScale.circuit_spec,
      true_implies, and_true, List.append_nil, Nat.add_zero] at h_holds
    let inputVar : Var Input Bit := {
      v1 := input_var_v1, v2 := input_var_v2, imm := input_var_imm,
      flags := input_var_flags, dt := input_var_dt, pc4 := input_var_pc4
    }
    simp only [main, Circuit.bind_output_eq, Circuit.pure_output_eq,
      Circuit.bind_operations_eq, Circuit.pure_operations_eq,
      subcircuit, Circuit.operations, Circuit.output, Circuit.localLength,
      Operations.localLength, FormalCircuit.toSubcircuit_localLength,
      AluArithmetic.circuit_length, AluEquality.circuit_length,
      AluSelector.circuit_length, AluIndirect.circuit_length,
      AluBranch.circuit_length, WordScale.circuit_length, Nat.add_zero]
    generalize hArithmetic :
      AluArithmetic.circuit.output (arithmeticInput inputVar) i₀ = arithmeticVar at h_holds ⊢
    dsimp only [Spec]
    dsimp only [field, id_eq, CircuitType.var_of_provableType,
      CircuitType.value_of_provableType] at *
    simp only [AluArithmetic.Spec, AluEquality.Spec, AluSelector.Spec,
      AluIndirect.Spec, AluBranch.Spec, WordScale.Spec] at h_holds
    rcases h_input with ⟨hv1, hv2, himm, hf, hdt, hpc4⟩
    have hflag (i : ℕ) (hi : i < 15) := congrArg (fun flags : Vector Bit 15 => flags[i]) hf
    simp only [Vector.getElem_map] at hflag
    have hsign := congrArg (fun word : Vector Bit 64 => word[63]) hv1
    simp only [Vector.getElem_map] at hsign
    let inputValue : Input Bit := {
      v1 := input_v1
      v2 := input_v2
      imm := input_imm
      flags := input_flags
      dt := input_dt
      pc4 := input_pc4
    }
    simp only [Operations.Requirements, Operations.forAllNoOffset_append,
      Operations.forAllNoOffset, FormalCircuit.toSubcircuit_channelsWithRequirements,
      AluArithmetic.circuit_requirements, AluEquality.circuit_requirements,
      AluSelector.circuit_requirements, AluIndirect.circuit_requirements,
      AluBranch.circuit_requirements, WordScale.circuit_requirements,
      true_or, and_true]
    have hb : (operand inputVar).map (Expression.eval env) = operand inputValue := by
      change (AluEquality.difference input_var_v2 input_var_imm).map (Expression.eval env) = _
      rw [AluEquality.eval_difference, hv2, himm]
      rfl
    dsimp +instances only [inputVar, inputValue] at hb
    have hbsign := congrArg (fun word : Vector Bit 64 => word[63]) hb
    simp only [Vector.getElem_map] at hbsign
    simp +instances only [arithmeticInput, circuit_norm, hb, hv1, hf,
      hdt, hpc4, hflag, hsign, hbsign, AluEquality.eval_difference] at h_holds
    rcases h_holds with ⟨harithmetic, hne, hselected, hindirect, htaken, hjump⟩
    let arithmetic : Adder.Output 64 Bit := {
      sum := arithmeticVar.sum.map (Expression.eval env),
      carry := Expression.eval env arithmeticVar.carry
    }
    refine ⟨arithmetic, ?_, ?_⟩
    · simpa +instances only [arithmetic, arithmeticInput, AluArithmetic.Spec] using harithmetic
    · simp only [afterArithmetic]
      simp only [WordScale.select_boolean] at hjump
      simp only [FormalCircuitBase.output] at *
      simp +instances only [circuit_norm, arithmetic]
      simp_all +instances only [true_and]
  completeness := by
    circuit_proof_start_core
    simp only [main, Circuit.bind_operations_eq, Circuit.pure_operations_eq,
      subcircuit, Circuit.operations, Circuit.output, Circuit.localLength,
      Operations.localLength, FormalCircuit.toSubcircuit_localLength,
      AluArithmetic.circuit_length, AluEquality.circuit_length,
      AluSelector.circuit_length, AluIndirect.circuit_length,
      AluBranch.circuit_length, WordScale.circuit_length,
      ConstraintsHold.Completeness, Operations.forAllNoOffset_append,
      Operations.forAllNoOffset, FormalCircuit.toSubcircuit_completeness,
      AluArithmetic.circuit_assumptions, AluEquality.circuit_assumptions,
      AluSelector.circuit_assumptions, AluIndirect.circuit_assumptions,
      AluBranch.circuit_assumptions, WordScale.circuit_assumptions,
      and_true, Nat.add_zero]

@[circuit_norm] theorem circuit_assumptions : circuit.Assumptions = fun _ => True := rfl
@[circuit_norm] theorem circuit_spec : circuit.Spec = Spec := rfl
@[circuit_norm] theorem circuit_requirements : circuit.channelsWithRequirements = [] := rfl
@[circuit_norm] theorem circuit_guarantees : circuit.elaborated.channelsWithGuarantees = [] := rfl
@[circuit_norm] theorem circuit_length (input : Var Input Bit) : circuit.localLength input = 551 := by
  change 64 + 63 + 290 + 64 + 6 + 64 = 551
  rfl

end LeanVMCircuits.Alu
