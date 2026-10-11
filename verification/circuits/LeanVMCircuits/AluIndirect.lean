module

public import LeanVMCircuits.AluEquality
public import LeanVMCircuits.WordScale

@[expose] public section

namespace LeanVMCircuits.AluIndirect

structure Input (F : Type) where
  indirect : F
  value : Vector F 64
  pc4 : Vector F 64
  dt : Vector F 64
  deriving ProvableStruct

structure Output (F : Type) where
  value : Vector F 64
  offset : Vector F 64
  deriving ProvableStruct

def offset {α : Type} [Add α] [Zero α] (dt old next : Vector α 64) : Vector α 64 :=
  Vector.mapFinRange 64 fun i => dt[i.val] + if i.val = 0 then 0 else old[i.val] + next[i.val]

def addMoved {α : Type} [Add α] [Zero α] (dt moved : Vector α 64) : Vector α 64 :=
  Vector.mapFinRange 64 fun i => dt[i.val] + if i.val = 0 then 0 else moved[i.val]

theorem eval_addMoved (env : Environment Bit) (dt moved : Vector (Expression Bit) 64) :
    (addMoved dt moved).map (Expression.eval env) =
      addMoved (dt.map (Expression.eval env)) (moved.map (Expression.eval env)) := by
  apply Vector.ext
  intro i hi
  simp only [addMoved, Vector.getElem_map, Vector.getElem_mapFinRange]
  split <;> simp [circuit_norm]

theorem value_selected (old pc4 : Vector Bit 64) (indirect : Bit) :
    AluEquality.difference old (WordScale.select 64 {
      selector := indirect, word := AluEquality.difference old pc4 }) =
      if indirect = 1 then pc4 else old := by
  rcases bit_zero_or_one indirect with hs | hs <;>
    apply Vector.ext <;> intro i hi <;>
    rcases bit_zero_or_one old[i] with ho | ho <;>
    rcases bit_zero_or_one pc4[i] with hp | hp <;>
    simp [AluEquality.difference, WordScale.select, hs, ho, hp]

theorem offset_value (dt old moved : Vector Bit 64) :
    addMoved dt moved = offset dt old (AluEquality.difference old moved) := by
  apply Vector.ext
  intro i hi
  rcases bit_zero_or_one old[i] with ho | ho <;>
    rcases bit_zero_or_one moved[i] with hm | hm <;>
    simp [addMoved, offset, AluEquality.difference, Vector.getElem_mapFinRange, ho, hm]

def main (input : Var Input Bit) : Circuit Bit (Var Output Bit) := do
  let moved ← WordScale.circuit 64 {
    selector := input.indirect, word := AluEquality.difference input.value input.pc4 }
  return { value := AluEquality.difference input.value moved, offset := addMoved input.dt moved }

instance elaborated : ElaboratedCircuit Bit Input Output main := by elaborate_circuit

def Spec (input : Input Bit) (output : Output Bit) : Prop :=
  output.value = (if input.indirect = 1 then input.pc4 else input.value) ∧
    output.offset = offset input.dt input.value output.value

def circuit : FormalCircuit Bit Input Output where
  main
  elaborated
  Spec
  soundness := by
    circuit_proof_start [main, Spec, WordScale.Spec]
    rcases h_input with ⟨hindirect, hvalue, hpc4, hdt⟩
    simp only [AluEquality.eval_difference, hvalue, hpc4] at h_holds
    simp only [FormalCircuitBase.output, WordScale.circuit] at h_holds
    simp only [AluEquality.eval_difference, eval_addMoved, hdt, hvalue]
    constructor
    · exact (congrArg (AluEquality.difference input_value) h_holds).trans (value_selected _ _ _)
    · exact offset_value _ _ _
  completeness := by circuit_proof_start [main]
@[circuit_norm] theorem circuit_assumptions : circuit.Assumptions = fun _ => True := rfl
@[circuit_norm] theorem circuit_spec : circuit.Spec = Spec := rfl
@[circuit_norm] theorem circuit_requirements : circuit.channelsWithRequirements = [] := rfl
@[circuit_norm] theorem circuit_guarantees : circuit.elaborated.channelsWithGuarantees = [] := rfl
@[circuit_norm] theorem circuit_length (input : Var Input Bit) : circuit.localLength input = 64 := by
  change (WordScale.circuit 64).localLength {
    selector := input.indirect, word := AluEquality.difference input.value input.pc4 } = 64
  simp only [circuit_norm]


end LeanVMCircuits.AluIndirect
