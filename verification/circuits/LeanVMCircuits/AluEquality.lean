module

public import LeanVMCircuits.BooleanAny

@[expose] public section

set_option maxRecDepth 2048

namespace LeanVMCircuits.AluEquality

theorem not_present {n : ℕ} (word : Vector Bit n) :
    ¬ BooleanAny.present word ↔ word = Vector.replicate n 0 := by
  constructor
  · intro h
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_replicate]
    rcases bit_zero_or_one word[i] with hb | hb
    · exact hb
    · exfalso
      apply h
      change (1 : Bit) ∈ word.toList
      rw [← hb]
      simp
  · rintro rfl
    simp [BooleanAny.present]

theorem present_iff {n : ℕ} (word : Vector Bit n) :
    BooleanAny.present word ↔ word ≠ Vector.replicate n 0 := by
  have h := not_present word
  tauto

def difference {α : Type} [Add α] (x y : Vector α 64) : Vector α 64 := Vector.zipWith (· + ·) x y

theorem difference_zero (x y : Vector Bit 64) :
    difference x y = Vector.replicate 64 0 ↔ x = y := by
  constructor
  · intro h
    apply Vector.ext
    intro i hi
    have hb := congrArg (fun word : Vector Bit 64 => word[i]) h
    simp only [difference, Vector.getElem_zipWith, Vector.getElem_replicate] at hb
    rcases bit_zero_or_one x[i] with hx | hx <;>
      rcases bit_zero_or_one y[i] with hy | hy <;> simp_all
  · rintro rfl
    apply Vector.ext
    intro i hi
    rcases bit_zero_or_one x[i] with hx | hx <;> simp [difference, hx]

theorem eval_difference (env : Environment Bit) (x y : Vector (Expression Bit) 64) :
    (difference x y).map (Expression.eval env) =
      difference (x.map (Expression.eval env)) (y.map (Expression.eval env)) := by
  apply Vector.ext
  intro i hi
  simp [difference, circuit_norm]

structure Input (F : Type) where
  x : Vector F 64
  y : Vector F 64
  deriving ProvableStruct

def main (input : Var Input Bit) : Circuit Bit (Expression Bit) := do
  BooleanAny.circuit 63 { word := difference input.x input.y }

instance elaborated : ElaboratedCircuit Bit Input field main := by elaborate_circuit

def Spec (input : Input Bit) (output : Bit) : Prop := output = if input.x ≠ input.y then 1 else 0

def circuit : FormalCircuit Bit Input field where
  main
  elaborated
  Spec
  soundness := by
    circuit_proof_start [main, Spec]
    rcases h_input with ⟨hx, hy⟩
    simp only [BooleanAny.Spec, circuit_norm] at h_holds ⊢
    rw [eval_difference, hx, hy] at h_holds
    have hp : BooleanAny.present (difference input_x input_y) ↔ input_x ≠ input_y :=
      (present_iff _).trans (not_congr (difference_zero input_x input_y))
    simp only [hp] at h_holds
    simp only [FormalCircuitBase.output, BooleanAny.circuit] at h_holds
    exact h_holds
  completeness := by circuit_proof_start [main]

@[circuit_norm] theorem circuit_assumptions : circuit.Assumptions = fun _ => True := rfl
@[circuit_norm] theorem circuit_spec : circuit.Spec = Spec := rfl
@[circuit_norm] theorem circuit_requirements : circuit.channelsWithRequirements = [] := rfl
@[circuit_norm] theorem circuit_guarantees : circuit.elaborated.channelsWithGuarantees = [] := rfl
@[circuit_norm] theorem circuit_length (input : Var Input Bit) : circuit.localLength input = 63 := by
  change (BooleanAny.circuit 63).localLength { word := difference input.x input.y } = 63
  simp only [circuit_norm]

end LeanVMCircuits.AluEquality
