module

public import LeanVMCircuits.AluWords

@[expose] public section

namespace LeanVMCircuits.AluArithmetic

structure Input (F : Type) where
  x : Vector F 64
  y : Vector F 64
  sub : F
  deriving ProvableStruct

def flip {α : Type} [Add α] (word : Vector α 64) (sub : α) : Vector α 64 := word.map (· + sub)

theorem flip_zero (word : Vector Bit 64) : flip word 0 = word := by simp [flip]

theorem flip_one (word : Vector Bit 64) : flip word 1 = AluWord.complement word := by
  simp [flip, AluWord.complement, add_comm]

theorem eval_flip (env : Environment Bit) (word : Vector (Expression Bit) 64) (sub : Expression Bit) :
    (flip word sub).map (Expression.eval env) =
      flip (word.map (Expression.eval env)) (Expression.eval env sub) := by
  apply Vector.ext
  intro i hi
  simp [flip, circuit_norm]

def main (input : Var Input Bit) : Circuit Bit (Var (Adder.Output 64) Bit) := do
  Adder.circuit 64 { x := input.x, y := flip input.y input.sub, carry := input.sub }

instance elaborated : ElaboratedCircuit Bit Input (Adder.Output 64) main := by elaborate_circuit

def Spec (input : Input Bit) (output : Adder.Output 64 Bit) : Prop :=
  Adder.value output.sum + 2 ^ 64 * output.carry.val =
    Adder.value input.x + Adder.value (flip input.y input.sub) + input.sub.val

def circuit : FormalCircuit Bit Input (Adder.Output 64) where
  main
  elaborated
  Spec
  soundness := by
    circuit_proof_start [main, Spec, Adder.Spec]
    rcases h_input with ⟨hx, hy, hs⟩
    rw [eval_flip, hy, hs] at h_holds
    simp only [FormalCircuitBase.output, Adder.circuit] at h_holds
    exact h_holds
  completeness := by circuit_proof_start [main]

@[circuit_norm] theorem circuit_assumptions : circuit.Assumptions = fun _ => True := rfl
@[circuit_norm] theorem circuit_spec : circuit.Spec = Spec := rfl
@[circuit_norm] theorem circuit_requirements : circuit.channelsWithRequirements = [] := rfl
@[circuit_norm] theorem circuit_guarantees : circuit.elaborated.channelsWithGuarantees = [] := rfl
@[circuit_norm] theorem circuit_length (input : Var Input Bit) : circuit.localLength input = 64 := by
  change (Adder.circuit 64).localLength { x := input.x, y := flip input.y input.sub, carry := input.sub } = 64
  simp only [circuit_norm]

theorem sum_correct (input : Input Bit) (output : Adder.Output 64 Bit) (h : Spec input output) :
    output.sum = Words.ofNat 64 (if input.sub = 1 then
      Adder.value input.x + 2 ^ 64 - Adder.value input.y
    else Adder.value input.x + Adder.value input.y) := by
  rcases bit_zero_or_one input.sub with hs | hs
  · simp only [Spec, hs, flip_zero, ZMod.val_zero, add_zero] at h
    simpa [hs] using AluWord.sum_add h
  · simp only [Spec, hs, flip_one, bit_one_val] at h
    simpa [hs] using AluWord.sum_sub h

theorem unsigned_correct (input : Input Bit) (output : Adder.Output 64 Bit)
    (hs : input.sub = 1) (h : Spec input output) :
    1 + output.carry = 1 ↔ Adder.value input.x < Adder.value input.y := by
  simp only [Spec, hs, flip_one, bit_one_val] at h
  have hb := AluWord.borrow h
  rcases bit_zero_or_one output.carry with hc | hc <;> simp [hc] at hb ⊢ <;> exact hb

theorem signed_correct (input : Input Bit) (output : Adder.Output 64 Bit)
    (hs : input.sub = 1) (h : Spec input output) :
    (1 + output.carry) + input.x[63] + input.y[63] = 1 ↔
      AluWord.signed input.x < AluWord.signed input.y :=
  AluWord.signed_less input.x input.y (1 + output.carry) (unsigned_correct input output hs h)

end LeanVMCircuits.AluArithmetic
