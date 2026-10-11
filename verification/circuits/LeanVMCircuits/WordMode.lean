module

public import LeanVMCircuits.BarrelShift

@[expose] public section

namespace LeanVMCircuits.Words

variable {α β : Type}

def lower (bits : Vector α 64) : Vector α 32 :=
  Vector.mapFinRange 32 fun i => bits[i.val]'(by omega)

def upper (bits : Vector α 64) : Vector α 32 :=
  Vector.mapFinRange 32 fun i => bits[32 + i.val]'(by omega)

def join (lo hi : Vector α 32) : Vector α 64 :=
  Vector.mapFinRange 64 fun i => if h : i.val < 32 then lo[i.val] else hi[i.val - 32]'(by omega)

def high (fill : α) (bits : Vector α 64) : Vector α 64 :=
  join (lower bits) (Vector.replicate 32 fill)

theorem lower_map (f : α → β) (bits : Vector α 64) :
    (lower bits).map f = lower (bits.map f) := by
  apply Vector.ext
  intro i hi
  simp [lower, Vector.getElem_mapFinRange]

theorem upper_map (f : α → β) (bits : Vector α 64) :
    (upper bits).map f = upper (bits.map f) := by
  apply Vector.ext
  intro i hi
  simp [upper, Vector.getElem_mapFinRange]

theorem join_map (f : α → β) (lo hi : Vector α 32) :
    (join lo hi).map f = join (lo.map f) (hi.map f) := by
  apply Vector.ext
  intro i hi
  simp only [join, Vector.getElem_map, Vector.getElem_mapFinRange]
  split <;> simp

theorem join_lower_upper (bits : Vector α 64) : join (lower bits) (upper bits) = bits := by
  apply Vector.ext
  intro i hi
  simp only [join, lower, upper, Vector.getElem_mapFinRange]
  by_cases h : i < 32
  · simp [h]
  · have heq : 32 + (i - 32) = i := by omega
    simp [h, heq]

end LeanVMCircuits.Words

namespace LeanVMCircuits.WordMode

structure Input (F : Type) where
  selector : F
  fill : F
  word : Vector F 64
  deriving ProvableStruct

def main (input : Var Input Bit) : Circuit Bit (Var (fields 64) Bit) := do
  let hi ← WordMux.circuit 32 { selector := input.selector, x := Vector.replicate 32 input.fill, y := Words.upper input.word }
  return Words.join (Words.lower input.word) hi

instance elaborated : ElaboratedCircuit Bit Input (fields 64) main := by elaborate_circuit

@[circuit_norm]
def circuit : FormalCircuit Bit Input (fields 64) where
  main
  elaborated
  Spec := fun input output => output = if input.selector = 1 then Words.high input.fill input.word else input.word
  soundness := by
    circuit_proof_start
    rcases h_input with ⟨hs, hf, hw⟩
    simp only [WordMux.Spec, WordMux.select, circuit_norm, Vector.map_replicate, Words.upper_map] at h_holds
    rw [hf, hw] at h_holds
    simp only [Words.join_map, Words.lower_map, hw]
    dsimp +instances only [WordMux.circuit] at h_holds ⊢
    simp only [FormalCircuitBase.output] at h_holds ⊢
    rw [h_holds]
    by_cases h : input_selector = 1 <;> simp [h, Words.high, Words.join_lower_upper]
  completeness := by circuit_proof_start

end LeanVMCircuits.WordMode
