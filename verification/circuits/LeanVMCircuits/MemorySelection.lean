module

public import LeanVMCircuits.MemorySemantics

@[expose] public section

namespace LeanVMCircuits.LoadSign

structure Input (F : Type) where
  low : F
  high : F
  signed : F
  bit7 : F
  bit15 : F
  bit31 : F
  deriving ProvableStruct

def sign (input : Input Bit) : Bit :=
  if input.signed = 1 then
    if input.low = 1 then input.bit15 else if input.high = 1 then input.bit31 else input.bit7
  else 0

def main (input : Var Input Bit) : Circuit Bit (Expression Bit) := do
  let ge2 := input.low + input.high
  let first ← Product.circuit { x := 1 + ge2, y := input.bit7 }
  let second ← Product.circuit { x := ge2 + input.high, y := input.bit15 }
  let third ← Product.circuit { x := input.high, y := input.bit31 }
  Product.circuit { x := input.signed, y := first + second + third }

instance elaborated : ElaboratedCircuit Bit Input field main := by elaborate_circuit

@[circuit_norm]
def circuit : FormalCircuit Bit Input field where
  main
  elaborated
  Assumptions := fun input => Memory.LegalWidth input.low input.high
  Spec := fun input output => output = sign input
  soundness := by
    circuit_proof_start [main, Product.circuit, Product.Spec]
    rcases h_holds with ⟨hfirst, hsecond, hthird, hext⟩
    rw [hext, hfirst, hsecond, hthird]
    rcases bit_zero_or_one input_low with hlow | hlow <;>
      rcases bit_zero_or_one input_high with hhigh | hhigh <;>
      rcases bit_zero_or_one input_signed with hsigned | hsigned <;>
      simp_all [Memory.LegalWidth, Memory.logWidth, sign]
  completeness := by circuit_proof_start [main, Product.circuit]

@[circuit_norm] theorem circuit_length (input : Var Input Bit) :
    circuit.localLength input = 4 := by
  change ElaboratedCircuit.localLength (Output := field) main input = 4
  rw [← ElaboratedCircuit.localLength_eq (Output := field) (main := main) input 0]
  simp only [main, Product.circuit, circuit_norm]

end LeanVMCircuits.LoadSign

namespace LeanVMCircuits.Memory

def extend (low high signed : Bit) (word : Vector Bit 32) : Vector Bit 64 :=
  let width := 8 * 2 ^ logWidth low high
  Vector.mapFinRange 64 fun i =>
    if i.val < width then Words.filled word 0 i.val
    else if signed = 1 then Words.filled word 0 (width - 1) else 0

theorem load_eq_extend (low high signed : Bit) (address cell : Vector Bit 64)
    (hlegal : LegalWidth low high) :
    load low high signed address cell =
      extend low high signed (Words.resize 32 0 (Words.right (8 * offset address) 0 cell)) := by
  have hwidth : 8 * 2 ^ logWidth low high ≤ 32 := by
    simp [LegalWidth] at hlegal
    rcases hlegal with h | h | h <;> rw [h] <;> decide
  have hpositive : 0 < 8 * 2 ^ logWidth low high := by positivity
  apply Vector.ext
  intro i hi
  simp only [load, extend, Vector.getElem_mapFinRange]
  by_cases hin : i < 8 * 2 ^ logWidth low high
  · have hi32 : i < 32 := by omega
    simp [hin, Words.filled, Words.resize, Vector.getElem_mapFinRange, hi32, hi]
  · have htop32 : 8 * 2 ^ logWidth low high - 1 < 32 := by omega
    have htop64 : 8 * 2 ^ logWidth low high - 1 < 64 := by omega
    simp [hin, Words.filled, Words.resize, Vector.getElem_mapFinRange, htop32, htop64]

end LeanVMCircuits.Memory

namespace LeanVMCircuits.LoadExtend

def assemble {F : Type} (lower middle : Vector F 8) (upper : Vector F 16) (extension : F) : Vector F 64 :=
  Vector.mapFinRange 64 fun i =>
    if h : i.val < 8 then lower[i.val]
    else if h : i.val < 16 then middle[i.val - 8]'(by omega)
    else if h : i.val < 32 then upper[i.val - 16]'(by omega)
    else extension

theorem assemble_map {F G : Type} (f : F → G)
    (lower middle : Vector F 8) (upper : Vector F 16) (extension : F) :
    (assemble lower middle upper extension).map f =
      assemble (lower.map f) (middle.map f) (upper.map f) (f extension) := by
  apply Vector.ext
  intro i hi
  simp only [assemble, Vector.getElem_map, Vector.getElem_mapFinRange]
  by_cases h8 : i < 8 <;> by_cases h16 : i < 16 <;> by_cases h32 : i < 32 <;>
    simp [h8, h16, h32]

theorem assemble_selection (low high signed : Bit) (word : Vector Bit 32)
    (hlegal : Memory.LegalWidth low high) :
    let extension := LoadSign.sign { low, high, signed, bit7 := word[7], bit15 := word[15], bit31 := word[31] }
    assemble (Words.resize 8 0 word)
      (WordMux.select 8 {
        selector := low + high
        x := Words.resize 8 0 (Words.right 8 0 word)
        y := Vector.replicate 8 extension
      })
      (WordMux.select 16 {
        selector := high
        x := Words.resize 16 0 (Words.right 16 0 word)
        y := Vector.replicate 16 extension
      })
      extension = Memory.extend low high signed word := by
  rcases bit_zero_or_one low with rfl | rfl <;>
    rcases bit_zero_or_one high with rfl | rfl <;>
    norm_num [Memory.LegalWidth, Memory.logWidth] at hlegal
  all_goals
    apply Vector.ext
    intro i hi
    by_cases h8 : i < 8
    · have h16 : i < 16 := by omega
      have h32 : i < 32 := by omega
      simp [assemble, Memory.extend, Memory.logWidth, WordMux.select, LoadSign.sign,
        Words.resize, Words.right, Words.filled, Vector.getElem_mapFinRange, h8, h16, h32]
    · have hs8 : i - 8 + 8 = i := by omega
      by_cases h16 : i < 16
      · have h32 : i < 32 := by omega
        have hj8 : i - 8 < 32 := by omega
        simp [assemble, Memory.extend, Memory.logWidth, WordMux.select, LoadSign.sign,
          Words.resize, Words.right, Words.filled, Vector.getElem_mapFinRange, h8, h16, h32, hj8, hs8]
      · have hs16 : i - 16 + 16 = i := by omega
        by_cases h32 : i < 32
        · have hj16 : i - 16 < 32 := by omega
          simp [assemble, Memory.extend, Memory.logWidth, WordMux.select, LoadSign.sign,
            Words.resize, Words.right, Words.filled, Vector.getElem_mapFinRange, h8, h16, h32, hj16, hs16]
        · simp [assemble, Memory.extend, Memory.logWidth, WordMux.select, LoadSign.sign,
            Words.resize, Words.right, Words.filled, Vector.getElem_mapFinRange, h8, h16, h32]

structure Input (F : Type) where
  low : F
  high : F
  signed : F
  word : Vector F 32
  deriving ProvableStruct

def main (input : Var Input Bit) : Circuit Bit (Var (fields 64) Bit) := do
  let extension ← LoadSign.circuit {
    low := input.low, high := input.high, signed := input.signed,
    bit7 := input.word[7], bit15 := input.word[15], bit31 := input.word[31]
  }
  let middle ← WordMux.circuit 8 {
    selector := input.low + input.high
    x := Words.resize 8 0 (Words.right 8 0 input.word)
    y := Vector.replicate 8 extension
  }
  let upper ← WordMux.circuit 16 {
    selector := input.high
    x := Words.resize 16 0 (Words.right 16 0 input.word)
    y := Vector.replicate 16 extension
  }
  return assemble (Words.resize 8 0 input.word) middle upper extension

instance elaborated : ElaboratedCircuit Bit Input (fields 64) main := by elaborate_circuit

def circuit : FormalCircuit Bit Input (fields 64) where
  main
  elaborated
  Assumptions := fun input => Memory.LegalWidth input.low input.high
  Spec := fun input output => output = Memory.extend input.low input.high input.signed input.word
  soundness := by
    circuit_proof_start [main, LoadSign.circuit]
    rcases h_input with ⟨hl, hh, hs, hw⟩
    have h7 := congrArg (fun v : Vector Bit 32 => v[7]) hw
    have h15 := congrArg (fun v : Vector Bit 32 => v[15]) hw
    have h31 := congrArg (fun v : Vector Bit 32 => v[31]) hw
    simp only [Vector.getElem_map] at h7 h15 h31
    simp only [WordMux.Spec, circuit_norm, Words.resize_map, Words.right_map,
      Vector.map_replicate, h7, h15, h31, hw] at h_holds
    rcases h_holds with ⟨hextension, hmiddle, hupper⟩
    have hextension := hextension h_assumptions
    dsimp +instances only [FormalCircuitBase.output, WordMux.circuit] at hmiddle hupper ⊢
    simp only [← ElaboratedCircuit.output_eq, circuit_norm] at hmiddle hupper ⊢
    simp only [assemble_map, Words.resize_map, hw]
    rw [hmiddle, hupper, hextension]
    simpa only [circuit_norm, hextension] using
      assemble_selection input_low input_high input_signed input_word h_assumptions
  completeness := by
    circuit_proof_start [main, LoadSign.circuit]
    exact h_assumptions

@[circuit_norm] theorem circuit_assumptions :
    circuit.Assumptions = fun input => Memory.LegalWidth input.low input.high := rfl
@[circuit_norm] theorem circuit_spec :
    circuit.Spec = fun input output => output = Memory.extend input.low input.high input.signed input.word := rfl
@[circuit_norm] theorem circuit_requirements :
    circuit.channelsWithRequirements = [] := by simp only [circuit, circuit_norm]
@[circuit_norm] theorem circuit_guarantees :
    circuit.elaborated.channelsWithGuarantees = [] := by
  dsimp +instances only [circuit, elaborated]
  simp only [circuit_norm]

@[circuit_norm] theorem circuit_length (input : Var Input Bit) :
    circuit.localLength input = 28 := by
  change ElaboratedCircuit.localLength main input = 28
  rw [← ElaboratedCircuit.localLength_eq (main := main) input 0]
  simp only [main, circuit_norm]

end LeanVMCircuits.LoadExtend
