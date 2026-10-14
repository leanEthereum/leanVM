module

public import LeanVMCircuits.AluLogicWord
public import LeanVMCircuits.WordMode
public import LeanVMCircuits.WordScale

@[expose] public section

namespace LeanVMCircuits.AluSelector
set_option maxRecDepth 65536


structure Input (F : Type) where
  x : Vector F 64
  y : Vector F 64
  sum : Vector F 64
  difference : Vector F 64
  flags : Vector F 15
  lt : F
  ltu : F
  deriving ProvableStruct

def none {α : Type} [Add α] [OfNat α 1] (flags : Vector α 15) : α :=
  (1 : α) + flags[2] + flags[3] + flags[4] + flags[5] + flags[6]

def combine {α : Type} [Add α] [Zero α] (masked logical : Vector α 64)
    (lt ltu : α) : Vector α 64 := Vector.mapFinRange 64 fun i =>
  masked[i.val] + logical[i.val] + if i.val = 0 then lt + ltu else 0

theorem eval_combine (env : Environment Bit) (masked logical : Vector (Expression Bit) 64)
    (lt ltu : Expression Bit) :
    (combine masked logical lt ltu).map (Expression.eval env) =
      combine (masked.map (Expression.eval env)) (logical.map (Expression.eval env))
        (Expression.eval env lt) (Expression.eval env ltu) := by
  apply Vector.ext
  intro i hi
  simp only [combine, Vector.getElem_map, Vector.getElem_mapFinRange]
  split <;> simp [circuit_norm]

def main (input : Var Input Bit) : Circuit Bit (Var (fields 64) Bit) := do
  let extended ← WordMode.circuit { selector := input.flags[1], fill := input.sum[31], word := input.sum }
  let masked ← WordScale.circuit 64 { selector := none input.flags, word := extended }
  let logical ← AluLogicWord.circuit 64 {
    andOr := input.flags[4] + input.flags[5]
    orXor := input.flags[5] + input.flags[6]
    x := input.x
    y := input.y
    difference := input.difference
  }
  let lt ← Product.circuit { x := input.flags[2], y := input.lt }
  let ltu ← Product.circuit { x := input.flags[3], y := input.ltu }
  return combine masked logical lt ltu

instance elaborated : ElaboratedCircuit Bit Input (fields 64) main := by elaborate_circuit

def selected (input : Input Bit) : Vector Bit 64 :=
  let extended := if input.flags[1] = 1 then Words.high input.sum[31] input.sum else input.sum
  let masked := if none input.flags = 1 then extended else Vector.replicate 64 0
  let logical := AluLogicWord.select 64 {
    andOr := input.flags[4] + input.flags[5]
    orXor := input.flags[5] + input.flags[6]
    x := input.x
    y := input.y
    difference := input.difference
  }
  combine masked logical (input.flags[2] * input.lt) (input.flags[3] * input.ltu)

def Spec (input : Input Bit) (output : Vector Bit 64) : Prop := output = selected input

def circuit : FormalCircuit Bit Input (fields 64) where
  main
  elaborated
  Spec
  soundness := by
    circuit_proof_start [main, Spec, WordScale.Spec, Product.Spec, AluLogicWord.Spec]
    rcases h_input with ⟨hx, hy, hs, hd, hf, hlt, hltu⟩
    have hflag (i : ℕ) (hi : i < 15) := congrArg (fun flags : Vector Bit 15 => flags[i]) hf
    simp only [Vector.getElem_map] at hflag
    have hsign := congrArg (fun word : Vector Bit 64 => word[31]) hs
    simp only [Vector.getElem_map] at hsign
    simp only [circuit_norm, none, hflag, hsign] at h_holds
    simp only [eval_combine, none]
    rcases h_holds with ⟨hextended, hmasked, hlogical, hlt, hltu⟩
    simp only [WordScale.select_boolean] at hmasked
    simp only [FormalCircuitBase.output, WordScale.circuit] at hmasked
    simp only [FormalCircuitBase.output, AluLogicWord.circuit] at hlogical
    have hmask := hmasked.trans (congrArg (fun word : Vector Bit 64 =>
      if none input_flags = 1 then word else Vector.replicate 64 0) hextended)
    exact congrArg₂ (fun (words : Vector Bit 64 × Vector Bit 64) (terms : Bit × Bit) =>
      combine words.1 words.2 terms.1 terms.2)
      (congrArg₂ Prod.mk hmask hlogical) (congrArg₂ Prod.mk hlt hltu)
  completeness := by circuit_proof_start [main]
@[circuit_norm] theorem circuit_assumptions : circuit.Assumptions = fun _ => True := rfl
@[circuit_norm] theorem circuit_spec : circuit.Spec = Spec := rfl
@[circuit_norm] theorem circuit_requirements : circuit.channelsWithRequirements = [] := rfl
@[circuit_norm] theorem circuit_guarantees : circuit.elaborated.channelsWithGuarantees = [] := rfl
@[circuit_norm] theorem circuit_length (input : Var Input Bit) : circuit.localLength input = 290 := by
  change 32 + 64 + 192 + 1 + 1 = 290
  rfl


end LeanVMCircuits.AluSelector
