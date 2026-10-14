module

public import LeanVMCircuits.ClockStep
public import LeanVMCircuits.Flatten
public import LeanVMCircuits.Completeness
import all Init.Data.Array.Basic
import all Init.Data.Vector.FinRange

-- Closed kernel reduction traverses every access's compare and the carry chain.
set_option maxRecDepth 65536

@[expose] public section

/-!
# The clock circuits production builds

`ClockStep.circuit` lowered to Flock rows for each slot list of a production table's clock circuit (`TableId::ALL`'s
`ClassSpec::slots` in `crates/leanvm_core/src/tables/spec.rs`), whose emitted gates `Clock::builder` builds:

- `Registers`: `[0, 1, 3]` (ALU, SHIFT, MUL, MULH, DIV);
- `Load`: `[0, 3, 2]` (LOAD, LD);
- `Store`: `[0, 1, 2]` (STORE, SD);
- `Hash`: `[0, 1, .., 17]` (HASH);
- `Ext`: `[0, 1, 3, 4, .., 12]` (EXT).

Each artifact's input variables are the clock port's bits 5 to 40 at `0` to `35`, then bit `b` of the `i`-th previous
timestamp at `36 + 41 i + b`; its outputs are the step port's bits 5 to 41, of which bits 6 to 40 are the carry chain's
products, which Rust commits straight to the step port (`outputProducts`). Each list's `soundness` says that every
assignment satisfying the rows spells ports with `Clock.Holds`.
-/

namespace LeanVMCircuits.Flock.Clock

open LeanVMCircuits

/-- The variables of `n` accesses' clock circuit: the clock's bits 5 to 40, then each previous timestamp's 41 bits. -/
def inputs (n : ℕ) : Var (ClockStep.Input n) Bit := {
  ts := Vector.mapFinRange 36 fun j => .var ⟨j.val⟩
  prev := Vector.mapFinRange n fun i => Vector.mapFinRange 41 fun b => .var ⟨36 + 41 * i.val + b.val⟩
}

/-- The input variables of `n` accesses. -/
def width (n : ℕ) : ℕ := 36 + 41 * n

def source (slot : Fin 32) (rest : List (Fin 32)) :=
  (ClockStep.circuit slot rest).toSubcircuit (width (rest.length + 1)) (inputs (rest.length + 1))

def output (slot : Fin 32) (rest : List (Fin 32)) :=
  (ClockStep.circuit slot rest).output (inputs (rest.length + 1)) (width (rest.length + 1))

def lowerClock (slot : Fin 32) (rest : List (Fin 32)) : Except String Artifact :=
  lowerAt (source slot rest).ops (toElements (M := fields 37) (output slot rest)).toList

/-- The clock's integer at an assignment: its bits 5 to 40 at variables 0 to 35. -/
def tsNum (assignment : ℕ → Bit) : ℕ := 2 ^ 5 * Adder.value (Vector.ofFn fun j : Fin 36 => assignment j.val)

/-- Each of `n` previous timestamps' integers at an assignment: the `i`-th's 41 bits at variables `36 + 41 i` on. -/
def prevNums (n : ℕ) (assignment : ℕ → Bit) : List ℕ :=
  (Vector.ofFn fun i : Fin n => Vector.ofFn fun b : Fin 41 => assignment (36 + 41 * i.val + b.val)).toList.map
    Adder.value

/-- The step port's integer at an assignment: an artifact's outputs are its bits 5 to 41. -/
def stepNum (artifact : Artifact) (assignment : ℕ → Bit) : ℕ := 2 ^ 5 * artifact.value assignment

theorem eval_inputs (n : ℕ) (env : Environment Bit) :
    eval env (inputs n) = {
      ts := Vector.ofFn fun j : Fin 36 => env.get j.val
      prev := Vector.ofFn fun i : Fin n => Vector.ofFn fun b : Fin 41 => env.get (36 + 41 * i.val + b.val) } := by
  simp only [inputs, circuit_norm]
  refine ⟨?_, ?_⟩
  · apply Vector.ext; intro j hj
    simp [Vector.getElem_mapFinRange, circuit_norm]
  · rw [eval_vector]
    apply Vector.ext; intro i hi
    apply Vector.ext; intro b hb
    simp [Vector.getElem_mapFinRange, ProvableType.eval_fields, circuit_norm]

theorem value_outputs (artifact : Artifact) (assignment : ℕ → Bit) :
    artifact.value assignment = ClockValues.valueL (artifact.outputs.map (Affine.eval assignment)) := by
  rw [Artifact.value, ClockValues.valueL, List.foldr_map]

theorem value_toElements {n : ℕ} (v : fields n Bit) :
    ClockValues.valueL (toElements (M := fields n) v).toList = Adder.value v := rfl

/-- A lowering of the clock circuit of `slot :: rest`: every assignment satisfying its rows spells ports with
`Clock.Holds`. -/
theorem soundness_of (slot : Fin 32) (rest : List (Fin 32)) (artifact : Artifact)
    (hcode : lowerClock slot rest = .ok artifact) (env : Environment Bit)
    (hrows : artifact.rows.Forall (Row.Holds env.get)) :
    LeanVMCircuits.Clock.Holds ((slot :: rest).map Fin.val) (prevNums (rest.length + 1) env.get) (tsNum env.get)
      (stepNum artifact env.get) := by
  have h := lowerAt_correct _ _ artifact hcode env
  have hs := ((source slot rest).soundness env (by change True; trivial) (h.1.mp hrows) h.2.1).1
  change ClockStep.Spec (slot :: rest) (eval env (inputs (rest.length + 1))) (eval env (output slot rest)) at hs
  have hout : artifact.value env.get = Adder.value (eval env (output slot rest)) := by
    rw [value_outputs, h.2.2, ← Vector.toList_map, ← ProvableType.toElements_eval]
    exact value_toElements _
  rw [eval_inputs] at hs
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h36 := Adder.value_lt (Vector.ofFn fun j : Fin 36 => env.get j.val)
    show 2 ^ 5 * _ < 2 ^ 41
    have h41 : (2 : ℕ) ^ 41 = 2 ^ 5 * 2 ^ 36 := by norm_num
    rw [h41]
    exact Nat.mul_lt_mul_of_pos_left h36 (by norm_num)
  · exact ⟨_, rfl⟩
  · simp [prevNums]
  · intro p hp
    simp only [prevNums, List.mem_map] at hp
    obtain ⟨v, -, rfl⟩ := hp
    exact Adder.value_lt v
  · rw [stepNum, hout, hs]
    rfl

end LeanVMCircuits.Flock.Clock

/-! The clock circuit of the registers' slots (ALU, SHIFT, MUL, MULH, DIV), `[0, 1, 3]`. -/
namespace LeanVMCircuits.Flock.Clock.Registers

open LeanVMCircuits.Flock.Clock

theorem supported : (lowerClock 0 [1, 3]).isOk = true := by decide +kernel

def artifact : Artifact := checked (lowerClock 0 [1, 3]) supported

theorem source_eq : lowerClock 0 [1, 3] = .ok artifact := checked_eq _ _

theorem soundness (env : Environment Bit) (hrows : artifact.rows.Forall (Row.Holds env.get)) :
    LeanVMCircuits.Clock.Holds [0, 1, 3] (prevNums 3 env.get) (tsNum env.get) (stepNum artifact env.get) :=
  soundness_of 0 [1, 3] artifact source_eq env hrows

theorem layout :
    artifact.rows.map Row.output = (List.range 154).map (159 + ·) ∧ artifact.outputs.length = 37 := by
  decide +kernel

/-- The step's carries are its bits 6 to 40, not private product slots. -/
def outputProducts : List (Nat × Nat × Nat) := (List.range 35).map fun j => (278 + j, 0, 6 + j)

theorem output_products_layout :
    (artifact.outputs.drop 1).take 35 = (List.range 35).map (fun j => Affine.var (278 + j)) := by
  decide +kernel

theorem wellFormed : Flock.wellFormed 159 artifact.rows = true := by decide +kernel

theorem complete (initial : ℕ → Bit) :
    ∃ final, AgreeBelow 159 initial final ∧ artifact.rows.Forall (Row.Holds final) :=
  witness_exists artifact.rows 159 initial wellFormed

end LeanVMCircuits.Flock.Clock.Registers

/-! The clock circuit of a load's slots (LOAD, LD), `[0, 3, 2]`. -/
namespace LeanVMCircuits.Flock.Clock.Load

open LeanVMCircuits.Flock.Clock

theorem supported : (lowerClock 0 [3, 2]).isOk = true := by decide +kernel

def artifact : Artifact := checked (lowerClock 0 [3, 2]) supported

theorem source_eq : lowerClock 0 [3, 2] = .ok artifact := checked_eq _ _

theorem soundness (env : Environment Bit) (hrows : artifact.rows.Forall (Row.Holds env.get)) :
    LeanVMCircuits.Clock.Holds [0, 3, 2] (prevNums 3 env.get) (tsNum env.get) (stepNum artifact env.get) :=
  soundness_of 0 [3, 2] artifact source_eq env hrows

theorem layout :
    artifact.rows.map Row.output = (List.range 153).map (159 + ·) ∧ artifact.outputs.length = 37 := by
  decide +kernel

/-- The step's carries are its bits 6 to 40, not private product slots. -/
def outputProducts : List (Nat × Nat × Nat) := (List.range 35).map fun j => (277 + j, 0, 6 + j)

theorem output_products_layout :
    (artifact.outputs.drop 1).take 35 = (List.range 35).map (fun j => Affine.var (277 + j)) := by
  decide +kernel

theorem wellFormed : Flock.wellFormed 159 artifact.rows = true := by decide +kernel

theorem complete (initial : ℕ → Bit) :
    ∃ final, AgreeBelow 159 initial final ∧ artifact.rows.Forall (Row.Holds final) :=
  witness_exists artifact.rows 159 initial wellFormed

end LeanVMCircuits.Flock.Clock.Load

/-! The clock circuit of a store's slots (STORE, SD), `[0, 1, 2]`. -/
namespace LeanVMCircuits.Flock.Clock.Store

open LeanVMCircuits.Flock.Clock

theorem supported : (lowerClock 0 [1, 2]).isOk = true := by decide +kernel

def artifact : Artifact := checked (lowerClock 0 [1, 2]) supported

theorem source_eq : lowerClock 0 [1, 2] = .ok artifact := checked_eq _ _

theorem soundness (env : Environment Bit) (hrows : artifact.rows.Forall (Row.Holds env.get)) :
    LeanVMCircuits.Clock.Holds [0, 1, 2] (prevNums 3 env.get) (tsNum env.get) (stepNum artifact env.get) :=
  soundness_of 0 [1, 2] artifact source_eq env hrows

theorem layout :
    artifact.rows.map Row.output = (List.range 153).map (159 + ·) ∧ artifact.outputs.length = 37 := by
  decide +kernel

/-- The step's carries are its bits 6 to 40, not private product slots. -/
def outputProducts : List (Nat × Nat × Nat) := (List.range 35).map fun j => (277 + j, 0, 6 + j)

theorem output_products_layout :
    (artifact.outputs.drop 1).take 35 = (List.range 35).map (fun j => Affine.var (277 + j)) := by
  decide +kernel

theorem wellFormed : Flock.wellFormed 159 artifact.rows = true := by decide +kernel

theorem complete (initial : ℕ → Bit) :
    ∃ final, AgreeBelow 159 initial final ∧ artifact.rows.Forall (Row.Holds final) :=
  witness_exists artifact.rows 159 initial wellFormed

end LeanVMCircuits.Flock.Clock.Store

/-! The clock circuit of HASH's slots, `[0, 1, .., 17]`. -/
namespace LeanVMCircuits.Flock.Clock.Hash

open LeanVMCircuits.Flock.Clock

theorem supported : (lowerClock 0 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]).isOk = true := by decide +kernel

def artifact : Artifact := checked (lowerClock 0 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]) supported

theorem source_eq : lowerClock 0 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17] = .ok artifact := checked_eq _ _

theorem soundness (env : Environment Bit) (hrows : artifact.rows.Forall (Row.Holds env.get)) :
    LeanVMCircuits.Clock.Holds [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17] (prevNums 18 env.get) (tsNum env.get) (stepNum artifact env.get) :=
  soundness_of 0 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17] artifact source_eq env hrows

theorem layout :
    artifact.rows.map Row.output = (List.range 754).map (774 + ·) ∧ artifact.outputs.length = 37 := by
  decide +kernel

/-- The step's carries are its bits 6 to 40, not private product slots. -/
def outputProducts : List (Nat × Nat × Nat) := (List.range 35).map fun j => (1493 + j, 0, 6 + j)

theorem output_products_layout :
    (artifact.outputs.drop 1).take 35 = (List.range 35).map (fun j => Affine.var (1493 + j)) := by
  decide +kernel

theorem wellFormed : Flock.wellFormed 774 artifact.rows = true := by decide +kernel

theorem complete (initial : ℕ → Bit) :
    ∃ final, AgreeBelow 774 initial final ∧ artifact.rows.Forall (Row.Holds final) :=
  witness_exists artifact.rows 774 initial wellFormed

end LeanVMCircuits.Flock.Clock.Hash

/-! The clock circuit of EXT's slots, `[0, 1, 3, 4, .., 12]`. -/
namespace LeanVMCircuits.Flock.Clock.Ext

open LeanVMCircuits.Flock.Clock

theorem supported : (lowerClock 0 [1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]).isOk = true := by decide +kernel

def artifact : Artifact := checked (lowerClock 0 [1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]) supported

theorem source_eq : lowerClock 0 [1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] = .ok artifact := checked_eq _ _

theorem soundness (env : Environment Bit) (hrows : artifact.rows.Forall (Row.Holds env.get)) :
    LeanVMCircuits.Clock.Holds [0, 1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] (prevNums 12 env.get) (tsNum env.get) (stepNum artifact env.get) :=
  soundness_of 0 [1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] artifact source_eq env hrows

theorem layout :
    artifact.rows.map Row.output = (List.range 514).map (528 + ·) ∧ artifact.outputs.length = 37 := by
  decide +kernel

/-- The step's carries are its bits 6 to 40, not private product slots. -/
def outputProducts : List (Nat × Nat × Nat) := (List.range 35).map fun j => (1007 + j, 0, 6 + j)

theorem output_products_layout :
    (artifact.outputs.drop 1).take 35 = (List.range 35).map (fun j => Affine.var (1007 + j)) := by
  decide +kernel

theorem wellFormed : Flock.wellFormed 528 artifact.rows = true := by decide +kernel

theorem complete (initial : ℕ → Bit) :
    ∃ final, AgreeBelow 528 initial final ∧ artifact.rows.Forall (Row.Holds final) :=
  witness_exists artifact.rows 528 initial wellFormed

end LeanVMCircuits.Flock.Clock.Ext
