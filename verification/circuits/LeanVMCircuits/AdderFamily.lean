module

public import LeanVMCircuits.Completeness

@[expose] public section

namespace LeanVMCircuits.Flock

def adder32 : Artifact := checked (lowerCircuit 31) (by decide +kernel)

theorem adder32_source : lowerCircuit 31 = .ok adder32 := checked_eq _ _

theorem adder32_soundness (env : Environment Bit)
    (hrows : adder32.rows.Forall (Row.Holds env.get)) :
    adder32.value env.get =
      (Adder.value ((inputs 31).x.map (Expression.eval env)) +
        Adder.value ((inputs 31).y.map (Expression.eval env))) % 2 ^ 32 :=
  exported_soundness 31 adder32 adder32_source env hrows

theorem adder32_layout :
    adder32.rows.map Row.output = (List.range 31).map (64 + ·) ∧ adder32.outputs.length = 32 := by
  decide +kernel

theorem adder32_wellFormed : wellFormed 64 adder32.rows = true := by decide +kernel

theorem adder32_complete (inputs : ℕ → Bit) :
    ∃ assignment, AgreeBelow 64 inputs assignment ∧ adder32.rows.Forall (Row.Holds assignment) :=
  witness_exists adder32.rows 64 inputs adder32_wellFormed

def carryInputs (n : ℕ) : Var (Adder.Input n) Bit :=
  { x := Vector.mapRange n fun i => var ⟨i⟩,
    y := Vector.mapRange n fun i => var ⟨n + i⟩,
    carry := var ⟨2 * n⟩ }

def carrySource (n : ℕ) := (Adder.circuit n).toSubcircuit (2 * n + 1) (carryInputs n)

def carryOutput (n : ℕ) : Vector (Expression Bit) (n + 1) :=
  let output := (Adder.circuit n).output (carryInputs n) (2 * n + 1)
  output.sum.push output.carry

def lowerCarry (n : ℕ) : Except String Artifact :=
  lowerAt (carrySource n).ops (carryOutput n).toList

theorem carry_exported_soundness (n : ℕ) (artifact : Artifact)
    (hcode : lowerCarry n = .ok artifact) (env : Environment Bit)
    (hrows : artifact.rows.Forall (Row.Holds env.get)) :
    artifact.value env.get = Adder.value ((carryInputs n).x.map (Expression.eval env)) +
      Adder.value ((carryInputs n).y.map (Expression.eval env)) + (env.get (2 * n)).val := by
  have h := lowerAt_correct _ _ artifact hcode env
  have hassumptions : (carrySource n).Assumptions env := by
    change (Adder.circuit n).Assumptions (eval env (carryInputs n))
    rw [Adder.circuit_assumptions]
    trivial
  have hspec := ((carrySource n).soundness env hassumptions (h.1.mp hrows) h.2.1).1
  change (Adder.circuit n).Spec (eval env (carryInputs n))
    (eval env ((Adder.circuit n).output (carryInputs n) (2 * n + 1))) at hspec
  rw [Adder.circuit_spec] at hspec
  dsimp [Artifact.value]
  rw [← List.foldr_map (f := Affine.eval env.get) (g := fun b acc => b.val + 2 * acc), h.2.2,
    ← Vector.toList_map]
  change Adder.value ((carryOutput n).map (Expression.eval env)) = _
  rw [carryOutput, Vector.map_push, Adder.value_push]
  generalize hout : (Adder.circuit n).output (carryInputs n) (2 * n + 1) = output at *
  rcases output with ⟨sum, carry⟩
  provable_struct_simp
  simpa only [Adder.Spec, carryInputs, circuit_norm] using hspec

def carryAdder64 : Artifact := checked (lowerCarry 64) (by decide +kernel)

theorem carryAdder64_source : lowerCarry 64 = .ok carryAdder64 := checked_eq _ _

theorem carryAdder64_soundness (env : Environment Bit)
    (hrows : carryAdder64.rows.Forall (Row.Holds env.get)) :
    carryAdder64.value env.get = Adder.value ((carryInputs 64).x.map (Expression.eval env)) +
      Adder.value ((carryInputs 64).y.map (Expression.eval env)) + (env.get 128).val :=
  carry_exported_soundness 64 carryAdder64 carryAdder64_source env hrows

theorem carryAdder64_layout :
    carryAdder64.rows.map Row.output = (List.range 64).map (129 + ·) ∧
      carryAdder64.outputs.length = 65 := by decide +kernel

theorem carryAdder64_wellFormed : wellFormed 129 carryAdder64.rows = true := by decide +kernel

theorem carryAdder64_complete (inputs : ℕ → Bit) :
    ∃ assignment, AgreeBelow 129 inputs assignment ∧ carryAdder64.rows.Forall (Row.Holds assignment) :=
  witness_exists carryAdder64.rows 129 inputs carryAdder64_wellFormed

end LeanVMCircuits.Flock
