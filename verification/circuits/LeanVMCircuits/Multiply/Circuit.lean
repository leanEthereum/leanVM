module

public import LeanVMCircuits.Multiply.Checked
public import LeanVMCircuits.WordValues

@[expose] public section

/-!
The multiplier as a Clean circuit: the low `n` bits of the product of two words, for `n` 64 or 128.
-/

namespace LeanVMCircuits.Multiply

open LeanVMCircuits Netlist BigOperators Finset

structure Input (F : Type) where
  a : Vector F 64
  b : Vector F 64
  deriving ProvableStruct

/-- Input `j` of the gates: `a_j`, then `b_{j - 64}`. -/
def inputsOf (input : Var Input Bit) (j : ℕ) : Expression Bit :=
  if h : j < 64 then input.a[j] else if h' : j - 64 < 64 then input.b[j - 64] else 0

/-- The product's bits: the ripple's sums. -/
def outs (n : ℕ) : Vector Aff n := Vector.mapRange n fun p => .loc (rippleBase n 64 + 5 * p + 4)

/-- The number of gates: 64 steps, as `Checked` shows for both widths, then the ripple. -/
def total (n : ℕ) : ℕ := rippleBase n 64 + 5 * n

theorem plan_steps (n : ℕ) (hn : n = 64 ∨ n = 128) : (plan n).1.length = 64 := by
  rcases hn with rfl | rfl; exacts [steps64, steps128]

theorem gates_length (n : ℕ) (hn : n = 64 ∨ n = 128) : (layout n).gates.length = total n := by
  simp only [Layout.gates, List.length_map, List.length_range, Layout.total, total]
  rw [show (layout n).steps = (plan n).1 from rfl, plan_steps n hn]; rfl

def main (n : ℕ) (input : Var Input Bit) : Circuit Bit (Var (fields n) Bit) :=
  Netlist.main inputsOf (layout n).gates (outs n) input

@[instance_reducible] def elaborated (n : ℕ) (hn : n = 64 ∨ n = 128) : ElaboratedCircuit Bit Input (fields n) (main n) :=
  Netlist.elaborated inputsOf (layout n).gates (outs n) (total n) (gates_length n hn)

def Spec (n : ℕ) (input : Input Bit) (output : Vector Bit n) : Prop :=
  Adder.value output = Adder.value input.a * Adder.value input.b % 2 ^ n

theorem value_eq_sum : ∀ {n : ℕ} (v : Vector Bit n),
    (Adder.value v : ℤ) = ∑ i ∈ range n, 2 ^ i * iv (if h : i < n then v[i] else 0)
  | 0, v => by simp [Adder.value_zero]
  | n + 1, v => by
    rw [Adder.value_pop, Finset.sum_range_succ]
    push_cast
    rw [value_eq_sum v.pop]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      have hi' : i < n := by simpa using Finset.mem_range.mp hi
      simp [hi', Nat.le_of_lt hi']
    · simp [iv]

theorem holds_of (n : ℕ) (env : Environment Bit) (input : Var Input Bit) (offset : ℕ)
    (h : ConstraintsHold.Soundness env ((main n input).operations offset)) (i : ℕ) (hi : i < (layout n).total) :
    ((layout n).gateAt i).Holds (fun j => (inputsOf input j).eval env) (fun l => env.get (offset + l)) i := by
  have := (holds_iff env (inputsOf input) offset 0 (layout n).gates).mp h i (by simpa [Layout.gates] using hi)
  simpa [Layout.gates] using this

theorem eval_inputs (env : Environment Bit) (input_var : Var Input Bit) (input : Input Bit)
    (h : eval env input_var = input) :
    word (aBits fun j => (inputsOf input_var j).eval env) = Adder.value input.a ∧
      word (bBits fun j => (inputsOf input_var j).eval env) = Adder.value input.b := by
  obtain ⟨va, vb⟩ := input_var
  have ha : input.a = va.map (Expression.eval env) := by subst h; simp [circuit_norm]
  have hb : input.b = vb.map (Expression.eval env) := by subst h; simp [circuit_norm]
  constructor
  · rw [value_eq_sum, word]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    simp [aBits, inputsOf, hi', ha]
  · rw [value_eq_sum, word]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    simp [bBits, inputsOf, hi', hb]

theorem eval_output (n : ℕ) (hn : n = 64 ∨ n = 128) (env : Environment Bit) (input_var : Var Input Bit)
    (offset : ℕ) :
    (Adder.value (eval env ((elaborated n hn).output input_var offset)) : ℤ) =
      rowValue n fun p => env.get (offset + (rippleBase n 64 + 5 * p + 4)) := by
  rw [show (elaborated n hn).output input_var offset = (outs n).map (Aff.expr (inputsOf input_var) offset) from rfl,
    value_eq_sum, rowValue]
  apply Finset.sum_congr rfl
  intro p hp
  have hp' := Finset.mem_range.mp hp
  simp [hp', outs, circuit_norm, Aff.expr]

theorem mod_of_eq {n : ℕ} {v ab : ℕ} {k : ℤ} (hlt : v < 2 ^ n) (h : (v : ℤ) = ab + 2 ^ n * k) : v = ab % 2 ^ n := by
  have hmod := congrArg (· % (2 ^ n : ℤ)) h
  simp only [Int.add_mul_emod_self_left] at hmod
  rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hlt)] at hmod
  exact_mod_cast hmod

theorem soundness (n : ℕ) (hn : n = 64 ∨ n = 128) :
    Soundness Bit (main n) (elaborated := elaborated n hn) (fun _ => True) (Spec n) := by
  intro offset env input_var input hinput _ hholds
  have hc : check n = true := by rcases hn with rfl | rfl; exacts [check64, check128]
  obtain ⟨k, hk⟩ := gates_product n hn hc _ _ (holds_of n env input_var offset hholds)
  refine ⟨?_, Netlist.requirements _ _ _ _ _⟩
  obtain ⟨ha, hb⟩ := eval_inputs env input_var input hinput
  rw [ha, hb, plan_steps n hn, ← eval_output n hn] at hk
  exact mod_of_eq (Adder.value_lt _) (by exact_mod_cast hk)

theorem completeness (n : ℕ) : Completeness Bit (main n) (fun _ => True) := by
  intro offset env input_var henv _ _ _
  have := Netlist.complete env (inputsOf input_var) offset 0 (layout n).gates (by rw [Nat.add_zero]; exact henv)
  exact this

/-- The low `n` bits of `a b`, for `n` 64 or 128. -/
def circuit (n : ℕ) (hn : n = 64 ∨ n = 128 := by decide) : FormalCircuit Bit Input (fields n) where
  main := main n
  elaborated := elaborated n hn
  Spec := Spec n
  soundness := soundness n hn
  completeness := completeness n
  requirementsChannelsLawful := by
    intro input offset
    exact Netlist.requirementsLawful (inputsOf input) offset _ 0 (layout n).gates

section
variable (n : ℕ) (hn : n = 64 ∨ n = 128)

@[circuit_norm] theorem circuit_assumptions : (circuit n hn).Assumptions = fun _ => True := rfl
@[circuit_norm] theorem circuit_requirements : (circuit n hn).channelsWithRequirements = [] := rfl
@[circuit_norm] theorem circuit_guarantees : (circuit n hn).elaborated.channelsWithGuarantees = [] := rfl
@[circuit_norm] theorem circuit_length (input : Var Input Bit) :
    (circuit n hn).localLength input = total n := rfl
@[circuit_norm] theorem circuit_spec : (circuit n hn).Spec = Spec n := rfl

end

-- Callers see the product only through `Spec`, never its gates.
attribute [irreducible] elaborated

end LeanVMCircuits.Multiply
