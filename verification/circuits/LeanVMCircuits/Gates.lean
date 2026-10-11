module

public import LeanVMCircuits.Completeness

@[expose] public section

/-!
Lowering of Boolean Clean circuits whose free wires are named.

A Flock gate list has two kinds of wires past its inputs: committed products and uncommitted XORs. A Clean circuit
names an uncommitted XOR as a scalar witness constrained to an affine expression of earlier variables. Lowering
turns that pair into a definition step, which a consumer realizes as XOR gates with no slot, and a witness constrained
to a product of two affine operands into a product step, which takes the next product slot. Naming the free wires
keeps the source's expressions small when a circuit chains thousands of additions.
-/

namespace LeanVMCircuits.Gates

open Flock

/-- One named wire, in exactly the source order. -/
inductive Step where
  /-- An uncommitted wire equal to an affine combination of earlier wires. -/
  | define (output : ℕ) (value : Affine)
  /-- A committed product of two affine combinations of earlier wires. -/
  | product (output : ℕ) (left right : Affine)
  deriving Repr, DecidableEq

def Step.output : Step → ℕ
  | .define output _ | .product output _ _ => output

def Step.Holds (assignment : ℕ → Bit) : Step → Prop
  | .define output value => assignment output = value.eval assignment
  | .product output left right => assignment output = left.eval assignment * right.eval assignment

/-- Lower one witness, constrained right after it, to its step. The variable must be the next one. -/
def lower (next : ℕ) : List (FlatOperation Bit) → Except String (List Step)
  | [] => .ok []
  | .witness 1 _ :: .assert (.add (.var output) (.mul (.const coefficient) value)) :: rest =>
    if coefficient = -1 then
      if output.index = next then
        match value with
        | .mul a b =>
          match lowerAffine a with
          | .error message => .error message
          | .ok left =>
            match lowerAffine b with
            | .error message => .error message
            | .ok right =>
              if left.bounded next && right.bounded next then
                match lower (next + 1) rest with
                | .error message => .error message
                | .ok steps => .ok (.product next left right :: steps)
              else .error "product operand names a later variable"
        | expression =>
          match lowerAffine expression with
          | .error message => .error message
          | .ok affine =>
            if affine.bounded next then
              match lower (next + 1) rest with
              | .error message => .error message
              | .ok steps => .ok (.define next affine :: steps)
            else .error "definition names a later variable"
      else .error "witness constrained out of order"
    else .error "constraint must subtract its right-hand side"
  | .witness _ _ :: _ => .error "unsupported witness or missing constraint"
  | .assert _ :: _ => .error "unsupported assertion"
  | .lookup _ :: _ => .error "gate lowering does not support lookups"
  | .interact _ :: _ => .error "gate lowering does not support interactions"

private theorem bit_add_eq_zero_iff (a b : Bit) : a + b = 0 ↔ a = b := by
  simpa only [sub_eq_add_neg, ZMod.neg_eq_self_mod_two] using (sub_eq_zero : a - b = 0 ↔ a = b)

private theorem neg_one_mul (x : Bit) : (-1 : Bit) * x = x := by
  rw [ZMod.neg_eq_self_mod_two, one_mul]

/-- The steps characterize all satisfying source witnesses, not just honest evaluation. -/
theorem lower_correct (next : ℕ) (operations : List (FlatOperation Bit)) (steps : List Step)
    (h : lower next operations = .ok steps) (env : Environment Bit) :
    steps.Forall (Step.Holds env.get) ↔ FlatOperation.ConstraintsHoldFlat env operations := by
  fun_induction lower next operations generalizing steps <;>
    simp_all [FlatOperation.ConstraintsHoldFlat, Expression.eval]
  · subst steps
    rename_i rest x y left hx right hy tail _ _ ih
    simp only [List.forall_cons, Step.Holds, lowerAffine_correct x left hx env,
      lowerAffine_correct y right hy env, bit_add_eq_zero_iff, ih]
  · subst steps
    rename_i rest e affine tail _ he _ _ ih
    simp only [List.forall_cons, Step.Holds, lowerAffine_correct e affine he env,
      bit_add_eq_zero_iff, ih]

theorem lower_append (next : ℕ) (first rest : List (FlatOperation Bit)) (steps : List Step)
    (h : lower next first = .ok steps) :
    lower next (first ++ rest) = (lower (next + steps.length) rest).map (steps ++ ·) := by
  fun_induction lower next first generalizing steps
  all_goals first
    | (simp at h; done)
    | (simp only [Except.ok.injEq] at h; subst h
       simp only [List.nil_append, List.length_nil, Nat.add_zero, Except.map]
       generalize lower _ rest = L; cases L <;> rfl)
    | skip
  all_goals
    rename_i ih
    simp only [Except.ok.injEq] at h
    subst h
    simp only [List.cons_append, lower, ↓reduceIte, *]
    rw [ih _ ‹lower (_ + 1) _ = Except.ok _›]
    simp only [Except.map, List.length_cons]
    rw [show ∀ a b : ℕ, a + 1 + b = a + (b + 1) from fun a b => by omega]
    generalize lower _ rest = L
    cases L <;> rfl

theorem lower_no_interactions (next : ℕ) (operations : List (FlatOperation Bit)) (steps : List Step)
    (h : lower next operations = .ok steps) : FlatOperation.interactions operations = [] := by
  fun_induction lower next operations generalizing steps <;> simp_all [FlatOperation.interactions]

/-- Every step defines the next variable from earlier ones only. -/
def wellFormed (next : ℕ) : List Step → Bool
  | [] => true
  | .define output value :: rest => output == next && value.bounded next && wellFormed (next + 1) rest
  | .product output left right :: rest =>
    output == next && left.bounded next && right.bounded next && wellFormed (next + 1) rest

theorem lower_wellFormed (next : ℕ) (operations : List (FlatOperation Bit)) (steps : List Step)
    (h : lower next operations = .ok steps) : wellFormed next steps = true := by
  fun_induction lower next operations generalizing steps
  all_goals first
    | (simp_all [wellFormed]; done)
    | (simp only [Except.ok.injEq] at h; subst steps; simp_all [wellFormed])

/-- Every assignment of the variables below `next` extends to one satisfying every step. -/
theorem witness_exists (steps : List Step) (next : ℕ) (assignment : ℕ → Bit)
    (hwell : wellFormed next steps = true) :
    ∃ final, AgreeBelow next assignment final ∧ steps.Forall (Step.Holds final) := by
  induction steps generalizing next assignment with
  | nil => exact ⟨assignment, fun _ _ => rfl, by simp⟩
  | cons step rest ih =>
    let value : Bit := match step with
      | .define _ affine => affine.eval assignment
      | .product _ left right => left.eval assignment * right.eval assignment
    have hrest : wellFormed (next + 1) rest = true := by
      cases step <;> simp only [wellFormed, Bool.and_eq_true] at hwell <;> exact hwell.2
    obtain ⟨final, hagree, htail⟩ := ih (next + 1) (Function.update assignment next value) hrest
    have htotal : AgreeBelow next assignment final := by
      intro index hindex
      rw [hagree index (by omega)]
      exact Function.update_of_ne (by omega) _ _
    refine ⟨final, htotal, ?_⟩
    simp only [List.forall_cons]
    refine ⟨?_, htail⟩
    have hnext : final next = value := by rw [hagree next (by omega)]; simp
    cases step with
    | define output affine =>
      simp only [wellFormed, Bool.and_eq_true, beq_iff_eq] at hwell
      rcases hwell with ⟨⟨houtput, hbound⟩, _⟩
      subst houtput
      simp only [Step.Holds, hnext, value, Affine.eval_agree affine output assignment final hbound htotal]
    | product output left right =>
      simp only [wellFormed, Bool.and_eq_true, beq_iff_eq] at hwell
      rcases hwell with ⟨⟨⟨houtput, hleft⟩, hright⟩, _⟩
      subst houtput
      simp only [Step.Holds, hnext, value, Affine.eval_agree left output assignment final hleft htotal,
        Affine.eval_agree right output assignment final hright htotal]

/-- A lowered circuit: its steps from its first local variable, and its outputs. -/
structure Artifact where
  start : ℕ
  steps : List Step
  outputs : List Affine
  deriving Repr, DecidableEq

def Artifact.Holds (artifact : Artifact) (assignment : ℕ → Bit) : Prop :=
  artifact.steps.Forall (Step.Holds assignment)

def Artifact.products (artifact : Artifact) : List (Affine × Affine) :=
  artifact.steps.filterMap fun
    | .product _ left right => some (left, right)
    | .define _ _ => none

def lowerAt (start : ℕ) (nested : NestedOperations Bit) (output : List (Expression Bit)) :
    Except String Artifact :=
  match lower start nested.toFlat, lowerOutputs output with
  | .ok steps, .ok outputs => .ok { start, steps, outputs }
  | .error message, _ => .error message
  | _, .error message => .error message

theorem lowerAt_correct (start : ℕ) (nested : NestedOperations Bit) (output : List (Expression Bit))
    (artifact : Artifact) (hcode : lowerAt start nested output = .ok artifact) (env : Environment Bit) :
    (artifact.Holds env.get ↔ FlatOperation.ConstraintsHoldFlat env nested.toFlat) ∧
      FlatOperation.Guarantees env nested.toFlat ∧
      artifact.outputs.map (Affine.eval env.get) = output.map (Expression.eval env) ∧
      artifact.start = start ∧ wellFormed start artifact.steps = true := by
  cases hr : lower start nested.toFlat with
  | error message => simp [lowerAt, hr] at hcode
  | ok steps =>
    cases ho : lowerOutputs output with
    | error message => simp [lowerAt, hr, ho] at hcode
    | ok outputs =>
      simp [lowerAt, hr, ho] at hcode
      subst artifact
      refine ⟨lower_correct start _ steps hr env, ?_, lowerOutputs_correct _ _ ho env, rfl,
        lower_wellFormed start _ steps hr⟩
      rw [FlatOperation.guarantees_iff_forall_mem, lower_no_interactions _ _ _ hr]
      simp

/-- The lowering of a formal circuit at `start`, its inputs already named below `start`. -/
def lowerCircuit {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (circuit : FormalCircuit Bit Input Output) (start : ℕ) (input : Var Input Bit) : Except String Artifact :=
  lowerAt start (circuit.toSubcircuit start input).ops (toElements (M := Output) (circuit.output input start)).toList

/-- Arbitrary-witness soundness transfers from the Clean circuit to every successful lowering. -/
theorem lowerCircuit_soundness {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (circuit : FormalCircuit Bit Input Output) (start : ℕ) (input : Var Input Bit) (artifact : Artifact)
    (hcode : lowerCircuit circuit start input = .ok artifact) (env : Environment Bit)
    (hassumptions : circuit.Assumptions (eval env input)) (hholds : artifact.Holds env.get) :
    circuit.Spec (eval env input) (eval env (circuit.output input start)) ∧
      artifact.outputs.map (Affine.eval env.get) =
        (toElements (M := Output) (circuit.output input start)).toList.map (Expression.eval env) := by
  have h := lowerAt_correct _ _ _ artifact hcode env
  exact ⟨((circuit.toSubcircuit start input).soundness env hassumptions (h.1.mp hholds) h.2.1).1, h.2.2.1⟩

/-- Every assignment of the inputs extends to one satisfying every step of a successful lowering. -/
theorem lowerCircuit_completeness {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (circuit : FormalCircuit Bit Input Output) (start : ℕ) (input : Var Input Bit) (artifact : Artifact)
    (hcode : lowerCircuit circuit start input = .ok artifact) (inputs : ℕ → Bit) :
    ∃ final, AgreeBelow start inputs final ∧ artifact.Holds final := by
  have h := (lowerAt_correct _ _ _ artifact hcode { get := inputs, data := fun _ _ => #[] }).2.2.2.2
  exact witness_exists artifact.steps start inputs h

end LeanVMCircuits.Gates
