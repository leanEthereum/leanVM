module

public import LeanVMCircuits.Blake2s.Linkage

@[expose] public section

/-!
A Clean circuit from a list of gates over the circuit's inputs and its own earlier wires.

Gate `i` names local wire `i`: a free wire equal to an affine combination, or a product of two. The circuit witnesses
each one and constrains it to its gate, so its constraints are exactly the gates and its lowering is exactly the
gates' steps, whatever the gates: a generator of gates proves what they compute once, about the gates themselves.
-/

namespace LeanVMCircuits.Netlist

open LeanVMCircuits Flock Gates

/-- An affine combination of input wires, earlier local wires and the constants. -/
inductive Aff where
  | zero
  | one
  | input (j : ℕ)
  | loc (i : ℕ)
  | xor (l r : Aff)
  deriving Repr, DecidableEq, Inhabited

/-- A gate: a free wire equal to an affine combination, or the product of two. -/
inductive Gate where
  | define (v : Aff)
  | product (l r : Aff)
  deriving Repr, DecidableEq

def Aff.eval (inp loc : ℕ → Bit) : Aff → Bit
  | .zero => 0
  | .one => 1
  | .input j => inp j
  | .loc i => loc i
  | .xor l r => l.eval inp loc + r.eval inp loc

/-- The combination as a Clean expression, local wire `i` being variable `base + i`. -/
def Aff.expr (inp : ℕ → Expression Bit) (base : ℕ) : Aff → Expression Bit
  | .zero => .const 0
  | .one => .const 1
  | .input j => inp j
  | .loc i => var ⟨base + i⟩
  | .xor l r => .add (l.expr inp base) (r.expr inp base)

/-- The combination as a lowered affine, the inputs lowered to `inp`. -/
def Aff.lower (inp : ℕ → Affine) (base : ℕ) : Aff → Affine
  | .zero => .zero
  | .one => .one
  | .input j => inp j
  | .loc i => .var (base + i)
  | .xor l r => .xor (l.lower inp base) (r.lower inp base)

/-- Every local wire it names is below `n`. -/
def Aff.within (n : ℕ) : Aff → Bool
  | .loc i => decide (i < n)
  | .xor l r => l.within n && r.within n
  | _ => true

def Gate.Holds (inp loc : ℕ → Bit) (i : ℕ) : Gate → Prop
  | .define v => loc i = v.eval inp loc
  | .product l r => loc i = l.eval inp loc * r.eval inp loc

def Gate.value (inp : ℕ → Expression Bit) (base : ℕ) : Gate → Expression Bit
  | .define v => v.expr inp base
  | .product l r => l.expr inp base * r.expr inp base

def Gate.step (inp : ℕ → Affine) (base i : ℕ) : Gate → Step
  | .define v => .define (base + i) (v.lower inp base)
  | .product l r => .product (base + i) (l.lower inp base) (r.lower inp base)

def Gate.within (i : ℕ) : Gate → Bool
  | .define v => v.within i
  | .product l r => l.within i && r.within i

/-- Gate `i`'s witness and constraint. -/
def Gate.ops (inp : ℕ → Expression Bit) (base i : ℕ) (g : Gate) : List (Operation Bit) :=
  [.witness 1 (.ofFExpr (.expr (g.value inp base))), .assert (var ⟨base + i⟩ - g.value inp base)]

def opsFrom (inp : ℕ → Expression Bit) (base : ℕ) : ℕ → List Gate → List (Operation Bit)
  | _, [] => []
  | i, g :: gs => g.ops inp base i ++ opsFrom inp base (i + 1) gs

def stepsFrom (inp : ℕ → Affine) (base : ℕ) : ℕ → List Gate → List Step
  | _, [] => []
  | i, g :: gs => g.step inp base i :: stepsFrom inp base (i + 1) gs

/-- Each gate names only earlier local wires. -/
def wellOrdered : ℕ → List Gate → Bool
  | _, [] => true
  | i, g :: gs => g.within i && wellOrdered (i + 1) gs

theorem opsFrom_length (inp : ℕ → Expression Bit) (base : ℕ) :
    ∀ (i : ℕ) (gs : List Gate), Operations.localLength (opsFrom inp base i gs) = gs.length
  | _, [] => rfl
  | i, g :: gs => by
    simp only [opsFrom, Gate.ops, List.cons_append, List.nil_append, Operations.localLength, List.length_cons]
    rw [opsFrom_length inp base (i + 1) gs]
    omega

theorem Aff.eval_expr (env : Environment Bit) (inp : ℕ → Expression Bit) (base : ℕ) :
    ∀ a : Aff, (a.expr inp base).eval env =
      a.eval (fun j => (inp j).eval env) (fun i => env.get (base + i))
  | .zero => rfl
  | .one => rfl
  | .input _ => rfl
  | .loc _ => rfl
  | .xor l r => by simp only [Aff.expr, Aff.eval, Expression.eval, Aff.eval_expr env inp base l,
      Aff.eval_expr env inp base r]

theorem bit_sub_eq_zero (a b : Bit) : a - b = 0 ↔ a = b := sub_eq_zero

/-- The constraints of the gates from gate `i` are the gates. -/
theorem holds_iff (env : Environment Bit) (inp : ℕ → Expression Bit) (base : ℕ) :
    ∀ (i : ℕ) (gs : List Gate), ConstraintsHold.Soundness env (opsFrom inp base i gs) ↔
      ∀ k (hk : k < gs.length), gs[k].Holds (fun j => (inp j).eval env) (fun l => env.get (base + l)) (i + k)
  | _, [] => by simp [opsFrom, ConstraintsHold.Soundness, Operations.forAllNoOffset]
  | i, g :: gs => by
    have ih := holds_iff env inp base (i + 1) gs
    have hg : ConstraintsHold.Soundness env (g.ops inp base i ++ opsFrom inp base (i + 1) gs) ↔
        g.Holds (fun j => (inp j).eval env) (fun l => env.get (base + l)) i ∧
          ConstraintsHold.Soundness env (opsFrom inp base (i + 1) gs) := by
      simp only [Gate.ops, List.cons_append, List.nil_append, ConstraintsHold.Soundness, Operations.forAllNoOffset,
        true_and]
      apply and_congr_left'
      show Expression.eval env (.add (var ⟨base + i⟩) (.mul (.const (-1)) (g.value inp base))) = 0 ↔ _
      simp only [Expression.eval, neg_one_mul, ← sub_eq_add_neg, bit_sub_eq_zero]
      cases g with
      | define v => simp only [Gate.value, Gate.Holds, Aff.eval_expr]
      | product l r => simp only [Gate.value, Gate.Holds, Expression.eval, Aff.eval_expr]
    simp only [opsFrom]
    rw [hg, ih]
    constructor
    · rintro ⟨h0, hs⟩ k hk
      cases k with
      | zero => exact h0
      | succ k =>
        have := hs k (by simpa using hk)
        rwa [show i + 1 + k = i + (k + 1) by omega] at this
    · intro h
      refine ⟨h 0 (by simp), fun k hk => ?_⟩
      have := h (k + 1) (by simpa using hk)
      rwa [show i + (k + 1) = i + 1 + k by omega] at this


/-! Lowering. -/

/-- The inputs lower to affines naming only variables below the circuit's first. -/
def InputsLower (inp : ℕ → Expression Bit) (ainp : ℕ → Affine) (base : ℕ) : Prop :=
  ∀ j, lowerAffine (inp j) = .ok (ainp j) ∧ (ainp j).bounded base = true

theorem Aff.lower_expr (inp : ℕ → Expression Bit) (ainp : ℕ → Affine) (base : ℕ) (h : InputsLower inp ainp base) :
    ∀ a : Aff, lowerAffine (a.expr inp base) = .ok (a.lower ainp base)
  | .zero => by simp [Aff.expr, Aff.lower, lowerAffine]
  | .one => by simp [Aff.expr, Aff.lower, lowerAffine]
  | .input j => (h j).1
  | .loc i => rfl
  | .xor l r => by
    simp only [Aff.expr, Aff.lower, lowerAffine, Aff.lower_expr inp ainp base h l, Aff.lower_expr inp ainp base h r]

theorem Aff.lower_bounded (ainp : ℕ → Affine) (base : ℕ) (hb : ∀ j, (ainp j).bounded base = true) (i : ℕ) :
    ∀ a : Aff, a.within i = true → (a.lower ainp base).bounded (base + i) = true
  | .zero, _ => rfl
  | .one, _ => rfl
  | .input j, _ => Blake2s.Affine.bounded_mono _ (hb j) (by omega)
  | .loc l, h => by simpa [Aff.lower, Affine.bounded, Aff.within] using h
  | .xor l r, h => by
    simp only [Aff.within, Bool.and_eq_true] at h
    simp only [Aff.lower, Affine.bounded, Bool.and_eq_true]
    exact ⟨Aff.lower_bounded ainp base hb i l h.1, Aff.lower_bounded ainp base hb i r h.2⟩

theorem toFlat_ops (inp : ℕ → Expression Bit) (base i : ℕ) (g : Gate) :
    Operations.toFlat (g.ops inp base i) =
      [.witness 1 (.ofFExpr (.expr (g.value inp base))), .assert (var ⟨base + i⟩ - g.value inp base)] := rfl

/-- The circuit lowers to the gates' steps. -/
theorem lower_opsFrom (inp : ℕ → Expression Bit) (ainp : ℕ → Affine) (base : ℕ) (h : InputsLower inp ainp base) :
    ∀ (i : ℕ) (gs : List Gate), wellOrdered i gs = true →
      Gates.lower (base + i) (Operations.toFlat (opsFrom inp base i gs)) = .ok (stepsFrom ainp base i gs)
  | _, [], _ => rfl
  | i, g :: gs, hw => by
    simp only [wellOrdered, Bool.and_eq_true] at hw
    simp only [opsFrom, stepsFrom]
    rw [Blake2s.toFlat_append, toFlat_ops]
    have hb := fun j => (h j).2
    have hstep : Gates.lower (base + i) [.witness 1 (.ofFExpr (.expr (g.value inp base))),
        .assert (var ⟨base + i⟩ - g.value inp base)] = .ok [g.step ainp base i] := by
      cases g with
      | define v =>
        simp only [Gate.within] at hw
        exact Blake2s.lower_define _ _ _ _ (Aff.lower_expr inp ainp base h v)
          (Aff.lower_bounded ainp base hb i v hw.1)
      | product l r =>
        simp only [Gate.within, Bool.and_eq_true] at hw
        exact Blake2s.lower_product _ _ _ _ _ _ (Aff.lower_expr inp ainp base h l) (Aff.lower_expr inp ainp base h r)
          (Aff.lower_bounded ainp base hb i l hw.1.1) (Aff.lower_bounded ainp base hb i r hw.1.2)
    rw [Gates.lower_append _ _ _ _ hstep, show base + i + [g.step ainp base i].length = base + (i + 1) by simp; omega,
      lower_opsFrom inp ainp base h (i + 1) gs hw.2]
    rfl


/-! Honest witnesses. -/

theorem complete (env : ProverEnvironment Bit) (inp : ℕ → Expression Bit) (base : ℕ) :
    ∀ (i : ℕ) (gs : List Gate), env.UsesLocalWitnessesCompleteness (base + i) (opsFrom inp base i gs) →
      ConstraintsHold.Completeness env (opsFrom inp base i gs)
  | _, [], _ => by simp [opsFrom, ConstraintsHold.Completeness, Operations.forAllNoOffset]
  | i, g :: gs, h => by
    simp only [opsFrom, Gate.ops, List.cons_append, List.nil_append,
      ProverEnvironment.UsesLocalWitnessesCompleteness] at h
    simp only [opsFrom, Gate.ops, List.cons_append, List.nil_append, ConstraintsHold.Completeness,
      Operations.forAllNoOffset, true_and]
    refine ⟨?_, complete env inp base (i + 1) gs (by simpa [Nat.add_assoc] using h.2)⟩
    have h1 := h.1
    simp [circuit_norm, ProverEnvironment.ExtendsVector] at h1
    show Expression.eval _ (.add (var ⟨base + i⟩) (.mul (.const (-1)) (g.value inp base))) = 0
    simp only [Expression.eval, neg_one_mul, ← sub_eq_add_neg, bit_sub_eq_zero]
    exact h1


/-! A formal circuit of gates. -/

theorem subcircuitsConsistent (inp : ℕ → Expression Bit) (base : ℕ) :
    ∀ (i : ℕ) (gs : List Gate), Operations.SubcircuitsConsistent (base + i) (opsFrom inp base i gs)
  | _, [] => by simp [opsFrom, Operations.SubcircuitsConsistent, Operations.forAll]
  | i, g :: gs => by
    simp only [opsFrom, Gate.ops, List.cons_append, List.nil_append, Operations.SubcircuitsConsistent,
      Operations.forAll, true_and]
    have := subcircuitsConsistent inp base (i + 1) gs
    simp only [Operations.SubcircuitsConsistent] at this
    rwa [show 1 + (base + i) = base + (i + 1) by omega]

theorem channels (inp : ℕ → Expression Bit) (base : ℕ) :
    ∀ (i : ℕ) (gs : List Gate), Operations.subcircuitChannelsWithGuarantees (opsFrom inp base i gs) ⊆ [] ∧
      (∀ env : Environment Bit, Operations.InChannelsOrGuarantees [] env (opsFrom inp base i gs)) ∧
      Operations.SubcircuitChannelsLawful (opsFrom inp base i gs)
  | _, [] => by
    simp [opsFrom, Operations.subcircuitChannelsWithGuarantees, Operations.InChannelsOrGuarantees,
      Operations.SubcircuitChannelsLawful, Operations.forAllNoOffset, Operations.subcircuits]
  | i, g :: gs => by
    have ih := channels inp base (i + 1) gs
    simp only [Operations.InChannelsOrGuarantees, Operations.SubcircuitChannelsLawful] at ih ⊢
    simp only [opsFrom, Gate.ops, List.cons_append, List.nil_append, Operations.subcircuitChannelsWithGuarantees,
      Operations.forAllNoOffset, true_and]
    exact ih

theorem requirements (env : Environment Bit) (inp : ℕ → Expression Bit) (base : ℕ) :
    ∀ (i : ℕ) (gs : List Gate), Operations.Requirements env (opsFrom inp base i gs)
  | _, [] => by simp [opsFrom, Operations.Requirements, Operations.forAllNoOffset]
  | i, g :: gs => by
    have ih := requirements env inp base (i + 1) gs
    simp only [Operations.Requirements] at ih ⊢
    simp only [opsFrom, Gate.ops, List.cons_append, List.nil_append, Operations.forAllNoOffset, true_and]
    exact ih

theorem requirementsLawful (inp : ℕ → Expression Bit) (base : ℕ) (G : List (RawChannel Bit)) :
    ∀ (i : ℕ) (gs : List Gate), Operations.subcircuitChannelsWithRequirements (opsFrom inp base i gs) ⊆ [] ∧
      (∀ channel ∈ Operations.shallowChannels (opsFrom inp base i gs), channel ∈ G ∨ channel ∈ []) ∧
      ∀ env : Environment Bit, ConstraintsHold.Shallow env (opsFrom inp base i gs) →
        Operations.InChannelsOrRequirements [] env (opsFrom inp base i gs)
  | _, [] => by
    simp [opsFrom, Operations.subcircuitChannelsWithRequirements, Operations.shallowChannels,
      Operations.InChannelsOrRequirements, Operations.forAllNoOffset]
  | i, g :: gs => by
    have ih := requirementsLawful inp base G (i + 1) gs
    simp only [Operations.InChannelsOrRequirements, ConstraintsHold.Shallow] at ih ⊢
    simp only [opsFrom, Gate.ops, List.cons_append, List.nil_append, Operations.subcircuitChannelsWithRequirements,
      Operations.shallowChannels, Operations.forAllNoOffset, true_and]
    exact ⟨ih.1, ih.2.1, fun env h => ih.2.2 env h.2⟩

/-- The circuit of `gates` on the inputs `inputsOf`, its output the `m` affines `outs`. -/
def main {Input : TypeMap} [ProvableType Input] {m : ℕ} (inputsOf : Var Input Bit → ℕ → Expression Bit)
    (gates : List Gate) (outs : Vector Aff m) (input : Var Input Bit) : Circuit Bit (Var (fields m) Bit) :=
  fun base => (outs.map (Aff.expr (inputsOf input) base), opsFrom (inputsOf input) base 0 gates)

/-- Its local length is `len`, given as a literal so that callers never reduce the gates to count them. -/
@[instance_reducible] def elaborated {Input : TypeMap} [ProvableType Input] {m : ℕ} (inputsOf : Var Input Bit → ℕ → Expression Bit)
    (gates : List Gate) (outs : Vector Aff m) (len : ℕ) (hlen : gates.length = len) :
    ElaboratedCircuit Bit Input (fields m) (main inputsOf gates outs) where
  localLength _ := len
  localLength_eq input offset := (opsFrom_length _ _ 0 gates).trans hlen
  subcircuitsConsistent input offset := by
    have := subcircuitsConsistent (inputsOf input) offset 0 gates
    show Operations.SubcircuitsConsistent offset (opsFrom (inputsOf input) offset 0 gates)
    simpa using this
  channelsLawful := by
    intro input_var offset
    show Operations.subcircuitChannelsWithGuarantees (opsFrom (inputsOf input_var) offset 0 gates) ⊆ [] ∧ _ ∧ _
    exact channels (inputsOf input_var) offset 0 gates

end LeanVMCircuits.Netlist
