module

public import LeanVMCircuits.Adder

@[expose] public section

namespace LeanVMCircuits.Flock

-- Clean's generic equality transports through `propext`; use GF(2)'s computable representation here.
local instance : DecidableEq Bit := inferInstanceAs (DecidableEq (Fin 2))

/-- Flock's free affine wires. Product variables are committed row slots. -/
inductive Affine where
  | zero
  | one
  | var (index : ℕ)
  | xor (left right : Affine)
  deriving Repr, DecidableEq

def Affine.eval (assignment : ℕ → Bit) : Affine → Bit
  | .zero => 0
  | .one => 1
  | .var i => assignment i
  | .xor a b => a.eval assignment + b.eval assignment

/-- One committed product, in exactly the source order. -/
structure Row where
  output : ℕ
  left : Affine
  right : Affine
  deriving Repr, DecidableEq

def Row.Holds (assignment : ℕ → Bit) (row : Row) : Prop :=
  assignment row.output = row.left.eval assignment * row.right.eval assignment

/-- Only affine operands are supported; no multiplication is silently expanded. -/
def lowerAffine : Expression Bit → Except String Affine
  | .var v => .ok (.var v.index)
  | .const c => if c = 0 then .ok .zero else if c = 1 then .ok .one else .error "unsupported constant"
  | .add a b =>
    match lowerAffine a, lowerAffine b with
    | .ok left, .ok right => .ok (.xor left right)
    | .error message, _ => .error message
    | _, .error message => .error message
  | .mul _ _ => .error "non-affine product operand"

/-- A scalar witness followed by its defining product assertion is the supported operation pair. -/
def lower : List (FlatOperation Bit) → Except String (List Row)
  | [] => .ok []
  | .witness 1 _ :: .assert (.add (.var output) (.mul (.const coefficient) (.mul a b))) :: rest =>
    if coefficient = -1 then
      match lowerAffine a with
      | .error message => .error message
      | .ok left =>
        match lowerAffine b with
        | .error message => .error message
        | .ok right =>
          match lower rest with
          | .error message => .error message
          | .ok rows => .ok ({ output := output.index, left, right } :: rows)
    else .error "product assertion must subtract its right-hand side"
  | .witness _ _ :: _ => .error "unsupported witness or missing product assertion"
  | .assert _ :: _ => .error "unsupported assertion"
  | .lookup _ :: _ => .error "Flock lowering does not support lookups"
  | .interact _ :: _ => .error "Flock lowering does not support interactions"

/-- Successful affine lowering preserves evaluation for every assignment. -/
theorem lowerAffine_correct (expression : Expression Bit) (affine : Affine)
    (h : lowerAffine expression = .ok affine) (env : Environment Bit) :
    affine.eval env.get = expression.eval env := by
  induction expression generalizing affine with
  | var v => simp [lowerAffine] at h; subst affine; rfl
  | const c =>
    simp only [lowerAffine] at h
    split at h
    · rename_i hc; cases h; simp [Affine.eval, Expression.eval, hc]
    · split at h
      · rename_i hc; cases h; simp [Affine.eval, Expression.eval, hc]
      · cases h
  | add a b ia ib =>
    cases ha : lowerAffine a with
    | error e => simp [lowerAffine, ha] at h
    | ok aa =>
      cases hb : lowerAffine b with
      | error e => simp [lowerAffine, ha, hb] at h
      | ok bb =>
        simp [lowerAffine, ha, hb] at h
        subst affine
        simp [Affine.eval, Expression.eval, ia _ ha, ib _ hb]
  | mul a b => simp [lowerAffine] at h

private theorem bit_add_eq_zero_iff (a b : Bit) : a + b = 0 ↔ a = b := by
  simpa only [sub_eq_add_neg, ZMod.neg_eq_self_mod_two] using
    (sub_eq_zero : a - b = 0 ↔ a = b)

/-- The exported rows characterize all satisfying source witnesses, not just honest evaluation. -/
theorem lower_correct (operations : List (FlatOperation Bit)) (rows : List Row)
    (h : lower operations = .ok rows) (env : Environment Bit) :
    rows.Forall (Row.Holds env.get) ↔ FlatOperation.ConstraintsHoldFlat env operations := by
  fun_induction lower operations generalizing rows <;>
    simp_all [FlatOperation.ConstraintsHoldFlat, Expression.eval]
  subst rows
  rename_i ir output a b rest left ha right hb tail ht ih
  have ea := lowerAffine_correct a left ha env
  have eb := lowerAffine_correct b right hb env
  simp only [List.forall_cons, Row.Holds, ea, eb, bit_add_eq_zero_iff, ih]

theorem lower_no_interactions (operations : List (FlatOperation Bit)) (rows : List Row)
    (h : lower operations = .ok rows) : FlatOperation.interactions operations = [] := by
  fun_induction lower operations generalizing rows <;>
    simp_all [FlatOperation.interactions]

theorem lookup_rejected (lookup : Lookup Bit) (rest : List (FlatOperation Bit)) :
    lower (.lookup lookup :: rest) = .error "Flock lowering does not support lookups" := rfl

theorem interaction_rejected (interaction : AbstractInteraction Bit) (rest : List (FlatOperation Bit)) :
    lower (.interact interaction :: rest) = .error "Flock lowering does not support interactions" := rfl

end LeanVMCircuits.Flock
