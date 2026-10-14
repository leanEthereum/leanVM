import Whir.AnchoredHeaderCodec

/-! One operational source algorithm, parameterized by the primitive `Arith` operations shared by Native and Rows. No dense sum is used to execute the algorithm. -/
namespace Whir.AnchorPrefixRefinementArith
open Concrete AnchoredHeaderCodec

structure Arith (A : Type) where
  one : A
  add : A → A → A
  addConst : A → E → A
  mul : A → A → A
  mulAdd : A → A → A → A

structure PrefixStateWith (A : Type) [One A] where
  full : A := 1
  «partial» : A := 1
  started : Bool := false

def native : Arith E :=
  ⟨E.one, E.add, E.add, E.mul, fun a b c => E.add (E.mul a b) c⟩

/-- Source `eq_eval` on one contiguous coordinate segment. -/
def eqEvalWith {A : Type} (a : Arith A) (n : Nat) (r x : Nat → A) : A :=
  (List.range n).foldl (fun acc j => a.mulAdd acc (a.add (r j) (x j)) acc) a.one

def prefixStepWith {A : Type} [One A] (a : Arith A) (shape : Shape)
    (r x : Nat → A) (j : Nat) (s : PrefixStateWith A) : PrefixStateWith A :=
  let logRows := shape.logN-shape.logBatch
  let rj := r (logRows+j)
  let xj := x (logRows+j)
  let factor := a.addConst (a.add rj xj) E.one
  let bit := shape.lanes.testBit j
  let s := if bit || s.started then
    let hi := a.mul rj xj
    let lo := a.add factor hi
    if bit then
      let lowerFull := if j = 0 then lo else a.mul lo s.full
      {s with «partial» := if s.started then a.mulAdd hi s.partial lowerFull else lowerFull, started := true}
    else {s with «partial» := a.mul lo s.partial}
  else s
  if shape.lanes >>> (j+1) ≠ 0 then
    {s with full := if j = 0 then factor else a.mul s.full factor}
  else s

def anchorAtWith {A : Type} [One A] (a : Arith A) (shape : Shape)
    (n : Nat) (r x : Nat → A) : A :=
  if shape.lanes = 2^shape.logBatch then eqEvalWith a n r x
  else
    let low := eqEvalWith a (shape.logN-shape.logBatch) r x
    let state := (List.range shape.logBatch).foldl
      (fun s j => prefixStepWith a shape r x j s) ⟨a.one,a.one,false⟩
    a.mul low state.partial

/-- Only primitive arithmetic semantics are assumed by an operational adapter, never an anchor-weight specification. -/
structure Adapter {A : Type} (a : Arith A) (eval : A → E) : Prop where
  one : eval a.one = E.one
  add : ∀ u v, eval (a.add u v) = E.add (eval u) (eval v)
  addConst : ∀ u c, eval (a.addConst u c) = E.add (eval u) c
  mul : ∀ u v, eval (a.mul u v) = E.mul (eval u) (eval v)
  mulAdd : ∀ u v w, eval (a.mulAdd u v w) = E.add (E.mul (eval u) (eval v)) (eval w)

def mapState {A : Type} [One A] (eval : A → E) (s : PrefixStateWith A) : PrefixStateWith E :=
  ⟨eval s.full,eval s.partial,s.started⟩

lemma prefixStep_adapter {A : Type} [One A] (a : Arith A) (eval : A → E)
    (h : Adapter a eval) (shape : Shape) (r x : Nat → A) (j : Nat) (s : PrefixStateWith A) :
    mapState eval (prefixStepWith a shape r x j s) =
      prefixStepWith native shape (eval ∘ r) (eval ∘ x) j (mapState eval s) := by
  simp only [mapState]
  cases hb : shape.lanes.testBit j <;> cases hs : s.started <;>
    by_cases hn : shape.lanes >>> (j+1) ≠ 0 <;> by_cases hj : j = 0
  all_goals
    simp only [prefixStepWith, hb, hs, Bool.or_false, Bool.or_true,
      Bool.false_eq_true, ↓reduceIte]
    simp [hn, hj, native, Function.comp_apply, h.add, h.addConst, h.mul, h.mulAdd, hs]
  all_goals split_ifs <;> simp [h.add, h.addConst, h.mul, h.mulAdd, hs]

lemma eqEval_adapter {A : Type} (a : Arith A) (eval : A → E) (h : Adapter a eval)
    (n : Nat) (r x : Nat → A) :
    eval (eqEvalWith a n r x) = eqEvalWith native n (eval ∘ r) (eval ∘ x) := by
  unfold eqEvalWith
  have fold (l : List Nat) (s : A) :
      eval (l.foldl (fun acc j => a.mulAdd acc (a.add (r j) (x j)) acc) s) =
      l.foldl (fun acc j => E.add (E.mul acc (E.add (eval (r j)) (eval (x j)))) acc) (eval s) := by
    induction l generalizing s with
    | nil => rfl
    | cons j l ih => simp only [List.foldl_cons, ih, h.mulAdd, h.add]
  simpa only [native, Function.comp_apply, h.one] using fold (List.range n) a.one

lemma anchorAt_adapter {A : Type} [One A] (a : Arith A) (eval : A → E) (h : Adapter a eval)
    (shape : Shape) (n : Nat) (r x : Nat → A) :
    eval (anchorAtWith a shape n r x) = anchorAtWith native shape n (eval ∘ r) (eval ∘ x) := by
  have fold (l : List Nat) (s : PrefixStateWith A) :
      mapState eval (l.foldl (fun s j => prefixStepWith a shape r x j s) s) =
      l.foldl (fun s j => prefixStepWith native shape (eval ∘ r) (eval ∘ x) j s) (mapState eval s) := by
    induction l generalizing s with
    | nil => rfl
    | cons j l ih => rw [List.foldl_cons, List.foldl_cons, ih, prefixStep_adapter a eval h]
  unfold anchorAtWith
  split_ifs
  · exact eqEval_adapter a eval h n r x
  · rw [h.mul, eqEval_adapter a eval h]
    have hs := congrArg PrefixStateWith.partial (fold (List.range shape.logBatch) ⟨a.one,a.one,false⟩)
    simp only [mapState, h.one] at hs
    simpa only [native] using congrArg (E.mul (eqEvalWith native (shape.logN-shape.logBatch) (eval ∘ r) (eval ∘ x))) hs

/-- Arithmetic expressions preserve the source primitive distinction between `add_const` and `mul_add`. Their evaluation is the operational meaning of a Rows expression, not a correctness axiom about its final weight. -/
inductive RowsExpr where
  | constant (value : E)
  | add (left right : RowsExpr)
  | addConst (value : RowsExpr) (constant : E)
  | mul (left right : RowsExpr)
  | mulAdd (left right addend : RowsExpr)

instance : One RowsExpr := ⟨.constant E.one⟩
instance : Inhabited RowsExpr := ⟨.constant E.zero⟩

def rows : Arith RowsExpr :=
  ⟨.constant E.one,.add,.addConst,.mul,.mulAdd⟩

def RowsExpr.eval : RowsExpr → E
  | .constant value => value
  | .add left right => E.add left.eval right.eval
  | .addConst value c => E.add value.eval c
  | .mul left right => E.mul left.eval right.eval
  | .mulAdd left right addend => E.add (E.mul left.eval right.eval) addend.eval

lemma rows_adapter : Adapter rows RowsExpr.eval := by constructor <;> intros <;> rfl

/-- Native and Rows execute the same source branch schedule and have equal terminal arithmetic. -/
theorem native_rows_anchor (shape : Shape) (n : Nat) (r x : Nat → RowsExpr) :
    (anchorAtWith rows shape n r x).eval =
      anchorAtWith native shape n (RowsExpr.eval ∘ r) (RowsExpr.eval ∘ x) :=
  anchorAt_adapter rows RowsExpr.eval rows_adapter shape n r x

#print axioms prefixStep_adapter
#print axioms anchorAt_adapter
#print axioms native_rows_anchor

end Whir.AnchorPrefixRefinementArith
