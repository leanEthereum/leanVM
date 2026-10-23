/-
  LeanVM.Protocol.ToClean.ExpressionPolynomial

  Below this header, a verbatim copy of Clean's `Clean/Circuit/ExpressionPolynomial.lean` at
  `b449bf59` (Clean pull request 466), which no Clean revision built for this repository's Lean
  contains yet. Deleted when the pin contains it; its importer then imports
  `Clean.Circuit.ExpressionPolynomial`, and the aggregate drops it.

  Clean's licence notice:

  MIT License

  Copyright (c) 2024-2025 zkSecurity, LLC

  Permission is hereby granted, free of charge, to any person obtaining a copy
  of this software and associated documentation files (the "Software"), to deal
  in the Software without restriction, including without limitation the rights
  to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
  copies of the Software, and to permit persons to whom the Software is
  furnished to do so, subject to the following conditions:

  The above copyright notice and this permission notice shall be included in all
  copies or substantial portions of the Software.

  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
  IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
  FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
  AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
  LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
  OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
  SOFTWARE.
-/

module

public import Clean.Circuit.Expression
public import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Polynomial interpretation of circuit expressions

Expressions have a polynomial interpretation and a syntactic degree bound. A finite-width
interpretation additionally requires a proof that every referenced variable is in range.
The evaluation theorem then connects the polynomial to the actual array-backed environment.
The prover-data field is irrelevant to expression evaluation.

This is the expression-algebra input to leanerVM's M3 constraint relation. It does not interpret
lookups, directed messages, or global table balance.
-/

namespace Expression

@[expose] public section

variable {F : Type}

/-- A syntactic upper bound on the total degree of an expression. -/
def degreeBound : Expression F → ℕ
  | .var _ => 1
  | .const _ => 0
  | .add a b => max a.degreeBound b.degreeBound
  | .mul a b => a.degreeBound + b.degreeBound

/-- Every variable used by the expression lies below the declared width. -/
def WithinWidth (width : ℕ) : Expression F → Prop
  | .var v => v.index < width
  | .const _ => True
  | .add a b => a.WithinWidth width ∧ b.WithinWidth width
  | .mul a b => a.WithinWidth width ∧ b.WithinWidth width

instance instDecidableWithinWidth (width : ℕ) (e : Expression F) : Decidable (e.WithinWidth width) :=
  match e with
  | .var v => inferInstanceAs (Decidable (v.index < width))
  | .const _ => isTrue trivial
  | .add a b =>
    let _ := instDecidableWithinWidth width a
    let _ := instDecidableWithinWidth width b
    inferInstanceAs (Decidable (a.WithinWidth width ∧ b.WithinWidth width))
  | .mul a b =>
    let _ := instDecidableWithinWidth width a
    let _ := instDecidableWithinWidth width b
    inferInstanceAs (Decidable (a.WithinWidth width ∧ b.WithinWidth width))

variable [Field F]

/-- Interpret every variable index directly, with no truncation or default value. -/
noncomputable def toMvPolynomial : Expression F → MvPolynomial ℕ F
  | .var v => MvPolynomial.X v.index
  | .const c => MvPolynomial.C c
  | .add a b => a.toMvPolynomial + b.toMvPolynomial
  | .mul a b => a.toMvPolynomial*b.toMvPolynomial

/-- Polynomial evaluation agrees with the expression evaluator in every environment. -/
theorem eval_toMvPolynomial (e : Expression F) (env : Environment F) :
    MvPolynomial.eval env.get e.toMvPolynomial = e.eval env := by
  induction e with
  | var v => simp [toMvPolynomial, eval]
  | const c => simp [toMvPolynomial, eval]
  | add a b ha hb => simp [toMvPolynomial, eval, ha, hb]
  | mul a b ha hb => simp [toMvPolynomial, eval, ha, hb]

/-- Total polynomial degree is at most the syntactic bound. -/
theorem totalDegree_toMvPolynomial_le (e : Expression F) :
    e.toMvPolynomial.totalDegree ≤ e.degreeBound := by
  induction e with
  | var v => simp [toMvPolynomial, degreeBound]
  | const c => simp [toMvPolynomial, degreeBound]
  | add a b ha hb =>
    exact (MvPolynomial.totalDegree_add _ _).trans (max_le_max ha hb)
  | mul a b ha hb =>
    exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add ha hb)

/-- Interpret an expression over exactly `width` variables, using its range proof. -/
noncomputable def toBoundedPolynomial (width : ℕ) (e : Expression F)
    (h : e.WithinWidth width) : MvPolynomial (Fin width) F :=
  match e with
  | .var v => MvPolynomial.X ⟨v.index, h⟩
  | .const c => MvPolynomial.C c
  | .add a b => a.toBoundedPolynomial width h.1 + b.toBoundedPolynomial width h.2
  | .mul a b => a.toBoundedPolynomial width h.1*b.toBoundedPolynomial width h.2

/-- The finite-variable interpretation has the same syntactic degree bound. -/
theorem totalDegree_toBoundedPolynomial_le (width : ℕ) (e : Expression F)
    (h : e.WithinWidth width) :
    (e.toBoundedPolynomial width h).totalDegree ≤ e.degreeBound := by
  induction e with
  | var v => simp [toBoundedPolynomial, degreeBound]
  | const c => simp [toBoundedPolynomial, degreeBound]
  | add a b ha hb =>
    exact (MvPolynomial.totalDegree_add _ _).trans (max_le_max (ha h.1) (hb h.2))
  | mul a b ha hb =>
    exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add (ha h.1) (hb h.2))

/-- In-range row entries evaluate exactly as Clean's array-backed environment. The width
hypothesis prevents out-of-range variables from being silently replaced by zero. -/
theorem eval_toBoundedPolynomial (width : ℕ) (e : Expression F)
    (h : e.WithinWidth width) (row : Vector F width) (data : ProverData F) :
    MvPolynomial.eval (fun i : Fin width ↦ row[i.val]) (e.toBoundedPolynomial width h) =
      e.eval (Environment.fromArray row.toArray data) := by
  induction e with
  | var v =>
    have hv : v.index < row.toArray.size := by
      rw [row.size_toArray]
      exact h
    simp [toBoundedPolynomial, eval, Array.getElem?_eq_getElem hv]
  | const c => simp [toBoundedPolynomial, eval]
  | add a b ha hb => simp [toBoundedPolynomial, eval, ha h.1, hb h.2]
  | mul a b ha hb => simp [toBoundedPolynomial, eval, ha h.1, hb h.2]

end
end Expression
