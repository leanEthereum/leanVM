/-
  LeanVM.Protocol.EndToEnd.Front.TableFidLeanIsaRows

  The Python verifier's instruction tables are the leanISA instance's at values in `E`: their
  flush forms and their constraints, evaluated at any values of a table's columns in the challenge
  field, are the instance's polynomials evaluated there through `algebraMap K E`.
-/

module

public import LeanVM.Protocol.EndToEnd.Complete.Flushes

/-!
# The Python tables at values in `E`

`LeanVM.Protocol.EndToEnd.Complete.Flushes` compares the Python's instruction tables
(`python-verifier/verifier.py:686-855` at leanVM `127510d14c98ade4e8a97646c44fa7f1ff5e752d`) with
the leanISA instance's on rows in `K`. The table sumcheck's terminal check evaluates them at the
claimed column values, which lie in `E`; this module lifts the comparison to `E`:

* `pyFlush_evalE`: at any values `e` of table `t`'s columns in `E`, the Python's flushes of a side,
  each coordinate a `Form` evaluated on `e` and padded to sixteen slots, are the instance's flushes
  of that side evaluated by `eval₂ (algebraMap K E)` on `e`, in order;
* `jumpConstraints_evalE`: `JUMP`'s Python constraints at `e` are the instance's constraint
  polynomials at `e`.

**Method.** Kernel evaluation cannot unfold `E`'s arithmetic in a module, so nothing is evaluated
over `E`: the canonical forms are still compared over `K` (`pyNF_eq_clNF`), and the two
evaluations at `E` points through the canonical forms are proved structurally, by induction over
the term lists (`termsEval_liftTerms_canon`) and over Clean's expressions
(`termsEval_liftTerms_exprTerms`): lifting a list of terms' coefficients by `algebraMap K E`
commutes with the canonical form, and Clean's expansion into terms evaluates as `eval₂`.
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Arithmetization LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd.Complete CompPoly CPoly

@[expose] public section

/-! ## Lifting the coefficients -/

/-- A list of terms over `K` with its coefficients lifted to `E`. -/
def liftTerms (l : Terms K) : Terms E := l.map fun t ↦ (t.1, ofK t.2)

/-- No terms, lifted. -/
@[simp] theorem liftTerms_nil : liftTerms [] = [] := rfl

/-- A term then the rest, lifted. -/
@[simp] theorem liftTerms_cons (t : List ℕ × K) (l : Terms K) :
    liftTerms (t :: l) = (t.1, ofK t.2) :: liftTerms l := rfl

/-- Lifting commutes with concatenation. -/
theorem liftTerms_append (a b : Terms K) : liftTerms (a ++ b) = liftTerms a ++ liftTerms b := by
  simp [liftTerms]

/-- Lifting commutes with the product of term lists. -/
theorem liftTerms_termsMul (a b : Terms K) :
    liftTerms (termsMul a b) = termsMul (liftTerms a) (liftTerms b) := by
  simp only [liftTerms, termsMul, List.map_flatMap, List.flatMap_map, List.map_map]
  congr 1
  funext u
  refine List.map_congr_left fun v _ ↦ ?_
  simp [ofK_mul]

/-- Inserting a term, lifted: its lifted term added to the rest. -/
theorem termsEval_liftTerms_insertTerm (r : ℕ → E) (t : List ℕ × K) :
    ∀ l : Terms K, termsEval r (liftTerms (insertTerm t l)) =
      ofK t.2 * (t.1.map r).prod + termsEval r (liftTerms l)
  | [] => by simp [insertTerm]
  | u :: us => by
    unfold insertTerm
    split_ifs with h1 h2
    · simp only [liftTerms_cons, termsEval_cons, h1, ofK_add]; ring
    · simp
    · simp only [liftTerms_cons, termsEval_cons, termsEval_liftTerms_insertTerm r t us]; ring

/-- **The canonical form, lifted, evaluates as the lifted terms** at any values in `E`. -/
theorem termsEval_liftTerms_canon (r : ℕ → E) (l : Terms K) :
    termsEval r (liftTerms (canon l)) = termsEval r (liftTerms l) := by
  have hf : ∀ m : Terms K,
      termsEval r (liftTerms (m.filter fun t ↦ decide (t.2 ≠ 0))) = termsEval r (liftTerms m) := by
    intro m
    induction m with
    | nil => rfl
    | cons t m ih =>
      rw [List.filter_cons]
      split
      · rw [liftTerms_cons, liftTerms_cons, termsEval_cons, termsEval_cons, ih]
      · rename_i h
        have h0 : t.2 = 0 := by simpa using h
        rw [ih, liftTerms_cons, termsEval_cons, h0, ofK_zero', zero_mul, zero_add]
  have hfold : ∀ m : Terms K,
      termsEval r (liftTerms (m.foldr insertTerm [])) = termsEval r (liftTerms m) := by
    intro m
    induction m with
    | nil => rfl
    | cons t m ih =>
      rw [List.foldr_cons, termsEval_liftTerms_insertTerm, ih, liftTerms_cons, termsEval_cons]
  rw [canon, hf, hfold]
  induction l with
  | nil => rfl
  | cons t l ih =>
    simp only [List.map_cons, liftTerms_cons, termsEval_cons, ih]
    congr 2
    exact ((monoSort_perm t.1).map r).prod_eq

/-! ## Values of a table's columns -/

/-- Values of a table's `n` columns, read by index with zeros past the width. -/
def rowE {n : ℕ} (e : Fin n → E) : ℕ → E := fun i ↦ if h : i < n then e ⟨i, h⟩ else 0

/-- A symbolic form at values in `E` is the value of its canonical form, lifted. -/
theorem evaluate_toForm_E (f : FormC) (r : ℕ → E) :
    f.toForm.evaluate r = termsEval r (liftTerms (canon f.termsK)) := by
  have ht : f.toForm.terms = liftTerms f.termsK := by
    simp [FormC.toForm, FormC.termsK, liftTerms, Coef.ev_eq]
  rw [evaluate_eq_termsEval, termsEval_liftTerms_canon, ht]

section Eval₂

variable {n : ℕ} {R S : Type} [CommSemiring R] {_ : BEq R} {_ : LawfulBEq R} [CommSemiring S]
  (f : R →+* S) (e : Fin n → S)

/-- `eval₂` of `0`, at any `BEq` instance on the coefficients. -/
theorem eval₂_zero' : (0 : CMvPolynomial n R).eval₂ f e = 0 :=
  (CMvPolynomial.eval₂Hom f e).map_zero

/-- `eval₂` of a sum, at any `BEq` instance on the coefficients. -/
theorem eval₂_add' (p q : CMvPolynomial n R) : (p + q).eval₂ f e = p.eval₂ f e + q.eval₂ f e :=
  (CMvPolynomial.eval₂Hom f e).map_add p q

/-- `eval₂` of a product, at any `BEq` instance on the coefficients. -/
theorem eval₂_mul' (p q : CMvPolynomial n R) : (p * q).eval₂ f e = p.eval₂ f e * q.eval₂ f e :=
  (CMvPolynomial.eval₂Hom f e).map_mul p q

end Eval₂

/-- Clean's expansion of an expression into terms, lifted, evaluates at values in `E` as the
expression's polynomial does through `eval₂ (algebraMap K E)`. -/
theorem termsEval_liftTerms_exprTerms {n : ℕ} (e : Fin n → E) (x : Expression K) :
    termsEval (rowE e) (liftTerms (exprTerms x)) =
      (x.toCMvPolynomial n).eval₂ (algebraMap K E) e := by
  induction x with
  | var v =>
    simp only [exprTerms, liftTerms_cons, liftTerms_nil, termsEval_cons, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, mul_one, termsEval_nil, add_zero,
      Expression.toCMvPolynomial, rowE, ofK_one', one_mul]
    split_ifs with h
    · simp [CMvPolynomial.eval₂_X]
    · exact (eval₂_zero' _ e).symm
  | const c =>
    simp [exprTerms, Expression.toCMvPolynomial, CMvPolynomial.eval₂_C]
  | add a b ha hb =>
    rw [exprTerms, liftTerms_append, termsEval_append, ha, hb, Expression.toCMvPolynomial]
    exact (eval₂_add' _ e _ _).symm
  | mul a b ha hb =>
    rw [exprTerms, liftTerms_termsMul, termsEval_termsMul, ha, hb, Expression.toCMvPolynomial]
    exact (eval₂_mul' _ e _ _).symm

/-- Slot `k` of an interaction's flush polynomials at values in `E` is the value of its terms,
lifted. -/
theorem flushPolys_slot_eval₂ {n : ℕ} (e : Fin n → E) (i : AbstractInteraction K) (k : Fin 16) :
    ((flushPolys channelSep n i).get k).eval₂ (algebraMap K E) e =
      termsEval (rowE e) (liftTerms (coordTerms i k)) := by
  simp only [flushPolys, Vector.get_ofFn, coordTerms]
  split_ifs with hk
  · simp [CMvPolynomial.eval₂_C]
  · cases i.msg.toArray[k.val - 1]? with
    | none =>
      simp only [Option.map_none, Option.getD_none, exprTerms, liftTerms_cons, liftTerms_nil,
        termsEval_cons, termsEval_nil, List.map_nil, List.prod_nil, mul_one, add_zero]
      rw [ofK_zero']
      exact eval₂_zero' _ e
    | some x => simp [termsEval_liftTerms_exprTerms]

/-! ## The flushes at values in `E` -/

/-- The Python's flushes of a side at values in `E` are the lifted canonical forms' values. -/
theorem pySide_evalE (t : Fin 6) (side : Side) (r : ℕ → E) :
    ((pySide t side).map fun coords ↦
        (List.range 16).map fun k ↦ (coords.getD k {}).evaluate r) =
      (pyNF t side).map (·.map fun l ↦ termsEval r (liftTerms l)) := by
  rw [pySide_eq, pyNF, List.map_map, List.map_map]
  refine List.map_congr_left fun coords _ ↦ ?_
  simp only [Function.comp_apply, List.map_map]
  refine List.map_congr_left fun k _ ↦ ?_
  have hd : ((coords.map FormC.toForm).getD k {}) = (coords.getD k {}).toForm := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases coords[k]? <;> rfl
  rw [Function.comp_apply, hd, evaluate_toForm_E]

/-- The instance's flushes of a side at values in `E` are the lifted canonical forms' values. -/
theorem instSide_evalE (t : Fin 6) (side : Side) (e : Fin (width (opIdx t)) → E) :
    (((LeanIsa.flushes (opIdx t)).filter fun f ↦ decide (f.1 = side)).map
        fun f ↦ f.2.toList.map fun P ↦ P.eval₂ (algebraMap K E) e) =
      (clNF t side).map (·.map fun l ↦ termsEval (rowE e) (liftTerms l)) := by
  rw [flushes_opIdx, List.filter_map, List.map_map, clNF, List.map_map]
  refine List.map_congr_left fun i _ ↦ ?_
  simp only [Function.comp_apply, List.map_map]
  apply List.ext_getElem (by simp)
  intro k h1 h2
  have hk : k < 16 := by simpa using h2
  simp only [List.getElem_map, Vector.getElem_toList, List.getElem_range, Function.comp_apply,
    termsEval_liftTerms_canon]
  exact flushPolys_slot_eval₂ e i ⟨k, hk⟩

/-- **The Python's flushes are the instance's at values in `E`.** At any values `e` of opcode
table `t`'s columns in `E`, the Python table's flushes of a side, each coordinate evaluated on `e`
and padded to sixteen slots, are the instance's flushes of that side evaluated on `e` by
`eval₂ (algebraMap K E)`, in order. -/
theorem pyFlush_evalE (t : Fin 6) (side : Side) (e : Fin (width (opIdx t)) → E) :
    ((pySide t side).map fun coords ↦
        (List.range 16).map fun k ↦ (coords.getD k {}).evaluate (rowE e)) =
      (((LeanIsa.flushes (opIdx t)).filter fun f ↦ decide (f.1 = side)).map
        fun f ↦ f.2.toList.map fun P ↦ P.eval₂ (algebraMap K E) e) := by
  rw [pySide_evalE, instSide_evalE, pyNF_eq_clNF]

/-! ## The constraints at values in `E` -/

/-- The instance's constraints of opcode table `t` are Clean's assertions as polynomials. -/
theorem constraints_opIdx (t : Fin 6) :
    LeanIsa.constraints (opIdx t) =
      (opcodeComponent t).rowOperations.constraints.map (·.toCMvPolynomial (width (opIdx t))) := by
  simp only [LeanIsa.constraints, opIdx, opcodeTable, Air.Flat.Component.toM3]
  rfl

/-- `JUMP`'s Python constraints, with the column indices resolved. -/
theorem jumpConstraints_getD (ev : List E) :
    jumpConstraints ev = [ev.getD 13 0 + ev.getD 5 0 * ev.getD 12 0,
      ev.getD 5 0 * (ev.getD 13 0 + 1)] := by
  have h5 : colIdx jumpColumns "v_cond" = 5 := by decide +kernel
  have h12 : colIdx jumpColumns "w" = 12 := by decide +kernel
  have h13 : colIdx jumpColumns "b" = 13 := by decide +kernel
  simp only [jumpConstraints, h5, h12, h13]

/-- **`JUMP`'s constraints at values in `E`**: the Python's `JUMP` constraints of values read by
index as `e` are the instance's constraint polynomials evaluated on `e`. -/
theorem jumpConstraints_evalE (e : Fin (width (opIdx 4)) → E) (ev : List E)
    (hev : ∀ i, ev.getD i 0 = rowE e i) :
    jumpConstraints ev = (LeanIsa.constraints (opIdx 4)).map (·.eval₂ (algebraMap K E) e) := by
  have hl : (LeanIsa.constraints (opIdx 4)).map (·.eval₂ (algebraMap K E) e) =
      ((opcodeComponent 4).rowOperations.constraints.map (canon ∘ exprTerms)).map
        fun l ↦ termsEval (rowE e) (liftTerms l) := by
    rw [constraints_opIdx, List.map_map, List.map_map]
    refine List.map_congr_left fun x _ ↦ ?_
    simp only [Function.comp_apply, termsEval_liftTerms_canon, termsEval_liftTerms_exprTerms]
  rw [hl, jump_constraints_canon, jumpConstraints_getD, hev, hev, hev]
  simp only [List.map_cons, List.map_nil, liftTerms_cons, liftTerms_nil, termsEval_cons,
    termsEval_nil, List.prod_cons, List.prod_nil, ofK_one', one_mul, mul_one, add_zero]
  simp only [List.cons.injEq, and_true]
  constructor <;> ring

end
end LeanVM.Protocol.EndToEnd.Front
