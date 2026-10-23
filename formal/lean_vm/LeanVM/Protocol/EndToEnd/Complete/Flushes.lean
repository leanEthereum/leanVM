/-
  LeanVM.Protocol.EndToEnd.Complete.Flushes

  The Python verifier's instruction tables are the leanISA instance's: their bus flushes evaluate
  to the instance's flush tuples, their count columns are the instance's, and their constraints
  are the instance's, row by row.
-/

module

public import LeanVM.Protocol.LeanIsa
public import LeanVM.Protocol.Verifier

/-!
# The Python tables are the instance's

Fidelity of the six instruction tables of `python-verifier/verifier.py` at leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`, lines 686-855 (`Flushes`, `_flushes_arith`,
`_flushes_set`, `_flushes_deref`, `_flushes_jump`, `_jump_constraints`, `_flushes_blake2s`,
`TABLES`), transcribed as `LeanVM.Protocol.Verifier.tables`, against the leanISA instance's
opcode tables (`LeanIsa.flushes`, `LeanIsa.counts`, `LeanIsa.constraints` at `opIdx t`), which are
Clean's components through `Component.toM3`.

* `pyFlush_eval`: on every row of table `t`, the Python's flushes of a side, each coordinate a
  `Form` evaluated on the row (`rowFn`) and padded to sixteen slots, are the instance's flushes of
  that side evaluated on the row, in the same order (an equality, not only a permutation).
* `pyCountColumns`: the Python's count columns (`cnt*`) are the instance's count columns.
* `pyConstraints_eval`: the Python's constraints of a row are the instance's constraint
  polynomials on the row, in order; `pyNConstraints`: only `JUMP` has any, two.
* `pyForm_terms`: every Python flush has at most sixteen coordinates, each a form of terms of at
  most two column indices below the table's width.

**Method.** Both sides are polynomials in the row's cells, compared in a canonical form over `K`
(`canon`: each monomial's indices sorted, terms gathered by monomial in lexicographic order with
their coefficients added, zero coefficients dropped), under which evaluation is invariant
(`termsEval_canon`). Clean's message expressions expand into terms over `K` (`exprTerms`). The
Python's forms have coefficients in `E`, which a module's kernel evaluation cannot compute; their
coefficients are only ever built from `0`, `1`, `g` and its powers by sums and products, so each
table is restated with symbolic coefficients (`FormC`, `FlushesC`, the `…C` tables, line for line
the transcription), and the transcription *is* the restatement read through `Coef.ev`, by
definitional unfolding (`pySide_eq`, `rfl`). The symbolic coefficients evaluate in `K`
(`Coef.evK`, `Coef.ev_eq`), and the two sides' canonical forms are compared by kernel evaluation
over `K` (`pyNF_eq_clNF`), once per table and side. No mismatch.
-/

namespace LeanVM.Protocol.EndToEnd.Complete

open LeanVM.Parameters LeanVM.Arithmetization LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.LeanIsa CompPoly CPoly

@[expose] public section

/-! ## Polynomials as lists of terms -/

/-- A polynomial as a list of terms: a monomial (column indices, with repetition) and its
coefficient. -/
abbrev Terms (R : Type) : Type := List (List ℕ × R)

/-- The value of a list of terms at an assignment of the columns. -/
def termsEval {R : Type} [CommRing R] (r : ℕ → R) (l : Terms R) : R :=
  (l.map fun t ↦ t.2 * (t.1.map r).prod).sum

section TermsEval

variable {R : Type} [CommRing R] (r : ℕ → R)

@[simp] theorem termsEval_nil : termsEval r ([] : Terms R) = 0 := rfl

@[simp] theorem termsEval_cons (t : List ℕ × R) (l : Terms R) :
    termsEval r (t :: l) = t.2 * (t.1.map r).prod + termsEval r l := by
  simp [termsEval]

theorem termsEval_append (a b : Terms R) :
    termsEval r (a ++ b) = termsEval r a + termsEval r b := by
  simp [termsEval]

/-- The product of two lists of terms. -/
def termsMul (a b : Terms R) : Terms R :=
  a.flatMap fun s ↦ b.map fun t ↦ (s.1 ++ t.1, s.2 * t.2)

theorem termsEval_map_mul (s : List ℕ × R) (b : Terms R) :
    termsEval r (b.map fun t ↦ (s.1 ++ t.1, s.2 * t.2)) =
      s.2 * (s.1.map r).prod * termsEval r b := by
  induction b with
  | nil => simp
  | cons t b ihb =>
    simp only [List.map_cons, termsEval_cons, List.map_append, List.prod_append, ihb]
    ring

theorem termsEval_termsMul (a b : Terms R) :
    termsEval r (termsMul a b) = termsEval r a * termsEval r b := by
  induction a with
  | nil => simp [termsMul]
  | cons s a ih =>
    simp only [termsMul, List.flatMap_cons, termsEval_append, termsEval_cons] at ih ⊢
    rw [ih, termsEval_map_mul, add_mul]

end TermsEval

/-- Lifting the coefficients evaluates as lifting the value. -/
theorem termsEval_map_ofK (r : ℕ → K) (l : Terms K) :
    termsEval (fun i ↦ ofK (r i)) (l.map fun u ↦ (u.1, ofK u.2)) = ofK (termsEval r l) := by
  induction l with
  | nil => simp
  | cons u l ih =>
    simp only [List.map_cons, termsEval_cons, ih, ofK_add, ofK_mul]
    congr 2
    induction u.1 with
    | nil => simp
    | cons i m ihm => simp only [List.map_cons, List.prod_cons, ihm, ofK_mul]

/-! ## The canonical form -/

/-- Lexicographic order on monomials. -/
def monoLt : List ℕ → List ℕ → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => decide (a < b) || (decide (a = b) && monoLt as bs)

/-- Insert an index into a sorted monomial. -/
def monoInsert (i : ℕ) : List ℕ → List ℕ
  | [] => [i]
  | j :: js => if i ≤ j then i :: j :: js else j :: monoInsert i js

/-- Sort a monomial's indices (insertion sort). -/
def monoSort : List ℕ → List ℕ
  | [] => []
  | i :: is => monoInsert i (monoSort is)

theorem monoSort_perm : ∀ m : List ℕ, (monoSort m).Perm m := by
  have hins : ∀ (i : ℕ) (m : List ℕ), (monoInsert i m).Perm (i :: m) := by
    intro i m
    induction m with
    | nil => rfl
    | cons j js ih =>
      unfold monoInsert
      split_ifs
      · rfl
      · exact (ih.cons j).trans (List.Perm.swap i j js)
  intro m
  induction m with
  | nil => rfl
  | cons i is ih => exact (hins i _).trans (ih.cons i)

/-- Insert a term into a list sorted by monomial, adding into an equal monomial's
coefficient. -/
def insertTerm (t : List ℕ × K) : Terms K → Terms K
  | [] => [t]
  | u :: us =>
    if u.1 = t.1 then (u.1, u.2 + t.2) :: us
    else if monoLt t.1 u.1 then t :: u :: us else u :: insertTerm t us

/-- The canonical form of a list of terms: monomials sorted, gathered in lexicographic order,
zero coefficients dropped. -/
def canon (l : Terms K) : Terms K :=
  ((l.map fun t ↦ (monoSort t.1, t.2)).foldr insertTerm []).filter fun t ↦ decide (t.2 ≠ 0)

theorem termsEval_insertTerm (r : ℕ → K) (t : List ℕ × K) :
    ∀ l : Terms K, termsEval r (insertTerm t l) = t.2 * (t.1.map r).prod + termsEval r l
  | [] => by simp [insertTerm]
  | u :: us => by
    unfold insertTerm
    split_ifs with h1 h2
    · simp only [termsEval_cons, h1]; ring
    · simp
    · simp only [termsEval_cons, termsEval_insertTerm r t us]; ring

/-- **Evaluation is invariant under the canonical form.** -/
theorem termsEval_canon (r : ℕ → K) (l : Terms K) : termsEval r (canon l) = termsEval r l := by
  have hf : ∀ m : Terms K, termsEval r (m.filter fun t ↦ decide (t.2 ≠ 0)) = termsEval r m := by
    intro m
    induction m with
    | nil => rfl
    | cons t m ih =>
      rw [List.filter_cons]
      split
      · rw [termsEval_cons, termsEval_cons, ih]
      · rename_i h
        have h0 : t.2 = 0 := by simpa using h
        rw [ih, termsEval_cons, h0, zero_mul, zero_add]
  have hfold : ∀ m : Terms K, termsEval r (m.foldr insertTerm []) = termsEval r m := by
    intro m
    induction m with
    | nil => rfl
    | cons t m ih => rw [List.foldr_cons, termsEval_insertTerm, ih, termsEval_cons]
  rw [canon, hf, hfold]
  induction l with
  | nil => rfl
  | cons t l ih =>
    simp only [List.map_cons, termsEval_cons, ih]
    congr 2
    exact ((monoSort_perm t.1).map r).prod_eq

/-! ## Rows -/

/-- A row read with zeros past its width. -/
def rowK {n : ℕ} (row : Fin n → K) : ℕ → K := fun i ↦ if h : i < n then row ⟨i, h⟩ else 0

/-- A row as the Python's forms read it: cell `i` lifted to `E`, `0` past the width. -/
def rowFn {n : ℕ} (row : Fin n → K) : ℕ → E := fun i ↦ if h : i < n then ofK (row ⟨i, h⟩) else 0

/-- `rowFn` is the lift of `rowK`. -/
theorem rowFn_eq {n : ℕ} (row : Fin n → K) : rowFn row = fun i ↦ ofK (rowK row i) := by
  funext i
  unfold rowFn rowK
  split_ifs <;> simp

/-! ## The Python's forms with symbolic coefficients -/

/-- A coefficient of a Python form, as the transcription builds it. -/
inductive Coef where
  /-- `0`. -/
  | zero
  /-- `1`. -/
  | one
  /-- `GEN`. -/
  | gen
  /-- `_gpow(e)`. -/
  | gpow (e : ℕ)
  /-- `GEN ** e`. -/
  | genPow (e : ℕ)
  /-- A sum. -/
  | add (a b : Coef)
  /-- A product. -/
  | mul (a b : Coef)

/-- A symbolic coefficient's value in `E`, as the transcription computes it. -/
def Coef.ev : Coef → E
  | .zero => 0
  | .one => 1
  | .gen => Verifier.gen
  | .gpow e => Verifier.gpow e
  | .genPow e => Verifier.gen ^ e
  | .add a b => a.ev + b.ev
  | .mul a b => a.ev * b.ev

/-- A symbolic coefficient's value in `K`. -/
def Coef.evK : Coef → K
  | .zero => 0
  | .one => 1
  | .gen => g
  | .gpow e => g ^ e
  | .genPow e => g ^ e
  | .add a b => a.evK + b.evK
  | .mul a b => a.evK * b.evK

/-- `GEN` is the generator of `K`, lifted. -/
theorem gen_eq_ofK : Verifier.gen = ofK g := rfl

/-- The lift of zero. -/
theorem ofK_zero' : ofK 0 = 0 := _root_.map_zero (algebraMap K E)

/-- The lift of one. -/
theorem ofK_one' : ofK 1 = 1 := _root_.map_one (algebraMap K E)

/-- The lift of a power. -/
theorem ofK_pow (a : K) (n : ℕ) : ofK (a ^ n) = ofK a ^ n := map_pow (algebraMap K E) a n

/-- Every coefficient lies in `K`: its value is the lift of its value in `K`. -/
theorem Coef.ev_eq : ∀ c : Coef, c.ev = ofK c.evK
  | .zero => by simp [Coef.ev, Coef.evK]
  | .one => by simp [Coef.ev, Coef.evK]
  | .gen => rfl
  | .gpow e => by simp [Coef.ev, Coef.evK, Verifier.gpow, gen_eq_ofK, ofK_pow]
  | .genPow e => by simp [Coef.ev, Coef.evK, gen_eq_ofK, ofK_pow]
  | .add a b => by simp [Coef.ev, Coef.evK, Coef.ev_eq a, Coef.ev_eq b, ofK_add]
  | .mul a b => by simp [Coef.ev, Coef.evK, Coef.ev_eq a, Coef.ev_eq b, ofK_mul]

/-- `Form` with symbolic coefficients. -/
structure FormC where
  /-- The terms. -/
  terms : List (List ℕ × Coef) := []

/-- `addTerm`. -/
def addTermC : List (List ℕ × Coef) → List ℕ → Coef → List (List ℕ × Coef)
  | [], m, c => [(m, .add .zero c)]
  | (m', c') :: rest, m, c =>
    if m' = m then (m', .add c' c) :: rest else (m', c') :: addTermC rest m c

/-- `Form.addScaled`. -/
def FormC.addScaled (f other : FormC) (weight : Coef) : FormC :=
  ⟨other.terms.foldl (fun acc t ↦ addTermC acc t.1 (.mul weight t.2)) f.terms⟩

/-- `Form.add`. -/
def FormC.add (f h : FormC) : FormC := f.addScaled h .one

/-- `Form.sum`. -/
def FormC.sum (forms : List FormC) : FormC := forms.foldl FormC.add {}

/-- `Form.const`. -/
def FormC.const (value : Coef) : FormC := ⟨[([], value)]⟩

/-- `Form.col`. -/
def FormC.col (index : ℕ) (exponent : ℕ := 0) : FormC := ⟨[([index], .gpow exponent)]⟩

/-- `Form.prod`. -/
def FormC.prod (a b : ℕ) (exponent : ℕ := 0) : FormC :=
  ⟨[([min a b, max a b], .gpow exponent)]⟩

/-- The form the symbolic one stands for. -/
def FormC.toForm (f : FormC) : Form := ⟨f.terms.map fun t ↦ (t.1, t.2.ev)⟩

/-- Its terms over `K`. -/
def FormC.termsK (f : FormC) : Terms K := f.terms.map fun t ↦ (t.1, t.2.evK)

/-- `Flushes` with symbolic coefficients. -/
structure FlushesC where
  /-- The pushed tuples. -/
  push : List (List FormC) := []
  /-- The pulled tuples. -/
  pull : List (List FormC) := []

namespace FlushesC

/-- `Flushes.pair`. -/
def pair (f : FlushesC) (push pull : List FormC) : FlushesC := ⟨f.push ++ [push], f.pull ++ [pull]⟩

/-- `Flushes.state_derived`. -/
def stateDerived (f : FlushesC) (pc fp : ℕ) (npc nfp : FormC) : FlushesC :=
  f.pair [FormC.const .one, npc, nfp] [FormC.const .one, FormC.col pc, FormC.col fp]

/-- `Flushes.state_step`. -/
def stateStep (f : FlushesC) (pc fp : ℕ) : FlushesC :=
  f.stateDerived pc fp (FormC.col pc 1) (FormC.col fp)

/-- `Flushes._counted`. -/
def counted (f : FlushesC) (pre : List FormC) (count : ℕ) (suffix : List FormC) : FlushesC :=
  f.pair (pre ++ [FormC.col count 1] ++ suffix) (pre ++ [FormC.col count] ++ suffix)

/-- `Flushes.bytecode`. -/
def bytecode (f : FlushesC) (pc count opcode : ℕ) (operands : List FormC) : FlushesC :=
  f.counted [FormC.const (.genPow 2), FormC.col pc] count (FormC.const (.gpow opcode) :: operands)

/-- `Flushes.memory`. -/
def memory (f : FlushesC) (address : FormC) (count : ℕ) (values : List FormC) : FlushesC :=
  f.counted [FormC.const .gen, address] count values

/-- `Flushes.memory_cols`. -/
def memoryCols (f : FlushesC) (address : FormC) (count : ℕ) (columns : List ℕ) : FlushesC :=
  f.memory address count
    (columns.map (FormC.col ·) ++ List.replicate (3 - columns.length) (FormC.const .zero))

end FlushesC

/-- `_flushes_arith(opcode, multiply)`, symbolically. -/
def flushesArithC (opcode : ℕ) (multiply : Bool) : FlushesC :=
  let c := colIdx arithColumns
  let va := [c "va_0", c "va_1", c "va_2"]
  let vb := [c "vb_0", c "vb_1", c "vb_2"]
  let result : List FormC :=
    if multiply then
      towerLanes.map fun lane ↦
        FormC.sum (lane.map fun (j, k) ↦ FormC.prod (va.getD j 0) (vb.getD k 0))
    else (List.range 3).map fun i ↦ (FormC.col (va.getD i 0)).add (FormC.col (vb.getD i 0))
  let f : FlushesC := {}
  let f := f.stateStep (c "pc") (c "fp")
  let f := f.bytecode (c "pc") (c "cnt_bc") opcode
    [FormC.col (c "o_a"), FormC.col (c "o_b"), FormC.col (c "o_c"), FormC.const .zero,
      FormC.const .zero]
  let f := f.memoryCols (FormC.prod (c "fp") (c "o_a")) (c "cnt_a") va
  let f := f.memoryCols (FormC.prod (c "fp") (c "o_b")) (c "cnt_b") vb
  f.memory (FormC.prod (c "fp") (c "o_c")) (c "cnt_c") result

/-- `_flushes_set()`, symbolically. -/
def flushesSetC : FlushesC :=
  let c := colIdx setColumns
  let k := [c "k_0", c "k_1", c "k_2"]
  let f : FlushesC := {}
  let f := f.stateStep (c "pc") (c "fp")
  let f := f.bytecode (c "pc") (c "cnt_bc") opSet
    (FormC.col (c "o") :: k.map (FormC.col ·) ++ [FormC.const .zero])
  f.memoryCols (FormC.prod (c "fp") (c "o")) (c "cnt") k

/-- `_flushes_deref()`, symbolically. -/
def flushesDerefC : FlushesC :=
  let c := colIdx derefColumns
  let pc := c "pc"
  let fp := c "fp"
  let fPc := c "f_pc"
  let fFp := c "f_fp"
  let v3 := [c "v3_0", c "v3_1", c "v3_2"]
  let gated := fun lane ↦ [FormC.col lane, FormC.prod fPc lane, FormC.prod fFp lane]
  let store : List FormC :=
    [FormC.sum (gated (v3.getD 0 0) ++ [FormC.prod fPc pc 2, FormC.prod fFp fp]),
      FormC.sum (gated (v3.getD 1 0)), FormC.sum (gated (v3.getD 2 0))]
  let f : FlushesC := {}
  let f := f.stateStep pc fp
  let f := f.bytecode pc (c "cnt_bc") opDeref
    [FormC.col (c "o1"), FormC.col (c "o2"), FormC.col (c "o3"), FormC.col fPc, FormC.col fFp]
  let f := f.memoryCols (FormC.prod fp (c "o1")) (c "cnt_ptr") [c "ptr"]
  let f := f.memory (FormC.prod (c "ptr") (c "o2")) (c "cnt_target") store
  f.memoryCols (FormC.prod fp (c "o3")) (c "cnt_local") v3

/-- `_flushes_jump()`, symbolically. -/
def flushesJumpC : FlushesC :=
  let c := colIdx jumpColumns
  let pc := c "pc"
  let fp := c "fp"
  let b := c "b"
  let f : FlushesC := {}
  let f := f.stateDerived pc fp
    (((FormC.prod b (c "v_pc")).add (FormC.prod b pc 1)).add (FormC.col pc 1))
    (((FormC.prod b (c "v_fp")).add (FormC.prod b fp)).add (FormC.col fp))
  let f := f.bytecode pc (c "cnt_bc") opJump
    [FormC.col (c "o_c"), FormC.col (c "o_d"), FormC.col (c "o_f"), FormC.const .zero,
      FormC.const .zero]
  let f := f.memoryCols (FormC.prod fp (c "o_c")) (c "cnt_c") [c "v_cond"]
  let f := f.memoryCols (FormC.prod fp (c "o_d")) (c "cnt_d") [c "v_pc"]
  f.memoryCols (FormC.prod fp (c "o_f")) (c "cnt_f") [c "v_fp"]

/-- `_flushes_blake2s()`, symbolically. -/
def flushesBlake2sC : FlushesC :=
  let c := colIdx blake2sColumns
  let operands := ["o_0", "o_1", "o_2", "o_3", "o_v", "o_out", "o_md"].map c
  let f : FlushesC := {}
  let f := f.stateStep (c "pc") (c "fp")
  let f := f.bytecode (c "pc") (c "cnt_bc") opBlake2s (operands.map (FormC.col ·))
  blake2sCells.foldl (fun f (cell, operand, exponent) ↦
    f.memoryCols (FormC.prod (c "fp") (c operand) exponent) (c ("cnt_" ++ cell))
      [c (cell ++ "_lo"), c (cell ++ "_hi")]) f

/-- The tables' flushes, symbolically, in opcode order. -/
def flushesC : Fin 6 → FlushesC
  | 0 => flushesArithC opXor false
  | 1 => flushesArithC opMul true
  | 2 => flushesSetC
  | 3 => flushesDerefC
  | 4 => flushesJumpC
  | 5 => flushesBlake2sC

/-- The Python table's flushes of a side. -/
def pySide (t : Fin 6) : Side → List (List Form)
  | .push => (tables.getD t default).flushes.push
  | .pull => (tables.getD t default).flushes.pull

/-- The symbolic flushes of a side. -/
def pySideC (t : Fin 6) : Side → List (List FormC)
  | .push => (flushesC t).push
  | .pull => (flushesC t).pull

/-- **The transcription is the symbolic restatement**, read through `Coef.ev`: by unfolding. -/
theorem pySide_eq : ∀ (t : Fin 6) (side : Side),
    pySide t side = (pySideC t side).map (·.map FormC.toForm)
  | 0, .push => rfl
  | 0, .pull => rfl
  | 1, .push => rfl
  | 1, .pull => rfl
  | 2, .push => rfl
  | 2, .pull => rfl
  | 3, .push => rfl
  | 3, .pull => rfl
  | 4, .push => rfl
  | 4, .pull => rfl
  | 5, .push => rfl
  | 5, .pull => rfl

/-- The canonical forms of the Python's flushes of a side over `K`, sixteen slots each. -/
def pyNF (t : Fin 6) (side : Side) : List (List (Terms K)) :=
  (pySideC t side).map fun coords ↦ (List.range 16).map fun k ↦ canon (coords.getD k {}).termsK

/-- `Form.evaluate` is the value of the form's terms. -/
theorem evaluate_eq_termsEval (f : Form) (r : ℕ → E) : f.evaluate r = termsEval r f.terms := by
  have hfold : ∀ (m : List ℕ) (c : E), m.foldl (fun acc i ↦ acc * r i) c = c * (m.map r).prod := by
    intro m
    induction m with
    | nil => simp
    | cons i m ih => intro c; rw [List.foldl_cons, ih, List.map_cons, List.prod_cons]; ring
  have hsum : ∀ (m : List E) (a : E), m.foldl (· + ·) a = a + m.sum := by
    intro m
    induction m with
    | nil => simp
    | cons x m ih => intro a; rw [List.foldl_cons, ih, List.sum_cons, add_assoc]
  simp only [Form.evaluate, sumE, hsum, zero_add, termsEval]
  exact congrArg List.sum (List.map_congr_left fun t _ ↦ hfold t.1 t.2)

/-- A symbolic form, evaluated on a row, is the lift of its terms' value over `K`. -/
theorem evaluate_toForm {n : ℕ} (f : FormC) (row : Fin n → K) :
    f.toForm.evaluate (rowFn row) = ofK (termsEval (rowK row) (canon f.termsK)) := by
  have ht : f.toForm.terms = f.termsK.map fun u ↦ (u.1, ofK u.2) := by
    simp [FormC.toForm, FormC.termsK, Coef.ev_eq]
  rw [evaluate_eq_termsEval, termsEval_canon, ← termsEval_map_ofK, rowFn_eq, ht]

/-- The Python's flushes of a side, evaluated on a row, are the lifts of their canonical forms'
values. -/
theorem pySide_eval (t : Fin 6) (side : Side) {n : ℕ} (row : Fin n → K) :
    ((pySide t side).map fun coords ↦
        (List.range 16).map fun k ↦ (coords.getD k {}).evaluate (rowFn row)) =
      (pyNF t side).map (·.map fun l ↦ ofK (termsEval (rowK row) l)) := by
  rw [pySide_eq, pyNF, List.map_map, List.map_map]
  refine List.map_congr_left fun coords _ ↦ ?_
  simp only [Function.comp_apply, List.map_map]
  refine List.map_congr_left fun k _ ↦ ?_
  have hd : ((coords.map FormC.toForm).getD k {}) = (coords.getD k {}).toForm := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases coords[k]? <;> rfl
  rw [Function.comp_apply, hd, evaluate_toForm]

/-! ## Clean's messages -/

/-- A Clean expression as a list of terms. -/
def exprTerms : Expression K → Terms K
  | .var v => [([v.index], 1)]
  | .const c => [([], c)]
  | .add a b => exprTerms a ++ exprTerms b
  | .mul a b => termsMul (exprTerms a) (exprTerms b)

/-- An expression's terms evaluate, at a row, as its polynomial in the row's variables. -/
theorem termsEval_exprTerms {n : ℕ} (row : Fin n → K) (e : Expression K) :
    termsEval (rowK row) (exprTerms e) = (e.toCMvPolynomial n).eval row := by
  induction e with
  | var v =>
    simp only [exprTerms, termsEval_cons, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, one_mul, termsEval_nil, add_zero, Expression.toCMvPolynomial, rowK]
    split_ifs with h
    · simp [CMvPolynomial.eval_X]
    · simp [CMvPolynomial.eval_zero]
  | const c => simp [exprTerms, Expression.toCMvPolynomial, CMvPolynomial.eval_C]
  | add a b ha hb =>
    simp only [exprTerms, termsEval_append, ha, hb, Expression.toCMvPolynomial,
      CMvPolynomial.eval_add]
  | mul a b ha hb =>
    simp only [exprTerms, termsEval_termsMul, ha, hb, Expression.toCMvPolynomial,
      CMvPolynomial.eval_mul]

/-- Slot `k` of an interaction's flush, as terms: the separator, then the message. -/
def coordTerms (i : AbstractInteraction K) (k : ℕ) : Terms K :=
  if k = 0 then [([], channelSep i.channel)]
  else exprTerms ((i.msg.toArray[k - 1]?).getD (.const 0))

/-- The canonical forms of the instance's flushes of a side, sixteen slots each. -/
def clNF (t : Fin 6) (side : Side) : List (List (Terms K)) :=
  (((opcodeComponent t).rowOperations.interactions.filter
    fun i ↦ decide (sideOf (channelDir i.channel) = side)).map
      fun i ↦ (List.range 16).map fun k ↦ canon (coordTerms i k))

/-- Slot `k` of an interaction's flush polynomials, evaluated on a row, is the value of its
terms. -/
theorem flushPolys_slot_eval {n : ℕ} (row : Fin n → K) (i : AbstractInteraction K) (k : Fin 16) :
    ((flushPolys channelSep n i).get k).eval row = termsEval (rowK row) (coordTerms i k) := by
  simp only [flushPolys, Vector.get_ofFn, coordTerms]
  split_ifs with hk
  · simp [CMvPolynomial.eval_C]
  · cases i.msg.toArray[k.val - 1]? with
    | none => simp [exprTerms, CMvPolynomial.eval_zero]
    | some e => simp [termsEval_exprTerms]

/-- The instance's flushes of opcode table `t`: the interactions of its Clean component, each on
its channel's side, as the sixteen flush polynomials. -/
theorem flushes_opIdx (t : Fin 6) :
    LeanIsa.flushes (opIdx t) = (opcodeComponent t).rowOperations.interactions.map
      fun i ↦ (sideOf (channelDir i.channel), flushPolys channelSep (width (opIdx t)) i) := by
  simp only [LeanIsa.flushes, opIdx, opcodeTable, Air.Flat.Component.toM3, List.map_map]
  rfl

/-- The instance's flushes of a side, evaluated on a row, are the lifts of the canonical forms'
values. -/
theorem instSide_eval (t : Fin 6) (side : Side) (row : Fin (width (opIdx t)) → K) :
    (((LeanIsa.flushes (opIdx t)).filter fun f ↦ decide (f.1 = side)).map
        fun f ↦ f.2.toList.map fun P ↦ ofK (P.eval row)) =
      (clNF t side).map (·.map fun l ↦ ofK (termsEval (rowK row) l)) := by
  rw [flushes_opIdx, List.filter_map, List.map_map, clNF, List.map_map]
  refine List.map_congr_left fun i _ ↦ ?_
  simp only [Function.comp_apply, List.map_map]
  apply List.ext_getElem (by simp)
  intro k h1 h2
  have hk : k < 16 := by simpa using h2
  simp only [List.getElem_map, Vector.getElem_toList, List.getElem_range, Function.comp_apply,
    termsEval_canon]
  exact congrArg ofK (flushPolys_slot_eval row i ⟨k, hk⟩)

/-! ## The flushes -/

/-- The Python's canonical flushes are Clean's, table by table and side by side (kernel
evaluation over `K`). -/
theorem pyNF_eq_clNF : ∀ (t : Fin 6) (side : Side), pyNF t side = clNF t side
  | 0, .push => by decide +kernel
  | 0, .pull => by decide +kernel
  | 1, .push => by decide +kernel
  | 1, .pull => by decide +kernel
  | 2, .push => by decide +kernel
  | 2, .pull => by decide +kernel
  | 3, .push => by decide +kernel
  | 3, .pull => by decide +kernel
  | 4, .push => by decide +kernel
  | 4, .pull => by decide +kernel
  | 5, .push => by decide +kernel
  | 5, .pull => by decide +kernel

/-- **The Python's flushes are the instance's.** On every row of opcode table `t`, the Python
table's flushes of a side, each coordinate evaluated on the row and padded to sixteen slots, are
the instance's flushes of that side evaluated on the row, in order. -/
theorem pyFlush_eval (t : Fin 6) (side : Side) (row : Fin (width (opIdx t)) → K) :
    ((pySide t side).map fun coords ↦
        (List.range 16).map fun k ↦ (coords.getD k {}).evaluate (rowFn row)) =
      (((LeanIsa.flushes (opIdx t)).filter fun f ↦ decide (f.1 = side)).map
        fun f ↦ f.2.toList.map fun P ↦ ofK (P.eval row)) := by
  rw [pySide_eval, instSide_eval, pyNF_eq_clNF]

/-- Every Python flush has at most sixteen coordinates, each a form of terms of at most two
column indices below the table's width. -/
theorem pyForm_terms : ∀ t : Fin 6,
    (∀ coords ∈ pySide t .push, coords.length ≤ 16 ∧ ∀ f ∈ coords, ∀ term ∈ f.terms,
      term.1.length ≤ 2 ∧ ∀ i ∈ term.1, i < width (opIdx t)) ∧
    (∀ coords ∈ pySide t .pull, coords.length ≤ 16 ∧ ∀ f ∈ coords, ∀ term ∈ f.terms,
      term.1.length ≤ 2 ∧ ∀ i ∈ term.1, i < width (opIdx t)) := by
  decide +kernel

/-! ## The count columns and the constraints -/

/-- **The Python's count columns are the instance's**, in order. -/
theorem pyCountColumns : ∀ t : Fin 6,
    (tables.getD t default).countColumns = (LeanIsa.counts (opIdx t)).map (·.val)
  | 0 => by
    rw [show (LeanIsa.counts (opIdx 0)).map (·.val) = [11, 12, 13, 14] by decide +kernel]
    simp [Table.countColumns, tables, arithColumns]
  | 1 => by
    rw [show (LeanIsa.counts (opIdx 1)).map (·.val) = [11, 12, 13, 14] by decide +kernel]
    simp [Table.countColumns, tables, arithColumns]
  | 2 => by
    rw [show (LeanIsa.counts (opIdx 2)).map (·.val) = [6, 7] by decide +kernel]
    simp [Table.countColumns, tables, setColumns]
  | 3 => by
    rw [show (LeanIsa.counts (opIdx 3)).map (·.val) = [11, 12, 13, 14] by decide +kernel]
    simp [Table.countColumns, tables, derefColumns]
  | 4 => by
    rw [show (LeanIsa.counts (opIdx 4)).map (·.val) = [8, 9, 10, 11] by decide +kernel]
    simp [Table.countColumns, tables, jumpColumns]
  | 5 => by
    rw [show (LeanIsa.counts (opIdx 5)).map (·.val) =
      [27, 28, 29, 30, 31, 32, 33, 34, 35, 36] by decide +kernel]
    simp [Table.countColumns, tables, blake2sColumns]

/-- Only `JUMP` has constraints, two. -/
theorem pyNConstraints : tables.map Table.nConstraints = [0, 0, 0, 0, 2, 0] := by
  decide +kernel

/-- The opcode tables other than `JUMP` assert nothing. -/
theorem constraints_opIdx_ne_jump : ∀ t : Fin 6, t ≠ 4 →
    (opcodeComponent t).rowOperations.constraints = [] := by
  decide +kernel

/-- `JUMP`'s two assertions in canonical form: `b + v_cond·w` and `v_cond·(b + 1)`. -/
theorem jump_constraints_canon :
    (opcodeComponent 4).rowOperations.constraints.map (canon ∘ exprTerms) =
      [[([5, 12], 1), ([13], 1)], [([5], 1), ([5, 13], 1)]] := by
  decide +kernel

/-- The instance's constraints, evaluated on a row and lifted to `E`, are the lifts of the
canonical forms' values. -/
theorem instConstraints_eval (t : Fin 6) (row : Fin (width (opIdx t)) → K) :
    (LeanIsa.constraints (opIdx t)).map (fun P ↦ ofK (P.eval row)) =
      ((opcodeComponent t).rowOperations.constraints.map (canon ∘ exprTerms)).map
        fun l ↦ ofK (termsEval (rowK row) l) := by
  have hc : LeanIsa.constraints (opIdx t) =
      (opcodeComponent t).rowOperations.constraints.map
        (·.toCMvPolynomial (width (opIdx t))) := by
    simp only [LeanIsa.constraints, opIdx, opcodeTable, Air.Flat.Component.toM3]
    rfl
  rw [hc, List.map_map, List.map_map]
  refine List.map_congr_left fun e _ ↦ ?_
  simp only [Function.comp_apply, termsEval_canon, termsEval_exprTerms]

/-- A cell of a row's value list. -/
theorem getD_finRange_map {n : ℕ} (f : Fin n → E) (i : ℕ) (h : i < n) :
    ((List.finRange n).map f).getD i 0 = f ⟨i, h⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_map, List.getElem_finRange]
  rfl

/-- **The Python's constraints are the instance's**: on every row, the Python table's
constraints of the row's values are the instance's constraint polynomials on the row, in
order. -/
theorem pyConstraints_eval (t : Fin 6) (row : Fin (width (opIdx t)) → K) :
    (tables.getD t default).constraints ((List.finRange (width (opIdx t))).map fun i ↦ ofK (row i))
      = (LeanIsa.constraints (opIdx t)).map fun P ↦ ofK (P.eval row) := by
  rw [instConstraints_eval]
  by_cases ht : t = 4
  · subst ht
    rw [jump_constraints_canon]
    have h5 : colIdx jumpColumns "v_cond" = 5 := by decide +kernel
    have h12 : colIdx jumpColumns "w" = 12 := by decide +kernel
    have h13 : colIdx jumpColumns "b" = 13 := by decide +kernel
    have hw : width (opIdx 4) = 14 := by decide +kernel
    have l5 : 5 < width (opIdx 4) := by rw [hw]; omega
    have l12 : 12 < width (opIdx 4) := by rw [hw]; omega
    have l13 : 13 < width (opIdx 4) := by rw [hw]; omega
    have g5 := getD_finRange_map (fun i ↦ ofK (row i)) 5 l5
    have g12 := getD_finRange_map (fun i ↦ ofK (row i)) 12 l12
    have g13 := getD_finRange_map (fun i ↦ ofK (row i)) 13 l13
    have r5 : rowK row 5 = row ⟨5, l5⟩ := by simp [rowK, l5]
    have r12 : rowK row 12 = row ⟨12, l12⟩ := by simp [rowK, l12]
    have r13 : rowK row 13 = row ⟨13, l13⟩ := by simp [rowK, l13]
    show jumpConstraints _ = _
    simp only [jumpConstraints, h5, h12, h13, g5, g12, g13, List.map_cons, List.map_nil,
      termsEval_cons, termsEval_nil, List.prod_cons, List.prod_nil, r5, r12, r13, ofK_add,
      ofK_mul, List.cons.injEq, and_true]
    simp only [mul_one, one_mul, ofK_one', ofK_zero', add_zero]
    constructor <;> ring
  · rw [constraints_opIdx_ne_jump t ht]
    fin_cases t
    all_goals first | exact absurd rfl ht | rfl

end
end LeanVM.Protocol.EndToEnd.Complete
