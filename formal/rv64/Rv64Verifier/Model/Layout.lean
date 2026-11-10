import Rv64Verifier.Model.Multilinear

/-!
# The layout as the Rust computes it

`crates/verifier/src/layout.rs` (`Form`, `Flushes`, the tables, `qkeccak_slot`, `build_layout`),
`bus.rs`'s `bus_layout` and `ColumnClaim::on_stack`, one mirror per function, following the Rust
(the conventions of `Model.Multilinear`: a loop is a `foldl`, a buffer a `List`, a `u64` a
`BitVec 64`), each proved to compute what `Statement/LeanVmVerifier.lean` defines.

The statement transcribes the code before it named columns by index constants: it finds a
column by its name, a count column by the prefix `cnt`, a table's constraint count on a zero row.
The mirrors use the index constants, and the theorems below show they are the statement's columns.
A form is a list of terms in first-added order in both, a repeated monomial merged into its first
term, so the forms are equal as data (`flushesRust_eq`), not only in value. The coefficients are
`E` values: `E::pow` and the products are `Model.FieldAlg`'s, written `^` and `*` here.
-/

namespace Rv64Verifier.Model

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier

/-! ## Forms -/

/-- `Monomial`: `One`, `X(i)`, `Xy(i, j)` with `i ≤ j`. -/
inductive Monomial where
  | one
  | x (i : ℕ)
  | xy (i j : ℕ)
  deriving DecidableEq

/-- The statement's monomial: its column indices, sorted. -/
def Monomial.toSpec : Monomial → List ℕ
  | .one => []
  | .x i => [i]
  | .xy i j => [i, j]

theorem Monomial.toSpec_inj (a b : Monomial) : a.toSpec = b.toSpec ↔ a = b := by
  cases a <;> cases b <;> simp [Monomial.toSpec]

/-- A term: a monomial and its coefficient. -/
abbrev Term : Type := Monomial × E

/-- The statement's term. -/
def Term.toSpec (t : Term) : List ℕ × E := (t.1.toSpec, t.2)

/-- `Form`: its terms, each monomial once, in the order first added. -/
structure FormRust where
  terms : List Term := []

/-- The statement's form. -/
def FormRust.toSpec (f : FormRust) : Form := ⟨f.terms.map Term.toSpec⟩

/-- `Form::term`. -/
def FormRust.term (monomial : Monomial) (coefficient : E) : FormRust := ⟨[(monomial, coefficient)]⟩

/-- One iteration of `add_scaled`'s loop: the term with the monomial (`iter_mut().find`) gains
`c`, or a new term is pushed. -/
def addTermRust (terms : List Term) (monomial : Monomial) (c : E) : List Term :=
  match terms.findIdx? (·.1 == monomial) with
  | some i => terms.modify i fun t ↦ (t.1, t.2 + c)
  | none => terms ++ [(monomial, c)]

/-- `Form::add_scaled`. -/
def FormRust.addScaled (f other : FormRust) (weight : E) : FormRust :=
  ⟨other.terms.foldl (fun acc t ↦ addTermRust acc t.1 (weight * t.2)) f.terms⟩

/-- `Form + Form`: `add_scaled(other, ONE)`. -/
def FormRust.add (f g : FormRust) : FormRust := f.addScaled g 1

/-- `Form::sum`: a fold from the empty form. -/
def FormRust.sum (forms : List FormRust) : FormRust := forms.foldl FormRust.add {}

/-- A term's value at a row (`Form::evaluate`'s closure). -/
def termValue (column : List E) : Term → E
  | (.one, c) => c
  | (.x i, c) => c * column.getD i 0
  | (.xy i j, c) => c * column.getD i 0 * column.getD j 0

/-- `Form::evaluate`: `E::sum` of the terms' values. -/
def FormRust.evaluate (f : FormRust) (column : List E) : E :=
  (f.terms.map (termValue column)).foldl (· + ·) 0

/-- `GEN`, `E::new(2, 0, 0)`. -/
def genRust : E := eNew 2#64

/-- `gpow(index)`: `GEN.pow(index)`. -/
def gpowRust (index : ℕ) : E := genRust ^ index

/-- `constant(value)`. -/
def constantRust (value : E) : FormRust := .term .one value

/-- `col(index, exponent)`. -/
def colRust (index exponent : ℕ) : FormRust := .term (.x index) (gpowRust exponent)

/-- `prod(a, b, exponent)`. -/
def prodRust (a b exponent : ℕ) : FormRust := .term (.xy (min a b) (max a b)) (gpowRust exponent)

theorem genRust_eq : genRust = gen := rfl

theorem gpowRust_eq (index : ℕ) : gpowRust index = gpow index := rfl

theorem addTermRust_toSpec (terms : List Term) (m : Monomial) (c : E) :
    (addTermRust terms m c).map Term.toSpec = addTerm (terms.map Term.toSpec) m.toSpec c := by
  induction terms with
  | nil => simp [addTermRust, addTerm, Term.toSpec]
  | cons t rest ih =>
    by_cases h : t.1 = m
    · simp [addTermRust, addTerm, Term.toSpec, List.findIdx?_cons, h]
    · have h' : ¬ t.1.toSpec = m.toSpec := fun e ↦ h ((Monomial.toSpec_inj _ _).mp e)
      rw [List.map_cons, addTerm, ite_eq_right (by simpa [Term.toSpec] using h'), ← ih]
      unfold addTermRust
      rw [List.findIdx?_cons]
      have hb : (t.1 == m) = false := by simpa using h
      simp only [hb, Bool.false_eq_true, ite_false]
      cases rest.findIdx? (·.1 == m) with
      | none => simp
      | some i => simp [List.modify_succ_cons]

theorem FormRust.toSpec_addScaled (f g : FormRust) (w : E) :
    (f.addScaled g w).toSpec = f.toSpec.addScaled g.toSpec w := by
  simp only [FormRust.addScaled, FormRust.toSpec, Form.addScaled, Form.mk.injEq, List.foldl_map]
  generalize f.terms = A
  induction g.terms generalizing A with
  | nil => rfl
  | cons t rest ih =>
    simp only [List.foldl_cons]
    rw [ih, addTermRust_toSpec]
    rfl

theorem FormRust.toSpec_add (f g : FormRust) : (f.add g).toSpec = f.toSpec.add g.toSpec :=
  FormRust.toSpec_addScaled f g 1

theorem FormRust.toSpec_sum (forms : List FormRust) :
    (FormRust.sum forms).toSpec = Form.sum (forms.map FormRust.toSpec) := by
  suffices ∀ acc : FormRust, (forms.foldl FormRust.add acc).toSpec =
      (forms.map FormRust.toSpec).foldl Form.add acc.toSpec from this {}
  induction forms with
  | nil => intro acc; rfl
  | cons f rest ih =>
    intro acc
    simp only [List.foldl_cons, List.map_cons]
    rw [ih, FormRust.toSpec_add]

theorem FormRust.evaluate_eq (f : FormRust) (column : List E) :
    f.evaluate column = f.toSpec.evaluate (fun i ↦ column.getD i 0) := by
  unfold FormRust.evaluate Form.evaluate sumE FormRust.toSpec
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  rintro ⟨m, c⟩ _
  cases m <;> simp [termValue, Term.toSpec, Monomial.toSpec]

@[simp] theorem toSpec_constantRust (v : E) : (constantRust v).toSpec = Form.const v := rfl

@[simp] theorem toSpec_colRust (i e : ℕ) : (colRust i e).toSpec = Form.col i e := rfl

@[simp] theorem toSpec_prodRust (a b e : ℕ) : (prodRust a b e).toSpec = Form.prod a b e := rfl

/-- The empty form plus a one-term form is that form (the statement's `addTerm` writes `0 + c`). -/
theorem Form.empty_add_single (m : List ℕ) (c : E) : ({} : Form).add ⟨[(m, c)]⟩ = ⟨[(m, c)]⟩ := by
  simp [Form.add, Form.addScaled, addTerm]

/-! ## Flushes -/

/-- `SEP_STATE`, `SEP_MEM`, `SEP_BYTECODE`. -/
def sepStateRust : E := 1
def sepMemRust : E := genRust
def sepBytecodeRust : E := eNew 4#64

theorem sepBytecodeRust_eq : sepBytecodeRust = sepBytecode := by decide +kernel

/-- `Flushes`. -/
structure FlushesRust where
  push : List (List FormRust) := []
  pull : List (List FormRust) := []

/-- The statement's flushes. -/
def FlushesRust.toSpec (f : FlushesRust) : Flushes :=
  ⟨f.push.map (·.map FormRust.toSpec), f.pull.map (·.map FormRust.toSpec)⟩

namespace FlushesRust

/-- `Flushes::pair`. -/
def pair (f : FlushesRust) (push pull : List FormRust) : FlushesRust :=
  ⟨f.push ++ [push], f.pull ++ [pull]⟩

/-- `Flushes::state_derived`. -/
def stateDerived (f : FlushesRust) (pc fp : ℕ) (npc nfp : FormRust) : FlushesRust :=
  f.pair [constantRust sepStateRust, npc, nfp]
    [constantRust sepStateRust, colRust pc 0, colRust fp 0]

/-- `Flushes::state_step`. -/
def stateStep (f : FlushesRust) (pc fp : ℕ) : FlushesRust :=
  f.stateDerived pc fp (colRust pc 1) (colRust fp 0)

/-- `Flushes::counted`. -/
def counted (f : FlushesRust) (pre : List FormRust) (counter : FormRust) (count : ℕ)
    (suffix : List FormRust) : FlushesRust :=
  let side := fun counter : FormRust ↦ pre ++ [counter] ++ suffix
  f.pair (side counter) (side (colRust count 0))

/-- `Flushes::bytecode`. -/
def bytecode (f : FlushesRust) (pc count opcode : ℕ) (operands : List FormRust) : FlushesRust :=
  let suffix := [constantRust (gpowRust opcode)] ++ operands
  f.counted [constantRust sepBytecodeRust, colRust pc 0] (colRust count 1) count suffix

/-- `Flushes::memory`. -/
def memory (f : FlushesRust) (address : FormRust) (count : ℕ) (values : List FormRust) :
    FlushesRust :=
  f.counted [constantRust sepMemRust, address] (colRust count 1) count values

/-- `Flushes::memory_if`. -/
def memoryIf (f : FlushesRust) (flag : ℕ) (address : FormRust) (count : ℕ)
    (values : List FormRust) : FlushesRust :=
  let counter := ((colRust count 0).add (prodRust flag count 1)).add (prodRust flag count 0)
  f.counted [constantRust sepMemRust, address] counter count values

/-- `Flushes::memory_cols`: limb `i` is `col(columns[i], 0)`, or zero past the columns. -/
def memoryCols (f : FlushesRust) (address : FormRust) (count : ℕ) (columns : List ℕ) :
    FlushesRust :=
  let values := (List.range 3).map fun limb ↦ (columns[limb]?.map (colRust · 0)).getD (constantRust 0)
  f.memory address count values

theorem toSpec_pair (f : FlushesRust) (push pull : List FormRust) :
    (f.pair push pull).toSpec =
      f.toSpec.pair (push.map FormRust.toSpec) (pull.map FormRust.toSpec) := by
  simp [pair, toSpec, Flushes.pair]

theorem toSpec_stateDerived (f : FlushesRust) (pc fp : ℕ) (npc nfp : FormRust) :
    (f.stateDerived pc fp npc nfp).toSpec = f.toSpec.stateDerived pc fp npc.toSpec nfp.toSpec := by
  simp only [stateDerived, toSpec_pair, Flushes.stateDerived, List.map_cons, List.map_nil,
    toSpec_constantRust, toSpec_colRust]
  rfl

theorem toSpec_stateStep (f : FlushesRust) (pc fp : ℕ) :
    (f.stateStep pc fp).toSpec = f.toSpec.stateStep pc fp := by
  simp only [stateStep, toSpec_stateDerived, toSpec_colRust]
  rfl

theorem toSpec_counted (f : FlushesRust) (pre : List FormRust) (counter : FormRust) (count : ℕ)
    (suffix : List FormRust) :
    (f.counted pre counter count suffix).toSpec =
      f.toSpec.counted (pre.map FormRust.toSpec) counter.toSpec count
        (suffix.map FormRust.toSpec) := by
  simp only [counted, toSpec_pair, Flushes.counted, List.map_append, List.map_cons, List.map_nil,
    toSpec_colRust]

theorem toSpec_bytecode (f : FlushesRust) (pc count opcode : ℕ) (operands : List FormRust) :
    (f.bytecode pc count opcode operands).toSpec =
      f.toSpec.bytecode pc count opcode (operands.map FormRust.toSpec) := by
  simp only [bytecode, toSpec_counted, Flushes.bytecode, List.map_append, List.map_cons,
    List.map_nil, toSpec_constantRust, toSpec_colRust, sepBytecodeRust_eq, gpowRust_eq]
  rfl

theorem toSpec_memory (f : FlushesRust) (address : FormRust) (count : ℕ) (values : List FormRust) :
    (f.memory address count values).toSpec =
      f.toSpec.memory address.toSpec count (values.map FormRust.toSpec) := by
  simp only [memory, toSpec_counted, Flushes.memory, List.map_cons, List.map_nil,
    toSpec_constantRust, toSpec_colRust]
  rfl

theorem toSpec_memoryIf (f : FlushesRust) (flag : ℕ) (address : FormRust) (count : ℕ)
    (values : List FormRust) :
    (f.memoryIf flag address count values).toSpec =
      f.toSpec.memoryIf flag address.toSpec count (values.map FormRust.toSpec) := by
  simp only [memoryIf, toSpec_counted, Flushes.memoryIf, List.map_cons, List.map_nil,
    toSpec_constantRust, FormRust.toSpec_add, toSpec_colRust, toSpec_prodRust]
  have h : Form.sum [Form.col count, Form.prod flag count 1, Form.prod flag count] =
      ((Form.col count 0).add (Form.prod flag count 1)).add (Form.prod flag count 0) := by
    show ((({} : Form).add (Form.col count 0)).add _).add _ = _
    rw [Form.col, Form.empty_add_single]
  rw [h]
  rfl

theorem toSpec_memoryCols (f : FlushesRust) (address : FormRust) (count : ℕ) (columns : List ℕ)
    (h : columns.length ≤ 3) :
    (f.memoryCols address count columns).toSpec =
      f.toSpec.memoryCols address.toSpec count columns := by
  simp only [memoryCols, toSpec_memory, Flushes.memoryCols]
  congr 1
  match columns, h with
  | [], _ => rfl
  | [a], _ => rfl
  | [a, b], _ => rfl
  | [a, b, c], _ => rfl

end FlushesRust

/-! ## The tables' columns

Each table's local columns by index (`mod arith`, `set`, `deref`, `jump`, `keccak_head`), and
the statement's lookups of their names, which find the same indices. -/

/-- `OP_XOR` .. `OP_KECCAK`, `N_TABLES`. -/
def opXorRust : ℕ := 0
def opMulRust : ℕ := 1
def opSetRust : ℕ := 2
def opDerefRust : ℕ := 3
def opJumpRust : ℕ := 4
def opKeccakRust : ℕ := 5
def nTablesRust : ℕ := 6

/-- `STATE_LANES`, `KECCAK_CELLS`. -/
def stateLanesRust : ℕ := 25
def keccakCellsRust : ℕ := 13

namespace ArithCol
def pc : ℕ := 0
def fp : ℕ := 1
def oA : ℕ := 2
def oB : ℕ := 3
def oC : ℕ := 4
def va : List ℕ := [5, 6, 7]
def vb : List ℕ := [8, 9, 10]
def cntA : ℕ := 11
def cntB : ℕ := 12
def cntC : ℕ := 13
def cntBc : ℕ := 14
def width : ℕ := 15
def counts : List ℕ := [cntA, cntB, cntC, cntBc]
end ArithCol

namespace SetCol
def pc : ℕ := 0
def fp : ℕ := 1
def o : ℕ := 2
def k : List ℕ := [3, 4, 5]
def cnt : ℕ := 6
def cntBc : ℕ := 7
def width : ℕ := 8
def counts : List ℕ := [cnt, cntBc]
end SetCol

namespace DerefCol
def pc : ℕ := 0
def fp : ℕ := 1
def o1 : ℕ := 2
def o2 : ℕ := 3
def o3 : ℕ := 4
def fPc : ℕ := 5
def fFp : ℕ := 6
def ptr : ℕ := 7
def v3 : List ℕ := [8, 9, 10]
def cntPtr : ℕ := 11
def cntTarget : ℕ := 12
def cntLocal : ℕ := 13
def cntBc : ℕ := 14
def width : ℕ := 15
def counts : List ℕ := [cntPtr, cntTarget, cntLocal, cntBc]
end DerefCol

namespace JumpCol
def pc : ℕ := 0
def fp : ℕ := 1
def oC : ℕ := 2
def oD : ℕ := 3
def oF : ℕ := 4
def vCond : ℕ := 5
def vPc : ℕ := 6
def vFp : ℕ := 7
def cntC : ℕ := 8
def cntD : ℕ := 9
def cntF : ℕ := 10
def cntBc : ℕ := 11
def w : ℕ := 12
def b : ℕ := 13
def width : ℕ := 14
def counts : List ℕ := [cntC, cntD, cntF, cntBc]
end JumpCol

namespace KeccakCol
def pc : ℕ := 0
def fp : ℕ := 1
def oM : List ℕ := [2, 3, 4, 5]
def oTail : ℕ := 6
def oB8 : ℕ := 7
def oCap : ℕ := 8
def oOut : ℕ := 9
def oddIn : ℕ := 10
def oddOut : ℕ := 11
def outTwo : ℕ := 12
def outAll : ℕ := 13
def free : ℕ := 14
end KeccakCol

/-- `KECCAK_IN`, `KECCAK_OUT`, `KECCAK_CNT`, `KECCAK_CNT_BC`. -/
def keccakInRust : ℕ := KeccakCol.free + 1
def keccakOutRust : ℕ := keccakInRust + stateLanesRust
def keccakCntRust : ℕ := keccakOutRust + stateLanesRust
def keccakCntBcRust : ℕ := keccakCntRust + 2 * keccakCellsRust

/-- `KECCAK_COUNTS`: `KECCAK_CNT + i` for each `i`. -/
def keccakCountsRust : List ℕ := (List.range (2 * keccakCellsRust + 1)).map (keccakCntRust + ·)

/-- `TABLE_WIDTHS`. -/
def tableWidthsRust : List ℕ :=
  [ArithCol.width, ArithCol.width, SetCol.width, DerefCol.width, JumpCol.width, keccakCntBcRust + 1]

/-- `COUNT_COLUMNS`. -/
def countColumnsRust : List (List ℕ) :=
  [ArithCol.counts, ArithCol.counts, SetCol.counts, DerefCol.counts, JumpCol.counts,
    keccakCountsRust]

/-- `N_CONSTRAINTS`. -/
def nConstraintsRust : List ℕ := [0, 0, 0, 0, 2, 0]

/-- `NUM_GLOBAL_COLUMNS`, `QKECCAK`. -/
def numGlobalColumnsRust : ℕ := 6
def qkeccakRust : ℕ := 5

/-- `GLOBAL_COLUMN_BASES`: `bases[t] = bases[t - 1] + TABLE_WIDTHS[t - 1]` for `t` in `1..N_TABLES`. -/
def globalColumnBasesRust : List ℕ :=
  (List.range' 1 (nTablesRust - 1)).foldl
    (fun bases t ↦ bases.set t (bases.getD (t - 1) 0 + tableWidthsRust.getD (t - 1) 0))
    (List.replicate nTablesRust numGlobalColumnsRust)

theorem arith_names :
    columnIndexByName arithColumns "pc" = ArithCol.pc ∧
    columnIndexByName arithColumns "fp" = ArithCol.fp ∧
    columnIndexByName arithColumns "o_a" = ArithCol.oA ∧
    columnIndexByName arithColumns "o_b" = ArithCol.oB ∧
    columnIndexByName arithColumns "o_c" = ArithCol.oC ∧
    [columnIndexByName arithColumns "va_0", columnIndexByName arithColumns "va_1",
      columnIndexByName arithColumns "va_2"] = ArithCol.va ∧
    [columnIndexByName arithColumns "vb_0", columnIndexByName arithColumns "vb_1",
      columnIndexByName arithColumns "vb_2"] = ArithCol.vb ∧
    columnIndexByName arithColumns "cnt_a" = ArithCol.cntA ∧
    columnIndexByName arithColumns "cnt_b" = ArithCol.cntB ∧
    columnIndexByName arithColumns "cnt_c" = ArithCol.cntC ∧
    columnIndexByName arithColumns "cnt_bc" = ArithCol.cntBc := by decide +kernel

theorem set_names :
    columnIndexByName setColumns "pc" = SetCol.pc ∧
    columnIndexByName setColumns "fp" = SetCol.fp ∧
    columnIndexByName setColumns "o" = SetCol.o ∧
    [columnIndexByName setColumns "k_0", columnIndexByName setColumns "k_1",
      columnIndexByName setColumns "k_2"] = SetCol.k ∧
    columnIndexByName setColumns "cnt" = SetCol.cnt ∧
    columnIndexByName setColumns "cnt_bc" = SetCol.cntBc := by decide +kernel

theorem deref_names :
    columnIndexByName derefColumns "pc" = DerefCol.pc ∧
    columnIndexByName derefColumns "fp" = DerefCol.fp ∧
    columnIndexByName derefColumns "o1" = DerefCol.o1 ∧
    columnIndexByName derefColumns "o2" = DerefCol.o2 ∧
    columnIndexByName derefColumns "o3" = DerefCol.o3 ∧
    columnIndexByName derefColumns "f_pc" = DerefCol.fPc ∧
    columnIndexByName derefColumns "f_fp" = DerefCol.fFp ∧
    columnIndexByName derefColumns "ptr" = DerefCol.ptr ∧
    [columnIndexByName derefColumns "v3_0", columnIndexByName derefColumns "v3_1",
      columnIndexByName derefColumns "v3_2"] = DerefCol.v3 ∧
    columnIndexByName derefColumns "cnt_ptr" = DerefCol.cntPtr ∧
    columnIndexByName derefColumns "cnt_target" = DerefCol.cntTarget ∧
    columnIndexByName derefColumns "cnt_local" = DerefCol.cntLocal ∧
    columnIndexByName derefColumns "cnt_bc" = DerefCol.cntBc := by decide +kernel

theorem jump_names :
    columnIndexByName jumpColumns "pc" = JumpCol.pc ∧
    columnIndexByName jumpColumns "fp" = JumpCol.fp ∧
    columnIndexByName jumpColumns "o_c" = JumpCol.oC ∧
    columnIndexByName jumpColumns "o_d" = JumpCol.oD ∧
    columnIndexByName jumpColumns "o_f" = JumpCol.oF ∧
    columnIndexByName jumpColumns "v_cond" = JumpCol.vCond ∧
    columnIndexByName jumpColumns "v_pc" = JumpCol.vPc ∧
    columnIndexByName jumpColumns "v_fp" = JumpCol.vFp ∧
    columnIndexByName jumpColumns "cnt_c" = JumpCol.cntC ∧
    columnIndexByName jumpColumns "cnt_d" = JumpCol.cntD ∧
    columnIndexByName jumpColumns "cnt_f" = JumpCol.cntF ∧
    columnIndexByName jumpColumns "cnt_bc" = JumpCol.cntBc ∧
    columnIndexByName jumpColumns "w" = JumpCol.w ∧
    columnIndexByName jumpColumns "b" = JumpCol.b := by decide +kernel

theorem keccak_names :
    columnIndexByName keccakColumns "pc" = KeccakCol.pc ∧
    columnIndexByName keccakColumns "fp" = KeccakCol.fp ∧
    ["o_m0", "o_m1", "o_m2", "o_m3"].map (columnIndexByName keccakColumns) = KeccakCol.oM ∧
    columnIndexByName keccakColumns "o_tail" = KeccakCol.oTail ∧
    columnIndexByName keccakColumns "o_b8" = KeccakCol.oB8 ∧
    columnIndexByName keccakColumns "o_cap" = KeccakCol.oCap ∧
    columnIndexByName keccakColumns "o_out" = KeccakCol.oOut ∧
    columnIndexByName keccakColumns "odd_in" = KeccakCol.oddIn ∧
    columnIndexByName keccakColumns "odd_out" = KeccakCol.oddOut ∧
    columnIndexByName keccakColumns "out_two" = KeccakCol.outTwo ∧
    columnIndexByName keccakColumns "out_all" = KeccakCol.outAll ∧
    columnIndexByName keccakColumns "free" = KeccakCol.free ∧
    columnIndexByName keccakColumns "cnt_bc" = keccakCntBcRust ∧
    keccakIn = keccakInRust ∧ keccakOut = keccakOutRust ∧ keccakCnt = keccakCntRust := by
  decide +kernel

theorem tableWidthsRust_eq : tables.map Table.width = tableWidthsRust := by decide +kernel

theorem countColumnsRust_eq : tables.map Table.countColumns = countColumnsRust := by decide +kernel

theorem opcodes_eq : tables.map Table.opcode = List.range nTablesRust := by decide +kernel

theorem globalColumnBasesRust_eq : globalColumnBasesRust = globalColumnBases := by decide +kernel

/-! ## Each table's flushes -/

/-- `TOWER_LANES`. -/
def towerLanesRust : List (List (ℕ × ℕ)) :=
  [[(0, 0), (1, 2), (2, 1)], [(0, 1), (1, 0), (1, 2), (2, 1), (2, 2)],
    [(0, 2), (1, 1), (2, 0), (2, 2)]]

/-- `flushes_arith(opcode, multiply)`. -/
def flushesArithRust (opcode : ℕ) (multiply : Bool) : FlushesRust :=
  let f : FlushesRust := {}
  let f := f.stateStep ArithCol.pc ArithCol.fp
  let operands := [colRust ArithCol.oA 0, colRust ArithCol.oB 0, colRust ArithCol.oC 0,
    constantRust 0, constantRust 0]
  let f := f.bytecode ArithCol.pc ArithCol.cntBc opcode operands
  let f := f.memoryCols (prodRust ArithCol.fp ArithCol.oA 0) ArithCol.cntA ArithCol.va
  let f := f.memoryCols (prodRust ArithCol.fp ArithCol.oB 0) ArithCol.cntB ArithCol.vb
  let result := if multiply then
      towerLanesRust.map fun lane ↦
        FormRust.sum (lane.map fun jk ↦ prodRust (ArithCol.va.getD jk.1 0) (ArithCol.vb.getD jk.2 0) 0)
    else (List.range 3).map fun i ↦
      (colRust (ArithCol.va.getD i 0) 0).add (colRust (ArithCol.vb.getD i 0) 0)
  f.memory (prodRust ArithCol.fp ArithCol.oC 0) ArithCol.cntC result

/-- `flushes_set()`. -/
def flushesSetRust : FlushesRust :=
  let f : FlushesRust := {}
  let f := f.stateStep SetCol.pc SetCol.fp
  let operands := [colRust SetCol.o 0, colRust (SetCol.k.getD 0 0) 0, colRust (SetCol.k.getD 1 0) 0,
    colRust (SetCol.k.getD 2 0) 0, constantRust 0]
  let f := f.bytecode SetCol.pc SetCol.cntBc opSetRust operands
  f.memoryCols (prodRust SetCol.fp SetCol.o 0) SetCol.cnt SetCol.k

/-- `flushes_deref()`. -/
def flushesDerefRust : FlushesRust :=
  let gated := fun lane ↦
    [colRust lane 0, prodRust DerefCol.fPc lane 0, prodRust DerefCol.fFp lane 0]
  let store := [
    FormRust.sum (gated (DerefCol.v3.getD 0 0) ++
      [prodRust DerefCol.fPc DerefCol.pc 2, prodRust DerefCol.fFp DerefCol.fp 0]),
    FormRust.sum (gated (DerefCol.v3.getD 1 0)),
    FormRust.sum (gated (DerefCol.v3.getD 2 0))]
  let f : FlushesRust := {}
  let f := f.stateStep DerefCol.pc DerefCol.fp
  let operands := [colRust DerefCol.o1 0, colRust DerefCol.o2 0, colRust DerefCol.o3 0,
    colRust DerefCol.fPc 0, colRust DerefCol.fFp 0]
  let f := f.bytecode DerefCol.pc DerefCol.cntBc opDerefRust operands
  let f := f.memoryCols (prodRust DerefCol.fp DerefCol.o1 0) DerefCol.cntPtr [DerefCol.ptr]
  let f := f.memory (prodRust DerefCol.ptr DerefCol.o2 0) DerefCol.cntTarget store
  f.memoryCols (prodRust DerefCol.fp DerefCol.o3 0) DerefCol.cntLocal DerefCol.v3

/-- `flushes_jump()`. -/
def flushesJumpRust : FlushesRust :=
  let f : FlushesRust := {}
  let f := f.stateDerived JumpCol.pc JumpCol.fp
    (((prodRust JumpCol.b JumpCol.vPc 0).add (prodRust JumpCol.b JumpCol.pc 1)).add
      (colRust JumpCol.pc 1))
    (((prodRust JumpCol.b JumpCol.vFp 0).add (prodRust JumpCol.b JumpCol.fp 0)).add
      (colRust JumpCol.fp 0))
  let operands := [colRust JumpCol.oC 0, colRust JumpCol.oD 0, colRust JumpCol.oF 0,
    constantRust 0, constantRust 0]
  let f := f.bytecode JumpCol.pc JumpCol.cntBc opJumpRust operands
  let f := f.memoryCols (prodRust JumpCol.fp JumpCol.oC 0) JumpCol.cntC [JumpCol.vCond]
  let f := f.memoryCols (prodRust JumpCol.fp JumpCol.oD 0) JumpCol.cntD [JumpCol.vPc]
  f.memoryCols (prodRust JumpCol.fp JumpCol.oF 0) JumpCol.cntF [JumpCol.vFp]

/-- `jump_constraints(columns)`. -/
def jumpConstraintsRust (columns : List E) : List E :=
  let condition := columns.getD JumpCol.vCond 0
  let inverse := columns.getD JumpCol.w 0
  let flag := columns.getD JumpCol.b 0
  [flag + condition * inverse, condition * (flag + 1)]

/-- `keccak_cell_lanes(odd)[cell]`. -/
def keccakCellLanesAt (odd : Bool) (cell : ℕ) : Option ℕ × Option ℕ :=
  if 9 ≤ cell ∨ (odd ∧ 1 ≤ cell) then (some (2 * cell - 1), some (2 * cell))
  else if odd then (none, some 0)
  else if cell = 8 then (some 16, none)
  else (some (2 * cell), some (2 * cell + 1))

/-- `keccak_cell_lanes(odd)`: the array, by `from_fn`. -/
def keccakCellLanesRust (odd : Bool) : List (Option ℕ × Option ℕ) :=
  (List.range keccakCellsRust).map (keccakCellLanesAt odd)

/-- `layout_limb(even, odd, flag, missing)`. -/
def layoutLimbRust (even odd : Option ℕ) (flag : ℕ) (missing : Option ℕ) : FormRust :=
  let a := even.or missing
  let b := odd.or missing
  if a = b then (a.map (colRust · 0)).getD (constantRust 0)
  else FormRust.sum ([a.map (colRust · 0), a.map (prodRust flag · 0), b.map (prodRust flag · 0)].filterMap id)

/-- `flushes_keccak()`'s address of read cell `cell`. -/
def keccakAddressRust (cell : ℕ) : FormRust :=
  if cell < 4 then prodRust KeccakCol.fp (KeccakCol.oM.getD cell 0) 0
  else if cell < 8 then prodRust KeccakCol.fp KeccakCol.oTail (cell - 4)
  else if cell = 8 then prodRust KeccakCol.fp KeccakCol.oB8 0
  else prodRust KeccakCol.fp KeccakCol.oCap (cell - 9)

/-- One iteration of `flushes_keccak()`'s loop over the cells, on side `side`. -/
def keccakCellRust (side lanes flag : ℕ) (missing : Option ℕ) (f : FlushesRust) (cell : ℕ) :
    FlushesRust :=
  let even := keccakCellLanesRust false
  let odd := keccakCellLanesRust true
  let lane := fun l : Option ℕ ↦ l.map (lanes + ·)
  let limb := fun (e o : Option ℕ) ↦ layoutLimbRust (lane e) (lane o) flag missing
  let values := [limb (even.getD cell (none, none)).1 (odd.getD cell (none, none)).1,
    limb (even.getD cell (none, none)).2 (odd.getD cell (none, none)).2, constantRust 0]
  let count := keccakCntRust + keccakCellsRust * side + cell
  match side, cell with
  | 0, _ => f.memory (keccakAddressRust cell) count values
  | _, 0 => f.memory (prodRust KeccakCol.fp KeccakCol.oOut 0) count values
  | _, _ =>
    let flag := if cell = 1 then KeccakCol.outTwo else KeccakCol.outAll
    f.memoryIf flag (prodRust KeccakCol.fp KeccakCol.oOut cell) count values

/-- `flushes_keccak()`. -/
def flushesKeccakRust : FlushesRust :=
  let f : FlushesRust := {}
  let f := f.stateStep KeccakCol.pc KeccakCol.fp
  let operands := KeccakCol.oM ++ [KeccakCol.oTail, KeccakCol.oB8, KeccakCol.oCap, KeccakCol.oOut,
    KeccakCol.oddIn, KeccakCol.oddOut, KeccakCol.outTwo, KeccakCol.outAll]
  let f := f.bytecode KeccakCol.pc keccakCntBcRust opKeccakRust (operands.map (colRust · 0))
  let sides := [(0, keccakInRust, KeccakCol.oddIn, some KeccakCol.free),
    (1, keccakOutRust, KeccakCol.oddOut, none)]
  sides.foldl (fun f s ↦
    (List.range keccakCellsRust).foldl (keccakCellRust s.1 s.2.1 s.2.2.1 s.2.2.2) f) f

@[simp] theorem FlushesRust.toSpec_empty : ({} : FlushesRust).toSpec = {} := rfl

theorem flushesArithRust_eq (opcode : ℕ) (multiply : Bool) :
    (flushesArithRust opcode multiply).toSpec = flushesArith opcode multiply := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := arith_names
  have hr : List.range 3 = [0, 1, 2] := rfl
  cases multiply <;>
  simp (disch := decide) only [flushesArithRust, flushesArith, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hr,
    FlushesRust.toSpec_empty, FlushesRust.toSpec_stateStep, FlushesRust.toSpec_bytecode,
    FlushesRust.toSpec_memory, FlushesRust.toSpec_memoryCols, FormRust.toSpec_sum,
    FormRust.toSpec_add, toSpec_colRust, toSpec_prodRust, toSpec_constantRust, towerLanesRust,
    towerLanes, List.map_cons, List.map_nil, ArithCol.va, ArithCol.vb, List.getD_cons_zero,
    List.getD_cons_succ, Bool.false_eq_true, ite_false, ite_true]

theorem flushesSetRust_eq : flushesSetRust.toSpec = flushesSet := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := set_names
  simp (disch := decide) only [flushesSetRust, flushesSet, h1, h2, h3, h4, h5, h6,
    FlushesRust.toSpec_empty, FlushesRust.toSpec_stateStep, FlushesRust.toSpec_bytecode,
    FlushesRust.toSpec_memoryCols, toSpec_colRust, toSpec_prodRust, toSpec_constantRust,
    List.map_cons, List.map_nil, SetCol.k, List.getD_cons_zero, List.getD_cons_succ,
    List.cons_append, List.nil_append]
  rfl

theorem flushesDerefRust_eq : flushesDerefRust.toSpec = flushesDeref := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := deref_names
  simp (disch := decide) only [flushesDerefRust, flushesDeref, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    h10, h11, h12, h13, FlushesRust.toSpec_empty, FlushesRust.toSpec_stateStep,
    FlushesRust.toSpec_bytecode, FlushesRust.toSpec_memory, FlushesRust.toSpec_memoryCols,
    FormRust.toSpec_sum, toSpec_colRust, toSpec_prodRust, List.map_cons, List.map_nil, DerefCol.v3,
    List.getD_cons_zero, List.getD_cons_succ, List.cons_append, List.nil_append]
  rfl

theorem flushesJumpRust_eq : flushesJumpRust.toSpec = flushesJump := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, -, h14⟩ := jump_names
  simp (disch := decide) only [flushesJumpRust, flushesJump, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    h10, h11, h12, h14, FlushesRust.toSpec_empty, FlushesRust.toSpec_stateDerived,
    FlushesRust.toSpec_bytecode, FlushesRust.toSpec_memoryCols, FormRust.toSpec_add,
    toSpec_colRust, toSpec_prodRust, toSpec_constantRust, List.map_cons, List.map_nil]
  rfl

theorem jumpConstraintsRust_eq (columns : List E) :
    jumpConstraintsRust columns = jumpConstraints columns := by
  obtain ⟨-, -, -, -, -, h6, -, -, -, -, -, -, h13, h14⟩ := jump_names
  simp only [jumpConstraintsRust, jumpConstraints, h6, h13, h14]

theorem keccakCellLanesRust_getD (odd : Bool) {cell : ℕ} (h : cell < 13) :
    (keccakCellLanesRust odd).getD cell (none, none) = cellLanes odd cell := by
  rw [List.getD_eq_getElem?_getD, keccakCellLanesRust, List.getElem?_map,
    List.getElem?_range (by simpa [keccakCellsRust] using h)]
  rfl

theorem layoutLimbRust_eq (even odd : Option ℕ) (flag : ℕ) (missing : Option ℕ) :
    (layoutLimbRust even odd flag missing).toSpec = layoutLimb even odd flag missing := by
  have ho : ∀ x : Option ℕ, (x.orElse fun _ ↦ missing) = x.or missing := by
    intro x; cases x <;> rfl
  simp only [layoutLimbRust, layoutLimb, ho]
  generalize even.or missing = a
  generalize odd.or missing = b
  by_cases h : a = b
  · subst h
    cases a <;> simp
  · simp only [h, ite_false, FormRust.toSpec_sum]
    cases a <;> cases b <;> simp

theorem toSpec_keccakAddressRust (cell : ℕ) :
    (keccakAddressRust cell).toSpec =
      if cell < 4 then Form.prod KeccakCol.fp (KeccakCol.oM.getD cell 0)
      else if cell < 8 then Form.prod KeccakCol.fp KeccakCol.oTail (cell - 4)
      else if cell = 8 then Form.prod KeccakCol.fp KeccakCol.oB8
      else Form.prod KeccakCol.fp KeccakCol.oCap (cell - 9) := by
  unfold keccakAddressRust
  split_ifs <;> rfl

theorem FlushesRust.foldl_toSpec {α : Type} (l : List α) (g : FlushesRust → α → FlushesRust)
    (g' : Flushes → α → Flushes) (f : FlushesRust) (f' : Flushes) (hf : f.toSpec = f')
    (h : ∀ f, ∀ x ∈ l, (g f x).toSpec = g' f.toSpec x) : (l.foldl g f).toSpec = l.foldl g' f' := by
  induction l generalizing f f' with
  | nil => exact hf
  | cons x l ih =>
    simp only [List.foldl_cons]
    exact ih _ _ (by rw [h f x (by simp), hf]) (fun f y hy ↦ h f y (by simp [hy]))

theorem flushesKeccakRust_eq : flushesKeccakRust.toSpec = flushesKeccak := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := keccak_names
  simp only [flushesKeccak, h3]
  simp only [flushesKeccakRust, List.map_cons, List.map_nil, List.zipIdx_cons, List.zipIdx_nil,
    List.foldl_cons, List.foldl_nil, h1, h2, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
    h16, keccakCellsRust]
  apply FlushesRust.foldl_toSpec
  · apply FlushesRust.foldl_toSpec
    · simp only [FlushesRust.toSpec_empty, FlushesRust.toSpec_stateStep,
        FlushesRust.toSpec_bytecode, KeccakCol.oM, List.map_cons, List.map_nil, List.cons_append,
        List.nil_append, toSpec_colRust]
      rfl
    · intro f cell hcell
      rw [List.mem_range] at hcell
      simp only [keccakCellRust, keccakCellLanesRust_getD _ hcell, FlushesRust.toSpec_memory,
        toSpec_keccakAddressRust, layoutLimbRust_eq, List.map_cons, List.map_nil,
        toSpec_constantRust, keccakCellsRust]
      simp
  · intro f cell hcell
    rw [List.mem_range] at hcell
    rcases cell with _ | cell
    · simp only [keccakCellRust, keccakCellLanesRust_getD _ hcell, FlushesRust.toSpec_memory,
        layoutLimbRust_eq, List.map_cons, List.map_nil, toSpec_constantRust, toSpec_prodRust,
        keccakCellsRust]
      simp
    · simp only [keccakCellRust, keccakCellLanesRust_getD _ hcell, FlushesRust.toSpec_memoryIf,
        layoutLimbRust_eq, List.map_cons, List.map_nil, toSpec_constantRust, toSpec_prodRust,
        keccakCellsRust]
      simp

/-! ## The tables -/

/-- `Table`: its opcode, the row a padding row holds, its flushes. -/
structure TableRust where
  opcode : ℕ
  padding : List E
  flushes : FlushesRust

/-- `Table::width`: `TABLE_WIDTHS[opcode]`. -/
def TableRust.width (t : TableRust) : ℕ := tableWidthsRust.getD t.opcode 0

/-- `Table::count_columns`: `COUNT_COLUMNS[opcode]`. -/
def TableRust.countColumns (t : TableRust) : List ℕ := countColumnsRust.getD t.opcode []

/-- `Table::n_constraints`: `N_CONSTRAINTS[opcode]`. -/
def TableRust.nConstraints (t : TableRust) : ℕ := nConstraintsRust.getD t.opcode 0

/-- `Table::constraints`: JUMP's, and none elsewhere. -/
def TableRust.constraints (t : TableRust) (columns : List E) : List E :=
  if t.opcode = opJumpRust then jumpConstraintsRust columns else []

/-- `keccak_f` on a state of twenty-five words: the statement's permutation (`Statement/Fast`'s
`roundLanes` is the shape of its machine code). -/
def keccakFRust (state : List (BitVec 64)) : List (BitVec 64) :=
  ((keccakF1600 (Vector.ofFn fun i : Fin 25 ↦ UInt64.ofBitVec (state.getD i 0))).toList).map
    UInt64.toBitVec

/-- `tables()`: zero padding rows, but for KECCAK's output lanes, the lanes of `keccak_f` of the
zero state (`iter_mut().zip(output)`, as many as the shorter of the two). -/
def tablesRust : List TableRust :=
  let table := fun (opcode : ℕ) (flushes : FlushesRust) ↦
    (⟨opcode, List.replicate (tableWidthsRust.getD opcode 0) 0, flushes⟩ : TableRust)
  let keccak := table opKeccakRust flushesKeccakRust
  let output := keccakFRust (List.replicate stateLanesRust 0#64)
  let padding := (List.range (min (keccak.padding.length - keccakOutRust) output.length)).foldl
    (fun padding l ↦ padding.set (keccakOutRust + l) (eNew (output.getD l 0))) keccak.padding
  let keccak := { keccak with padding := padding }
  [table opXorRust (flushesArithRust opXorRust false), table opMulRust (flushesArithRust opMulRust true),
    table opSetRust flushesSetRust, table opDerefRust flushesDerefRust,
    table opJumpRust flushesJumpRust, keccak]

theorem tablesRust_opcode : tablesRust.map TableRust.opcode = tables.map Table.opcode := by
  decide +kernel

theorem tablesRust_width :
    tablesRust.map (fun t ↦ (t.opcode, t.width)) = tables.map (fun t ↦ (t.opcode, t.width)) := by
  decide +kernel

theorem tablesRust_counts :
    tablesRust.map (fun t ↦ (t.opcode, t.countColumns)) =
      tables.map (fun t ↦ (t.opcode, t.countColumns)) := by
  decide +kernel

theorem tablesRust_nConstraints :
    tablesRust.map TableRust.nConstraints = tables.map Table.nConstraints := by
  simp only [tablesRust, tables, List.map_cons, List.map_nil, TableRust.nConstraints,
    Table.nConstraints, jumpConstraints, List.length_cons, List.length_nil]
  rfl

theorem tablesRust_flushes :
    tablesRust.map (fun t ↦ t.flushes.toSpec) = tables.map Table.flushes := by
  simp only [tablesRust, tables, List.map_cons, List.map_nil, flushesArithRust_eq, flushesSetRust_eq,
    flushesDerefRust_eq, flushesJumpRust_eq, flushesKeccakRust_eq]
  rfl

theorem tablesRust_constraints :
    ∀ i < nTablesRust, ∀ columns : List E,
      (tablesRust.getD i ⟨0, [], {}⟩).constraints columns = (tables.getD i default).constraints columns := by
  intro i hi columns
  simp only [nTablesRust] at hi
  interval_cases i <;> simp [tablesRust, tables, TableRust.constraints, jumpConstraintsRust_eq,
    opJumpRust, opXorRust, opMulRust, opSetRust, opDerefRust, opKeccakRust]

theorem foldl_set_range (o : ℕ) (v : ℕ → E) (P : List E) :
    ∀ n, o + n ≤ P.length →
      (List.range n).foldl (fun p l ↦ p.set (o + l) (v l)) P =
        (List.range P.length).map fun i ↦ if o ≤ i ∧ i < o + n then v (i - o) else P.getD i 0
  | 0, _ => by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    have hi : i < P.length := by simpa using h1
    simp only [List.range_zero, List.foldl_nil, List.getElem_map, List.getElem_range,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    split_ifs <;> first | omega | rfl
  | n + 1, h => by
    rw [List.range_succ, List.foldl_append, foldl_set_range o v P n (by omega)]
    simp only [List.foldl_cons, List.foldl_nil]
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.getElem_set, List.getElem_map, List.getElem_range]
    split_ifs <;> first | omega | (subst_vars; simp)

theorem keccakFRust_zero : keccakFRust (List.replicate 25 0#64) =
    (keccakF1600 (Vector.replicate 25 0)).toList.map UInt64.toBitVec := by
  have : (Vector.ofFn fun i : Fin 25 ↦ UInt64.ofBitVec ((List.replicate 25 0#64).getD i 0)) =
      Vector.replicate 25 0 := by
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_ofFn, Vector.getElem_replicate, List.getD_eq_getElem?_getD,
      List.getElem?_replicate, hi, ite_true, Option.getD_some]
    rfl
  rw [keccakFRust, this]

theorem Table.padding_of_ne (t : Table) (h : t.opcode ≠ opKeccak) :
    t.padding = List.replicate t.width 0 := by
  simp [Table.padding, h, Table.width]

theorem lane_toList (out : KeccakState) {j : ℕ} (hj : j < 25) :
    (out.toList.map UInt64.toBitVec).getD j 0 = (Keccak.lane out j).toBitVec := by
  simp [Keccak.lane, List.getD_eq_getElem?_getD, Array.getD, hj]

theorem eNew_eq (x : BitVec 64) : eNew x = eOfNat x.toNat := by
  simp only [eNew, eOfNat, K.ofBits, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem tablesRust_padding : tablesRust.map TableRust.padding = tables.map Table.padding := by
  simp only [tablesRust, tables, List.map_cons, List.map_nil, stateLanesRust, keccakFRust_zero]
  refine List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_,
    List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, rfl⟩⟩⟩⟩⟩⟩
  iterate 5 · rw [Table.padding_of_ne _ (by decide)]; rfl
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, h15, -⟩ := keccak_names
  have hw : tableWidthsRust.getD opKeccakRust 0 = 92 := by decide +kernel
  have hk : keccakColumns.length = 92 := by decide +kernel
  have ho : keccakOutRust = 40 := rfl
  simp only [Table.padding, Table.width, hw, hk, h15, ho, List.length_replicate, List.length_map,
    Vector.length_toList]
  generalize keccakF1600 (Vector.replicate 25 0) = out
  rw [show min (92 - 40) 25 = 25 from rfl, foldl_set_range 40 _ _ 25 (by simp),
    List.length_replicate]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  by_cases hc : 40 ≤ i ∧ i < 40 + 25
  · simp only [hc, and_self, ite_true, lane_toList out (show i - 40 < 25 by omega), eNew_eq]
    rfl
  · simp only [hc, and_false, ite_false, List.getD_eq_getElem?_getD, List.getElem?_replicate]
    simp [hi]

/-! ## `q_keccak`'s slots -/

/-- `ROUNDS`, `KECCAK_DEPTH`, `KECCAK_MIN_STEPS_LOG`. -/
def roundsRust : ℕ := 24
def keccakDepthRust : ℕ := 12
def keccakMinStepsLogRust : ℕ := 9

/-- `KeccakShape::slot_bits`: `log2_ceil(STATE_LANES * segments())`, `segments() = ROUNDS / depth`. -/
def slotBitsRust (depth : ℕ) : ℕ :=
  log2CeilRust (BitVec.ofNat 64 (stateLanesRust * (roundsRust / depth)))

/-- `QKECCAK_SLOTS`, `QKECCAK_SPARE`. -/
def qkeccakSlotsRust : ℕ := stateLanesRust * (roundsRust / keccakDepthRust)
def qkeccakSpareRust : ℕ := 2 ^ log2CeilRust (BitVec.ofNat 64 qkeccakSlotsRust) - qkeccakSlotsRust

/-- `spare_local(k)`. -/
def spareLocalRust (k : ℕ) : ℕ := if k < keccakInRust then k else keccakCntRust + (k - keccakInRust)

/-- `qkeccak_slot(column)`: `checked_sub` of the KECCAK base, then a spare slot's column (the
first `k` with `spare_local(k) == local`), then an input lane. -/
def qkeccakSlotRust (column : ℕ) : Option ℕ :=
  let base := globalColumnBasesRust.getD opKeccakRust 0
  if column < base then none
  else
    let l := column - base
    match (List.range qkeccakSpareRust).find? (fun k ↦ spareLocalRust k == l) with
    | some k => some (qkeccakSlotsRust + k)
    | none => if keccakInRust ≤ l ∧ l < keccakOutRust then some (l - keccakInRust) else none

/-- What a slot is: the columns `73 ..` of KECCAK, its first fourteen at slots `50 ..`, its input
lanes (local `15 .. 40`) at slots `0 .. 25`. -/
def slotOf (c : ℕ) : Option ℕ :=
  if c < 73 then none
  else if c - 73 < 14 then some (50 + (c - 73))
  else if 15 ≤ c - 73 ∧ c - 73 < 40 then some (c - 73 - 15)
  else none

theorem qkeccakSlotRust_spec (c : ℕ) : qkeccakSlotRust c = slotOf c := by
  have hb : globalColumnBasesRust.getD opKeccakRust 0 = 73 := by decide +kernel
  have hs : qkeccakSpareRust = 14 := by decide +kernel
  unfold qkeccakSlotRust slotOf
  simp only [hb, hs]
  by_cases h : c < 73
  · simp [h]
  simp only [h, ite_false]
  generalize c - 73 = l
  by_cases hl : l < 14
  · have : (List.range 14).find? (fun k ↦ spareLocalRust k == l) = some l := by
      interval_cases l <;> decide
    simp only [this, hl, ite_true]
    rfl
  · have : (List.range 14).find? (fun k ↦ spareLocalRust k == l) = none := by
      rw [List.find?_eq_none]
      intro k hk
      rw [List.mem_range] at hk
      have hk' : k < keccakInRust := by simp only [keccakInRust, KeccakCol.free]; omega
      have : spareLocalRust k = k := by simp only [spareLocalRust, hk', ite_true]
      simp only [this, beq_iff_eq]
      omega
    simp only [this, hl, ite_false, keccakInRust, keccakOutRust, KeccakCol.free, stateLanesRust]
    rfl

theorem keccakSlot_spec (c : ℕ) : keccakSlot c = slotOf c := by
  have hb : globalColumnBases.getD opKeccak 0 = 73 := by decide +kernel
  have hc : keccakCommitted.take qkeccakSpare = List.range 14 := by decide +kernel
  have hq : qkeccakSlots = 50 := by decide +kernel
  have hi : keccakIn = 15 := by decide +kernel
  unfold keccakSlot keccakSlotOf slotOf
  simp only [hb, hc, hq, hi]
  by_cases h : c < 73
  · simp [h]
  simp only [h, ite_false, show 73 ≤ c by omega, ite_true]
  generalize c - 73 = l
  by_cases hl : l < 14
  · have : (List.range 14).idxOf? l = some l := by interval_cases l <;> decide
    simp only [this, hl, ite_true, Option.map_some]
    rw [ite_eq_right (by omega)]
  · have : (List.range 14).idxOf? l = none := by
      rw [List.idxOf?_eq_none_iff, List.mem_range]
      omega
    simp only [this, hl, ite_false, Option.map_none]

theorem qkeccakSlotRust_eq (c : ℕ) : qkeccakSlotRust c = keccakSlot c := by
  rw [qkeccakSlotRust_spec, keccakSlot_spec]

theorem slotOf_lt {c s : ℕ} (h : slotOf c = some s) : s < 64 := by
  unfold slotOf at h
  split_ifs at h <;> simp at h <;> omega

theorem mem_keccakOutputColumns (c : ℕ) : c ∈ keccakOutputColumns ↔ 113 ≤ c ∧ c < 138 := by
  have hb : globalColumnBases.getD opKeccak 0 = 73 := by decide +kernel
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, h15, -⟩ := keccak_names
  simp only [keccakOutputColumns, hb, h15, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨a, ha, rfl⟩
    simp only [keccakOutRust, keccakInRust, KeccakCol.free, stateLanesRust]
    omega
  · intro h
    refine ⟨c - 113, by omega, ?_⟩
    simp only [keccakOutRust, keccakInRust, KeccakCol.free, stateLanesRust]
    omega

/-! ## `build_layout` -/

/-- `MAX_TABLE_LOG`, `MIN_STACKED_LOG`, `BUS_BITS`. -/
def maxTableLogRust : ℕ := 32
def minStackedLogRust : ℕ := 15
def busBitsRust : ℕ := 4

/-- `TABLE_LOG_FLOORS`. -/
def tableLogFloorsRust : List ℕ := [0, 0, 0, 0, 0, keccakMinStepsLogRust]

/-- `BusBlock`. -/
structure BusBlockRust where
  logRows : ℕ
  rows : BitVec 64
  coordinates : List FormRust
  owner : ℕ

/-- The statement's block. -/
def BusBlockRust.toSpec (b : BusBlockRust) : BusBlock :=
  ⟨b.logRows, b.rows.toNat, b.coordinates.map FormRust.toSpec, b.owner⟩

/-- `table_log_heights`: `log2_ceil(rows).max(floor)` over `table_rows` zipped with the floors. -/
def tableLogHeightsRust (tableRows : List (BitVec 64)) : List ℕ :=
  (tableRows.zip tableLogFloorsRust).map fun rf ↦ max (log2CeilRust rf.1) rf.2

/-- The loop over the tables zipped with their heights and rows: each table's blocks pushed onto
`push`, `pull` and `count`. -/
def busBlocksRust (tables : List TableRust) (heights : List ℕ) (tableRows : List (BitVec 64)) :
    List BusBlockRust × List BusBlockRust × List BusBlockRust :=
  ((tables.zip heights).zip tableRows).foldl (fun acc x ↦
    let block := fun coordinates ↦ (⟨x.1.2, x.2, coordinates, x.1.1.opcode⟩ : BusBlockRust)
    (acc.1 ++ x.1.1.flushes.push.map block, acc.2.1 ++ x.1.1.flushes.pull.map block,
      acc.2.2 ++ x.1.1.countColumns.map fun l ↦ block [colRust l 0])) ([], [], [])

/-- `kappas`: the framework columns', q_keccak's, then each table's width at its height. -/
def kappasRust (tables : List TableRust) (logMemory logBytecode qkeccakKappa : ℕ)
    (heights : List ℕ) : List ℕ :=
  tables.foldl (fun kappas t ↦ kappas ++ List.replicate t.width (heights.getD t.opcode 0))
    [logMemory, logMemory, logMemory, logMemory, logBytecode, qkeccakKappa]

/-- `outputs`, the output lanes' global columns, as a range. -/
def outputsRust : ℕ × ℕ :=
  let base := globalColumnBasesRust.getD opKeccakRust 0
  (base + keccakOutRust, base + keccakOutRust + stateLanesRust)

/-- The columns that get a block, stacked by `stack_offsets`; `offsets`, `stack_log`, `qkeccak`
and `placements`. -/
def placementsRust (kappas : List ℕ) (qkeccakKappa : ℕ) :
    List (Option PlacementRust) × PlacementRust × ℕ :=
  let isOutput := fun column ↦ decide (outputsRust.1 ≤ column ∧ column < outputsRust.2)
  let blocks := (List.range kappas.length).filter fun column ↦
    (qkeccakSlotRust column).isNone && !isOutput column
  let blockKappas := blocks.map fun column ↦ kappas.getD column 0
  let stacked := stackOffsetsRust blockKappas
  let offsets := (blocks.zip stacked.1).foldl (fun offsets co ↦ offsets.set co.1 co.2)
    (List.replicate kappas.length 0#64)
  let stackLog := max minStackedLogRust stacked.2
  let qkeccak : PlacementRust := ⟨qkeccakKappa, offsets.getD qkeccakRust 0⟩
  let placements := kappas.zipIdx.map fun kc ↦
    match qkeccakSlotRust kc.2 with
    | some slot =>
      some (⟨kc.1, qkeccak.index + (BitVec.ofNat 64 slot <<< (kc.1 % 64))⟩ : PlacementRust)
    | none => if isOutput kc.2 then none else some ⟨kc.1, offsets.getD kc.2 0⟩
  (placements, qkeccak, stackLog)

/-- `Layout`, but for the bytecode it borrows (`build_layout` reads only its length). -/
structure LayoutRust where
  logMemory : ℕ
  logBytecode : ℕ
  tables : List TableRust
  push : List BusBlockRust
  pull : List BusBlockRust
  count : List BusBlockRust
  placements : List (Option PlacementRust)
  qkeccak : PlacementRust
  stackLog : ℕ
  tableLogHeights : List ℕ
  /-- `keccak.log_steps`; its `depth` is `KECCAK_DEPTH`. -/
  keccakLogSteps : ℕ

/-- The statement's layout, over the bytecode. -/
def LayoutRust.toSpec (l : LayoutRust) (bytecode : List K) : Layout :=
  ⟨l.logMemory, l.logBytecode, bytecode, l.push.map BusBlockRust.toSpec,
    l.pull.map BusBlockRust.toSpec, l.count.map BusBlockRust.toSpec,
    l.placements.map (Option.map PlacementRust.toSpec), l.stackLog, l.tableLogHeights⟩

/-- `build_layout(bytecode, log_memory, table_rows)`, `bytecodeLen` being `bytecode.len() as u64`. -/
def buildLayoutRust (bytecodeLen logMemory : BitVec 64) (tableRows : List (BitVec 64)) :
    Option LayoutRust :=
  match log2StrictRust bytecodeLen with
  | none => none
  | some logBytecode =>
    if (16#64 ≤ logMemory ∧ logMemory ≤ 32#64) ∧
        tableRows.all (fun rows ↦ rows ≤ 1#64 <<< maxTableLogRust) ∧
        (busBitsRust ≤ logBytecode ∧ logBytecode ≤ 32 + busBitsRust) then
      let logBytecode := logBytecode - busBitsRust
      let logMemory := logMemory.toNat
      let heights := tableLogHeightsRust tableRows
      let tables := tablesRust
      let blocks := busBlocksRust tables heights tableRows
      let keccakLogSteps := heights.getD opKeccakRust 0
      let qkeccakKappa := keccakLogSteps + slotBitsRust keccakDepthRust
      let kappas := kappasRust tables logMemory logBytecode qkeccakKappa heights
      let placed := placementsRust kappas qkeccakKappa
      some ⟨logMemory, logBytecode, tables, blocks.1, blocks.2.1, blocks.2.2, placed.1, placed.2.1,
        placed.2.2, heights, keccakLogSteps⟩
    else none

/-! ### Lists -/

theorem map_pair {α α' β γ : Type} {l : List α} {l' : List α'} {f : α → β} {f' : α' → β}
    {g : α → γ} {g' : α' → γ} (h1 : l.map f = l'.map f') (h2 : l.map g = l'.map g') :
    l.map (fun x ↦ (f x, g x)) = l'.map (fun x ↦ (f' x, g' x)) := by
  induction l generalizing l' with
  | nil => cases l' with
    | nil => rfl
    | cons _ _ => simp at h1
  | cons a l ih => cases l' with
    | nil => simp at h1
    | cons a' l' =>
      simp only [List.map_cons, List.cons.injEq] at h1 h2 ⊢
      exact ⟨by rw [h1.1, h2.1], ih h1.2 h2.2⟩

theorem flatMap_of_map_eq {α α' β γ : Type} {l : List α} {l' : List α'} {f : α → β}
    {f' : α' → β} (G : β → List γ) (h : l.map f = l'.map f') :
    l.flatMap (fun x ↦ G (f x)) = l'.flatMap (fun x ↦ G (f' x)) := by
  induction l generalizing l' with
  | nil => cases l' with
    | nil => rfl
    | cons _ _ => simp at h
  | cons a l ih => cases l' with
    | nil => simp at h
    | cons a' l' =>
      simp only [List.map_cons, List.cons.injEq] at h
      simp only [List.flatMap_cons, h.1, ih h.2]

theorem foldl_append_eq_flatMap {α β : Type} (l : List α) (f : α → List β) (init : List β) :
    l.foldl (fun acc a ↦ acc ++ f a) init = init ++ l.flatMap f := by
  induction l generalizing init with
  | nil => simp
  | cons a l ih => simp [ih, List.append_assoc]

theorem foldl_append3 {α β : Type} (l : List α) (f g h : α → List β) (P Q R : List β) :
    l.foldl (fun (acc : List β × List β × List β) a ↦
        (acc.1 ++ f a, acc.2.1 ++ g a, acc.2.2 ++ h a)) (P, Q, R) =
      (P ++ l.flatMap f, Q ++ l.flatMap g, R ++ l.flatMap h) := by
  induction l generalizing P Q R with
  | nil => simp
  | cons a l ih => simp [ih, List.append_assoc]

theorem flatMap_zip_transfer {β κ : Type} (key : TableRust → κ) (key' : Table → κ) :
    ∀ (ts : List TableRust) (ss : List Table) (H : List ℕ) (R : List (BitVec 64))
      (F : (TableRust × ℕ) × BitVec 64 → List β) (G : Table × ℕ × ℕ → List β),
      ts.map key = ss.map key' →
      (∀ t s h r, key t = key' s → F ((t, h), r) = G (s, h, r.toNat)) →
      ((ts.zip H).zip R).flatMap F = (ss.zip (H.zip (R.map BitVec.toNat))).flatMap G
  | [], [], _, _, _, _, _, _ => by simp
  | [], _ :: _, _, _, _, _, hk, _ => by simp at hk
  | _ :: _, [], _, _, _, _, hk, _ => by simp at hk
  | t :: ts, s :: ss, [], _, _, _, _, _ => by simp
  | t :: ts, s :: ss, h :: H, [], _, _, _, _ => by simp
  | t :: ts, s :: ss, h :: H, r :: R, F, G, hk, hFG => by
    simp only [List.map_cons, List.cons.injEq] at hk
    simp only [List.zip_cons_cons, List.map_cons, List.flatMap_cons]
    rw [hFG t s h r hk.1, flatMap_zip_transfer key key' ts ss H R F G hk.2 hFG]

theorem log2Ceil_le {n k : ℕ} (h : n ≤ 2 ^ k) : log2Ceil n ≤ k := by
  unfold log2Ceil bitLength
  split
  · omega
  · next h0 =>
    have := (Nat.log2_lt h0).mpr (show n - 1 < 2 ^ k by have := Nat.one_le_two_pow (n := k); omega)
    omega

theorem getD_map_toNat (L : List (BitVec 64)) (i : ℕ) :
    (L.map BitVec.toNat).getD i 0 = (L.getD i 0).toNat := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases L[i]? <;> rfl

/-- After writing `v[k]` at `l[k]` for each `k`, a position holds what was last written there. -/
theorem foldl_set_zip_getD {α : Type} (d : α) :
    ∀ (l : List ℕ) (v o : List α), l.Nodup → v.length = l.length → (∀ c ∈ l, c < o.length) →
      ∀ c, ((l.zip v).foldl (fun o cv ↦ o.set cv.1 cv.2) o).getD c d =
        if c ∈ l then v.getD (l.idxOf c) d else o.getD c d
  | [], v, o, _, _, _, c => by simp
  | a :: l, [], o, _, hv, _, c => by simp at hv
  | a :: l, x :: v, o, hn, hv, hl, c => by
    have ha := (List.nodup_cons.mp hn).1
    simp only [List.zip_cons_cons, List.foldl_cons]
    rw [foldl_set_zip_getD d l v (o.set a x) (List.nodup_cons.mp hn).2 (by simpa using hv)
      (by intro c hc; rw [List.length_set]; exact hl c (by simp [hc])) c]
    have hao : a < o.length := hl a (by simp)
    by_cases hc : c ∈ l
    · have hne : a ≠ c := fun e ↦ ha (e ▸ hc)
      simp [hc, hne]
    · by_cases hca : a = c
      · subst hca
        simp [hc, List.getD_eq_getElem?_getD, hao]
      · have hca' : c ≠ a := Ne.symm hca
        simp [hc, hca, hca', List.getD_eq_getElem?_getD]

theorem stackFold_le (size : ℕ → ℕ) : ∀ (Q o : List ℕ) (t : ℕ), (∀ x ∈ o, x ≤ t) →
    (∀ x ∈ (Q.foldl (fun (acc : List ℕ × ℕ) i ↦ (acc.1.set i acc.2, acc.2 + 2 ^ size i))
        (o, t)).1, x ≤ t + (Q.map fun i ↦ 2 ^ size i).sum) ∧
      (Q.foldl (fun (acc : List ℕ × ℕ) i ↦ (acc.1.set i acc.2, acc.2 + 2 ^ size i)) (o, t)).2 =
        t + (Q.map fun i ↦ 2 ^ size i).sum
  | [], o, t, h => by simpa using h
  | i :: Q, o, t, h => by
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    have := stackFold_le size Q (o.set i t) (t + 2 ^ size i) (by
      intro x hx
      rcases List.mem_or_eq_of_mem_set hx with hx | hx
      · exact Nat.le_add_right_of_le (h x hx)
      · exact hx ▸ Nat.le_add_right _ _)
    refine ⟨fun x hx ↦ ?_, by rw [this.2]; ring⟩
    simpa [Nat.add_assoc] using this.1 x hx

theorem stackOffsets_le (sizes : List ℕ) :
    ∀ x ∈ (stackOffsets sizes).1, x ≤ (sizes.map (2 ^ ·)).sum := by
  intro x hx
  have h := (stackFold_le (fun i ↦ sizes.getD i 0)
    ((List.range sizes.length).mergeSort fun i j ↦
      decide (sizes.getD j 0 < sizes.getD i 0) ||
        (decide (sizes.getD i 0 = sizes.getD j 0) && decide (i ≤ j)))
    (List.replicate sizes.length 0) 0 (by simp)).1 x hx
  rw [((List.mergeSort_perm _ _).map _).sum_eq, sum_map_range_getD] at h
  simpa using h

theorem stackOffsetsRust_length (sizes : List ℕ) :
    (stackOffsetsRust sizes).1.length = sizes.length := by
  have h : ∀ (Q : List ℕ) (st : List (BitVec 64) × BitVec 64), (Q.foldl (fun st i ↦
      (st.1.set i st.2, st.2 + 1#64 <<< (sizes.getD i 0 % 64))) st).1.length = st.1.length := by
    intro Q
    induction Q with
    | nil => intro st; rfl
    | cons i Q ih => intro st; rw [List.foldl_cons, ih]; simp
  simp only [stackOffsetsRust, stackPasses_eq, h, List.length_replicate]

theorem sum_pow_le (l : List ℕ) (b : ℕ) (h : ∀ k ∈ l, k ≤ b) :
    (l.map (2 ^ ·)).sum ≤ l.length * 2 ^ b := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (h a (by simp))
    have h2 := ih (fun k hk ↦ h k (by simp [hk]))
    rw [Nat.succ_mul]
    omega

/-! ### The pieces of `build_layout` -/

theorem tableLogHeightsRust_eq (tableRows : List (BitVec 64)) :
    tableLogHeightsRust tableRows = List.zipWith (fun rows floor ↦ max (log2Ceil rows) floor)
      (tableRows.map BitVec.toNat) tableLogFloors := by
  unfold tableLogHeightsRust
  rw [show tableLogFloorsRust = tableLogFloors from rfl]
  generalize tableLogFloors = fl
  induction tableRows generalizing fl with
  | nil => simp
  | cons r rs ih => cases fl with
    | nil => simp
    | cons f fs =>
      simp only [List.zip_cons_cons, List.map_cons, List.zipWith_cons_cons]
      rw [ih, log2CeilRust_eq]

theorem tablesRust_key :
    tablesRust.map (fun t ↦ (t.flushes.toSpec, t.opcode, t.countColumns)) =
      tables.map (fun t ↦ (t.flushes, t.opcode, t.countColumns)) :=
  map_pair tablesRust_flushes tablesRust_counts

theorem busBlocksRust_eq (heights : List ℕ) (tableRows : List (BitVec 64)) :
    (busBlocksRust tablesRust heights tableRows).1.map BusBlockRust.toSpec =
        (busBlocks heights (tableRows.map BitVec.toNat)).1 ∧
      (busBlocksRust tablesRust heights tableRows).2.1.map BusBlockRust.toSpec =
        (busBlocks heights (tableRows.map BitVec.toNat)).2.1 ∧
      (busBlocksRust tablesRust heights tableRows).2.2.map BusBlockRust.toSpec =
        (busBlocks heights (tableRows.map BitVec.toNat)).2.2 := by
  unfold busBlocksRust busBlocks
  rw [foldl_append3]
  simp only [List.nil_append, List.map_flatMap]
  refine ⟨?_, ?_, ?_⟩ <;>
    refine flatMap_zip_transfer _ _ _ _ _ _ _ _ tablesRust_key ?_ <;>
    intro t s h r hk <;>
    simp only [Prod.mk.injEq] at hk <;>
    obtain ⟨hf, ho, hc⟩ := hk
  · rw [← ho, ← hf]
    simp only [FlushesRust.toSpec, List.map_map]
    rfl
  · rw [← ho, ← hf]
    simp only [FlushesRust.toSpec, List.map_map]
    rfl
  · rw [← ho, ← hc]
    simp only [List.map_map]
    rfl

theorem kappasRust_eq (logMemory logBytecode : ℕ) (heights : List ℕ) :
    kappasRust tablesRust logMemory logBytecode
        (heights.getD opKeccakRust 0 + slotBitsRust keccakDepthRust) heights =
      columnKappas logMemory logBytecode heights := by
  have hs : slotBitsRust keccakDepthRust = qkeccakSlotBits := by decide +kernel
  unfold kappasRust columnKappas
  have h := flatMap_of_map_eq (fun p : ℕ × ℕ ↦ List.replicate p.2 (heights.getD p.1 0))
    tablesRust_width
  simp only at h
  rw [foldl_append_eq_flatMap, hs, h]
  rfl

theorem outputsRust_eq : outputsRust = (113, 138) := by decide +kernel

theorem bitvec_add_shift (a : BitVec 64) (s k : ℕ) (hs : s < 64) (hk : k ≤ 38)
    (ha : a.toNat < 2 ^ 60) :
    (a + (BitVec.ofNat 64 s <<< (k % 64))).toNat = a.toNat + s * 2 ^ k := by
  have hk' : k % 64 = k := Nat.mod_eq_of_lt (by omega)
  have hp : 2 ^ k ≤ 2 ^ 38 := Nat.pow_le_pow_right (by norm_num) hk
  have hsk : s * 2 ^ k < 2 ^ 44 := by
    calc s * 2 ^ k < 64 * 2 ^ 38 := by
          apply Nat.mul_lt_mul_of_lt_of_le hs hp (by positivity)
      _ = 2 ^ 44 := by norm_num
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, hk', BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (show s < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show s * 2 ^ k < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (by omega)]

theorem placementsRust_eq (kappas : List ℕ) (qkeccakKappa : ℕ)
    (hq : kappas.getD qkeccak 0 = qkeccakKappa) (hb : ∀ k ∈ kappas, k ≤ 38)
    (hl : kappas.length ≤ 1024) :
    (placementsRust kappas qkeccakKappa).1.map (Option.map PlacementRust.toSpec) =
        (placementsOf kappas).1 ∧
      (placementsRust kappas qkeccakKappa).2.2 = (placementsOf kappas).2 ∧
      (qkeccak < kappas.length →
        (placementsRust kappas qkeccakKappa).1.getD qkeccak none =
          some (placementsRust kappas qkeccakKappa).2.1) := by
  have hblocks : (List.range kappas.length).filter (fun column ↦
      (qkeccakSlotRust column).isNone && !decide (outputsRust.1 ≤ column ∧ column < outputsRust.2)) =
      (List.range kappas.length).filter fun c ↦
        (keccakSlot c).isNone ∧ c ∉ keccakOutputColumns := by
    apply List.filter_congr
    intro c _
    simp only [qkeccakSlotRust_eq, outputsRust_eq, mem_keccakOutputColumns]
    cases (keccakSlot c).isNone <;> simp only [decide_not, Bool.true_and, Bool.false_and,
      decide_false, true_and, false_and, Bool.false_eq_true]
  unfold placementsRust placementsOf
  simp only [hblocks]
  generalize hB : (List.range kappas.length).filter (fun c ↦
    (keccakSlot c).isNone ∧ c ∉ keccakOutputColumns) = blocks
  have hnd : blocks.Nodup := hB ▸ List.nodup_range.filter _
  have hlt : ∀ c ∈ blocks, c < kappas.length := by
    intro c hc
    rw [← hB, List.mem_filter, List.mem_range] at hc
    exact hc.1
  have hbk : ∀ k ∈ blocks.map (fun c ↦ kappas.getD c 0), k ≤ 38 := by
    intro k hk
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hk
    rw [List.getD_eq_getElem _ _ (hlt c hc)]
    exact hb _ (List.getElem_mem _)
  have hblen : blocks.length ≤ 1024 :=
    (hB ▸ List.length_filter_le _ _).trans (by simpa using hl)
  have hsum : ((blocks.map fun c ↦ kappas.getD c 0).map (2 ^ ·)).sum ≤ 1024 * 2 ^ 38 :=
    (sum_pow_le _ 38 hbk).trans (Nat.mul_le_mul_right _ (by simpa using hblen))
  obtain ⟨hoff, htot⟩ := stackOffsetsRust_eq (blocks.map fun c ↦ kappas.getD c 0)
    (by have : 1024 * 2 ^ 38 < 2 ^ 64 := by norm_num
        omega)
  generalize hR : stackOffsetsRust (blocks.map fun c ↦ kappas.getD c 0) = R at hoff htot
  generalize hS : stackOffsets (blocks.map fun c ↦ kappas.getD c 0) = S at hoff htot
  have hRlen : R.1.length = blocks.length := by
    rw [← hR, stackOffsetsRust_length, List.length_map]
  have hSle : ∀ x ∈ S.1, x ≤ 1024 * 2 ^ 38 := by
    intro x hx
    rw [← hS] at hx
    exact (stackOffsets_le _ x hx).trans hsum
  obtain ⟨R1, R2⟩ := R
  obtain ⟨S1, S2⟩ := S
  simp only at hoff htot hRlen ⊢
  -- the offsets array, at every column
  have hoffs : ∀ c, (((blocks.zip R1).foldl (fun offsets co ↦ offsets.set co.1 co.2)
      (List.replicate kappas.length 0#64)).getD c 0).toNat = S1.getD (blocks.idxOf c) 0 := by
    intro c
    rw [foldl_set_zip_getD (0 : BitVec 64) blocks R1 _ hnd hRlen (by simpa using hlt), ← hoff,
      getD_map_toNat]
    split
    · rfl
    · next hc =>
      rw [List.getD_eq_default R1 _ (by rw [List.idxOf_eq_length hc, hRlen])]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
      split <;> rfl
  generalize hO : (blocks.zip R1).foldl (fun offsets co ↦ offsets.set co.1 co.2)
    (List.replicate kappas.length 0#64) = O at hoffs
  have hO5 : (O.getD qkeccakRust 0).toNat < 2 ^ 60 := by
    rw [show qkeccakRust = qkeccak from rfl, hoffs]
    have : S1.getD (blocks.idxOf qkeccak) 0 ≤ 1024 * 2 ^ 38 := by
      rw [List.getD_eq_getElem?_getD]
      cases h : S1[blocks.idxOf qkeccak]? with
      | none => simp
      | some x => exact hSle x (List.mem_of_getElem? h)
    have : 1024 * 2 ^ 38 < 2 ^ 60 := by norm_num
    omega
  refine ⟨?_, by rw [htot]; rfl, ?_⟩
  · rw [List.map_map]
    apply List.map_congr_left
    rintro ⟨kappa, column⟩ hkc
    have hk : kappa ≤ 38 := hb kappa (List.mem_zipIdx' hkc |>.2 ▸ List.getElem_mem _)
    simp only [Function.comp_apply, qkeccakSlotRust_eq]
    cases hs : keccakSlot column with
    | some slot =>
      have hs64 : slot < 64 := slotOf_lt (keccakSlot_spec column ▸ hs)
      simp only [Option.map_some, PlacementRust.toSpec, Option.some.injEq, Placement.mk.injEq,
        true_and]
      rw [bitvec_add_shift _ _ _ hs64 hk hO5, show qkeccakRust = qkeccak from rfl, hoffs]
    | none =>
      have hiff := mem_keccakOutputColumns column
      by_cases ho : column ∈ keccakOutputColumns
      · have h' : 113 ≤ column ∧ column < 138 := hiff.mp ho
        simp [outputsRust_eq, ho, h']
      · have h' : ¬ (113 ≤ column ∧ column < 138) := fun h ↦ ho (hiff.mpr h)
        simp only [outputsRust_eq, ho, h', decide_false, Bool.false_eq_true, ite_false,
          Option.map_some, PlacementRust.toSpec, hoffs]
  · intro h5
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_zipIdx,
      List.getElem?_eq_getElem h5]
    have h5s : qkeccakSlotRust qkeccak = none := by decide +kernel
    simp only [Option.map_some, Nat.zero_add, h5s, outputsRust_eq, Option.getD_some]
    rw [← List.getD_eq_getElem _ 0 h5, hq]
    rfl

theorem tableLogHeightsRust_le (tableRows : List (BitVec 64))
    (h : ∀ r ∈ tableRows, r.toNat ≤ 2 ^ 32) : ∀ x ∈ tableLogHeightsRust tableRows, x ≤ 32 := by
  intro x hx
  unfold tableLogHeightsRust at hx
  obtain ⟨⟨r, f⟩, hrf, rfl⟩ := List.mem_map.mp hx
  have hr := h r (List.of_mem_zip hrf).1
  have hf : f ≤ 9 := by
    have := (List.of_mem_zip hrf).2
    simp only [tableLogFloorsRust, keccakMinStepsLogRust, List.mem_cons, List.not_mem_nil,
      or_false] at this
    omega
  rw [log2CeilRust_eq]
  exact max_le (log2Ceil_le hr) (by omega)

theorem getD_le {l : List ℕ} {b : ℕ} (h : ∀ x ∈ l, x ≤ b) (i : ℕ) : l.getD i 0 ≤ b := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : l[i]? with
  | none => simp
  | some x => exact h x (List.mem_of_getElem? hi)

theorem columnKappas_le (lm lb : ℕ) (H : List ℕ) (hm : lm ≤ 32) (hb : lb ≤ 32)
    (hH : ∀ x ∈ H, x ≤ 32) : ∀ k ∈ columnKappas lm lb H, k ≤ 38 := by
  have hq : qkeccakSlotBits = 6 := by decide +kernel
  intro k hk
  simp only [columnKappas, hq, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatMap, List.mem_replicate] at hk
  have h5 := getD_le hH opKeccak
  rcases hk with (rfl | rfl | rfl | rfl | rfl | rfl) | ⟨t, _, _, rfl⟩
  all_goals first | omega | exact (getD_le hH _).trans (by norm_num)

theorem columnKappas_length (lm lb : ℕ) (H : List ℕ) : (columnKappas lm lb H).length = 165 := by
  simp only [columnKappas, List.length_append, List.length_cons, List.length_nil,
    List.length_flatMap, List.length_replicate]
  decide +kernel

/-- `build_layout` computes the statement's `buildLayout`: `none` exactly where it returns an error,
and the same layout otherwise. The verifier passes `N_TABLES` row counts. -/
theorem buildLayoutRust_eq (bytecode : List K) (logMemory : BitVec 64)
    (tableRows : List (BitVec 64)) (hlen : bytecode.length < 2 ^ 64)
    (hrows : tableRows.length = nTablesRust) :
    (buildLayoutRust (BitVec.ofNat 64 bytecode.length) logMemory tableRows).map
        (·.toSpec bytecode) =
      buildLayout bytecode logMemory.toNat (tableRows.map BitVec.toNat) := by
  have hbb : busBitsRust = busBits := rfl
  unfold buildLayoutRust buildLayout
  rw [log2StrictRust_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen]
  cases log2Strict bytecode.length with
  | none => rfl
  | some L =>
    simp only [hbb]
    have hcond : ((16#64 ≤ logMemory ∧ logMemory ≤ 32#64) ∧
        tableRows.all (fun rows ↦ rows ≤ 1#64 <<< maxTableLogRust) = true ∧
        (busBits ≤ L ∧ L ≤ 32 + busBits)) ↔
        (busBits ≤ L ∧ 16 ≤ logMemory.toNat ∧ logMemory.toNat ≤ 32 ∧
          (tableRows.map BitVec.toNat).all (· ≤ 2 ^ 32) = true ∧ L - busBits ≤ 32 ∧
          (tableRows.map BitVec.toNat).length = tables.length) := by
      have h1 : (1#64 <<< maxTableLogRust) = BitVec.ofNat 64 (2 ^ 32) := by decide +kernel
      have ht : tables.length = nTablesRust := by decide +kernel
      have hr : ∀ r : BitVec 64, r ≤ BitVec.ofNat 64 (2 ^ 32) ↔ r.toNat ≤ 2 ^ 32 := by
        intro r
        rw [BitVec.le_def, BitVec.toNat_ofNat]
        norm_num
      have hall : tableRows.all (fun rows ↦ rows ≤ 1#64 <<< maxTableLogRust) =
          (tableRows.map BitVec.toNat).all (· ≤ 2 ^ 32) := by
        rw [List.all_map]
        exact congrArg _ (funext fun r ↦ by rw [h1]; exact decide_eq_decide.mpr (hr r))
      have h16 : 16#64 ≤ logMemory ↔ 16 ≤ logMemory.toNat := by rw [BitVec.le_def]; rfl
      have h32 : logMemory ≤ 32#64 ↔ logMemory.toNat ≤ 32 := by rw [BitVec.le_def]; rfl
      have h4 : busBits = 4 := rfl
      rw [hall, h16, h32, List.length_map, hrows, ht]
      constructor
      · rintro ⟨⟨a, b⟩, c, d, e⟩
        exact ⟨d, a, b, c, by omega, rfl⟩
      · rintro ⟨a, b, c, d, e, -⟩
        exact ⟨⟨b, c⟩, d, a, by omega⟩
    by_cases hc : busBits ≤ L ∧ 16 ≤ logMemory.toNat ∧ logMemory.toNat ≤ 32 ∧
          (tableRows.map BitVec.toNat).all (· ≤ 2 ^ 32) = true ∧ L - busBits ≤ 32 ∧
          (tableRows.map BitVec.toNat).length = tables.length
    · rw [ite_eq_left (hcond.mpr hc), ite_eq_left hc, Option.map_some]
      obtain ⟨-, -, hm, hall, hlb, -⟩ := hc
      have hrows' : ∀ r ∈ tableRows, r.toNat ≤ 2 ^ 32 := by
        intro r hr
        simpa using List.all_eq_true.mp hall r.toNat (List.mem_map_of_mem hr)
      have hH := tableLogHeightsRust_le tableRows hrows'
      obtain ⟨hpush, hpull, hcount⟩ := busBlocksRust_eq (tableLogHeightsRust tableRows) tableRows
      rw [kappasRust_eq]
      rw [← tableLogHeightsRust_eq]
      have hK := columnKappas_le logMemory.toNat (L - busBits) _ hm hlb hH
      have hKl := columnKappas_length logMemory.toNat (L - busBits) (tableLogHeightsRust tableRows)
      have hq : (columnKappas logMemory.toNat (L - busBits) (tableLogHeightsRust tableRows)).getD
          qkeccak 0 = (tableLogHeightsRust tableRows).getD opKeccakRust 0 +
            slotBitsRust keccakDepthRust := by
        have hs : slotBitsRust keccakDepthRust = qkeccakSlotBits := by decide +kernel
        rw [hs]
        rfl
      obtain ⟨hpl, hsl, -⟩ := placementsRust_eq _ _ hq hK (by omega)
      generalize busBlocks (tableLogHeightsRust tableRows) (tableRows.map BitVec.toNat) = B
        at hpush hpull hcount
      generalize placementsOf (columnKappas logMemory.toNat (L - busBits)
        (tableLogHeightsRust tableRows)) = P at hpl hsl
      obtain ⟨b1, b2, b3⟩ := B
      obtain ⟨p1, p2⟩ := P
      simp only at hpush hpull hcount hpl hsl ⊢
      rw [LayoutRust.toSpec, hpush, hpull, hcount, hpl, hsl]
    · rw [ite_eq_right (fun h ↦ hc (hcond.mp h)), ite_eq_right hc]
      rfl
