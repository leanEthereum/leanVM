module

public import Rv64mc.Model.KeccakGkr

/-!
# `layout.rs` as the Rust computes it

Mirrors of `crates/verifier/src/layout.rs` (`Form`, `Flushes`, the tables, `qkeccak_slot`,
`column_kappas`, `stack`, `build_layout`, `min_execution_stacked_log`), under `Model.Multilinear`'s
conventions: a loop is a `foldl`, a `Vec` a `List`, a `u64` a `BitVec 64`, a shift by a `usize`
masked to six bits. `KeccakShape` is `Model.KeccakGkr`'s, `stack_offsets` `Model.Multilinear`'s. A
mirror fails (`none`) exactly where the Rust returns `Err`; where the Rust panics it may return
anything. `buildLayoutRust_spec` is the equality: `build_layout` fails exactly where `buildLayout`
does, and otherwise returns its layout (`LayoutRust.Rel`).

A form is the statement's `Form`: its terms, kept sorted by monomial as the Rust keeps them
(`Form::add_scaled` inserts at `partition_point`, core's binary search, `partitionPointRust`). The
statement appends a new monomial instead, so the two lists hold the same terms in another order. The
verifier reads a form only through `Form::evaluate` and `Form::add_scaled`, so a mirror's form is
related to the statement's by its value at every row (`Form.evaluate`, the `den` of a list of
forms), whatever index the binary search returns (`evaluate_addTermRust`).

The statement names a table's columns by string (`columnIndexByName`), finds its count columns by
the prefix `cnt` and its constraint count on a zero row; the Rust's index constants are those
(`TableRust.Rel`, `tablesRust_rel`, by `decide`).
-/

namespace Rv64mc.Model

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-! ## `partition_point` -/

/-- `pred` of `l[i]`, `false` out of range (core reads it unchecked, always in range). -/
def predAt {α : Type} (l : List α) (pred : α → Bool) (i : ℕ) : Bool := (l[i]?.map pred).getD false

/-- `binary_search_by`'s loop: while `size > 1`, probe `base + size / 2`, moving `base` there when
the probe is `Less` (`pred` holds). -/
def partitionLoop {α : Type} (l : List α) (pred : α → Bool) (size base : ℕ) : ℕ :=
  if 1 < size then
    partitionLoop l pred (size - size / 2)
      (if predAt l pred (base + size / 2) then base + size / 2 else base)
  else base
termination_by size
decreasing_by omega

/-- `slice::partition_point(pred)`: `binary_search_by(|x| if pred(x) { Less } else { Greater })`,
`Err(i)` read as `i` (core, `slice/mod.rs`): `0` on an empty slice, else the loop's `base` plus one
if `pred` holds there. -/
def partitionPointRust {α : Type} (l : List α) (pred : α → Bool) : ℕ :=
  if l.length = 0 then 0
  else
    let base := partitionLoop l pred l.length 0
    base + if predAt l pred base then 1 else 0

theorem partitionLoop_lt {α : Type} (l : List α) (pred : α → Bool) :
    ∀ size base, 1 ≤ size → base + size ≤ l.length → partitionLoop l pred size base < l.length := by
  intro size
  induction size using Nat.strong_induction_on with
  | _ size ih =>
    intro base h1 h2
    rw [partitionLoop]
    split
    · apply ih _ (by omega) _ (by omega)
      split <;> omega
    · omega

/-- The index is at most the length: `Vec::insert` there never panics. -/
theorem partitionPointRust_le {α : Type} (l : List α) (pred : α → Bool) :
    partitionPointRust l pred ≤ l.length := by
  unfold partitionPointRust
  split
  · omega
  · have := partitionLoop_lt l pred l.length 0 (by omega) (by omega)
    dsimp only
    split <;> omega

/-! ## `Form` -/

/-- A term's value at a row: `monomial.iter().fold(c, |acc, &index| acc * column[index])`. -/
def termValue (column : ℕ → E) (t : List ℕ × E) : E := t.1.foldl (fun acc i ↦ acc * column i) t.2

/-- One term of `Form::add_scaled`: at `partition_point(|(m, _)| m < monomial)`, added into the term
there if it has the monomial, else inserted there. -/
def addTermRust (terms : List (List ℕ × E)) (monomial : List ℕ) (c : E) : List (List ℕ × E) :=
  let idx := partitionPointRust terms fun t ↦ decide (t.1 < monomial)
  match terms[idx]? with
  | some (m, c') =>
    if m = monomial then terms.set idx (m, c' + c) else terms.insertIdx idx (monomial, c)
  | none => terms.insertIdx idx (monomial, c)

/-- `Form::add_scaled(other, weight)`: each of `other`'s terms, times `weight`. -/
def addScaledRust (f other : Form) (weight : E) : Form :=
  ⟨other.terms.foldl (fun terms t ↦ addTermRust terms t.1 (weight * t.2)) f.terms⟩

/-- `Form + Form`: `add_scaled(&other, ONE)`. -/
def addRust (f g : Form) : Form := addScaledRust f g 1

/-- `Form::sum(forms)`: a fold of `+` from the empty form. -/
def formSumRust (forms : List Form) : Form := forms.foldl addRust {}

/-- `Form::evaluate(column)`: `E::sum` of the terms' values, `column[index]` a `getD`. -/
def formEvaluateRust (f : Form) (column : List E) : E :=
  (f.terms.map (termValue (column.getD · 0))).foldl (· + ·) 0

theorem formEvaluateRust_eq (f : Form) (column : List E) :
    formEvaluateRust f column = f.evaluate (column.getD · 0) := rfl

section FormValue

theorem termValue_scale (column : ℕ → E) (m : List ℕ) (c : E) :
    termValue column (m, c) = c * termValue column (m, 1) := by
  unfold termValue
  induction m generalizing c with
  | nil => simp
  | cons i m ih =>
    simp only [List.foldl_cons]
    rw [ih (c * column i), ih (1 * column i)]
    ring

theorem termValue_add (column : ℕ → E) (m : List ℕ) (a b : E) :
    termValue column (m, a + b) = termValue column (m, a) + termValue column (m, b) := by
  rw [termValue_scale, termValue_scale column m a, termValue_scale column m b]
  ring

theorem evaluate_eq_sum (f : Form) (column : ℕ → E) :
    f.evaluate column = (f.terms.map (termValue column)).sum := by
  rw [Form.evaluate, sumE_eq_sum]
  rfl

theorem sum_map_set {α : Type} (g : α → E) (l : List α) (i : ℕ) (a : α) (hi : i < l.length) :
    ((l.set i a).map g).sum = (l.map g).sum - g l[i] + g a := by
  have hi' : i < (l.map g).length := by simpa using hi
  have h2 : (l.map g).sum = ((l.map g).take i).sum + g l[i] + ((l.map g).drop (i + 1)).sum := by
    conv_lhs => rw [← List.take_append_drop i (l.map g), List.drop_eq_getElem_cons hi']
    simp only [List.sum_append, List.sum_cons, List.getElem_map]
    ring
  rw [List.set_eq_take_append_cons_drop, ite_eq_left hi, h2]
  simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons, List.map_take,
    List.map_drop]
  ring

/-- **A term added by the Rust adds its value**, whatever index the binary search returns. -/
theorem evaluate_addTermRust (terms : List (List ℕ × E)) (m : List ℕ) (c : E)
    (column : ℕ → E) :
    (⟨addTermRust terms m c⟩ : Form).evaluate column =
      (⟨terms⟩ : Form).evaluate column + termValue column (m, c) := by
  have hle := partitionPointRust_le terms fun t ↦ decide (t.1 < m)
  have hins : ∀ idx, idx ≤ terms.length →
      (⟨terms.insertIdx idx (m, c)⟩ : Form).evaluate column =
        (⟨terms⟩ : Form).evaluate column + termValue column (m, c) := by
    intro idx hat
    rw [evaluate_eq_sum, evaluate_eq_sum, ((List.perm_insertIdx (m, c) terms hat).map _).sum_eq]
    simp [add_comm]
  unfold addTermRust
  dsimp only
  split
  · rename_i m' c' h
    have hlt : partitionPointRust terms (fun t ↦ decide (t.1 < m)) < terms.length :=
      (List.getElem?_eq_some_iff.mp h).1
    have hget := (List.getElem?_eq_some_iff.mp h).2
    split
    · rename_i hm
      subst hm
      rw [evaluate_eq_sum, evaluate_eq_sum, sum_map_set _ _ _ _ hlt, hget, termValue_add]
      ring
    · exact hins _ hle
  · exact hins _ hle

/-- **`Form::add_scaled` adds `weight` times the value.** -/
theorem evaluate_addScaledRust (f g : Form) (weight : E) (column : ℕ → E) :
    (addScaledRust f g weight).evaluate column =
      f.evaluate column + weight * g.evaluate column := by
  obtain ⟨F⟩ := f
  obtain ⟨G⟩ := g
  simp only [addScaledRust]
  induction G generalizing F with
  | nil => simp [evaluate_eq_sum]
  | cons t G ih =>
    rw [List.foldl_cons, ih, evaluate_addTermRust]
    simp only [evaluate_eq_sum, List.map_cons, List.sum_cons]
    rw [termValue_scale column t.1 (weight * t.2), termValue_scale column t.1 t.2]
    ring

theorem evaluate_addTerm (terms : List (List ℕ × E)) (m : List ℕ) (c : E) (column : ℕ → E) :
    (⟨addTerm terms m c⟩ : Form).evaluate column =
      (⟨terms⟩ : Form).evaluate column + termValue column (m, c) := by
  induction terms with
  | nil => simp [addTerm, evaluate_eq_sum]
  | cons t rest ih =>
    obtain ⟨m', c'⟩ := t
    unfold addTerm
    split
    · rename_i h
      subst h
      simp only [evaluate_eq_sum, List.map_cons, List.sum_cons, termValue_add]
      ring
    · simp only [evaluate_eq_sum, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]
      ring

/-- The statement's `Form.addScaled` adds `weight` times the value. -/
theorem evaluate_addScaled (f g : Form) (weight : E) (column : ℕ → E) :
    (f.addScaled g weight).evaluate column = f.evaluate column + weight * g.evaluate column := by
  obtain ⟨F⟩ := f
  obtain ⟨G⟩ := g
  simp only [Form.addScaled]
  induction G generalizing F with
  | nil => simp [evaluate_eq_sum]
  | cons t G ih =>
    rw [List.foldl_cons, ih, evaluate_addTerm]
    simp only [evaluate_eq_sum, List.map_cons, List.sum_cons]
    rw [termValue_scale column t.1 (weight * t.2), termValue_scale column t.1 t.2]
    ring

theorem den_addScaledRust {f f' g g' : Form} (hf : f.evaluate = f'.evaluate)
    (hg : g.evaluate = g'.evaluate) (weight : E) :
    (addScaledRust f g weight).evaluate = (f'.addScaled g' weight).evaluate := by
  funext column
  rw [evaluate_addScaledRust, evaluate_addScaled, hf, hg]

theorem den_addRust {f f' g g' : Form} (hf : f.evaluate = f'.evaluate)
    (hg : g.evaluate = g'.evaluate) : (addRust f g).evaluate = (f'.add g').evaluate :=
  den_addScaledRust hf hg 1

theorem den_formSumRust : ∀ {l l' : List Form}, l.map Form.evaluate = l'.map Form.evaluate →
    (formSumRust l).evaluate = (Form.sum l').evaluate := by
  suffices ∀ (l l' : List Form) (a a' : Form), a.evaluate = a'.evaluate →
      l.map Form.evaluate = l'.map Form.evaluate →
      (l.foldl addRust a).evaluate = (l'.foldl Form.add a').evaluate from
    fun {l l'} h ↦ this l l' {} {} rfl h
  intro l
  induction l with
  | nil =>
    intro l' a a' ha h
    cases l' with
    | nil => exact ha
    | cons _ _ => cases h
  | cons x l ih =>
    intro l' a a' ha h
    cases l' with
    | nil => cases h
    | cons x' l' =>
      simp only [List.map_cons, List.cons.injEq] at h
      exact ih l' _ _ (den_addRust ha h.1) h.2

end FormValue

/-! ## Constants and the basic forms -/

/-- `gpow(index) = GEN.pow(index)`, `E::pow` being `Model.Field`'s `ePow`. -/
def gpowRust (index : BitVec 64) : E := ofLimbsW (ePow (limbs gen) index)

theorem gpowRust_eq (index : BitVec 64) : gpowRust index = gpow index.toNat := by
  rw [gpowRust, ePow_eq, ofLimbsW_limbs, gpow]

theorem gpowRust_ofNat {n : ℕ} (h : n < 2 ^ 64) : gpowRust (BitVec.ofNat 64 n) = gpow n := by
  rw [gpowRust_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- `SEP_BYTECODE = E::new(4, 0)`. -/
def sepBytecodeRust : E := ofLimbsW (4#64, 0#64)

theorem sepBytecodeRust_eq : sepBytecodeRust = sepBytecode := by
  have h : limbs sepBytecode = (4#64, 0#64) := by
    rw [sepBytecode, show gen = ofK g from rfl, pow_two,
      show ofK g * ofK g = ofK (g * g) from (map_mul (algebraMap K E) g g).symm, limbs_ofK,
      ← timesX_eq]
    decide
  rw [← ofLimbsW_limbs sepBytecode, h]
  rfl

/-- `constant(value)`. -/
def constantRust (value : E) : Form := ⟨[([], value)]⟩

/-- `col(index, exponent)`: `Form::term(vec![index], gpow(exponent))`. -/
def colRust (index exponent : ℕ) : Form := ⟨[([index], gpowRust (BitVec.ofNat 64 exponent))]⟩

/-- `prod(a, b, exponent)`: `Form::term(vec![a.min(b), a.max(b)], gpow(exponent))`. -/
def prodRust (a b exponent : ℕ) : Form :=
  ⟨[([min a b, max a b], gpowRust (BitVec.ofNat 64 exponent))]⟩

theorem constantRust_eq (value : E) : constantRust value = Form.const value := rfl

theorem colRust_eq (index exponent : ℕ) (h : exponent < 2 ^ 64) :
    colRust index exponent = Form.col index exponent := by
  rw [colRust, gpowRust_ofNat h]
  rfl

@[simp] theorem colRust_zero (index : ℕ) : colRust index 0 = Form.col index 0 :=
  colRust_eq index 0 (by norm_num)

theorem prodRust_eq (a b exponent : ℕ) (h : exponent < 2 ^ 64) :
    prodRust a b exponent = Form.prod a b exponent := by
  rw [prodRust, gpowRust_ofNat h]
  rfl

/-! ## `Flushes` -/

/-- A list of forms by value: what the verifier reads of it. -/
def Forms.den (l : List Form) : List ((ℕ → E) → E) := l.map Form.evaluate

/-- Flushes by value. -/
def flushesDen (f : Flushes) : List (List ((ℕ → E) → E)) × List (List ((ℕ → E) → E)) :=
  (f.push.map Forms.den, f.pull.map Forms.den)

namespace FlushesRust

/-- `Flushes::pair`. -/
def pair (f : Flushes) (push pull : List Form) : Flushes := ⟨f.push ++ [push], f.pull ++ [pull]⟩

/-- `Flushes::state_derived`. -/
def stateDerived (f : Flushes) (pc fp : ℕ) (npc nfp : Form) : Flushes :=
  f.pair [constantRust 1, npc, nfp] [constantRust 1, colRust pc 0, colRust fp 0]

/-- `Flushes::state_step`. -/
def stateStep (f : Flushes) (pc fp : ℕ) : Flushes :=
  stateDerived f pc fp (colRust pc 1) (colRust fp 0)

/-- `Flushes::counted`: `[&prefix[..], &[counter], suffix].concat()`, the pull at
`col(count, 0)`. -/
def counted (f : Flushes) (pre : List Form) (counter : Form) (count : ℕ) (suffix : List Form) :
    Flushes :=
  pair f (pre ++ [counter] ++ suffix) (pre ++ [colRust count 0] ++ suffix)

/-- `Flushes::bytecode`. -/
def bytecode (f : Flushes) (pc count opcode : ℕ) (operands : List Form) : Flushes :=
  counted f [constantRust sepBytecodeRust, colRust pc 0] (colRust count 1) count
    ([constantRust (gpowRust (BitVec.ofNat 64 opcode))] ++ operands)

/-- `Flushes::memory`. -/
def memory (f : Flushes) (address : Form) (count : ℕ) (values : List Form) : Flushes :=
  counted f [constantRust gen, address] (colRust count 1) count values

/-- `Flushes::memory_if`. -/
def memoryIf (f : Flushes) (flag : ℕ) (address : Form) (count : ℕ) (values : List Form) :
    Flushes :=
  counted f [constantRust gen, address]
    (addRust (addRust (colRust count 0) (prodRust flag count 1)) (prodRust flag count 0)) count
    values

/-- `Flushes::memory_cols`: limb `l` is `columns.get(l).map_or(constant(ZERO), col)`. -/
def memoryCols (f : Flushes) (address : Form) (count : ℕ) (columns : List ℕ) : Flushes :=
  memory f address count ((List.range 2).map fun limb ↦
    match columns[limb]? with
    | some column => colRust column 0
    | none => constantRust 0)

end FlushesRust

section FlushesDen

variable {f f' : Flushes}

theorem den_pair (hf : flushesDen f = flushesDen f') {p p' q q' : List Form}
    (hp : Forms.den p = Forms.den p')
    (hq : Forms.den q = Forms.den q') :
    (flushesDen (FlushesRust.pair f p q)) = (flushesDen (f'.pair p' q')) := by
  simp only [flushesDen, FlushesRust.pair, Flushes.pair, List.map_append, List.map_cons,
    List.map_nil] at hf ⊢
  rw [Prod.mk.injEq] at hf ⊢
  rw [hf.1, hf.2, hp, hq]
  exact ⟨rfl, rfl⟩

theorem den_cons {x x' : Form} {l l' : List Form} (hx : x.evaluate = x'.evaluate)
    (hl : Forms.den l = Forms.den l') : Forms.den (x :: l) = Forms.den (x' :: l') := by
  simp only [Forms.den, List.map_cons] at hl ⊢
  rw [hx, hl]

theorem den_append {l l' m m' : List Form} (hl : Forms.den l = Forms.den l')
    (hm : Forms.den m = Forms.den m') : Forms.den (l ++ m) = Forms.den (l' ++ m') := by
  simp only [Forms.den, List.map_append] at hl hm ⊢
  rw [hl, hm]

theorem den_stateDerived (hf : flushesDen f = flushesDen f') (pc fp : ℕ) {npc npc' nfp nfp' : Form}
    (h1 : npc.evaluate = npc'.evaluate) (h2 : nfp.evaluate = nfp'.evaluate) :
    flushesDen (FlushesRust.stateDerived f pc fp npc nfp) =
      flushesDen (f'.stateDerived pc fp npc' nfp') := by
  unfold FlushesRust.stateDerived Flushes.stateDerived
  refine den_pair hf (den_cons rfl (den_cons h1 (den_cons h2 rfl))) ?_
  rw [colRust_eq _ _ (by norm_num), colRust_eq _ _ (by norm_num)]
  rfl

theorem den_stateStep (hf : flushesDen f = flushesDen f') (pc fp : ℕ) :
    (flushesDen (FlushesRust.stateStep f pc fp)) = (flushesDen (f'.stateStep pc fp)) := by
  unfold FlushesRust.stateStep Flushes.stateStep
  refine den_stateDerived hf pc fp ?_ ?_ <;> rw [colRust_eq _ _ (by norm_num)]

theorem den_counted (hf : flushesDen f = flushesDen f') {pre pre' : List Form}
    (hpre : Forms.den pre = Forms.den pre')
    {counter counter' : Form} (hc : counter.evaluate = counter'.evaluate) (count : ℕ)
    {suffix suffix' : List Form} (hs : Forms.den suffix = Forms.den suffix') :
    flushesDen (FlushesRust.counted f pre counter count suffix) =
      flushesDen (f'.counted pre' counter' count suffix') := by
  unfold FlushesRust.counted Flushes.counted
  refine den_pair hf (den_append (den_append hpre (den_cons hc rfl)) hs)
    (den_append (den_append hpre ?_) hs)
  rw [colRust_eq _ _ (by norm_num)]

theorem den_bytecode (hf : flushesDen f = flushesDen f') (pc count opcode : ℕ)
    (hop : opcode < 2 ^ 64)
    {operands operands' : List Form} (ho : Forms.den operands = Forms.den operands') :
    (flushesDen (FlushesRust.bytecode f pc count opcode operands)) =
      (flushesDen (f'.bytecode pc count opcode operands')) := by
  unfold FlushesRust.bytecode Flushes.bytecode
  refine den_counted hf ?_ ?_ count ?_
  · rw [sepBytecodeRust_eq, colRust_eq _ _ (by norm_num)]
    rfl
  · rw [colRust_eq _ _ (by norm_num)]
  · rw [gpowRust_ofNat hop]
    exact den_cons rfl ho

theorem den_memory (hf : flushesDen f = flushesDen f') {address address' : Form}
    (ha : address.evaluate = address'.evaluate) (count : ℕ) {values values' : List Form}
    (hv : Forms.den values = Forms.den values') :
    flushesDen (FlushesRust.memory f address count values) =
      flushesDen (f'.memory address' count values') := by
  unfold FlushesRust.memory Flushes.memory
  refine den_counted hf (den_cons rfl (den_cons ha rfl)) ?_ count hv
  rw [colRust_eq _ _ (by norm_num)]

theorem den_memoryIf (hf : flushesDen f = flushesDen f') (flag : ℕ) {address address' : Form}
    (ha : address.evaluate = address'.evaluate) (count : ℕ) {values values' : List Form}
    (hv : Forms.den values = Forms.den values') :
    (flushesDen (FlushesRust.memoryIf f flag address count values)) =
      (flushesDen (f'.memoryIf flag address' count values')) := by
  unfold FlushesRust.memoryIf Flushes.memoryIf
  refine den_counted hf (den_cons rfl (den_cons ha rfl)) ?_ count hv
  have h0 : (colRust count 0).evaluate = (({} : Form).add (Form.col count)).evaluate := by
    funext column
    rw [colRust_eq _ _ (by norm_num), Form.add, evaluate_addScaled]
    simp [evaluate_eq_sum]
  rw [prodRust_eq _ _ _ (by norm_num), prodRust_eq _ _ _ (by norm_num)]
  simp only [Form.sum, List.foldl_cons, List.foldl_nil]
  exact den_addRust (den_addRust h0 rfl) rfl

theorem den_memoryCols (hf : flushesDen f = flushesDen f') {address address' : Form}
    (ha : address.evaluate = address'.evaluate) (count : ℕ) (columns : List ℕ)
    (hc : columns.length ≤ 2) :
    (flushesDen (FlushesRust.memoryCols f address count columns)) =
      (flushesDen (f'.memoryCols address' count columns)) := by
  unfold FlushesRust.memoryCols Flushes.memoryCols
  refine den_memory hf ha count ?_
  congr 1
  simp only [show List.range 2 = [0, 1] from rfl, List.map_cons, List.map_nil]
  match columns, hc with
  | [], _ => rfl
  | [a], _ => simp [constantRust_eq]
  | [a, b], _ => simp

end FlushesDen

/-! ## The tables' columns (`layout.rs`) -/

/-- `OP_KECCAK`. -/
def opKeccakRust : ℕ := 5

/-- `STATE_LANES` (`hash.rs`). -/
def stateLanesRust : ℕ := 25

/-- `KECCAK_CELLS`. -/
def keccakCellsRust : ℕ := 13

/-! XOR's and MUL's columns (`mod arith`). -/
namespace ArithCol
def pc : ℕ := 0
def fp : ℕ := 1
def oA : ℕ := 2
def oB : ℕ := 3
def oC : ℕ := 4
def va : List ℕ := [5, 6]
def vb : List ℕ := [7, 8]
def cntA : ℕ := 9
def cntB : ℕ := 10
def cntC : ℕ := 11
def cntBc : ℕ := 12
def width : ℕ := 13
def counts : List ℕ := [cntA, cntB, cntC, cntBc]
end ArithCol

/-! `mod set`. -/
namespace SetCol
def pc : ℕ := 0
def fp : ℕ := 1
def o : ℕ := 2
def k : List ℕ := [3, 4]
def cnt : ℕ := 5
def cntBc : ℕ := 6
def width : ℕ := 7
def counts : List ℕ := [cnt, cntBc]
end SetCol

/-! `mod deref`. -/
namespace DerefCol
def pc : ℕ := 0
def fp : ℕ := 1
def o1 : ℕ := 2
def o2 : ℕ := 3
def o3 : ℕ := 4
def fPc : ℕ := 5
def fFp : ℕ := 6
def ptr : ℕ := 7
def v3 : List ℕ := [8, 9]
def cntPtr : ℕ := 10
def cntTarget : ℕ := 11
def cntLocal : ℕ := 12
def cntBc : ℕ := 13
def width : ℕ := 14
def counts : List ℕ := [cntPtr, cntTarget, cntLocal, cntBc]
end DerefCol

/-! `mod jump`. -/
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

/-! `mod keccak_head`. -/
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
def len : ℕ := 15
end KeccakCol

/-- `KECCAK_IN`. -/
def keccakInRust : ℕ := KeccakCol.len

/-- `KECCAK_OUT`. -/
def keccakOutRust : ℕ := keccakInRust + stateLanesRust

/-- `KECCAK_CNT`. -/
def keccakCntRust : ℕ := keccakOutRust + stateLanesRust

/-- `KECCAK_CNT_BC`. -/
def keccakCntBcRust : ℕ := keccakCntRust + 2 * keccakCellsRust

/-- `KECCAK_COUNTS`: `KECCAK_CNT + i` for each of its `2 · 13 + 1` entries. -/
def keccakCountsRust : List ℕ := (List.range (2 * keccakCellsRust + 1)).map (keccakCntRust + ·)

/-- `TABLE_WIDTHS`. -/
def tableWidthsRust : List ℕ :=
  [ArithCol.width, ArithCol.width, SetCol.width, DerefCol.width, JumpCol.width,
    keccakCntBcRust + 1]

/-- `COUNT_COLUMNS`. -/
def countColumnsRust : List (List ℕ) :=
  [ArithCol.counts, ArithCol.counts, SetCol.counts, DerefCol.counts, JumpCol.counts,
    keccakCountsRust]

/-- `N_CONSTRAINTS`. -/
def nConstraintsRust : List ℕ := [0, 0, 0, 0, 2, 0]

/-- `GLOBAL_COLUMN_BASES`: from `NUM_GLOBAL_COLUMNS`, each table's base past the previous. -/
def globalColumnBasesRust : List ℕ :=
  ((List.range 5).foldl (fun (acc : List ℕ × ℕ) t ↦
    (acc.1 ++ [acc.2 + tableWidthsRust.getD t 0], acc.2 + tableWidthsRust.getD t 0)) ([5], 5)).1

theorem globalColumnBasesRust_eq : globalColumnBasesRust = globalColumnBases := by decide +kernel

/-! ## The flushes (`layout.rs`) -/

/-- `TOWER_LANES`. -/
def towerLanesRust : List (List (ℕ × ℕ × ℕ)) :=
  [[(0, 0, 0), (1, 1, 0)], [(0, 1, 0), (1, 0, 0), (1, 1, 1)]]

/-- `flushes_arith(opcode, multiply)`. -/
def flushesArithRust (opcode : ℕ) (multiply : Bool) : Flushes :=
  open ArithCol in
  let f := FlushesRust.stateStep {} pc fp
  let operands := [colRust oA 0, colRust oB 0, colRust oC 0, constantRust 0, constantRust 0]
  let f := FlushesRust.bytecode f pc cntBc opcode operands
  let f := FlushesRust.memoryCols f (prodRust fp oA 0) cntA va
  let f := FlushesRust.memoryCols f (prodRust fp oB 0) cntB vb
  let result : List Form :=
    if multiply then
      towerLanesRust.map fun lane ↦
        formSumRust (lane.map fun (j, k, e) ↦ prodRust (va.getD j 0) (vb.getD k 0) e)
    else (List.range 2).map fun i ↦ addRust (colRust (va.getD i 0) 0) (colRust (vb.getD i 0) 0)
  FlushesRust.memory f (prodRust fp oC 0) cntC result

/-- `flushes_set()`. -/
def flushesSetRust : Flushes :=
  open SetCol in
  let f := FlushesRust.stateStep {} pc fp
  let operands := [colRust o 0, colRust (k.getD 0 0) 0, colRust (k.getD 1 0) 0, constantRust 0,
    constantRust 0]
  let f := FlushesRust.bytecode f pc cntBc 2 operands
  FlushesRust.memoryCols f (prodRust fp o 0) cnt k

/-- `flushes_deref()`. -/
def flushesDerefRust : Flushes :=
  open DerefCol in
  let gated := fun lane ↦ [colRust lane 0, prodRust fPc lane 0, prodRust fFp lane 0]
  let store := [formSumRust (gated (v3.getD 0 0) ++ [prodRust fPc pc 2, prodRust fFp fp 0]),
    formSumRust (gated (v3.getD 1 0))]
  let f := FlushesRust.stateStep {} pc fp
  let operands := [colRust o1 0, colRust o2 0, colRust o3 0, colRust fPc 0, colRust fFp 0]
  let f := FlushesRust.bytecode f pc cntBc 3 operands
  let f := FlushesRust.memoryCols f (prodRust fp o1 0) cntPtr [ptr]
  let f := FlushesRust.memory f (prodRust ptr o2 0) cntTarget store
  FlushesRust.memoryCols f (prodRust fp o3 0) cntLocal v3

/-- `flushes_jump()`. -/
def flushesJumpRust : Flushes :=
  open JumpCol in
  let f := FlushesRust.stateDerived {} pc fp
    (addRust (addRust (prodRust b vPc 0) (prodRust b pc 1)) (colRust pc 1))
    (addRust (addRust (prodRust b vFp 0) (prodRust b fp 0)) (colRust fp 0))
  let operands := [colRust oC 0, colRust oD 0, colRust oF 0, constantRust 0, constantRust 0]
  let f := FlushesRust.bytecode f pc cntBc 4 operands
  let f := FlushesRust.memoryCols f (prodRust fp oC 0) cntC [vCond]
  let f := FlushesRust.memoryCols f (prodRust fp oD 0) cntD [vPc]
  FlushesRust.memoryCols f (prodRust fp oF 0) cntF [vFp]

/-- `jump_constraints(columns)`: `[flag + condition * inverse, condition * (flag + ONE)]`. -/
def jumpConstraintsRust (columns : List E) : List E :=
  let condition := columns.getD JumpCol.vCond 0
  let inverse := columns.getD JumpCol.w 0
  let flag := columns.getD JumpCol.b 0
  [flag + condition * inverse, condition * (flag + 1)]

/-- `keccak_cell_lanes(odd)[cell]`: the `match (odd, cell)` of its loop. -/
def keccakCellLanesRust (odd : Bool) (cell : ℕ) : Option ℕ × Option ℕ :=
  if 9 ≤ cell ∨ (odd ∧ 1 ≤ cell) then (some (2 * cell - 1), some (2 * cell))
  else if odd then (none, some 0)
  else if cell = 8 then (some 16, none)
  else (some (2 * cell), some (2 * cell + 1))

/-- `layout_limb(even, odd, flag, missing)`. -/
def layoutLimbRust (even odd : Option ℕ) (flag : ℕ) (missing : Option ℕ) : Form :=
  let a := even.or missing
  let b := odd.or missing
  if a = b then
    match a with
    | none => constantRust 0
    | some a => colRust a 0
  else
    formSumRust
      ([a.map (colRust · 0), a.map (prodRust flag · 0), b.map (prodRust flag · 0)].filterMap id)

/-- The address of cell `cell` of a `KECCAK` read (`flushes_keccak`'s `address`). -/
def keccakAddressRust (cell : ℕ) : Form :=
  open KeccakCol in
  if cell < 4 then prodRust fp (oM.getD cell 0) 0
  else if cell < 8 then prodRust fp oTail (cell - 4)
  else if cell = 8 then prodRust fp oB8 0
  else prodRust fp oCap (cell - 9)

/-- One cell of `flushes_keccak`'s inner loop on a side. -/
def keccakCellRust (side lanes flag : ℕ) (missing : Option ℕ) (f : Flushes) (cell : ℕ) :
    Flushes :=
  open KeccakCol in
  let lane := fun (l : Option ℕ) ↦ l.map (lanes + ·)
  let limb := fun (e o : Option ℕ) ↦ layoutLimbRust (lane e) (lane o) flag missing
  let values := [limb (keccakCellLanesRust false cell).1 (keccakCellLanesRust true cell).1,
    limb (keccakCellLanesRust false cell).2 (keccakCellLanesRust true cell).2]
  let count := keccakCntRust + keccakCellsRust * side + cell
  if side = 0 then FlushesRust.memory f (keccakAddressRust cell) count values
  else if cell = 0 then FlushesRust.memory f (prodRust fp oOut 0) count values
  else
    FlushesRust.memoryIf f (if cell = 1 then outTwo else outAll) (prodRust fp oOut cell) count
      values

/-- `flushes_keccak()`. -/
def flushesKeccakRust : Flushes :=
  open KeccakCol in
  let f := FlushesRust.stateStep {} pc fp
  let operands :=
    (oM ++ [oTail, oB8, oCap, oOut, oddIn, oddOut, outTwo, outAll]).map (colRust · 0)
  let f := FlushesRust.bytecode f pc keccakCntBcRust opKeccakRust operands
  let sides : List (ℕ × ℕ × ℕ × Option ℕ) :=
    [(0, keccakInRust, oddIn, some free), (1, keccakOutRust, oddOut, none)]
  sides.foldl (fun f (side, lanes, flag, missing) ↦
    (List.range keccakCellsRust).foldl (keccakCellRust side lanes flag missing) f) f

/-! ## The tables (`Table`, `tables()`) -/

/-- `Table`: its opcode, its padding row, its flushes. -/
structure TableRust where
  /-- `opcode`. -/
  opcode : ℕ
  /-- `padding`. -/
  padding : List E
  /-- `flushes`. -/
  flushes : Flushes

/-- `Table::n_constraints`: `N_CONSTRAINTS[opcode]`. -/
def TableRust.nConstraints (t : TableRust) : ℕ := nConstraintsRust.getD t.opcode 0

/-- `Table::constraints(columns)`: `jump_constraints` for `JUMP`, none elsewhere. -/
def TableRust.constraints (t : TableRust) (columns : List E) : List E :=
  if t.opcode = 4 then jumpConstraintsRust columns else []

/-- `Table::width`: `TABLE_WIDTHS[opcode]`. -/
def TableRust.width (t : TableRust) : ℕ := tableWidthsRust.getD t.opcode 0

/-- `Table::count_columns`: `COUNT_COLUMNS[opcode]`. -/
def TableRust.countColumns (t : TableRust) : List ℕ := countColumnsRust.getD t.opcode []

/-- The `KECCAK` padding row: zeros, then `keccak_f` of the zero state at `KECCAK_OUT..`, by
`padding[KECCAK_OUT..].iter_mut().zip(output)`. -/
def keccakPaddingRust : List E :=
  let output := keccakFRust (List.replicate 25 0#64)
  (List.range stateLanesRust).foldl (fun padding lane ↦
    padding.set (keccakOutRust + lane) (eNew (output.getD lane 0)))
    (List.replicate (tableWidthsRust.getD opKeccakRust 0) 0)

/-- `tables()`. -/
def tablesRust : List TableRust :=
  let table := fun (opcode : ℕ) (flushes : Flushes) ↦
    ({ opcode, padding := List.replicate (tableWidthsRust.getD opcode 0) 0, flushes } :
      TableRust)
  [table 0 (flushesArithRust 0 false), table 1 (flushesArithRust 1 true), table 2 flushesSetRust,
    table 3 flushesDerefRust, table 4 flushesJumpRust,
    { opcode := opKeccakRust, padding := keccakPaddingRust, flushes := flushesKeccakRust }]

/-- A Rust table is a statement table: the same opcode, width, count columns, constraints and
padding, and its flushes by value. -/
structure TableRust.Rel (t : TableRust) (T : Table) : Prop where
  opcode : t.opcode = T.opcode
  width : t.width = T.width
  countColumns : t.countColumns = T.countColumns
  nConstraints : t.nConstraints = T.nConstraints
  constraints : ∀ columns, t.constraints columns = T.constraints columns
  padding : t.padding = T.padding
  flushes : flushesDen t.flushes = flushesDen T.flushes

/-! ## The tables are the statement's -/

section TablesEq

theorem evaluate_addRust_fun (f g : Form) :
    (addRust f g).evaluate = fun column ↦ f.evaluate column + g.evaluate column := by
  funext column
  rw [addRust, evaluate_addScaledRust, one_mul]

theorem evaluate_add_fun (f g : Form) :
    (f.add g).evaluate = fun column ↦ f.evaluate column + g.evaluate column := by
  funext column
  rw [Form.add, evaluate_addScaled, one_mul]

theorem evaluate_foldl_addRust (l : List Form) (a : Form) (column : ℕ → E) :
    (l.foldl addRust a).evaluate column = a.evaluate column + (l.map (·.evaluate column)).sum := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih, evaluate_addRust_fun]; simp [add_assoc]

theorem evaluate_foldl_add (l : List Form) (a : Form) (column : ℕ → E) :
    (l.foldl Form.add a).evaluate column = a.evaluate column + (l.map (·.evaluate column)).sum := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih, evaluate_add_fun]; simp [add_assoc]

theorem evaluate_empty (column : ℕ → E) : ({} : Form).evaluate column = 0 := rfl

theorem evaluate_formSumRust_fun (l : List Form) :
    (formSumRust l).evaluate = fun column ↦ (l.map (·.evaluate column)).sum := by
  funext column
  rw [formSumRust, evaluate_foldl_addRust, evaluate_empty, zero_add]

theorem evaluate_sum_fun (l : List Form) :
    (Form.sum l).evaluate = fun column ↦ (l.map (·.evaluate column)).sum := by
  funext column
  rw [Form.sum, evaluate_foldl_add, evaluate_empty, zero_add]

end TablesEq

section TablesEq

theorem den_foldl {α : Type} (l : List α) (g g' : Flushes → α → Flushes)
    (h : ∀ x ∈ l, ∀ f f', flushesDen f = flushesDen f' →
      flushesDen (g f x) = flushesDen (g' f' x)) :
    ∀ f f', flushesDen f = flushesDen f' →
      flushesDen (l.foldl g f) = flushesDen (l.foldl g' f') := by
  induction l with
  | nil => intro f f' hf; exact hf
  | cons x l ih =>
    intro f f' hf
    exact ih (fun y hy ↦ h y (by simp [hy])) _ _ (h x (by simp) f f' hf)

theorem den_layoutLimb (even odd : Option ℕ) (flag : ℕ) (missing : Option ℕ) :
    (layoutLimbRust even odd flag missing).evaluate =
      (layoutLimb even odd flag missing).evaluate := by
  have hor : ∀ o : Option ℕ, (o.orElse fun _ ↦ missing) = o.or missing := by
    intro o; cases o <;> rfl
  unfold layoutLimbRust layoutLimb
  simp only [hor]
  generalize even.or missing = a
  generalize odd.or missing = b
  split_ifs with hab
  · subst hab
    rcases a with _ | a <;> simp [constantRust_eq]
  · apply den_formSumRust
    rcases a with _ | a <;> rcases b with _ | b <;>
      simp [prodRust_eq _ _ 0 (by norm_num : 0 < 2 ^ 64)]

theorem keccakCellLanesRust_eq (odd : Bool) (cell : ℕ) :
    keccakCellLanesRust odd cell = cellLanes odd cell := rfl

private theorem arith_names :
    columnIndexByName arithColumns "pc" = 0 ∧ columnIndexByName arithColumns "fp" = 1 ∧
    columnIndexByName arithColumns "o_a" = 2 ∧ columnIndexByName arithColumns "o_b" = 3 ∧
    columnIndexByName arithColumns "o_c" = 4 ∧ columnIndexByName arithColumns "va_0" = 5 ∧
    columnIndexByName arithColumns "va_1" = 6 ∧ columnIndexByName arithColumns "vb_0" = 7 ∧
    columnIndexByName arithColumns "vb_1" = 8 ∧ columnIndexByName arithColumns "cnt_a" = 9 ∧
    columnIndexByName arithColumns "cnt_b" = 10 ∧ columnIndexByName arithColumns "cnt_c" = 11 ∧
    columnIndexByName arithColumns "cnt_bc" = 12 := by decide

private theorem set_names :
    columnIndexByName setColumns "pc" = 0 ∧ columnIndexByName setColumns "fp" = 1 ∧
    columnIndexByName setColumns "o" = 2 ∧ columnIndexByName setColumns "k_0" = 3 ∧
    columnIndexByName setColumns "k_1" = 4 ∧ columnIndexByName setColumns "cnt" = 5 ∧
    columnIndexByName setColumns "cnt_bc" = 6 := by decide

private theorem deref_names :
    columnIndexByName derefColumns "pc" = 0 ∧ columnIndexByName derefColumns "fp" = 1 ∧
    columnIndexByName derefColumns "o1" = 2 ∧ columnIndexByName derefColumns "o2" = 3 ∧
    columnIndexByName derefColumns "o3" = 4 ∧ columnIndexByName derefColumns "f_pc" = 5 ∧
    columnIndexByName derefColumns "f_fp" = 6 ∧ columnIndexByName derefColumns "ptr" = 7 ∧
    columnIndexByName derefColumns "v3_0" = 8 ∧ columnIndexByName derefColumns "v3_1" = 9 ∧
    columnIndexByName derefColumns "cnt_ptr" = 10 ∧
    columnIndexByName derefColumns "cnt_target" = 11 ∧
    columnIndexByName derefColumns "cnt_local" = 12 ∧
    columnIndexByName derefColumns "cnt_bc" = 13 := by decide

private theorem jump_names :
    columnIndexByName jumpColumns "pc" = 0 ∧ columnIndexByName jumpColumns "fp" = 1 ∧
    columnIndexByName jumpColumns "o_c" = 2 ∧ columnIndexByName jumpColumns "o_d" = 3 ∧
    columnIndexByName jumpColumns "o_f" = 4 ∧ columnIndexByName jumpColumns "v_cond" = 5 ∧
    columnIndexByName jumpColumns "v_pc" = 6 ∧ columnIndexByName jumpColumns "v_fp" = 7 ∧
    columnIndexByName jumpColumns "cnt_c" = 8 ∧ columnIndexByName jumpColumns "cnt_d" = 9 ∧
    columnIndexByName jumpColumns "cnt_f" = 10 ∧ columnIndexByName jumpColumns "cnt_bc" = 11 ∧
    columnIndexByName jumpColumns "w" = 12 ∧ columnIndexByName jumpColumns "b" = 13 := by decide

private theorem keccak_names :
    columnIndexByName keccakColumns "pc" = 0 ∧ columnIndexByName keccakColumns "fp" = 1 ∧
    columnIndexByName keccakColumns "o_m0" = 2 ∧ columnIndexByName keccakColumns "o_m1" = 3 ∧
    columnIndexByName keccakColumns "o_m2" = 4 ∧ columnIndexByName keccakColumns "o_m3" = 5 ∧
    columnIndexByName keccakColumns "o_tail" = 6 ∧ columnIndexByName keccakColumns "o_b8" = 7 ∧
    columnIndexByName keccakColumns "o_cap" = 8 ∧ columnIndexByName keccakColumns "o_out" = 9 ∧
    columnIndexByName keccakColumns "odd_in" = 10 ∧
    columnIndexByName keccakColumns "odd_out" = 11 ∧
    columnIndexByName keccakColumns "out_two" = 12 ∧
    columnIndexByName keccakColumns "out_all" = 13 ∧ columnIndexByName keccakColumns "free" = 14 ∧
    columnIndexByName keccakColumns "cnt_bc" = 91 ∧ keccakIn = 15 ∧ keccakOut = 40 ∧
    keccakCnt = 65 := by decide +kernel

theorem den_flushesArith (opcode : ℕ) (hop : opcode < 2 ^ 64) (multiply : Bool) :
    flushesDen (flushesArithRust opcode multiply) = flushesDen (flushesArith opcode multiply) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := arith_names
  simp only [flushesArith, flushesArithRust, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
    h13, flushesDen, Forms.den, FlushesRust.memory, FlushesRust.memoryCols, FlushesRust.bytecode,
    FlushesRust.stateStep, FlushesRust.stateDerived, FlushesRust.counted, FlushesRust.pair,
    Flushes.memory, Flushes.memoryCols, Flushes.bytecode, Flushes.stateStep, Flushes.stateDerived,
    Flushes.counted, Flushes.pair, colRust_zero, constantRust_eq, ArithCol.pc, ArithCol.fp,
    ArithCol.oA, ArithCol.oB, ArithCol.oC, ArithCol.va, ArithCol.vb, ArithCol.cntA, ArithCol.cntB,
    ArithCol.cntC, ArithCol.cntBc, sepBytecodeRust_eq, gpowRust_ofNat hop,
    colRust_eq _ 1 (by norm_num : 1 < 2 ^ 64), prodRust_eq _ _ 0 (by norm_num : 0 < 2 ^ 64),
    List.map_cons, List.map_nil, List.nil_append, List.cons_append,
    show List.range 2 = [0, 1] from rfl, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.getD_cons_zero, List.getD_cons_succ, sepState, sepMem, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub, List.replicate_zero]
  cases multiply
  · simp only [Bool.false_eq_true, ↓reduceIte, List.map_cons, List.map_nil, evaluate_addRust_fun,
      evaluate_add_fun]
  · simp only [↓reduceIte, towerLanesRust, towerLanes, List.map_cons, List.map_nil,
      evaluate_formSumRust_fun, evaluate_sum_fun, List.getD_cons_zero, List.getD_cons_succ,
      prodRust_eq _ _ 0 (by norm_num : 0 < 2 ^ 64), prodRust_eq _ _ 1 (by norm_num : 1 < 2 ^ 64)]

theorem den_flushesSet : flushesDen flushesSetRust = flushesDen flushesSet := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := set_names
  simp only [flushesSet, flushesSetRust, h1, h2, h3, h4, h5, h6, h7, flushesDen, Forms.den,
    FlushesRust.memory, FlushesRust.memoryCols, FlushesRust.bytecode, FlushesRust.stateStep,
    FlushesRust.stateDerived, FlushesRust.counted, FlushesRust.pair, Flushes.memory,
    Flushes.memoryCols, Flushes.bytecode, Flushes.stateStep, Flushes.stateDerived, Flushes.counted,
    Flushes.pair, colRust_zero, constantRust_eq, SetCol.pc, SetCol.fp, SetCol.o, SetCol.k,
    SetCol.cnt, SetCol.cntBc, sepBytecodeRust_eq, gpowRust_ofNat (by norm_num : 2 < 2 ^ 64),
    colRust_eq _ 1 (by norm_num : 1 < 2 ^ 64), prodRust_eq _ _ 0 (by norm_num : 0 < 2 ^ 64),
    List.map_cons, List.map_nil, List.nil_append, List.cons_append,
    show List.range 2 = [0, 1] from rfl, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.getD_cons_zero, List.getD_cons_succ, sepState, sepMem, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub, List.replicate_zero, opSet]

theorem den_flushesDeref : flushesDen flushesDerefRust = flushesDen flushesDeref := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := deref_names
  simp only [flushesDeref, flushesDerefRust, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
    h13, h14, flushesDen, Forms.den, FlushesRust.memory, FlushesRust.memoryCols,
    FlushesRust.bytecode, FlushesRust.stateStep, FlushesRust.stateDerived, FlushesRust.counted,
    FlushesRust.pair, Flushes.memory, Flushes.memoryCols, Flushes.bytecode, Flushes.stateStep,
    Flushes.stateDerived, Flushes.counted, Flushes.pair, colRust_zero, constantRust_eq,
    DerefCol.pc, DerefCol.fp, DerefCol.o1, DerefCol.o2, DerefCol.o3, DerefCol.fPc, DerefCol.fFp,
    DerefCol.ptr, DerefCol.v3, DerefCol.cntPtr, DerefCol.cntTarget, DerefCol.cntLocal,
    DerefCol.cntBc, sepBytecodeRust_eq, gpowRust_ofNat (by norm_num : 3 < 2 ^ 64),
    colRust_eq _ 1 (by norm_num : 1 < 2 ^ 64), prodRust_eq _ _ 0 (by norm_num : 0 < 2 ^ 64),
    prodRust_eq _ _ 2 (by norm_num : 2 < 2 ^ 64), List.map_cons, List.map_nil, List.nil_append,
    List.cons_append, show List.range 2 = [0, 1] from rfl, List.getElem?_cons_zero,
    List.getElem?_cons_succ, List.getD_cons_zero, List.getD_cons_succ, sepState, sepMem,
    List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, List.replicate_zero,
    List.replicate_succ, opDeref, evaluate_formSumRust_fun, evaluate_sum_fun, List.getElem?_nil]

theorem den_flushesJump : flushesDen flushesJumpRust = flushesDen flushesJump := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, -, h14⟩ := jump_names
  simp only [flushesJump, flushesJumpRust, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
    h14, flushesDen, Forms.den, FlushesRust.memory, FlushesRust.memoryCols,
    FlushesRust.bytecode, FlushesRust.stateDerived, FlushesRust.counted,
    FlushesRust.pair, Flushes.memory, Flushes.memoryCols, Flushes.bytecode,
    Flushes.stateDerived, Flushes.counted, Flushes.pair, colRust_zero, constantRust_eq,
    JumpCol.pc, JumpCol.fp, JumpCol.oC, JumpCol.oD, JumpCol.oF, JumpCol.vCond, JumpCol.vPc,
    JumpCol.vFp, JumpCol.cntC, JumpCol.cntD, JumpCol.cntF, JumpCol.cntBc, JumpCol.b,
    sepBytecodeRust_eq, gpowRust_ofNat (by norm_num : 4 < 2 ^ 64),
    colRust_eq _ 1 (by norm_num : 1 < 2 ^ 64), prodRust_eq _ _ 0 (by norm_num : 0 < 2 ^ 64),
    prodRust_eq _ _ 1 (by norm_num : 1 < 2 ^ 64), List.map_cons, List.map_nil, List.nil_append,
    List.cons_append, show List.range 2 = [0, 1] from rfl, List.getElem?_cons_zero,
    List.getElem?_cons_succ, sepState, sepMem,
    List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, List.replicate_zero,
    List.replicate_succ, opJump, evaluate_addRust_fun, evaluate_add_fun, List.getElem?_nil]

theorem den_flushesKeccak : flushesDen flushesKeccakRust = flushesDen flushesKeccak := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩ :=
    keccak_names
  unfold flushesKeccak flushesKeccakRust
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    List.zipIdx_cons, List.zipIdx_nil, List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil,
    Nat.zero_add]
  refine den_foldl _ _ _ ?_ _ _ (den_foldl _ _ _ ?_ _ _ ?_)
  rotate_left 2
  · refine den_bytecode (den_stateStep rfl _ _) _ _ _ (by norm_num [opKeccakRust]) ?_
    simp [Forms.den, KeccakCol.oM, KeccakCol.oTail, KeccakCol.oB8, KeccakCol.oCap, KeccakCol.oOut,
      KeccakCol.oddIn, KeccakCol.oddOut, KeccakCol.outTwo, KeccakCol.outAll]
  all_goals
    intro x hx f f' hf
    have hx' : x < 13 := List.mem_range.mp hx
    have hv : ∀ lanes flag missing, Forms.den
        [layoutLimbRust ((keccakCellLanesRust false x).1.map (lanes + ·))
          ((keccakCellLanesRust true x).1.map (lanes + ·)) flag missing,
         layoutLimbRust ((keccakCellLanesRust false x).2.map (lanes + ·))
          ((keccakCellLanesRust true x).2.map (lanes + ·)) flag missing] =
        Forms.den [layoutLimb ((cellLanes false x).1.map (lanes + ·))
          ((cellLanes true x).1.map (lanes + ·)) flag missing,
         layoutLimb ((cellLanes false x).2.map (lanes + ·))
          ((cellLanes true x).2.map (lanes + ·)) flag missing] := fun _ _ _ ↦
      den_cons (den_layoutLimb _ _ _ _) (den_cons (den_layoutLimb _ _ _ _) rfl)
    have ha : (keccakAddressRust x).evaluate = (if x < 4 then Form.prod 1 ([2, 3, 4, 5].getD x 0)
        else if x < 8 then Form.prod 1 6 (x - 4) else if x = 8 then Form.prod 1 7
        else Form.prod 1 8 (x - 9)).evaluate := by
      unfold keccakAddressRust
      split_ifs <;> rw [prodRust_eq _ _ _ (by omega)] <;> rfl
    simp only [keccakCellRust, one_ne_zero, ↓reduceIte, keccakCntRust, keccakOutRust,
      keccakInRust, stateLanesRust, keccakCellsRust, KeccakCol.len, KeccakCol.oddIn,
      KeccakCol.oddOut, KeccakCol.free, KeccakCol.fp, KeccakCol.oOut, KeccakCol.outTwo,
      KeccakCol.outAll, Nat.reduceAdd, Nat.reduceMul] at hv ⊢
    have hOut : ∀ e < 2 ^ 64, (prodRust 1 9 e).evaluate = (Form.prod 1 9 e).evaluate :=
      fun e he ↦ by rw [prodRust_eq _ _ _ he]
    first
      | exact den_memory hf ha _ (hv _ _ _)
      | split_ifs <;> first
        | exact den_memory hf (hOut 0 (by norm_num)) _ (hv _ _ _)
        | exact den_memoryIf hf _ (hOut x (by omega)) _ (hv _ _ _)

theorem length_foldl_setE (o : ℕ) (v : ℕ → E) :
    ∀ (n : ℕ) (P : List E),
      ((List.range n).foldl (fun p j ↦ p.set (o + j) (v j)) P).length = P.length
  | 0, _ => rfl
  | n + 1, P => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, List.length_set,
      length_foldl_setE o v n P]

theorem getElem?_foldl_setE (o : ℕ) (v : ℕ → E) (P : List E) (i : ℕ) :
    ∀ n, ((List.range n).foldl (fun p j ↦ p.set (o + j) (v j)) P)[i]? =
      if o ≤ i ∧ i < o + n ∧ i < P.length then some (v (i - o)) else P[i]?
  | 0 => by simp; omega
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, List.getElem?_set,
      length_foldl_setE, getElem?_foldl_setE o v P i n]
    by_cases h : o + n = i
    · subst h
      by_cases hl : o + n < P.length
      · simp [hl]
      · simp [hl]
    · simp only [h, ↓reduceIte]
      split_ifs <;> first | rfl | omega

theorem eNew_eq (x : BitVec 64) : eNew x = eOfNat x.toNat := by
  simp [eNew, eOfNat, K.ofBits]

theorem keccakPaddingRust_eq :
    keccakPaddingRust = (tables.getD opKeccak default).padding := by
  have hk : keccakFRust (List.replicate 25 0#64) =
      stateBits (keccakF1600 (Vector.replicate 25 0)) := by
    rw [← keccakFRust_eq]
    simp [stateBits]
  have hw : (tables.getD opKeccak default).width = 92 := by decide +kernel
  have hop : (tables.getD opKeccak default).opcode = opKeccak := rfl
  have ho : keccakOut = 40 := by decide +kernel
  have hr : tableWidthsRust.getD opKeccakRust 0 = 92 := rfl
  rw [Table.padding, hw, hop, ho, keccakPaddingRust]
  simp only [stateLanesRust, hr, hk]
  apply List.ext_getElem?
  intro i
  rw [getElem?_foldl_setE]
  simp only [List.getElem?_map, List.getElem?_replicate, List.length_replicate,
    keccakOutRust, keccakInRust, KeccakCol.len, stateLanesRust, true_and]
  by_cases h : i < 92
  · simp only [List.getElem?_range h, h, and_true, ↓reduceIte, Option.map_some,
      Nat.reduceAdd]
    split_ifs
    · rw [eNew_eq, getD_stateBits _ (by omega)]
      rfl
    · rfl
  · simp only [h, and_false, ↓reduceIte,
      List.getElem?_eq_none (show (List.range 92).length ≤ i by simp; omega), Option.map_none]

private theorem range_map_zero (n : ℕ) : (List.range n).map (fun _ ↦ (0 : E)) =
    List.replicate n 0 := by
  rw [List.map_const', List.length_range]

private theorem padding_of_ne (t : Table) (ht : t.opcode ≠ opKeccak) :
    List.replicate t.width 0 = t.padding := by
  rw [Table.padding, ← range_map_zero]
  exact List.map_congr_left fun i _ ↦ by simp [ht]

private theorem rel_arith (opcode : ℕ) (hop : opcode < 2) (multiply : Bool) :
    TableRust.Rel ⟨opcode, List.replicate (tableWidthsRust.getD opcode 0) 0,
      flushesArithRust opcode multiply⟩
      ⟨opcode, arithColumns, flushesArith opcode multiply, fun _ ↦ []⟩ := by
  have hw : tableWidthsRust.getD opcode 0 = 13 := by interval_cases opcode <;> rfl
  have hc : countColumnsRust.getD opcode [] = ArithCol.counts := by
    interval_cases opcode <;> rfl
  have hn : nConstraintsRust.getD opcode 0 = 0 := by interval_cases opcode <;> rfl
  have hc' : Table.countColumns ⟨opcode, arithColumns, flushesArith opcode multiply,
      fun _ ↦ []⟩ = ArithCol.counts := by
    simp [Table.countColumns, arithColumns, ArithCol.counts, ArithCol.cntA, ArithCol.cntB,
      ArithCol.cntC, ArithCol.cntBc]
  refine ⟨rfl, hw, hc.trans hc'.symm, by rw [TableRust.nConstraints, hn]; rfl,
    fun _ ↦ by simp [TableRust.constraints]; omega, ?_, den_flushesArith opcode (by omega) multiply⟩
  rw [hw]
  exact padding_of_ne ⟨opcode, arithColumns, flushesArith opcode multiply, fun _ ↦ []⟩
    (by simp [opKeccak]; omega)

private theorem rel_set :
    TableRust.Rel ⟨2, List.replicate (tableWidthsRust.getD 2 0) 0, flushesSetRust⟩
      ⟨opSet, setColumns, flushesSet, fun _ ↦ []⟩ := by
  refine ⟨rfl, rfl, by simp [TableRust.countColumns, countColumnsRust, SetCol.counts, SetCol.cnt,
    SetCol.cntBc, Table.countColumns, setColumns], rfl, fun _ ↦ rfl, ?_, den_flushesSet⟩
  exact padding_of_ne ⟨opSet, setColumns, flushesSet, fun _ ↦ []⟩ (by decide)

private theorem rel_deref :
    TableRust.Rel ⟨3, List.replicate (tableWidthsRust.getD 3 0) 0, flushesDerefRust⟩
      ⟨opDeref, derefColumns, flushesDeref, fun _ ↦ []⟩ := by
  refine ⟨rfl, rfl, by simp [TableRust.countColumns, countColumnsRust, DerefCol.counts,
    DerefCol.cntPtr, DerefCol.cntTarget, DerefCol.cntLocal, DerefCol.cntBc, Table.countColumns,
    derefColumns], rfl, fun _ ↦ rfl, ?_, den_flushesDeref⟩
  exact padding_of_ne ⟨opDeref, derefColumns, flushesDeref, fun _ ↦ []⟩ (by decide)

private theorem rel_jump :
    TableRust.Rel ⟨4, List.replicate (tableWidthsRust.getD 4 0) 0, flushesJumpRust⟩
      ⟨opJump, jumpColumns, flushesJump, jumpConstraints⟩ := by
  obtain ⟨-, -, -, -, -, h6, -, -, -, -, -, -, h13, h14⟩ := jump_names
  refine ⟨rfl, rfl, by simp [TableRust.countColumns, countColumnsRust, JumpCol.counts,
    JumpCol.cntC, JumpCol.cntD, JumpCol.cntF, JumpCol.cntBc, Table.countColumns, jumpColumns],
    by simp [TableRust.nConstraints, nConstraintsRust,
    Table.nConstraints, jumpConstraints], fun _ ↦ ?_, ?_, den_flushesJump⟩
  · simp [TableRust.constraints, jumpConstraintsRust, jumpConstraints, h6, h13, h14,
      JumpCol.vCond, JumpCol.w, JumpCol.b]
  · exact padding_of_ne ⟨opJump, jumpColumns, flushesJump, jumpConstraints⟩ (by decide)

private theorem rel_keccak :
    TableRust.Rel ⟨opKeccakRust, keccakPaddingRust, flushesKeccakRust⟩
      ⟨opKeccak, keccakColumns, flushesKeccak, fun _ ↦ []⟩ :=
  ⟨rfl, by decide +kernel, by simp [TableRust.countColumns, countColumnsRust, Table.countColumns,
    keccakColumns, laneNames, decimalNumeral, List.range_succ, opKeccakRust, keccakCountsRust,
    keccakCntRust, keccakOutRust, keccakInRust, KeccakCol.len, stateLanesRust, keccakCellsRust],
    rfl, fun _ ↦ rfl,
    keccakPaddingRust_eq, den_flushesKeccak⟩

/-- **`tables()` is the statement's `tables`**, table by table. -/
theorem tablesRust_rel : List.Forall₂ TableRust.Rel tablesRust tables :=
  .cons (rel_arith 0 (by norm_num) false) <| .cons (rel_arith 1 (by norm_num) true) <|
    .cons rel_set <| .cons rel_deref <| .cons rel_jump <| .cons rel_keccak .nil


end TablesEq

/-! ## `stack_offsets`'s bounds (`multilinear.rs`) -/

section StackOffsets

private theorem sum_map_range_getD (sizes : List ℕ) :
    ((List.range sizes.length).map fun i ↦ 2 ^ sizes.getD i 0).sum = (sizes.map (2 ^ ·)).sum := by
  congr 1
  apply List.ext_getElem (by simp)
  intro n h1 h2
  simp only [List.length_map, List.length_range] at h1
  simp [List.getElem?_eq_getElem h1]

theorem stackOffsetsRust_length (sizes : List ℕ) :
    (stackOffsetsRust sizes).1.length = sizes.length := by
  have hstep : ∀ size st i, (stackStep sizes size st i).1.length = st.1.length := by
    intro size st i
    unfold stackStep
    split <;> simp
  have hfold : ∀ {β : Type} (f : List (BitVec 64) × BitVec 64 → β → List (BitVec 64) × BitVec 64),
      (∀ st b, (f st b).1.length = st.1.length) →
      ∀ (l : List β) st, (l.foldl f st).1.length = st.1.length := by
    intro β f hf l
    induction l with
    | nil => intro st; rfl
    | cons b l ih => intro st; rw [List.foldl_cons, ih, hf]
  have hpass : ∀ st size, (stackPass sizes st size).1.length = st.1.length :=
    fun st size ↦ hfold _ (fun st i ↦ hstep size st i) _ st
  simp only [stackOffsetsRust, hfold _ hpass, List.length_replicate]

private theorem stackFold_le (size : ℕ → ℕ) : ∀ (Q o : List ℕ) (t : ℕ), (∀ x ∈ o, x ≤ t) →
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

/-- Every offset is at most the total. -/
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

end StackOffsets

/-! ## `qkeccak_slot`, `column_kappas`, `stack` -/

/-- `KECCAK_DEPTH`. -/
def keccakDepthRust : ℕ := 12

/-- `QKECCAK_SLOTS = STATE_LANES * (ROUNDS / KECCAK_DEPTH)`, a constant. -/
def qkeccakSlotsRust : ℕ := stateLanesRust * (24 / keccakDepthRust)

/-- `QKECCAK_SPARE = (1 << log2_ceil(QKECCAK_SLOTS)) - QKECCAK_SLOTS`, a constant. -/
def qkeccakSpareRust : ℕ :=
  2 ^ log2CeilRust (BitVec.ofNat 64 qkeccakSlotsRust) - qkeccakSlotsRust

/-- `spare_local(k)`. -/
def spareLocalRust (k : ℕ) : ℕ := if k < keccakInRust then k else keccakCntRust + (k - keccakInRust)

/-- `qkeccak_slot(column)`: past `KECCAK`'s base (`checked_sub`), the spare slot whose column it
is (`find`), else an input lane's slot. -/
def qkeccakSlotRust (column : ℕ) : Option ℕ :=
  let base := globalColumnBasesRust.getD opKeccakRust 0
  if column < base then none
  else
    let loc := column - base
    match (List.range qkeccakSpareRust).find? (fun k ↦ spareLocalRust k = loc) with
    | some k => some (qkeccakSlotsRust + k)
    | none => if keccakInRust ≤ loc ∧ loc < keccakOutRust then some (loc - keccakInRust) else none

/-- `is_output_lane(column)`. -/
def isOutputLaneRust (column : ℕ) : Bool :=
  let base := globalColumnBasesRust.getD opKeccakRust 0
  decide (base + keccakOutRust ≤ column ∧ column < base + keccakOutRust + stateLanesRust)

/-- `TABLE_LOG_FLOORS`. -/
def tableLogFloorsRust : List ℕ := [0, 0, 0, 0, 0, 9]

/-- `keccak_shape(table_log_heights)`. -/
def keccakShapeOf (heights : List ℕ) : KeccakShape :=
  ⟨heights.getD opKeccakRust 0, keccakDepthRust⟩

/-- `column_kappas(tables, log_memory, log_bytecode, table_log_heights)`. -/
def columnKappasRust (tables : List TableRust) (logMemory logBytecode : ℕ) (heights : List ℕ) :
    List ℕ :=
  let keccak := keccakShapeOf heights
  tables.foldl (fun kappas t ↦ kappas ++ List.replicate t.width (heights.getD t.opcode 0))
    [logMemory, logMemory, logMemory, logBytecode, keccak.logSteps + keccak.slotBits]

/-- `stacked_blocks(columns)`. -/
def stackedBlocksRust (columns : ℕ) : List ℕ :=
  (List.range columns).filter fun c ↦ (qkeccakSlotRust c).isNone && !isOutputLaneRust c

/-- `stack(kappas)`: each column's offset, `None` for one with no block of its own, and the
stack's log size, at least `MIN_STACKED_LOG`. -/
def stackRust (kappas : List ℕ) : List (Option (BitVec 64)) × ℕ :=
  let blocks := stackedBlocksRust kappas.length
  let stacked := stackOffsetsRust (blocks.map (kappas.getD · 0))
  let offsets := (blocks.zip stacked.1).foldl
    (fun offsets (c, offset) ↦ offsets.set c (some offset))
    (List.replicate kappas.length none)
  (offsets, max 16 stacked.2)

/-- `min_execution_stacked_log(log_bytecode)`. -/
def minExecutionStackedLogRust (logBytecode : ℕ) : ℕ :=
  (stackRust (columnKappasRust tablesRust 1 logBytecode tableLogFloorsRust)).2

/-! ## `build_layout` -/

/-- `Layout`, but for the bytecode it borrows (its callers pass it alongside). -/
structure LayoutRust where
  /-- `log_memory`. -/
  logMemory : ℕ
  /-- `log_bytecode`. -/
  logBytecode : ℕ
  /-- `tables`. -/
  tables : List TableRust
  /-- `push`. -/
  push : List BusBlock
  /-- `pull`. -/
  pull : List BusBlock
  /-- `count`. -/
  count : List BusBlock
  /-- `placements`. -/
  placements : List (Option PlacementRust)
  /-- `stack_log`. -/
  stackLog : ℕ
  /-- `table_log_heights`. -/
  tableLogHeights : List ℕ
  /-- `keccak`. -/
  keccak : KeccakShape

/-- `Layout::committed(column)`: a column nothing commits is refused (`CommittedSize`). -/
def LayoutRust.committed (l : LayoutRust) (column : ℕ) : Option PlacementRust :=
  l.placements.getD column none

/-- The loop over the tables: each table's push, pull and count blocks at its height and rows. -/
def busBlocksRust (tables : List TableRust) (heights : List ℕ) (tableRows : List (BitVec 64)) :
    List BusBlock × List BusBlock × List BusBlock :=
  ((tables.zip heights).zip tableRows).foldl (fun acc ((table, height), rows) ↦
    let block := fun (coordinates : List Form) ↦
      ({ logRows := height, rows := rows.toNat, coordinates, owner := table.opcode } : BusBlock)
    (acc.1 ++ table.flushes.push.map block, acc.2.1 ++ table.flushes.pull.map block,
      acc.2.2 ++ table.countColumns.map fun l ↦ block [colRust l 0])) ([], [], [])

/-- `build_layout`'s `placement` closure, at `(kappa, column)`: the outer `none` is its `Err`. -/
def placementRust (offsets : List (Option (BitVec 64))) (kc : ℕ × ℕ) :
    Option (Option PlacementRust) :=
  match qkeccakSlotRust kc.2 with
  | some slot => (offsets.getD 4 none).map fun offset ↦
      some ⟨kc.1, offset + (BitVec.ofNat 64 slot <<< (kc.1 % 64))⟩
  | none =>
    if isOutputLaneRust kc.2 then some none
    else (offsets.getD kc.2 none).map fun offset ↦ some ⟨kc.1, offset⟩

/-- `build_layout(bytecode, log_memory, table_rows)`, the bytecode by its length. -/
def buildLayoutRust (bytecodeLen : ℕ) (logMemory : BitVec 64) (tableRows : List (BitVec 64)) :
    Option LayoutRust := do
  let logLength ← log2StrictRust (BitVec.ofNat 64 bytecodeLen)
  if 1#64 ≤ logMemory ∧ logMemory ≤ 30#64 ∧ (tableRows.all fun rows ↦ rows ≤ 1#64 <<< 30) ∧
      4 ≤ logLength ∧ logLength ≤ 34 then
    let logBytecode := logLength - 4
    let heights := (tableRows.zip tableLogFloorsRust).map fun (rows, floor) ↦
      max (log2CeilRust rows) floor
    let blocks := busBlocksRust tablesRust heights tableRows
    let kappas := columnKappasRust tablesRust logMemory.toNat logBytecode heights
    let stacked := stackRust kappas
    let placements ← kappas.zipIdx.mapM (placementRust stacked.1)
    pure ⟨logMemory.toNat, logBytecode, tablesRust, blocks.1, blocks.2.1, blocks.2.2, placements,
      stacked.2, heights, keccakShapeOf heights⟩
  else none

/-- A bus block by value. -/
def busBlockDen (b : BusBlock) : ℕ × ℕ × List ((ℕ → E) → E) × ℕ :=
  (b.logRows, b.rows, Forms.den b.coordinates, b.owner)

/-- The Rust layout is the statement's: the same sizes, placements and stack, blocks by value. -/
structure LayoutRust.Rel (l : LayoutRust) (L : Layout) : Prop where
  logMemory : l.logMemory = L.logMemory
  logBytecode : l.logBytecode = L.logBytecode
  push : l.push.map busBlockDen = L.push.map busBlockDen
  pull : l.pull.map busBlockDen = L.pull.map busBlockDen
  count : l.count.map busBlockDen = L.count.map busBlockDen
  placements : l.placements.map (Option.map PlacementRust.toSpec) = L.placements
  stackLog : l.stackLog = L.stackLog
  heights : l.tableLogHeights = L.tableLogHeights
  tables : l.tables = tablesRust
  keccak : l.keccak = keccakShapeOf l.tableLogHeights

/-! ## `build_layout` is the statement's `buildLayout` -/

section BuildLayoutEq

private theorem find?_range_spare (l : ℕ) :
    ∀ n ≤ 15, (List.range n).find? (fun k ↦ decide (spareLocalRust k = l)) =
      if l < n then some l else none
  | 0, _ => by simp
  | n + 1, hn => by
    rw [List.range_succ, List.find?_append, find?_range_spare l n (by omega)]
    have hs : spareLocalRust n = n := by
      rw [spareLocalRust, ite_eq_left (show n < keccakInRust by
        simp only [keccakInRust, KeccakCol.len]; omega)]
    by_cases h : l < n
    · simp [h, show l < n + 1 by omega]
    · by_cases h' : l = n
      · subst h'; simp [hs]
      · simp [h, hs, show ¬ l < n + 1 by omega, Ne.symm h']

private theorem find?_range14 (l : ℕ) :
    (List.range 14).find? (fun k ↦ decide (spareLocalRust k = l)) =
      if l < 14 then some l else none :=
  find?_range_spare l 14 (by norm_num)

private theorem idxOf?_range14 (l : ℕ) :
    (List.range 14).idxOf? l = if l < 14 then some l else none := by
  by_cases h : l < 14
  · rw [ite_eq_left h]
    interval_cases l <;> rfl
  · rw [ite_eq_right h, List.idxOf?_eq_none_iff, List.mem_range]
    exact h

/-- **`qkeccak_slot` is `keccakSlot`.** -/
theorem qkeccakSlotRust_eq (c : ℕ) : qkeccakSlotRust c = keccakSlot c := by
  have hb : globalColumnBasesRust.getD opKeccakRust 0 = 66 := by decide +kernel
  have hb' : globalColumnBases.getD opKeccak 0 = 66 := by decide +kernel
  have hs : qkeccakSpareRust = 14 := by rw [qkeccakSpareRust, log2CeilRust_eq]; decide +kernel
  have hc : keccakCommitted.take qkeccakSpare = List.range 14 := by decide +kernel
  have hi : keccakIn = 15 := by decide +kernel
  have hq : qkeccakSlots = 50 := by decide +kernel
  unfold qkeccakSlotRust keccakSlot keccakSlotOf
  dsimp only
  rw [hb, hb', hs, hc, hi, hq, find?_range14, idxOf?_range14]
  by_cases h : c < 66
  · simp [h]
  · have h66 : 66 ≤ c := by omega
    have hq50 : qkeccakSlotsRust = 50 := rfl
    simp only [h, h66, ↓reduceIte, hq50, keccakInRust, KeccakCol.len, keccakOutRust,
      stateLanesRust]
    by_cases hl : c - 66 < 14
    · simp only [hl, ↓reduceIte, show ¬ (15 ≤ c - 66 ∧ c - 66 < 15 + 25) by omega,
        Option.map_some]
    · simp only [hl, ↓reduceIte, Option.map_none]
      by_cases h2 : 15 ≤ c - 66 ∧ c - 66 < 15 + 25 <;> simp [h2]

theorem mem_keccakOutputColumns (c : ℕ) : c ∈ keccakOutputColumns ↔ 106 ≤ c ∧ c < 131 := by
  have hb' : globalColumnBases.getD opKeccak 0 = 66 := by decide +kernel
  have ho : keccakOut = 40 := by decide +kernel
  simp only [keccakOutputColumns, hb', ho, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨l, hl, rfl⟩
    omega
  · intro h
    exact ⟨c - 106, by omega, by omega⟩

theorem isOutputLaneRust_eq (c : ℕ) : isOutputLaneRust c = decide (c ∈ keccakOutputColumns) := by
  have hb : globalColumnBasesRust.getD opKeccakRust 0 = 66 := by decide +kernel
  rw [isOutputLaneRust, hb, decide_eq_decide, mem_keccakOutputColumns]
  simp [keccakOutRust, keccakInRust, KeccakCol.len, stateLanesRust]

theorem foldl_append_eq_flatMap {α β : Type} (f : α → List β) :
    ∀ (l : List α) (init : List β), l.foldl (fun acc x ↦ acc ++ f x) init = init ++ l.flatMap f
  | [], _ => by simp
  | x :: l, init => by
    rw [List.foldl_cons, foldl_append_eq_flatMap f l, List.flatMap_cons, List.append_assoc]

theorem flatMap_forall₂ {α α' β : Type} {R : α → α' → Prop} {f : α → List β} {g : α' → List β}
    (h : ∀ a b, R a b → f a = g b) :
    ∀ {l : List α} {l' : List α'}, List.Forall₂ R l l' → l.flatMap f = l'.flatMap g
  | _, _, .nil => rfl
  | _, _, .cons hab hl => by rw [List.flatMap_cons, List.flatMap_cons, h _ _ hab,
      flatMap_forall₂ h hl]

/-- **`column_kappas` is `columnKappas`.** -/
theorem columnKappasRust_eq (logMemory logBytecode : ℕ) (heights : List ℕ) :
    columnKappasRust tablesRust logMemory logBytecode heights =
      columnKappas logMemory logBytecode heights := by
  unfold columnKappasRust columnKappas
  rw [foldl_append_eq_flatMap, keccakShapeOf, keccakDepthRust, slotBits_twelve,
    flatMap_forall₂ (fun t T h ↦ by rw [h.width, h.opcode]) tablesRust_rel]
  rfl

theorem tableLogHeightsRust_eq (tableRows : List (BitVec 64)) :
    (tableRows.zip tableLogFloorsRust).map (fun (rows, floor) ↦ max (log2CeilRust rows) floor) =
      List.zipWith (fun rows floor ↦ max (log2Ceil rows) floor) (tableRows.map BitVec.toNat)
        tableLogFloors := by
  rw [show tableLogFloorsRust = tableLogFloors from rfl]
  generalize tableLogFloors = floors
  induction tableRows generalizing floors with
  | nil => simp
  | cons r rs ih =>
    cases floors with
    | nil => simp
    | cons f fs =>
      rw [List.zip_cons_cons, List.map_cons, List.map_cons, List.zipWith_cons_cons, ih fs]
      dsimp only
      rw [log2CeilRust_eq]

theorem foldl_blocks {γ : Type} (f g h : γ → List BusBlock) :
    ∀ (l : List γ) (a b c : List BusBlock),
      l.foldl (fun acc x ↦ (acc.1 ++ f x, acc.2.1 ++ g x, acc.2.2 ++ h x)) (a, b, c) =
        (a ++ l.flatMap f, b ++ l.flatMap g, c ++ l.flatMap h)
  | [], _, _, _ => by simp
  | x :: l, a, b, c => by
    rw [List.foldl_cons, foldl_blocks f g h l]
    simp [List.append_assoc]

private theorem zip_rel : ∀ {ts : List TableRust} {Ts : List Table},
    List.Forall₂ TableRust.Rel ts Ts →
    ∀ (hs : List ℕ) (rs : List (BitVec 64)),
      List.Forall₂ (fun (x : (TableRust × ℕ) × BitVec 64) (y : Table × ℕ × ℕ) ↦
        TableRust.Rel x.1.1 y.1 ∧ x.1.2 = y.2.1 ∧ x.2.toNat = y.2.2)
        ((ts.zip hs).zip rs) (List.zip Ts (List.zip hs (rs.map BitVec.toNat)))
  | _, _, .nil, _, _ => by simp
  | _, _, .cons _ _, [], _ => by simp
  | _, _, .cons _ _, _ :: _, [] => by simp
  | _, _, .cons hab hl, h :: hs, r :: rs => by
    simp only [List.zip_cons_cons, List.map_cons]
    exact .cons ⟨hab, rfl, rfl⟩ (zip_rel hl hs rs)

/-- **The tables' blocks are the statement's**, by value. -/
theorem busBlocksRust_den (heights : List ℕ) (tableRows : List (BitVec 64)) :
    (busBlocksRust tablesRust heights tableRows).1.map busBlockDen =
        (busBlocks heights (tableRows.map BitVec.toNat)).1.map busBlockDen ∧
      (busBlocksRust tablesRust heights tableRows).2.1.map busBlockDen =
        (busBlocks heights (tableRows.map BitVec.toNat)).2.1.map busBlockDen ∧
      (busBlocksRust tablesRust heights tableRows).2.2.map busBlockDen =
        (busBlocks heights (tableRows.map BitVec.toNat)).2.2.map busBlockDen := by
  unfold busBlocksRust busBlocks
  rw [foldl_blocks]
  have hz := zip_rel tablesRust_rel heights tableRows
  simp only [List.nil_append, List.map_flatMap]
  have htuple : ∀ (l l' : List (List Form)) (a b o : ℕ), l.map Forms.den = l'.map Forms.den →
      l.map (fun c ↦ (a, b, Forms.den c, o)) = l'.map (fun c ↦ (a, b, Forms.den c, o)) := by
    intro l l' a b o h
    have := congrArg (List.map fun d ↦ (a, b, d, o)) h
    simpa [List.map_map, Function.comp_def] using this
  refine ⟨flatMap_forall₂ ?_ hz, flatMap_forall₂ ?_ hz, flatMap_forall₂ ?_ hz⟩ <;>
    rintro ⟨⟨t, h⟩, r⟩ ⟨T, h', n⟩ ⟨hr, rfl, rfl⟩ <;> dsimp only at hr ⊢ <;>
    simp only [List.map_map, Function.comp_def, busBlockDen, hr.opcode]
  · exact htuple _ _ _ _ _ (congrArg Prod.fst hr.flushes)
  · exact htuple _ _ _ _ _ (congrArg Prod.snd hr.flushes)
  · rw [hr.countColumns]
    apply List.map_congr_left
    intro l _
    simp [Forms.den]

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

private theorem sum_pow_le (l : List ℕ) (b : ℕ) (h : ∀ k ∈ l, k ≤ b) :
    (l.map (2 ^ ·)).sum ≤ l.length * 2 ^ b := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (h a (by simp))
    have h2 := ih (fun k hk ↦ h k (by simp [hk]))
    rw [Nat.succ_mul]
    omega

private theorem bitvec_add_shift (a : BitVec 64) (s k : ℕ) (hs : s < 64) (hk : k ≤ 40)
    (ha : a.toNat < 2 ^ 60) :
    (a + (BitVec.ofNat 64 s <<< (k % 64))).toNat = a.toNat + s * 2 ^ k := by
  have hk' : k % 64 = k := Nat.mod_eq_of_lt (by omega)
  have hp : 2 ^ k ≤ 2 ^ 40 := Nat.pow_le_pow_right (by norm_num) hk
  have hsk : s * 2 ^ k < 2 ^ 46 := by
    calc s * 2 ^ k < 64 * 2 ^ 40 := by
          apply Nat.mul_lt_mul_of_lt_of_le hs hp (by positivity)
      _ = 2 ^ 46 := by norm_num
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, hk', BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (show s < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show s * 2 ^ k < 2 ^ 64 by omega), Nat.mod_eq_of_lt (by omega)]

private theorem keccakSlot_lt {c s : ℕ} (h : keccakSlot c = some s) : s < 64 := by
  rw [← qkeccakSlotRust_eq] at h
  unfold qkeccakSlotRust at h
  dsimp only at h
  have hb : globalColumnBasesRust.getD opKeccakRust 0 = 66 := by decide +kernel
  have hs : qkeccakSpareRust = 14 := by rw [qkeccakSpareRust, log2CeilRust_eq]; decide +kernel
  rw [hb, hs, find?_range14] at h
  split_ifs at h <;> simp_all [qkeccakSlotsRust, stateLanesRust, keccakDepthRust, keccakInRust,
    keccakOutRust, KeccakCol.len] <;> omega

private theorem keccakSlot_ge {c s : ℕ} (h : keccakSlot c = some s) : 66 ≤ c := by
  have hb' : globalColumnBases.getD opKeccak 0 = 66 := by decide +kernel
  unfold keccakSlot at h
  rw [hb'] at h
  split_ifs at h with hc
  exact hc

private theorem mapM_some_map {α β γ : Type} [Inhabited β] (f : α → Option β) (g : β → γ)
    (s : α → γ) (l : List α) (h : ∀ x ∈ l, ∃ y, f x = some y ∧ g y = s x) :
    ∃ ys, l.mapM f = some ys ∧ ys.map g = l.map s := by
  refine ⟨_, mapM_eq_some_map f (fun x ↦ (f x).getD default) l fun x hx ↦ ?_, ?_⟩
  · obtain ⟨y, hy, -⟩ := h x hx
    rw [hy, Option.getD_some]
  · rw [List.map_map]
    refine List.map_congr_left fun x hx ↦ ?_
    obtain ⟨y, hy, hg⟩ := h x hx
    simp [hy, hg]

/-- **`stack` and the placements are the statement's `placementsOf`**, for at most `1024` columns
of at most `2^40` words: the placements exist (no `CommittedSize`), and the stack's log size. -/
theorem stackRust_spec (kappas : List ℕ) (hb : ∀ k ∈ kappas, k ≤ 40)
    (hl : kappas.length ≤ 1024) :
    (∃ ps, kappas.zipIdx.mapM (placementRust (stackRust kappas).1) = some ps ∧
      ps.map (Option.map PlacementRust.toSpec) = (placementsOf kappas).1) ∧
      (stackRust kappas).2 = (placementsOf kappas).2 := by
  have hblocks : stackedBlocksRust kappas.length = (List.range kappas.length).filter fun c ↦
      (keccakSlot c).isNone ∧ c ∉ keccakOutputColumns := by
    apply List.filter_congr
    intro c _
    rw [qkeccakSlotRust_eq, isOutputLaneRust_eq]
    cases (keccakSlot c).isNone <;> simp
  unfold stackRust placementsOf
  simp only [hblocks]
  generalize hB : (List.range kappas.length).filter (fun c ↦
    (keccakSlot c).isNone ∧ c ∉ keccakOutputColumns) = blocks
  have hnd : blocks.Nodup := hB ▸ List.nodup_range.filter _
  have hlt : ∀ c ∈ blocks, c < kappas.length := by
    intro c hc
    rw [← hB, List.mem_filter, List.mem_range] at hc
    exact hc.1
  have hmem : ∀ c, c ∈ blocks ↔ c < kappas.length ∧ keccakSlot c = none ∧
      c ∉ keccakOutputColumns := by
    intro c
    rw [← hB, List.mem_filter, List.mem_range]
    simp
  have hbk : ∀ k ∈ blocks.map (fun c ↦ kappas.getD c 0), k ≤ 40 := by
    intro k hk
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hk
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hlt c hc), Option.getD_some]
    exact hb _ (List.getElem_mem _)
  have hblen : blocks.length ≤ 1024 :=
    (hB ▸ List.length_filter_le _ _).trans (by simpa using hl)
  have hsum : ((blocks.map fun c ↦ kappas.getD c 0).map (2 ^ ·)).sum ≤ 1024 * 2 ^ 40 :=
    (sum_pow_le _ 40 hbk).trans (Nat.mul_le_mul_right _ (by simpa using hblen))
  obtain ⟨hoff, htot⟩ := stackOffsetsRust_eq (blocks.map fun c ↦ kappas.getD c 0)
    (by have : 1024 * 2 ^ 40 < 2 ^ 64 := by norm_num
        omega)
  have hRlen := stackOffsetsRust_length (blocks.map fun c ↦ kappas.getD c 0)
  have hSle := stackOffsets_le (blocks.map fun c ↦ kappas.getD c 0)
  generalize stackOffsetsRust (blocks.map fun c ↦ kappas.getD c 0) = R at hoff htot hRlen
  generalize stackOffsets (blocks.map fun c ↦ kappas.getD c 0) = S at hoff htot hSle
  obtain ⟨R1, R2⟩ := R
  obtain ⟨S1, S2⟩ := S
  simp only [List.length_map] at hoff htot hRlen hSle ⊢
  have hoffs : ∀ c, ((blocks.zip R1).foldl (fun offsets co ↦ offsets.set co.1 (some co.2))
      (List.replicate kappas.length none)).getD c none =
      if c ∈ blocks then some (R1.getD (blocks.idxOf c) 0) else none := by
    intro c
    have := foldl_set_zip_getD (none : Option (BitVec 64)) blocks (R1.map some)
      (List.replicate kappas.length none) hnd (by simpa using hRlen) (by simpa using hlt) c
    rw [List.zip_map_right, List.foldl_map] at this
    simp only [Prod.map_fst, Prod.map_snd, id_eq] at this
    rw [this]
    split
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
      rename_i hc
      rw [List.getElem?_eq_getElem (by rw [hRlen]; exact List.idxOf_lt_length_of_mem hc)]
      rfl
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
      split <;> rfl
  have hR : ∀ c, (R1.getD c 0).toNat = S1.getD c 0 := by
    intro c
    rw [← hoff]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases R1[c]? <;> rfl
  have hS : ∀ c, S1.getD c 0 ≤ 1024 * 2 ^ 40 := by
    intro c
    rw [List.getD_eq_getElem?_getD]
    cases h : S1[c]? with
    | none => simp
    | some x => exact (hSle x (List.mem_of_getElem? h)).trans hsum
  generalize hO : (blocks.zip R1).foldl (fun offsets co ↦ offsets.set co.1 (some co.2))
    (List.replicate kappas.length none) = O at hoffs
  refine ⟨?_, by rw [htot]; rfl⟩
  refine mapM_some_map _ _ _ kappas.zipIdx ?_
  rintro ⟨kappa, column⟩ hkc
  have hcl : column < kappas.length := by have := (List.mem_zipIdx hkc).2.1; omega
  have hk : kappa ≤ 40 := hb kappa (List.mem_zipIdx' hkc |>.2 ▸ List.getElem_mem _)
  simp only [placementRust, qkeccakSlotRust_eq, isOutputLaneRust_eq]
  cases hs : keccakSlot column with
  | some slot =>
    have h4 : 4 ∈ blocks := (hmem 4).mpr ⟨by have := keccakSlot_ge hs; omega, by decide +kernel,
      by rw [mem_keccakOutputColumns]; omega⟩
    rw [hoffs 4, ite_eq_left h4]
    refine ⟨_, rfl, ?_⟩
    simp only [Option.map_some, PlacementRust.toSpec, Option.some.injEq, Placement.mk.injEq,
      true_and]
    rw [bitvec_add_shift _ _ _ (keccakSlot_lt hs) hk (by
      rw [hR]; have := hS (blocks.idxOf 4); have : 1024 * 2 ^ 40 < 2 ^ 60 := by norm_num
      omega), hR]
    rfl
  | none =>
    by_cases ho : column ∈ keccakOutputColumns
    · exact ⟨none, by simp [ho], by simp [ho]⟩
    · have hc : column ∈ blocks := (hmem column).mpr ⟨hcl, hs, ho⟩
      simp only [ho, decide_false, Bool.false_eq_true, ↓reduceIte, hoffs column, hc,
        Option.map_some]
      refine ⟨_, rfl, ?_⟩
      simp only [Option.map_some, PlacementRust.toSpec, hR]

end BuildLayoutEq

section BuildLayoutSpec

theorem log2Ceil_le {n k : ℕ} (h : n ≤ 2 ^ k) : log2Ceil n ≤ k := by
  unfold log2Ceil bitLength
  split
  · omega
  · next h0 =>
    have := (Nat.log2_lt h0).mpr (show n - 1 < 2 ^ k by have := Nat.one_le_two_pow (n := k); omega)
    omega

private theorem getD_le {l : List ℕ} {b : ℕ} (h : ∀ x ∈ l, x ≤ b) (i : ℕ) : l.getD i 0 ≤ b := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : l[i]? with
  | none => simp
  | some x => exact h x (List.mem_of_getElem? hi)

theorem columnKappas_le (lm lb : ℕ) (H : List ℕ) (hm : lm ≤ 30) (hb : lb ≤ 30)
    (hH : ∀ x ∈ H, x ≤ 30) : ∀ k ∈ columnKappas lm lb H, k ≤ 40 := by
  have hq : qkeccakSlotBits = 6 := by decide +kernel
  intro k hk
  simp only [columnKappas, hq, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatMap, List.mem_replicate] at hk
  have h5 := getD_le hH opKeccak
  rcases hk with (rfl | rfl | rfl | rfl | rfl) | ⟨t, _, _, rfl⟩
  all_goals first | omega | exact (getD_le hH _).trans (by norm_num)

theorem columnKappas_length (lm lb : ℕ) (H : List ℕ) :
    (columnKappas lm lb H).length = 158 := by
  simp only [columnKappas, List.length_append, List.length_cons, List.length_nil,
    List.length_flatMap, List.length_replicate]
  decide +kernel

theorem tableLogHeights_le (tableRows : List ℕ) (h : ∀ r ∈ tableRows, r ≤ 2 ^ 30) :
    ∀ x ∈ List.zipWith (fun rows floor ↦ max (log2Ceil rows) floor) tableRows tableLogFloors,
      x ≤ 30 := by
  have hf : ∀ f ∈ tableLogFloors, f ≤ 9 := by decide
  generalize tableLogFloors = floors at hf
  induction tableRows generalizing floors with
  | nil => simp
  | cons r rs ih =>
    cases floors with
    | nil => simp
    | cons f fs =>
      intro x hx
      rw [List.zipWith_cons_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact max_le (log2Ceil_le (h r (by simp))) (by have := hf f (by simp); omega)
      · exact ih (fun r' hr' ↦ h r' (by simp [hr'])) fs (fun f' hf' ↦ hf f' (by simp [hf'])) x hx

/-- **`build_layout` is `buildLayout`**, on the verifier's `N_TABLES` row counts: it fails exactly
where the statement's does, and otherwise its layout is the statement's (`LayoutRust.Rel`). -/
theorem buildLayoutRust_spec (bytecode : List K) (logMemory : BitVec 64)
    (tableRows : List (BitVec 64)) (hlen : bytecode.length < 2 ^ 64)
    (hrows : tableRows.length = 6) :
    match buildLayout bytecode logMemory.toNat (tableRows.map BitVec.toNat) with
    | none => buildLayoutRust bytecode.length logMemory tableRows = none
    | some L => ∃ l, buildLayoutRust bytecode.length logMemory tableRows = some l ∧ l.Rel L := by
  have hshift : (1#64 <<< 30).toNat = 2 ^ 30 := by decide
  have hcond : ∀ logLength : ℕ,
      (1#64 ≤ logMemory ∧ logMemory ≤ 30#64 ∧ (tableRows.all fun rows ↦ rows ≤ 1#64 <<< 30) = true ∧
        4 ≤ logLength ∧ logLength ≤ 34) ↔
      (busBits ≤ logLength ∧ 1 ≤ logMemory.toNat ∧ logMemory.toNat ≤ 30 ∧
        ((tableRows.map BitVec.toNat).all fun x ↦ decide (x ≤ 2 ^ 30)) = true ∧
        logLength - busBits ≤ 30 ∧ (tableRows.map BitVec.toNat).length = tables.length) := by
    intro logLength
    have ht : tables.length = 6 := rfl
    have hall : (tableRows.all fun rows ↦ rows ≤ 1#64 <<< 30) =
        ((tableRows.map BitVec.toNat).all fun x ↦ decide (x ≤ 2 ^ 30)) := by
      rw [List.all_map]
      congr 1
    rw [hall, List.length_map, hrows, ht, busBits, BitVec.le_def, BitVec.le_def]
    simp only [BitVec.toNat_ofNat]
    constructor
    · rintro ⟨h1, h2, h3, h4, h5⟩
      exact ⟨h4, h1, h2, h3, by omega, trivial⟩
    · rintro ⟨h1, h2, h3, h4, h5, -⟩
      exact ⟨h2, h3, h4, h1, by omega⟩
  unfold buildLayout buildLayoutRust
  rw [log2StrictRust_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen]
  cases log2Strict bytecode.length with
  | none => rfl
  | some logLength =>
    simp only [Option.bind_eq_bind, Option.bind_some]
    by_cases hc : busBits ≤ logLength ∧ 1 ≤ logMemory.toNat ∧ logMemory.toNat ≤ 30 ∧
        ((tableRows.map BitVec.toNat).all fun x ↦ decide (x ≤ 2 ^ 30)) = true ∧
        logLength - busBits ≤ 30 ∧ (tableRows.map BitVec.toNat).length = tables.length
    · rw [ite_eq_left hc, ite_eq_left ((hcond logLength).mpr hc)]
      dsimp only
      rw [tableLogHeightsRust_eq, columnKappasRust_eq]
      have hrows' : ∀ r ∈ tableRows.map BitVec.toNat, r ≤ 2 ^ 30 := by
        have := hc.2.2.2.1
        simp only [List.all_eq_true, decide_eq_true_eq] at this
        exact this
      have hH := tableLogHeights_le _ hrows'
      have hb := columnKappas_le logMemory.toNat (logLength - 4) _ hc.2.2.1 (by
        have := hc.2.2.2.2.1; simp only [busBits] at this; omega) hH
      obtain ⟨⟨ps, hps, hpm⟩, hsl⟩ := stackRust_spec _ hb (by rw [columnKappas_length]; norm_num)
      rw [hps]
      obtain ⟨hpush, hpull, hcount⟩ := busBlocksRust_den
        (List.zipWith (fun rows floor ↦ max (log2Ceil rows) floor) (tableRows.map BitVec.toNat)
          tableLogFloors) tableRows
      refine ⟨_, rfl, ⟨rfl, rfl, hpush, hpull, hcount, hpm, hsl, rfl, rfl, rfl⟩⟩
    · rw [ite_eq_right hc, ite_eq_right (fun h ↦ hc ((hcond logLength).mp h))]

end BuildLayoutSpec

/-- **`min_execution_stacked_log` is the stack of the smallest execution**: the least memory,
every table at its floor. -/
theorem minExecutionStackedLogRust_eq (logBytecode : ℕ) (h : logBytecode ≤ 30) :
    minExecutionStackedLogRust logBytecode =
      (placementsOf (columnKappas 1 logBytecode tableLogFloors)).2 := by
  rw [minExecutionStackedLogRust, columnKappasRust_eq]
  refine (stackRust_spec _ (columnKappas_le 1 logBytecode _ (by norm_num) h (by decide)) ?_).2
  rw [columnKappas_length]
  norm_num

end

end Rv64mc.Model
