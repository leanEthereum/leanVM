/-
  LeanVM.Protocol.ToArkLib.Flock.Circuit

  Boolean circuits of product gates over GF(2) whose linear wires are substituted away, as data:
  linear forms are bitsets, a gate is a pair of forms, and the circuit lowers to a block R1CS with
  `C = I`. Candidate for ArkLib.
-/

module

public import LeanVM.Protocol.ToArkLib.Flock.BlockR1CS
public import Mathlib.Data.ZMod.Basic

/-!
# Product-gate circuits

A Boolean circuit whose XOR wires are substituted into their consumers has one committed wire
per AND gate: position `k` of a block of `2 ^ m` positions holds the product of two GF(2) linear
forms of other positions. This is a rank-one constraint system `(A z) ∘ (B z) = z` whose rows are
the gates' forms.

* `Form m`, a linear form over the positions: a bitset, bit `j` set when position `j` is a term.
  `Form.eval L z` is its value on a Boolean block, the parity of the selected positions.
* `ProductCircuit m`: the constant position (holding `1`), the input positions, and the gates in
  evaluation order. `rowOf c k` is the row of position `k`: its gate if it has one, else
  `(1, 1)` at the constant, `(z_k, 1)` at an input, `(0, 0)` elsewhere.
* `toBlockR1CS R c`: the circuit as a `BlockR1CS` over any commutative ring, with naive walks.
* `traceF c inp` (a function) and `trace c inp` (a bitset, executable, `trace_getLsbD`): the
  honest block, the gates evaluated in order from the inputs and the constant.
* `Bounded c`: every gate reads only the inputs, the constant and earlier gates, and sits at a
  fresh position.

The two directions, over any nontrivial ring of characteristic two (`holds_iff_gates`):
`trace_satisfies` (the trace of a bounded circuit satisfies the R1CS and holds `1` at the
constant) and `holds_eq_trace` (a Boolean block satisfying it with `1` at the constant is the
trace of its own inputs), with `gates_of_holds` (it satisfies every recorded gate), and their
forms for a block known only to hold `0`/`1` entries (`gates_of_holds_isBool`,
`eq_trace_of_holds_isBool`).

Nothing here transcribes a source. ArkLib's `R1CS.relation` is the general relation with a third
matrix; an R1CS export of Clean circuits allocates a fresh signal per product, so its third matrix
is not the identity.
-/

namespace LeanVM.Protocol

open CompPoly

@[expose] public section

/-- `Holds` reads only the two matrices, not the walks that evaluate them: two blocks with the
same matrices and different walks have the same solutions. -/
theorem BlockR1CS.holds_congr {R : Type*} [CommRing R] {m : ℕ} {C C' : BlockR1CS R m}
    (hA : C.A = C'.A) (hB : C.B = C'.B) (z : CMlPolynomialEval R m) : C.Holds z ↔ C'.Holds z := by
  unfold BlockR1CS.Holds
  simp only [BlockR1CS.rows_fst, BlockR1CS.rows_snd, hA, hB]

namespace ProductCircuit

/-! ## Positions and forms -/

/-- A position of a block of `2 ^ m`. -/
abbrev Pos (m : ℕ) := Fin (2 ^ m)

/-- A linear form over GF(2) on the positions: bit `j` set means position `j` is a term. -/
abbrev Form (m : ℕ) := BitVec (2 ^ m)

variable {m : ℕ}

/-- The position `n`, reduced modulo the block size. -/
def pos (n : ℕ) : Pos m := ⟨n % 2 ^ m, Nat.mod_lt _ (Nat.two_pow_pos m)⟩

/-- The form of the single position `j`. -/
def Form.var (j : Pos m) : Form m := BitVec.twoPow _ j

/-- A Boolean in GF(2). -/
def toZ (b : Bool) : ZMod 2 := if b then 1 else 0

/-- The value of a form on a Boolean block, in GF(2): the sum of the selected positions. -/
def Form.evalZ (L : Form m) (z : Pos m → Bool) : ZMod 2 :=
  ∑ j : Pos m, if L.getLsbD j then toZ (z j) else 0

/-- The value of a form on a Boolean block. -/
def Form.eval (L : Form m) (z : Pos m → Bool) : Bool := decide (L.evalZ z = 1)

/-- Parity of a bitvector of width `2 ^ k`, by `k` halving steps. -/
def par : (k : ℕ) → BitVec (2 ^ k) → Bool
  | 0, x => x.getLsbD 0
  | k + 1, x => par k (x.setWidth (2 ^ k) ^^^ (x >>> 2 ^ k).setWidth (2 ^ k))

/-- The value of a form on a block given as a bitset: the parity of `L ∧ z`. -/
def Form.evalB (L z : Form m) : Bool := par m (L &&& z)

/-! ## Circuits -/

/-- A product gate: the two forms whose product the gate's position holds. -/
structure Gate (m : ℕ) where
  /-- The left form, the gate's row of `A`. -/
  a : Form m
  /-- The right form, the gate's row of `B`. -/
  b : Form m
  deriving Inhabited

end ProductCircuit

open ProductCircuit

/-- A block circuit of product gates: the constant position, the input positions, and the gates
in evaluation order, each at its position. -/
structure ProductCircuit (m : ℕ) where
  /-- The position holding `1`. -/
  cpos : Pos m
  /-- The input positions. -/
  inputs : Form m
  /-- The gates, in evaluation order. -/
  gates : Array (Pos m × Gate m)

namespace ProductCircuit

variable {m : ℕ}

/-- The row of position `k`: its gate (the first one, in evaluation order) if it has one; else
`(1, 1)` at the constant, `(z_k, 1)` at an input, `(0, 0)` elsewhere. -/
def rowOf (c : ProductCircuit m) (k : Pos m) : Gate m :=
  match c.gates.toList.lookup k with
  | some g => g
  | none =>
    if k = c.cpos then ⟨Form.var c.cpos, Form.var c.cpos⟩
    else if c.inputs.getLsbD k then ⟨Form.var k, Form.var c.cpos⟩
    else ⟨0, 0⟩

/-- The circuit as a block R1CS with naive walks. -/
def toBlockR1CS (R : Type*) [CommRing R] (c : ProductCircuit m) : BlockR1CS R m :=
  BlockR1CS.ofMatrices (fun k j ↦ (c.rowOf k).a.getLsbD j) (fun k j ↦ (c.rowOf k).b.getLsbD j)

/-! ## The honest block -/

/-- The block before any gate: `1` at the constant, the inputs at the input positions, `0`
elsewhere. -/
def initF (c : ProductCircuit m) (inp : Pos m → Bool) : Pos m → Bool :=
  fun j ↦ decide (j = c.cpos) || (c.inputs.getLsbD j && inp j)

/-- One gate: its position takes the product of its forms. -/
def stepF (z : Pos m → Bool) (kg : Pos m × Gate m) : Pos m → Bool :=
  Function.update z kg.1 (kg.2.a.eval z && kg.2.b.eval z)

/-- The honest block of the inputs `inp`: the gates evaluated in order. -/
def traceF (c : ProductCircuit m) (inp : Pos m → Bool) : Pos m → Bool :=
  c.gates.toList.foldl stepF (c.initF inp)

/-- Set bit `k` of a bitset to `b`. -/
def setBitB (z : Form m) (k : Pos m) (b : Bool) : Form m :=
  if b then z ||| Form.var k else z &&& ~~~(Form.var k)

/-- One gate, on bitsets. -/
def stepB (z : Form m) (kg : Pos m × Gate m) : Form m :=
  setBitB z kg.1 (kg.2.a.evalB z && kg.2.b.evalB z)

/-- The block before any gate, as a bitset. -/
def initB (c : ProductCircuit m) (inp : Form m) : Form m := (c.inputs &&& inp) ||| Form.var c.cpos

/-- The honest block of the inputs `inp`, as a bitset: the executable `traceF`. -/
def trace (c : ProductCircuit m) (inp : Form m) : Form m := c.gates.foldl stepB (c.initB inp)

/-! ## Bounded circuits -/

/-- `L` mentions only positions of `avail`. -/
def Sub (L avail : Form m) : Prop := L &&& ~~~avail = 0

instance (L avail : Form m) : Decidable (Sub L avail) := inferInstanceAs (Decidable (_ = _))

/-- A schedule is bounded from the available positions `avail`: each gate reads only available
positions and sits at a fresh one, which becomes available. -/
def BoundedFrom : Form m → List (Pos m × Gate m) → Prop
  | _, [] => True
  | avail, (k, g) :: rest =>
    Sub g.a avail ∧ Sub g.b avail ∧ avail.getLsbD k = false ∧
      BoundedFrom (avail ||| Form.var k) rest

instance decBoundedFrom :
    (avail : Form m) → (L : List (Pos m × Gate m)) → Decidable (BoundedFrom avail L)
  | _, [] => isTrue trivial
  | avail, (k, _) :: rest =>
    have := decBoundedFrom (avail ||| Form.var k) rest
    inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- Every gate reads only the inputs, the constant and earlier gates, and the gate positions are
fresh: distinct, not inputs, not the constant. -/
def Bounded (c : ProductCircuit m) : Prop :=
  BoundedFrom (c.inputs ||| Form.var c.cpos) c.gates.toList

instance (c : ProductCircuit m) : Decidable c.Bounded :=
  inferInstanceAs (Decidable (BoundedFrom _ _))

/-! ## Boolean blocks over a ring -/

/-- A Boolean as `0` or `1` of a ring. -/
def ofBool (R : Type*) [CommRing R] (b : Bool) : R := if b then 1 else 0

/-- A Boolean block over a ring. -/
def liftBlock (R : Type*) [CommRing R] (z : Pos m → Bool) : CMlPolynomialEval R m :=
  Vector.ofFn fun k ↦ ofBool R (z k)

/-! ## Forms -/

theorem toZ_injective : Function.Injective toZ := by
  intro a b h
  cases a <;> cases b <;> simp_all [toZ]

theorem toZ_and (a b : Bool) : toZ (a && b) = toZ a * toZ b := by
  cases a <;> cases b <;> simp [toZ]

theorem toZ_xor (a b : Bool) : toZ (a ^^ b) = toZ a + toZ b := by
  cases a <;> cases b <;> decide

theorem toZ_eval (L : Form m) (z : Pos m → Bool) : toZ (L.eval z) = L.evalZ z := by
  unfold Form.eval toZ
  generalize L.evalZ z = x
  fin_cases x <;> rfl

/-- A form reads only the positions it selects. -/
theorem eval_congr {L : Form m} {z z' : Pos m → Bool}
    (h : ∀ j : Pos m, L.getLsbD j → z j = z' j) : L.eval z = L.eval z' := by
  have : L.evalZ z = L.evalZ z' := Finset.sum_congr rfl fun j _ ↦ by
    split_ifs with hj
    · rw [h j hj]
    · rfl
  rw [Form.eval, Form.eval, this]

@[simp] theorem eval_var (j : Pos m) (z : Pos m → Bool) : (Form.var j).eval z = z j := by
  apply toZ_injective
  rw [toZ_eval, Form.evalZ]
  simp only [Form.var, BitVec.getLsbD_twoPow, j.isLt, decide_true, Bool.true_and,
    decide_eq_true_eq, Fin.val_inj]
  rw [Finset.sum_ite_eq]
  simp

@[simp] theorem eval_zero (z : Pos m → Bool) : (0 : Form m).eval z = false := by
  apply toZ_injective
  rw [toZ_eval, Form.evalZ]
  simp [toZ]

/-- Forms are linear: the form of a sum evaluates to the sum. -/
theorem eval_xor (a b : Form m) (z : Pos m → Bool) :
    (a ^^^ b).eval z = (a.eval z ^^ b.eval z) := by
  apply toZ_injective
  rw [toZ_xor, toZ_eval, toZ_eval, toZ_eval, Form.evalZ, Form.evalZ, Form.evalZ,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [BitVec.getLsbD_xor]
  cases a.getLsbD j <;> cases b.getLsbD j <;> cases z j <;> decide

theorem getLsbD_var (k : Pos m) (j : ℕ) : (Form.var k).getLsbD j = decide ((k : ℕ) = j) := by
  simp [Form.var, BitVec.getLsbD_twoPow]

theorem pos_val {n : ℕ} (h : n < 2 ^ m) : ((pos n : Pos m) : ℕ) = n := Nat.mod_eq_of_lt h

theorem sub_getLsbD {L avail : Form m} (h : Sub L avail) {j : Pos m} (hj : L.getLsbD j) :
    avail.getLsbD j := by
  have := congrArg (·.getLsbD j) h
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, j.isLt, decide_true, Bool.true_and,
    hj] at this
  simpa using this

theorem sub_iff {L a : Form m} : Sub L a ↔ ∀ j, L.getLsbD j = true → a.getLsbD j = true := by
  constructor
  · intro h j hj
    by_cases hlt : j < 2 ^ m
    · exact sub_getLsbD h (j := ⟨j, hlt⟩) hj
    · simp [BitVec.getLsbD_of_ge L j (by omega)] at hj
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, hj, decide_true, Bool.true_and]
    cases hL : L.getLsbD j
    · simp
    · simp [h j hL]

theorem Sub.or_right {L a : Form m} (b : Form m) (h : Sub L a) : Sub L (a ||| b) :=
  sub_iff.mpr fun j hj ↦ by rw [BitVec.getLsbD_or, sub_iff.mp h j hj, Bool.true_or]

/-! ## The executable evaluation -/

/-- Parity in GF(2), over the bit indices. -/
private def parZ {n : ℕ} (x : BitVec n) : ZMod 2 := ∑ i ∈ Finset.range n, toZ (x.getLsbD i)

private theorem toZ_par (k : ℕ) (x : BitVec (2 ^ k)) : toZ (par k x) = parZ x := by
  induction k with
  | zero => simp [par, parZ]
  | succ k ih =>
    rw [par, ih, parZ, parZ,
      show Finset.range (2 ^ (k + 1)) = Finset.range (2 ^ k + 2 ^ k) by rw [pow_succ, mul_two],
      Finset.sum_range_add, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hi : i < 2 ^ k := Finset.mem_range.mp hi
    simp [hi, toZ_xor, Nat.add_comm]

/-- The executable evaluation is the mathematical one. -/
theorem evalB_eq_eval (L z : Form m) : L.evalB z = L.eval (fun j ↦ z.getLsbD j) := by
  apply toZ_injective
  rw [Form.evalB, toZ_par, toZ_eval, parZ, Form.evalZ, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [BitVec.getLsbD_and, toZ_and]
  cases L.getLsbD j <;> simp [toZ]

/-! ## The R1CS of a circuit -/

section Ring

variable {R : Type*} [CommRing R]

theorem ofBool_and (a b : Bool) : ofBool R (a && b) = ofBool R a * ofBool R b := by
  cases a <;> cases b <;> simp [ofBool]

theorem ofBool_injective [Nontrivial R] : Function.Injective (ofBool R) := by
  intro a b h
  cases a <;> cases b <;> simp_all [ofBool]

variable [CharP R 2]

private theorem castHom_toZ (b : Bool) : ZMod.castHom (dvd_refl 2) R (toZ b) = ofBool R b := by
  cases b <;> simp [toZ, ofBool]

/-- A row of `0`/`1` entries applied to a Boolean block is the form's value. -/
theorem sum_liftBlock (L : Form m) (z : Pos m → Bool) :
    (∑ j : Pos m, if L.getLsbD j then (liftBlock R z)[j] else 0) = ofBool R (L.eval z) := by
  rw [← castHom_toZ, toZ_eval, Form.evalZ, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  split_ifs
  · rw [castHom_toZ]
    simp [liftBlock]
  · simp

theorem rows_fst_liftBlock (c : ProductCircuit m) (z : Pos m → Bool) (k : Pos m) :
    ((c.toBlockR1CS R).rows (liftBlock R z)).1[k] = ofBool R ((c.rowOf k).a.eval z) := by
  rw [BlockR1CS.rows_fst]
  exact sum_liftBlock _ z

theorem rows_snd_liftBlock (c : ProductCircuit m) (z : Pos m → Bool) (k : Pos m) :
    ((c.toBlockR1CS R).rows (liftBlock R z)).2[k] = ofBool R ((c.rowOf k).b.eval z) := by
  rw [BlockR1CS.rows_snd]
  exact sum_liftBlock _ z

/-- Over a nontrivial ring of characteristic two, a Boolean block satisfies the R1CS of a circuit
if and only if every position holds the product of its row's two forms. -/
theorem holds_iff_gates [Nontrivial R] (c : ProductCircuit m) (z : Pos m → Bool) :
    (c.toBlockR1CS R).Holds (liftBlock R z) ↔
      ∀ k, z k = ((c.rowOf k).a.eval z && (c.rowOf k).b.eval z) := by
  refine forall_congr' fun k ↦ ?_
  rw [rows_fst_liftBlock, rows_snd_liftBlock, ← ofBool_and]
  simp only [liftBlock, Fin.getElem_fin, Vector.getElem_ofFn]
  exact ⟨fun h ↦ (ofBool_injective h).symm, fun h ↦ by rw [h]⟩

/-- The Boolean block a block of `0`/`1` entries holds: `true` where the entry is `1`. -/
def toBools [DecidableEq R] (z : CMlPolynomialEval R m) : Pos m → Bool := fun k ↦ decide (z[k] = 1)

omit [CharP R 2] in
/-- A block of `0`/`1` entries is the lift of the Boolean block it holds. -/
theorem eq_liftBlock_toBools [DecidableEq R] [Nontrivial R] {z : CMlPolynomialEval R m}
    (hz : ∀ k : Pos m, BlockR1CS.IsBool z[k]) : z = liftBlock R (toBools z) := by
  refine Vector.ext fun k hk ↦ ?_
  simp only [liftBlock, toBools, ofBool, Vector.getElem_ofFn]
  rcases hz ⟨k, hk⟩ with h | h <;> simp only [Fin.getElem_fin] at h <;> simp [h]

end Ring

/-! ## Schedules -/

private theorem foldl_stepF_of_not_mem (L : List (Pos m × Gate m)) (z : Pos m → Bool) (k : Pos m)
    (hk : k ∉ L.map Prod.fst) : L.foldl stepF z k = z k := by
  induction L generalizing z with
  | nil => rfl
  | cons kg rest ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hk
    rw [List.foldl_cons, ih _ hk.2, stepF, Function.update_of_ne hk.1]

private theorem boundedFrom_fresh {avail : Form m} {L : List (Pos m × Gate m)}
    (h : BoundedFrom avail L)
    {k : Pos m} (hk : k ∈ L.map Prod.fst) : avail.getLsbD k = false := by
  induction L generalizing avail with
  | nil => simp at hk
  | cons kg rest ih =>
    obtain ⟨k', g'⟩ := kg
    rw [BoundedFrom] at h
    obtain ⟨-, -, hk', hrest⟩ := h
    simp only [List.map_cons, List.mem_cons] at hk
    rcases hk with rfl | hk
    · exact hk'
    · have := ih hrest hk
      simp only [BitVec.getLsbD_or, Bool.or_eq_false_iff] at this
      exact this.1

private theorem mem_of_lookup {L : List (Pos m × Gate m)} {k : Pos m} {g : Gate m}
    (h : L.lookup k = some g) : k ∈ L.map Prod.fst := by
  induction L with
  | nil => simp at h
  | cons kg rest ih =>
    rw [List.lookup_cons] at h
    by_cases hk : k = kg.1
    · simp [hk]
    · have : (k == kg.1) = false := by simpa using hk
      rw [this] at h
      exact List.mem_cons_of_mem _ (ih h)

private theorem not_mem_of_lookup_none {L : List (Pos m × Gate m)} {k : Pos m}
    (h : L.lookup k = none) :
    k ∉ L.map Prod.fst := by
  rw [List.lookup_eq_none_iff] at h
  simp only [List.mem_map, not_exists, not_and]
  intro p hp hpk
  have := h p hp
  simp [hpk] at this

private theorem lookup_of_mem {avail : Form m} {L : List (Pos m × Gate m)} (h : BoundedFrom avail L)
    {k : Pos m} {g : Gate m} (hm : (k, g) ∈ L) : L.lookup k = some g := by
  induction L generalizing avail with
  | nil => simp at hm
  | cons kg rest ih =>
    obtain ⟨k', g'⟩ := kg
    rw [BoundedFrom] at h
    obtain ⟨-, -, -, hrest⟩ := h
    rw [List.lookup_cons]
    by_cases hkk : k = k'
    · subst hkk
      rcases List.mem_cons.mp hm with he | hm'
      · simp only [Prod.mk.injEq, true_and] at he
        simp [he]
      · have := boundedFrom_fresh hrest (List.mem_map_of_mem (f := Prod.fst) hm')
        simp [Form.var] at this
    · have : (k == k') = false := by simpa using hkk
      rw [this]
      exact ih hrest (by simpa [hkk] using hm)

/-- Along a bounded schedule, every gate's position holds the product of its forms at the end. -/
private theorem foldl_gate {avail : Form m} {L : List (Pos m × Gate m)} (h : BoundedFrom avail L)
    (z : Pos m → Bool) {k : Pos m} {g : Gate m} (hk : L.lookup k = some g) :
    L.foldl stepF z k = (g.a.eval (L.foldl stepF z) && g.b.eval (L.foldl stepF z)) := by
  induction L generalizing avail z with
  | nil => simp at hk
  | cons kg rest ih =>
    obtain ⟨k', g'⟩ := kg
    rw [BoundedFrom] at h
    obtain ⟨ha, hb, hk', hrest⟩ := h
    rw [List.lookup_cons] at hk
    by_cases hkk : k = k'
    · subst hkk
      simp only [beq_self_eq_true, Option.some.injEq] at hk
      subst hk
      have hnot : k ∉ rest.map Prod.fst := fun hm ↦ by
        have := boundedFrom_fresh hrest hm
        simp [Form.var] at this
      -- positions available before the gate keep their values to the end
      have keep : ∀ j : Pos m, avail.getLsbD j → rest.foldl stepF (stepF z (k, g')) j = z j := by
        intro j hj
        have hjr : j ∉ rest.map Prod.fst := fun hm ↦ by
          have := boundedFrom_fresh hrest hm
          rw [BitVec.getLsbD_or, hj, Bool.true_or] at this
          exact Bool.noConfusion this
        have hjk : j ≠ k := by rintro rfl; rw [hj] at hk'; exact Bool.noConfusion hk'
        rw [foldl_stepF_of_not_mem _ _ _ hjr, stepF, Function.update_of_ne hjk]
      have hstep : stepF z (k, g') k = (g'.a.eval z && g'.b.eval z) := Function.update_self ..
      rw [List.foldl_cons, foldl_stepF_of_not_mem _ _ _ hnot, hstep,
        eval_congr fun j hj ↦ (keep j (sub_getLsbD ha hj)).symm,
        eval_congr (L := g'.b) fun j hj ↦ (keep j (sub_getLsbD hb hj)).symm]
    · have : (k == k') = false := by simpa using hkk
      rw [this] at hk
      exact ih hrest _ hk

/-- A block satisfying a bounded schedule's gates is the schedule's run from any block it agrees
with off the gate positions. -/
private theorem foldl_unique {avail : Form m} {L : List (Pos m × Gate m)} (h : BoundedFrom avail L)
    (z t : Pos m → Bool) (hagree : ∀ j, j ∉ L.map Prod.fst → z j = t j)
    (hgates : ∀ k g, L.lookup k = some g → z k = (g.a.eval z && g.b.eval z)) :
    z = L.foldl stepF t := by
  induction L generalizing avail t with
  | nil => funext j; exact hagree j (by simp)
  | cons kg rest ih =>
    obtain ⟨k, g⟩ := kg
    -- `z` and `t` agree on the available positions
    have hav : ∀ j : Pos m, avail.getLsbD j → z j = t j := fun j hj ↦
      hagree j fun hm ↦ by
        have := boundedFrom_fresh h hm
        rw [hj] at this
        exact Bool.noConfusion this
    rw [BoundedFrom] at h
    obtain ⟨ha, hb, hk, hrest⟩ := h
    refine ih hrest _ (fun j hj ↦ ?_) (fun k' g' hk' ↦ ?_)
    · by_cases hjk : j = k
      · subst hjk
        rw [stepF, Function.update_self, hgates j g (by simp),
          eval_congr fun i hi ↦ hav i (sub_getLsbD ha hi),
          eval_congr (L := g.b) fun i hi ↦ hav i (sub_getLsbD hb hi)]
      · rw [stepF, Function.update_of_ne hjk]
        exact hagree j (by simp [hjk, hj])
    · have hne : k' ≠ k := by
        rintro rfl
        have := boundedFrom_fresh hrest (mem_of_lookup hk')
        simp [Form.var] at this
      apply hgates
      rw [List.lookup_cons]
      have : (k' == k) = false := by simpa using hne
      rw [this]
      exact hk'

/-! ## The trace satisfies the circuit, and is the only block that does -/

/-- The trace holds `1` at the constant position. -/
theorem traceF_cpos {c : ProductCircuit m} (hc : c.Bounded) (inp : Pos m → Bool) :
    c.traceF inp c.cpos = true := by
  have : c.cpos ∉ c.gates.toList.map Prod.fst := fun hm ↦ by
    have := boundedFrom_fresh hc hm
    simp [Form.var] at this
  rw [traceF, foldl_stepF_of_not_mem _ _ _ this]
  simp [initF]

/-- The trace keeps the input at every input position. -/
theorem traceF_input {c : ProductCircuit m} (hc : c.Bounded) (inp : Pos m → Bool) {j : Pos m}
    (hj : c.inputs.getLsbD j = true) (hjc : j ≠ c.cpos) : c.traceF inp j = inp j := by
  have hnm : j ∉ c.gates.toList.map Prod.fst := fun hm ↦ by
    have := boundedFrom_fresh hc hm
    rw [BitVec.getLsbD_or, hj, Bool.true_or] at this
    exact Bool.noConfusion this
  rw [traceF, foldl_stepF_of_not_mem _ _ _ hnm, initF]
  simp [hjc, hj]

/-- The trace of a bounded circuit satisfies every row. -/
theorem trace_holds {c : ProductCircuit m} (hc : c.Bounded) (inp : Pos m → Bool) (k : Pos m) :
    c.traceF inp k = ((c.rowOf k).a.eval (c.traceF inp) && (c.rowOf k).b.eval (c.traceF inp)) := by
  unfold rowOf
  split
  · next g hg => exact foldl_gate hc _ hg
  · next hg =>
    have hk := not_mem_of_lookup_none hg
    have h1 := traceF_cpos hc inp
    split_ifs with hkc hin
    · subst hkc; simp [h1]
    · rw [eval_var, eval_var, h1, Bool.and_true]
    · rw [eval_zero, Bool.and_false, traceF, foldl_stepF_of_not_mem _ _ _ hk, initF]
      simp at hin
      simp [hkc, hin]

/-- Completeness of the lowering: over a nontrivial ring of characteristic two, the trace of a
bounded circuit satisfies its R1CS and holds `1` at the constant position. -/
theorem trace_satisfies {R : Type*} [CommRing R] [CharP R 2]
    {c : ProductCircuit m} (hc : c.Bounded) (inp : Pos m → Bool) :
    (c.toBlockR1CS R).Holds (liftBlock R (c.traceF inp)) ∧
      (liftBlock R (c.traceF inp))[c.cpos] = 1 := by
  refine ⟨fun k ↦ ?_, ?_⟩
  · rw [rows_fst_liftBlock, rows_snd_liftBlock, ← ofBool_and, ← trace_holds hc inp k]
    simp [liftBlock]
  · simp [liftBlock, traceF_cpos hc, ofBool]

/-- Determinism: a Boolean block satisfying every row of a bounded circuit, with `1` at the
constant position, is the trace of its own inputs. -/
theorem holds_eq_trace {c : ProductCircuit m} (hc : c.Bounded) (z : Pos m → Bool)
    (hz : ∀ k, z k = ((c.rowOf k).a.eval z && (c.rowOf k).b.eval z)) (h1 : z c.cpos = true) :
    z = c.traceF z := by
  refine foldl_unique hc z (c.initF z) (fun j hj ↦ ?_) (fun k g hk ↦ ?_)
  · have hl : c.gates.toList.lookup j = none := by
      rw [List.lookup_eq_none_iff]
      intro p hp
      simp only [bne_iff_ne, ne_eq]
      rintro rfl
      exact hj (List.mem_map_of_mem hp)
    have := hz j
    simp only [rowOf, hl] at this
    unfold initF
    split_ifs at this with hjc hin
    · subst hjc; simp [h1]
    · simp [hjc, hin]
    · rw [eval_zero, Bool.and_false] at this
      simp [hjc, this]
  · have := hz k
    simp only [rowOf, hk] at this
    exact this

/-- In a bounded circuit, a block satisfying every row satisfies every recorded gate. -/
theorem gates_of_rows {c : ProductCircuit m} (hc : c.Bounded) (z : Pos m → Bool)
    (hz : ∀ k, z k = ((c.rowOf k).a.eval z && (c.rowOf k).b.eval z)) :
    ∀ kg ∈ c.gates, z kg.1 = (kg.2.a.eval z && kg.2.b.eval z) := by
  intro kg hkg
  have hl := lookup_of_mem hc (Array.mem_toList_iff.mpr hkg)
  have := hz kg.1
  simp only [rowOf, hl] at this
  exact this

/-- Soundness of the lowering: over a nontrivial ring of characteristic two, a Boolean block
satisfying the R1CS of a bounded circuit satisfies every recorded gate. -/
theorem gates_of_holds {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]
    {c : ProductCircuit m} (hc : c.Bounded) (z : Pos m → Bool)
    (hz : (c.toBlockR1CS R).Holds (liftBlock R z)) :
    ∀ kg ∈ c.gates, z kg.1 = (kg.2.a.eval z && kg.2.b.eval z) :=
  gates_of_rows hc z ((holds_iff_gates c z).mp hz)

/-- Soundness of the lowering for a block of `0`/`1` entries: if it satisfies the R1CS of a
bounded circuit, its Boolean block satisfies every recorded gate. -/
theorem gates_of_holds_isBool {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R] [DecidableEq R]
    {c : ProductCircuit m} (hc : c.Bounded) {z : CMlPolynomialEval R m}
    (hb : ∀ k : Pos m, BlockR1CS.IsBool z[k]) (hz : (c.toBlockR1CS R).Holds z) :
    ∀ kg ∈ c.gates, toBools z kg.1 = (kg.2.a.eval (toBools z) && kg.2.b.eval (toBools z)) :=
  gates_of_holds hc _ (eq_liftBlock_toBools hb ▸ hz)

/-- Determinism for a block of `0`/`1` entries: if it satisfies the R1CS of a bounded circuit and
holds `1` at the constant, it is the lift of the trace of its own inputs. -/
theorem eq_trace_of_holds_isBool {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]
    [DecidableEq R] {c : ProductCircuit m} (hc : c.Bounded) {z : CMlPolynomialEval R m}
    (hb : ∀ k : Pos m, BlockR1CS.IsBool z[k]) (hz : (c.toBlockR1CS R).Holds z)
    (h1 : z[c.cpos] = 1) : z = liftBlock R (c.traceF (toBools z)) := by
  have hz' := eq_liftBlock_toBools hb ▸ hz
  conv_lhs => rw [eq_liftBlock_toBools hb]
  rw [← holds_eq_trace hc _ ((holds_iff_gates c _).mp hz') (by simp [toBools, h1])]

/-- The executable trace computes the mathematical one. -/
theorem trace_getLsbD (c : ProductCircuit m) (inp : Form m) :
    (fun j : Pos m ↦ (c.trace inp).getLsbD j) = c.traceF (fun j ↦ inp.getLsbD j) := by
  rw [trace, traceF, ← Array.foldl_toList]
  have hinit : (fun j : Pos m ↦ (c.initB inp).getLsbD j) = c.initF (fun j ↦ inp.getLsbD j) := by
    funext j
    simp [initB, initF, Form.var, Bool.or_comm, Fin.val_inj]
  rw [← hinit]
  generalize c.initB inp = z0
  induction c.gates.toList generalizing z0 with
  | nil => rfl
  | cons kg rest ih =>
    rw [List.foldl_cons, List.foldl_cons, ih]
    congr 1
    funext j
    simp only [stepB, stepF, setBitB, evalB_eq_eval]
    by_cases hj : j = kg.1
    · subst hj
      split <;> simp_all [Form.var]
    · rw [Function.update_of_ne hj]
      have : (j : ℕ) ≠ kg.1 := fun h ↦ hj (Fin.ext h)
      split <;> simp [Form.var, this]

/-! ## Assembling bounded schedules -/

/-- The available positions after a schedule. -/
def availAfter (a : Form m) (L : List (Pos m × Gate m)) : Form m :=
  L.foldl (fun a kg ↦ a ||| Form.var kg.1) a

theorem boundedFrom_append (a : Form m) (l₁ l₂ : List (Pos m × Gate m)) :
    BoundedFrom a (l₁ ++ l₂) ↔ BoundedFrom a l₁ ∧ BoundedFrom (availAfter a l₁) l₂ := by
  induction l₁ generalizing a with
  | nil => simp [BoundedFrom, availAfter]
  | cons kg rest ih =>
    obtain ⟨k, g⟩ := kg
    simp only [List.cons_append, BoundedFrom, ih, availAfter, List.foldl_cons]
    tauto

theorem availAfter_append_singleton (a : Form m) (l : List (Pos m × Gate m))
    (kg : Pos m × Gate m) : availAfter a (l ++ [kg]) = availAfter a l ||| Form.var kg.1 := by
  simp [availAfter, List.foldl_append]

/-- Gates that read only `a`, at distinct positions fresh for `a`, are bounded from `a`. -/
theorem boundedFrom_of_nodup (L : List (Pos m × Gate m)) :
    ∀ a : Form m, (∀ kg ∈ L, Sub kg.2.a a ∧ Sub kg.2.b a) → (∀ kg ∈ L, a.getLsbD kg.1 = false) →
      (L.map Prod.fst).Nodup → BoundedFrom a L := by
  induction L with
  | nil => intros; trivial
  | cons kg rest ih =>
    intro a hsub hfresh hnd
    obtain ⟨k, g⟩ := kg
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [BoundedFrom]
    refine ⟨(hsub _ List.mem_cons_self).1, (hsub _ List.mem_cons_self).2,
      hfresh _ List.mem_cons_self, ih _ (fun kg' h ↦ ?_) (fun kg' h ↦ ?_) hnd.2⟩
    · exact ⟨(hsub kg' (List.mem_cons_of_mem _ h)).1.or_right _,
        (hsub kg' (List.mem_cons_of_mem _ h)).2.or_right _⟩
    · rw [BitVec.getLsbD_or, hfresh kg' (List.mem_cons_of_mem _ h), getLsbD_var, Bool.false_or,
        decide_eq_false_iff_not]
      intro he
      have hm := List.mem_map_of_mem (f := Prod.fst) h
      rw [← Fin.ext he] at hm
      exact hnd.1 hm

end ProductCircuit

end
end LeanVM.Protocol
