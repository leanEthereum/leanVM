module

public import LeanVMCircuits.Rec.BusLeaves
public import LeanVMCircuits.Rec.Dump

@[expose] public section

/-!
A side of the bus as `Side::decompose` makes it, certified call by call (`Bind.SideCert`).

`BusBlocks::new`'s blocks are recorded in the dumps (`bus side` and `bus block` marks, `BusBlocks::mark_lines`) with the
offsets `bus::layout` stacks them at: each block's `κ`, offset, owner and coordinates (`Bind.BlockD`, `Bind.CoordD`).
`Side::decompose` walks a side's blocks at the GKR's point `ζ`, the fingerprint weights `w` and `β`: block `b`'s
selector `eq_bits(q_b, ζ[κ_b..])` from a `one`, a `mul(acc, ζ_j)` or a `mul_add(acc, ζ_j, acc)` per coordinate from
the highest (`Bind.selCalls`), added to the selectors' sum; an index coordinate `int_index(base, shift, ζ[..κ])` (an
`e_const` then a `mul_const_add(ζ_k, 2^(k + shift), acc)` per low coordinate) and a public one (a hint, its value wire
named) join the block's known part at their weight, `mul_add(w_i, x, acc)`; an owned block's other coordinates
accumulate into its table's form (`BusForm::accumulate`: a constant's `mul_const_add(w_i, v, constant)`, a column's
`mul_add(sel, w_i, coeff)`, a product's `mul(sel, w_i)`), its constant at its selector; a framework block's leaf is
`β` plus its known part at its selector. The side's framework share is the accumulator plus the selectors' sum.

`Bind.SideCert.sem`: where the calls hold and the certificate passes, the named framework share is
`AirLink.framework` over the recorded blocks, its coordinates at the named weights, and each table's named form is
`AirLink.sideForm`'s at every column vector; the premise is that each public coordinate's named value is its column's
multilinear extension at `ζ[..κ]`. An index coordinate's value is its column's extension (`idx_mle`), certified.
-/

namespace LeanVMCircuits.Rec.Bind

open LeanVMCircuits.Rec Model AirLink Finset

/-! The recorded blocks. -/

/-- A term of a table block's coordinate (`bus::Coord` within a `Sum`): a constant word, a column, a product of two,
the columns the table's own. -/
inductive TermD where
  | const (v : ℕ)
  | col (c : ℕ)
  | prod (a b : ℕ)
  deriving Inhabited, Repr, DecidableEq

/-- A block's coordinate: an index column `base ^ (z << shift)`, a fixed public column (`Next(i)` or `Constant(i)`),
or a sum of terms. -/
inductive CoordD where
  | idx (base shift : ℕ)
  | pub (next : Bool) (i : ℕ)
  | terms (ts : List TermD)
  deriving Inhabited, Repr, DecidableEq

/-- A recorded block: `2^κ` rows at offset `off`, its owner (none for the framework's) and its coordinates. -/
structure BlockD where
  kappa : ℕ
  off : ℕ
  owner : Option Table
  coords : List CoordD
  deriving Inhabited, Repr, DecidableEq

/-- Its place among the blocks of its height, `offset >> κ`. -/
def BlockD.q (bd : BlockD) : ℕ := bd.off / 2 ^ bd.kappa

/-! The certificate. -/

/-- A coordinate's calls: an index one's `e_const` and `mul_const_add`s (`idx`), a public one's value (`x`), either's
`mul_add(w_i, x, acc)` (`addAt`), a sum's call per term (`terms`). -/
structure CoordCert where
  idx : List ℕ := []
  x : ℕ := 0
  addAt : ℕ := 0
  terms : List ℕ := []
  deriving Inhabited, Repr

/-- A block's calls: its selector's `one` and steps, the `add` to the selectors' sum, an owned block's known part's
`zero`, its coordinates', an owned block's constant's `mul_add(sel, constant, form.constant)` and the
`mul_add(sel, known, acc)` (a framework block's `mul_add(sel, leaf, acc)`). -/
structure BlockCert where
  one : ℕ := 0
  steps : List ℕ := []
  sumAt : ℕ := 0
  zero : ℕ := 0
  coords : List CoordCert := []
  constAt : ℕ := 0
  accAt : ℕ := 0
  deriving Inhabited, Repr

/-- A table's form as `Side::decompose` leaves it: its constant's wire, a coefficient wire per column, and its
products' columns and coefficient wires. -/
structure FormSt where
  const : ℕ := 0
  coeffs : List ℕ := []
  prods : List (ℕ × ℕ × ℕ) := []
  deriving Inhabited, Repr, DecidableEq

/-- A side's state between blocks: the framework accumulator, the selectors' sum and each table's form. -/
structure SideSt where
  acc : ℕ
  selSum : ℕ
  forms : Table → FormSt

/-- A side's certificate (side `0` the push side, `1` the pull side): the point's wires, the fingerprint weights and
`β`, the forms' `zero`, the accumulator's `zero`, the selectors' sum's `one`, the recorded blocks with their calls, and
the share's `add(acc, selSum)`. -/
structure SideCert where
  mu : ℕ
  zeta : List ℕ
  w : List ℕ
  beta : ℕ
  formZero : ℕ
  zeroAt : ℕ
  oneAt : ℕ
  blocks : List BlockD
  certs : List BlockCert
  fwAt : ℕ
  deriving Inhabited, Repr

section Calls

variable (os : Array (List ℕ))

/-- A chain's output: each call's output read by the next. -/
def chainOut : ℕ → List ℕ → ℕ
  | acc, [] => acc
  | _, s :: ss => chainOut (o os s) ss

/-- `Arith::eq_bits(q, ζ[κ..top])` past `acc`: coordinate `top - 1` first, a `mul(acc, ζ_j)` where bit `j - κ` of `q` is
set, else `times_one_plus(acc, ζ_j) = mul_add(acc, ζ_j, acc)`. -/
def selCalls (zeta : List ℕ) (kappa q : ℕ) : ℕ → ℕ → List ℕ → List (ℕ × Call)
  | _, _, [] => []
  | acc, top, s :: ss =>
    (s, if q.testBit (top - 1 - kappa) then .mul acc (zeta.getD (top - 1) 0)
      else .mulAdd acc (zeta.getD (top - 1) 0) acc) :: selCalls zeta kappa q (o os s) (top - 1) ss

/-- `Arith::int_index`'s steps past `acc`: a `mul_const_add(ζ_k, 2^(k + shift), acc)` from coordinate `k`. -/
def idxCalls (zeta : List ℕ) (shift : ℕ) : ℕ → ℕ → List ℕ → List (ℕ × Call)
  | _, _, [] => []
  | acc, k, s :: ss => (s, .mulConstAdd (zeta.getD k 0) (2 ^ (k + shift)) 0 0 acc) :: idxCalls zeta shift (o os s) (k + 1) ss

/-- An owned block's terms of one coordinate at weight `wi` (`BusForm::accumulate`), from the block's constant and its
table's form. -/
def termsRun (sel wi : ℕ) : List TermD → List ℕ → ℕ × FormSt → List (ℕ × Call) × (ℕ × FormSt)
  | t :: ts, j :: js, (k, f) =>
    let (c, s') : (ℕ × Call) × (ℕ × FormSt) := match t with
      | .const v => ((j, .mulConstAdd wi v 0 0 k), (o os j, f))
      | .col c => ((j, .mulAdd sel wi (f.coeffs.getD c 0)), (k, { f with coeffs := f.coeffs.set c (o os j) }))
      | .prod a b => ((j, .mul sel wi), (k, { f with prods := f.prods ++ [(a, b, o os j)] }))
    let r := termsRun sel wi ts js s'
    (c :: r.1, r.2)
  | _, _, s => ([], s)

/-- A block's coordinates from coordinate `i`: the known part (an owned block's) or leaf (a framework block's), the
block's constant and its table's form. -/
def coordRun (zeta w : List ℕ) (sel : ℕ) : ℕ → List CoordD → List CoordCert → ℕ × ℕ × FormSt →
    List (ℕ × Call) × (ℕ × ℕ × FormSt)
  | i, c :: cs, cc :: ccs, (k, cst, f) =>
    let wi := w.getD i 0
    let r : List (ℕ × Call) × (ℕ × ℕ × FormSt) := match c with
      | .idx base shift =>
        let x := chainOut os (o os (cc.idx.headD 0)) cc.idx.tail
        ((cc.idx.headD 0, .eConst base 0 0) :: idxCalls os zeta shift (o os (cc.idx.headD 0)) 0 cc.idx.tail ++
          [(cc.addAt, .mulAdd wi x k)], (o os cc.addAt, cst, f))
      | .pub _ _ => ([(cc.addAt, .mulAdd wi cc.x k)], (o os cc.addAt, cst, f))
      | .terms ts =>
        let t := termsRun os sel wi ts cc.terms (cst, f)
        (t.1, (k, t.2))
    let r' := coordRun zeta w sel (i + 1) cs ccs r.2
    (r.1 ++ r'.1, r'.2)
  | _, _, _, s => ([], s)

/-- A block's calls and the side's state after it. -/
def blockRun (mu : ℕ) (zeta w : List ℕ) (beta : ℕ) (bd : BlockD) (bc : BlockCert) (s : SideSt) :
    List (ℕ × Call) × SideSt :=
  let sel := chainOut os (o os bc.one) bc.steps
  let selL := (bc.one, Call.one) :: selCalls os zeta bd.kappa bd.q (o os bc.one) mu bc.steps
  let sumL := [(bc.sumAt, Call.add s.selSum sel)]
  match bd.owner with
  | some T =>
    let f := s.forms T
    let r := coordRun os zeta w sel 0 bd.coords bc.coords (o os bc.zero, beta, f)
    (selL ++ sumL ++ (bc.zero, Call.zero) :: r.1 ++
        [(bc.constAt, .mulAdd sel r.2.2.1 f.const), (bc.accAt, .mulAdd sel r.2.1 s.acc)],
      { acc := o os bc.accAt, selSum := o os bc.sumAt,
        forms := fun T' => if T' = T then { r.2.2.2 with const := o os bc.constAt } else s.forms T' })
  | none =>
    let r := coordRun os zeta w sel 0 bd.coords bc.coords (beta, beta, default)
    (selL ++ sumL ++ r.1 ++ [(bc.accAt, .mulAdd sel r.2.1 s.acc)],
      { s with acc := o os bc.accAt, selSum := o os bc.sumAt })

/-- The blocks' calls in order and the state after the last. -/
def sideRun (mu : ℕ) (zeta w : List ℕ) (beta : ℕ) : List BlockD → List BlockCert → SideSt → List (ℕ × Call) × SideSt
  | bd :: bds, bc :: bcs, s =>
    let r := blockRun os mu zeta w beta bd bc s
    let r' := sideRun mu zeta w beta bds bcs r.2
    (r.1 ++ r'.1, r'.2)
  | _, _, s => ([], s)

namespace SideCert

variable (sc : SideCert)

/-- The state before the first block: the accumulator `zero`, the selectors' sum `one`, each table's form the
forms' `zero` at each of its columns. -/
def init : SideSt where
  acc := o os sc.zeroAt
  selSum := o os sc.oneAt
  forms T := { const := o os sc.formZero, coeffs := List.replicate (nCols T) (o os sc.formZero) }

/-- Its calls. -/
def calls : List (ℕ × Call) :=
  let r := sideRun os sc.mu sc.zeta sc.w sc.beta sc.blocks sc.certs (sc.init os)
  [(sc.formZero, .zero), (sc.zeroAt, .zero), (sc.oneAt, .one)] ++ r.1 ++ [(sc.fwAt, .add r.2.acc r.2.selSum)]

/-- The state after the last block. -/
def final : SideSt := (sideRun os sc.mu sc.zeta sc.w sc.beta sc.blocks sc.certs (sc.init os)).2

/-- The share. -/
def fw : ℕ := o os sc.fwAt

end SideCert

end Calls

/-! The shape the semantics needs. -/

/-- A term reads columns among the first `n`. -/
def TermD.okIn (n : ℕ) : TermD → Bool
  | .const _ => true
  | .col c => decide (c < n)
  | .prod a b => decide (a < n) && decide (b < n)

/-- A coordinate's shape: an index one's `κ + 1` calls with its column a 64-bit word, a sum's call per term and, in an
owned block, its columns its table's; no sum in a framework block. -/
def CoordD.shapeOk (kappa : ℕ) (owner : Option Table) (c : CoordD) (cc : CoordCert) : Bool :=
  match c with
  | .idx base shift => cc.idx.length == kappa + 1 && decide (base < 2 ^ 64) && decide (kappa + shift ≤ 64)
  | .pub _ _ => true
  | .terms ts => match owner with
    | some T => ts.length == cc.terms.length && ts.all (·.okIn (nCols T))
    | none => false

/-- A block's shape at depth `μ`: `κ ≤ μ`, its selector a step per coordinate above `κ`, its offset aligned within the
layer, a call per coordinate, at most as many coordinates as weights. -/
def BlockD.shapeOk (mu nw : ℕ) (bd : BlockD) (bc : BlockCert) : Bool :=
  (bd.owner.all fun T => decide (T ∈ owned)) && decide (bd.kappa ≤ mu) && bc.steps.length == mu - bd.kappa && bd.off % 2 ^ bd.kappa == 0 &&
    decide (bd.off + 2 ^ bd.kappa ≤ 2 ^ mu) && bd.coords.length == bc.coords.length &&
    decide (bd.coords.length ≤ nw) && (bd.coords.zip bc.coords).all fun p => p.1.shapeOk bd.kappa bd.owner p.2

/-- Two blocks' rows are disjoint. -/
def BlockD.disjoint (a b : BlockD) : Bool := a.off + 2 ^ a.kappa ≤ b.off || b.off + 2 ^ b.kappa ≤ a.off

/-- The certificate's shape: the point has `μ` coordinates, a call record per block, each block's shape, and the
blocks' rows pairwise disjoint. -/
def SideCert.shapeOk (sc : SideCert) : Bool :=
  sc.zeta.length == sc.mu && sc.blocks.length == sc.certs.length &&
    (sc.blocks.zip sc.certs).all (fun p => p.1.shapeOk sc.mu sc.w.length p.2) &&
    (List.range sc.blocks.length).all fun i => (List.range sc.blocks.length).all fun j =>
      i == j || (sc.blocks.getD i default).disjoint (sc.blocks.getD j default)

/-- The certificate's check: its shape and its calls. -/
def SideCert.ok (sc : SideCert) (os : Array (List ℕ)) (cs : Array Call) (rl : Array Bool) : Bool :=
  sc.shapeOk && callsOk cs rl (sc.calls os)

/-! The chains' values where the calls hold. -/

section Sem

variable {cs : Array Call} {rl : Array Bool} {os : Array (List ℕ)} {st : ℕ → Fin 4 → K} {val : Val}

/-- The selector's factor at coordinate `j`: `ζ_j` where bit `j - κ` of `q` is set, else `1 + ζ_j`. -/
noncomputable def selFactor (zv : ℕ → E) (kappa q j : ℕ) : E := if q.testBit (j - kappa) then zv j else 1 + zv j

theorem selCalls_sem (hF : Facts cs rl os st val) (zeta : List ℕ) (kappa q : ℕ) :
    ∀ (ss : List ℕ) (acc top : ℕ), ss.length + kappa = top →
      callsOk cs rl (selCalls os zeta kappa q acc top ss) = true →
      Model.ev val (chainOut os acc ss) = Model.ev val acc *
        ∏ j ∈ Ico kappa top, selFactor (fun j => Model.ev val (zeta.getD j 0)) kappa q j
  | [], acc, top, h, _ => by
    simp only [List.length_nil, zero_add] at h
    subst h
    simp [chainOut]
  | s :: ss, acc, top, h, hc => by
    obtain ⟨t, rfl⟩ : ∃ t, top = t + 1 := ⟨top - 1, by simp only [List.length_cons] at h; omega⟩
    have hk : kappa ≤ t := by simp only [List.length_cons] at h; omega
    simp only [selCalls, Nat.add_sub_cancel] at hc
    obtain ⟨h1, h2⟩ := callsOk_cons hc
    have hs : Model.ev val (o os s) = Model.ev val acc * selFactor (fun j => Model.ev val (zeta.getD j 0)) kappa q t := by
      unfold selFactor
      by_cases hb : q.testBit (t - kappa)
      · rw [if_pos hb] at h1 ⊢
        exact holds_of_mem hF h1 (List.mem_singleton_self _)
      · rw [if_neg hb] at h1 ⊢
        have e : Model.ev val (o os s) = Model.ev val acc * Model.ev val (zeta.getD t 0) + Model.ev val acc :=
          holds_of_mem hF h1 (List.mem_singleton_self _)
        rw [e]
        ring
    rw [chainOut, selCalls_sem hF zeta kappa q ss (o os s) t (by simp only [List.length_cons] at h; omega) h2, hs,
      Finset.prod_Ico_succ_top hk]
    ring

/-- The selector over the whole point: `sel` is the product of its factors from `κ` up. -/
theorem sel_eq_prod {mu : ℕ} (zv : ℕ → E) (kappa q : ℕ) :
    sel (fun j : Fin mu => zv j) kappa q = ∏ j ∈ Ico kappa mu, selFactor zv kappa q j := by
  have e := Fin.prod_univ_eq_prod_range (fun j => if kappa ≤ j then selFactor zv kappa q j else 1) mu
  simp only [selFactor] at e ⊢
  rw [sel, e, ← Finset.prod_filter]
  refine Finset.prod_congr ?_ fun _ _ => rfl
  ext j
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  omega

theorem idxCalls_sem (hF : Facts cs rl os st val) (zeta : List ℕ) (shift : ℕ) :
    ∀ (ss : List ℕ) (acc k : ℕ), callsOk cs rl (idxCalls os zeta shift acc k ss) = true →
      Model.ev val (chainOut os acc ss) = Model.ev val acc +
        ∑ j ∈ Ico k (k + ss.length), Model.ev val (zeta.getD j 0) * emb (ofWord (2 ^ (j + shift)))
  | [], acc, k, _ => by simp [chainOut]
  | s :: ss, acc, k, hc => by
    obtain ⟨h1, h2⟩ := callsOk_cons hc
    have hs : Model.ev val (o os s) =
        Model.ev val (zeta.getD k 0) * toE (ofWord (2 ^ (k + shift))) (ofWord 0) (ofWord 0) + Model.ev val acc :=
      holds_of_mem hF h1 (List.mem_singleton_self _)
    rw [ofWord_zero, toE_emb] at hs
    rw [chainOut, idxCalls_sem hF zeta shift ss (o os s) (k + 1) h2, hs, List.length_cons,
      Finset.sum_eq_sum_Ico_succ_bot (by omega : k < k + (ss.length + 1)), show k + (ss.length + 1) = k + 1 + ss.length
        by omega]
    ring

/-- An index coordinate's value: `int_index(base, shift, ζ[..κ])`, an `e_const` of `base` then the steps. -/
theorem idx_sem (hF : Facts cs rl os st val) (zeta : List ℕ) (base shift : ℕ) (ss : List ℕ)
    (hc : callsOk cs rl ((ss.headD 0, .eConst base 0 0) :: idxCalls os zeta shift (o os (ss.headD 0)) 0 ss.tail) =
      true) :
    Model.ev val (chainOut os (o os (ss.headD 0)) ss.tail) = emb (ofWord base) +
      ∑ j ∈ range ss.tail.length, Model.ev val (zeta.getD j 0) * emb (ofWord (2 ^ (j + shift))) := by
  obtain ⟨h1, h2⟩ := callsOk_cons hc
  have h0 : Model.ev val (o os (ss.headD 0)) = toE (ofWord base) (ofWord 0) (ofWord 0) :=
    holds_of_mem hF h1 (List.mem_singleton_self _)
  rw [ofWord_zero, toE_emb] at h0
  rw [idxCalls_sem hF zeta shift _ _ 0 h2, h0, zero_add, Finset.range_eq_Ico]

/-- Disjoint bits add as they xor. -/
theorem two_pow_add_eq_xor {m y : ℕ} (hy : y < 2 ^ m) : 2 ^ m + y = 2 ^ m ^^^ y := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor]
  rcases lt_trichotomy j m with h | h | h
  · rw [Nat.testBit_two_pow_add_gt h, Nat.testBit_two_pow_of_ne (by omega)]
    simp
  · subst h
    rw [Nat.testBit_two_pow_add_eq, Nat.testBit_two_pow_self, Nat.testBit_lt_two_pow hy]
    simp
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (by omega : 2 ^ m + y < 2 ^ (m + 1))
      (Nat.pow_le_pow_right (by norm_num) h)), Nat.testBit_two_pow_of_ne (by omega),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hy (Nat.pow_le_pow_right (by norm_num) h.le))]
    simp

/-- One more low variable: where `f`'s upper half is its lower half plus `d`, the extension over `κ + 1` variables is
the one over `κ` plus `ζ_κ d`. -/
theorem mle_step {n κ : ℕ} (ζ : Fin n → E) (hκ : κ < n) (f : ℕ → E) (d : E)
    (hf : ∀ z < 2 ^ κ, f (2 ^ κ + z) = f z + d) :
    ∑ z ∈ range (2 ^ (κ + 1)), rowEq ζ (κ + 1) z * f z =
      ∑ z ∈ range (2 ^ κ), rowEq ζ κ z * f z + ζ ⟨κ, hκ⟩ * d := by
  rw [pow_succ, mul_two, sum_range_add]
  have e1 : ∀ z ∈ range (2 ^ κ), rowEq ζ (κ + 1) z = rowEq ζ κ z * (1 + ζ ⟨κ, hκ⟩) := fun z hz => by
    rw [rowEq_succ ζ hκ, Nat.testBit_lt_two_pow (mem_range.mp hz)]
    simp
  have e2 : ∀ z ∈ range (2 ^ κ), rowEq ζ (κ + 1) (2 ^ κ + z) = rowEq ζ κ z * ζ ⟨κ, hκ⟩ := fun z hz => by
    rw [rowEq_succ ζ hκ, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow (mem_range.mp hz)]
    simp only [Bool.not_false, if_true]
    congr 1
    simp only [rowEq]
    refine prod_congr rfl fun j _ => ?_
    by_cases hj : (j : ℕ) < κ
    · simp [hj, Nat.testBit_two_pow_add_gt hj]
    · simp [hj]
  have s1 : ∑ z ∈ range (2 ^ κ), rowEq ζ (κ + 1) z * f z = ∑ z ∈ range (2 ^ κ), rowEq ζ κ z * (1 + ζ ⟨κ, hκ⟩) * f z :=
    sum_congr rfl fun z hz => by rw [e1 z hz]
  have s2 : ∑ z ∈ range (2 ^ κ), rowEq ζ (κ + 1) (2 ^ κ + z) * f (2 ^ κ + z) =
      ∑ z ∈ range (2 ^ κ), rowEq ζ κ z * ζ ⟨κ, hκ⟩ * (f z + d) :=
    sum_congr rfl fun z hz => by rw [e2 z hz, hf z (mem_range.mp hz)]
  rw [s1, s2, ← sum_add_distrib]
  have hs := sum_rowEq ζ κ hκ.le
  have e3 : ∀ z ∈ range (2 ^ κ), rowEq ζ κ z * (1 + ζ ⟨κ, hκ⟩) * f z + rowEq ζ κ z * ζ ⟨κ, hκ⟩ * (f z + d) =
      rowEq ζ κ z * f z + ζ ⟨κ, hκ⟩ * d * rowEq ζ κ z := fun z _ => by
    linear_combination (rowEq ζ κ z * ζ ⟨κ, hκ⟩ * f z) * two_E
  rw [sum_congr rfl e3, sum_add_distrib, ← mul_sum, hs, mul_one]

/-- An index column's extension (`Coord::IntIndex`, linear): `base ^ (z << shift)` over the rows of `κ` variables
extends to `base + Σ_k ζ_k 2^(k + shift)`. -/
theorem idx_mle {n : ℕ} (ζ : Fin n → E) (zv : ℕ → E) (hz : ∀ j : Fin n, ζ j = zv j) {base : ℕ} (shift : ℕ)
    (hb : base < 2 ^ 64) : ∀ κ, κ ≤ n → κ + shift ≤ 64 →
      ∑ z ∈ range (2 ^ κ), rowEq ζ κ z * emb (ofWord (base ^^^ (z <<< shift))) =
        emb (ofWord base) + ∑ k ∈ range κ, zv k * emb (ofWord (2 ^ (k + shift)))
  | 0, _, _ => by simp [rowEq]
  | κ + 1, hn, hs => by
    have hκ : κ < n := hn
    rw [mle_step ζ hκ _ (emb (ofWord (2 ^ (κ + shift)))) fun z hz => ?_, idx_mle ζ zv hz shift hb κ hκ.le (by omega),
      hz, sum_range_succ]
    · ring
    · have hzs : z <<< shift < 2 ^ (κ + shift) := by
        rw [Nat.shiftLeft_eq, pow_add]
        exact Nat.mul_lt_mul_of_pos_right hz (by positivity)
      have hp : (2 ^ κ + z) <<< shift = 2 ^ (κ + shift) ^^^ (z <<< shift) := by
        rw [← two_pow_add_eq_xor hzs, Nat.shiftLeft_eq, Nat.shiftLeft_eq, pow_add]
        ring
      have h64 : 2 ^ (κ + shift) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hx : base ^^^ (z <<< shift) < 2 ^ 64 := Nat.xor_lt_two_pow hb (lt_of_lt_of_le hzs h64)
      have hP : 2 ^ (κ + shift) < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
      rw [hp, ← Nat.xor_assoc, Nat.xor_comm base, Nat.xor_assoc, Nat.xor_comm, ← PoolParse.ofWord_add hx hP, emb_add]

/-! The blocks as `AirLink`'s decomposition reads them. -/

/-- A term's coordinate. -/
noncomputable def TermD.dc : TermD → DCoord
  | .const v => .const (emb (ofWord v))
  | .col c => .col c
  | .prod a b => .prod a b

/-- A coordinate's weighted terms at weight `w`: an index column's values, a public column's (`pubF next i`), or a
sum's terms each at `w`. -/
noncomputable def CoordD.ts (pubF : Bool → ℕ → ℕ → E) (w : E) : CoordD → List (E × DCoord)
  | .idx base shift => [(w, .virt fun z => emb (ofWord (base ^^^ (z <<< shift))))]
  | .pub nx i => [(w, .virt (pubF nx i))]
  | .terms ts => ts.map fun t => (w, t.dc)

/-- Coordinates from `i` at their weights `wv`. -/
noncomputable def coordsTs (pubF : Bool → ℕ → ℕ → E) (wv : ℕ → E) : ℕ → List CoordD → List (E × DCoord)
  | _, [] => []
  | i, c :: cs => c.ts pubF (wv i) ++ coordsTs pubF wv (i + 1) cs

/-- A block's weighted terms (`ts` of `AirLink.blockLeaf`). -/
noncomputable def BlockD.ts (pubF : Bool → ℕ → ℕ → E) (wv : ℕ → E) (bd : BlockD) : List (E × DCoord) :=
  coordsTs pubF wv 0 bd.coords

/-- A coordinate's value in a form at columns `col`: a constant's, a column's, a product's; a virtual one's none. -/
noncomputable def dval (col : ℕ → E) : DCoord → E
  | .const v => v
  | .col c => col c
  | .prod a b => col a * col b
  | .scaled k c => k * col c
  | .virt _ => 0

theorem blockQuad_eval (β : E) (col : ℕ → E) :
    ∀ ts : List (E × DCoord), (blockQuad β ts).eval col = β + (ts.map fun t => t.1 * dval col t.2).sum
  | [] => by simp [blockQuad, Quad.eval]
  | (w, c) :: ts => by
    have ih := blockQuad_eval β col ts
    simp only [blockQuad, Quad.eval] at ih ⊢
    cases c <;> simp [dval] at ih ⊢ <;> linear_combination ih

theorem blockKnown_append {n : ℕ} (ζ : Fin n → E) (κ : ℕ) (a b : List (E × DCoord)) :
    blockKnown ζ κ (a ++ b) = blockKnown ζ κ a + blockKnown ζ κ b := by
  simp [blockKnown, List.map_append, List.sum_append]

theorem blockKnown_terms {n : ℕ} (ζ : Fin n → E) (κ : ℕ) (w : E) (ts : List TermD) :
    blockKnown ζ κ (ts.map fun t => (w, t.dc)) = 0 := by
  simp only [blockKnown, List.map_map]
  refine List.sum_eq_zero fun x hx => ?_
  obtain ⟨t, -, rfl⟩ := List.mem_map.mp hx
  cases t <;> rfl

/-- A form's linear part: each column's coefficient wire's value at its column, and its products'. -/
noncomputable def FormSt.lv (val : Val) (n : ℕ) (col : ℕ → E) (f : FormSt) : E :=
  ∑ c ∈ range n, Model.ev val (f.coeffs.getD c 0) * col c +
    (f.prods.map fun p => Model.ev val p.2.2 * (col p.1 * col p.2.1)).sum

theorem FormSt.lv_set (val : Val) (n : ℕ) (col : ℕ → E) (f : FormSt) {c : ℕ} (hc : c < n)
    (hl : f.coeffs.length = n) (x : ℕ) :
    ({ f with coeffs := f.coeffs.set c x } : FormSt).lv val n col =
      f.lv val n col + (Model.ev val x - Model.ev val (f.coeffs.getD c 0)) * col c := by
  simp only [FormSt.lv]
  have e : ∀ j ∈ range n, Model.ev val ((f.coeffs.set c x).getD j 0) * col j =
      Model.ev val (f.coeffs.getD j 0) * col j +
        if c = j then (Model.ev val x - Model.ev val (f.coeffs.getD c 0)) * col c else 0 := fun j hj => by
    by_cases h : c = j
    · subst h
      simp only [List.getD_eq_getElem?_getD, List.getElem?_set_self (by omega : c < f.coeffs.length), if_true,
        Option.getD_some]
      ring
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_set_ne h, if_neg h, add_zero]
  rw [sum_congr rfl e, sum_add_distrib, Finset.sum_ite_eq, if_pos (mem_range.mpr hc)]
  ring

theorem FormSt.lv_prods (val : Val) (n : ℕ) (col : ℕ → E) (f : FormSt) (a b x : ℕ) :
    ({ f with prods := f.prods ++ [(a, b, x)] } : FormSt).lv val n col =
      f.lv val n col + Model.ev val x * (col a * col b) := by
  simp only [FormSt.lv, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero]
  ring

theorem termsRun_sem (hF : Facts cs rl os st val) (sel wi n : ℕ) (col : ℕ → E) :
    ∀ (ts : List TermD) (js : List ℕ) (k : ℕ) (f : FormSt), ts.length = js.length →
      (∀ t ∈ ts, t.okIn n = true) → f.coeffs.length = n →
      callsOk cs rl (termsRun os sel wi ts js (k, f)).1 = true →
      Model.ev val (termsRun os sel wi ts js (k, f)).2.1 * Model.ev val sel +
          (termsRun os sel wi ts js (k, f)).2.2.lv val n col =
        Model.ev val k * Model.ev val sel + f.lv val n col +
          Model.ev val sel * (ts.map fun t => Model.ev val wi * dval col t.dc).sum ∧
      (termsRun os sel wi ts js (k, f)).2.2.coeffs.length = n ∧ (termsRun os sel wi ts js (k, f)).2.2.const = f.const
  | [], js, k, f, _, _, hl, _ => by cases js <;> simp [termsRun, hl]
  | t :: ts, [], k, f, h, _, _, _ => by simp at h
  | t :: ts, j :: js, k, f, h, hok, hl, hc => by
    simp only [termsRun] at hc ⊢
    obtain ⟨h1, h2⟩ := callsOk_cons hc
    have hlen : ts.length = js.length := by simpa using h
    have hok' : ∀ t ∈ ts, t.okIn n = true := fun t ht => hok t (List.mem_cons_of_mem _ ht)
    cases t with
    | const v =>
      have e : Model.ev val (o os j) = Model.ev val wi * toE (ofWord v) (ofWord 0) (ofWord 0) + Model.ev val k :=
        holds_of_mem hF h1 (List.mem_singleton_self _)
      rw [ofWord_zero, toE_emb] at e
      obtain ⟨ih1, ih2, ih3⟩ := termsRun_sem hF sel wi n col ts js (o os j) f hlen hok' hl h2
      refine ⟨?_, ih2, ih3⟩
      rw [ih1, e, List.map_cons, List.sum_cons]
      simp only [TermD.dc, dval]
      ring
    | col c =>
      have e : Model.ev val (o os j) = Model.ev val sel * Model.ev val wi + Model.ev val (f.coeffs.getD c 0) :=
        holds_of_mem hF h1 (List.mem_singleton_self _)
      have hc' : c < n := by simpa [TermD.okIn] using hok _ List.mem_cons_self
      obtain ⟨ih1, ih2, ih3⟩ := termsRun_sem hF sel wi n col ts js k { f with coeffs := f.coeffs.set c (o os j) } hlen
        hok' (by simp [hl]) h2
      refine ⟨?_, ih2, ih3⟩
      rw [ih1, FormSt.lv_set val n col f hc' hl, e, List.map_cons, List.sum_cons]
      simp only [TermD.dc, dval]
      ring
    | prod a b =>
      have e : Model.ev val (o os j) = Model.ev val sel * Model.ev val wi :=
        holds_of_mem hF h1 (List.mem_singleton_self _)
      obtain ⟨ih1, ih2, ih3⟩ := termsRun_sem hF sel wi n col ts js k { f with prods := f.prods ++ [(a, b, o os j)] }
        hlen hok' hl h2
      refine ⟨?_, ih2, ih3⟩
      rw [ih1, FormSt.lv_prods, e, List.map_cons, List.sum_cons]
      simp only [TermD.dc, dval]
      ring


theorem dval_virt_sum (col : ℕ → E) (w : E) (f : ℕ → E) :
    ([(w, DCoord.virt f)].map fun t => t.1 * dval col t.2).sum = 0 := by
  simp [dval]

theorem coordRun_sem (hF : Facts cs rl os st val) (zeta w : List ℕ) (sel kappa : ℕ) (owner : Option Table)
    (pubF : Bool → ℕ → ℕ → E) (col : ℕ → E) {mu : ℕ} (ζ : Fin mu → E)
    (hζ : ∀ j : Fin mu, ζ j = Model.ev val (zeta.getD j 0)) (hk : kappa ≤ mu) :
    ∀ (cds : List CoordD) (ccs : List CoordCert) (i k cst : ℕ) (f : FormSt), cds.length = ccs.length →
      (∀ p ∈ cds.zip ccs, p.1.shapeOk kappa owner p.2 = true) →
      (∀ T, owner = some T → f.coeffs.length = nCols T) →
      (∀ p ∈ cds.zip ccs, ∀ nx j, p.1 = .pub nx j →
        Model.ev val p.2.x = ∑ z ∈ range (2 ^ kappa), rowEq ζ kappa z * pubF nx j z) →
      callsOk cs rl (coordRun os zeta w sel i cds ccs (k, cst, f)).1 = true →
      Model.ev val (coordRun os zeta w sel i cds ccs (k, cst, f)).2.1 = Model.ev val k +
          blockKnown ζ kappa (coordsTs pubF (fun i => Model.ev val (w.getD i 0)) i cds) ∧
      (∀ T, owner = some T →
        Model.ev val (coordRun os zeta w sel i cds ccs (k, cst, f)).2.2.1 * Model.ev val sel +
            (coordRun os zeta w sel i cds ccs (k, cst, f)).2.2.2.lv val (nCols T) col =
          Model.ev val cst * Model.ev val sel + f.lv val (nCols T) col + Model.ev val sel *
            ((coordsTs pubF (fun i => Model.ev val (w.getD i 0)) i cds).map fun t => t.1 * dval col t.2).sum) ∧
      (∀ T, owner = some T → (coordRun os zeta w sel i cds ccs (k, cst, f)).2.2.2.coeffs.length = nCols T) ∧
      (coordRun os zeta w sel i cds ccs (k, cst, f)).2.2.2.const = f.const
  | [], ccs, i, k, cst, f, _, _, hl, _, _ => by
    cases ccs <;> simp [coordRun, coordsTs, blockKnown] <;> exact hl
  | c :: cds, [], i, k, cst, f, h, _, _, _, _ => by simp at h
  | c :: cds, cc :: ccs, i, k, cst, f, h, hsh, hl, hpub, hc => by
    have hlen : cds.length = ccs.length := by simpa using h
    have hsh0 : c.shapeOk kappa owner cc = true := hsh (c, cc) List.mem_cons_self
    have hsh' : ∀ p ∈ cds.zip ccs, p.1.shapeOk kappa owner p.2 = true := fun p hp =>
      hsh p (List.mem_cons_of_mem _ hp)
    have hpub' : ∀ p ∈ cds.zip ccs, ∀ nx j, p.1 = .pub nx j →
        Model.ev val p.2.x = ∑ z ∈ range (2 ^ kappa), rowEq ζ kappa z * pubF nx j z := fun p hp =>
      hpub p (List.mem_cons_of_mem _ hp)
    simp only [coordRun, coordsTs, blockKnown_append, List.map_append, List.sum_append] at hc ⊢
    cases c with
    | idx base shift =>
      simp only [callsOk_append, Bool.and_eq_true] at hc
      obtain ⟨⟨hidx, hadd⟩, hrest⟩ := hc
      simp only [CoordD.shapeOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hsh0
      obtain ⟨⟨hil, hb⟩, hs⟩ := hsh0
      have hx := idx_sem hF zeta base shift cc.idx hidx
      have ha : Model.ev val (o os cc.addAt) = Model.ev val (w.getD i 0) *
          Model.ev val (chainOut os (o os (cc.idx.headD 0)) cc.idx.tail) + Model.ev val k :=
        holds_of_mem hF hadd (List.mem_singleton_self _)
      obtain ⟨ih1, ih2, ih3, ih4⟩ := coordRun_sem hF zeta w sel kappa owner pubF col ζ hζ hk cds ccs (i + 1)
        (o os cc.addAt) cst f hlen hsh' hl hpub' hrest
      refine ⟨?_, fun T hT => ?_, ih3, ih4⟩
      · rw [ih1, ha, hx]
        have hm := idx_mle ζ (fun j => Model.ev val (zeta.getD j 0)) hζ shift hb kappa hk (by omega)
        have htl : cc.idx.tail.length = kappa := by rw [List.length_tail, hil]; rfl
        rw [htl]
        simp only [CoordD.ts, blockKnown, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
        rw [hm]
        ring
      · rw [ih2 T hT]
        simp only [CoordD.ts, dval_virt_sum, zero_add]
    | pub nx j =>
      have hadd : Model.ev val (o os cc.addAt) = Model.ev val (w.getD i 0) * Model.ev val cc.x + Model.ev val k :=
        holds_of_mem hF (callsOk_append.symm ▸ hc |> fun h => (Bool.and_eq_true _ _).mp h |>.1)
          (List.mem_singleton_self _)
      have hrest := ((Bool.and_eq_true _ _).mp (callsOk_append.symm ▸ hc)).2
      obtain ⟨ih1, ih2, ih3, ih4⟩ := coordRun_sem hF zeta w sel kappa owner pubF col ζ hζ hk cds ccs (i + 1)
        (o os cc.addAt) cst f hlen hsh' hl hpub' hrest
      refine ⟨?_, fun T hT => ?_, ih3, ih4⟩
      · rw [ih1, hadd, hpub (CoordD.pub nx j, cc) List.mem_cons_self nx j rfl]
        simp only [CoordD.ts, blockKnown, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
        ring
      · rw [ih2 T hT]
        simp only [CoordD.ts, dval_virt_sum, zero_add]
    | terms ts =>
      cases owner with
      | none => simp [CoordD.shapeOk] at hsh0
      | some T =>
        simp only [CoordD.shapeOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hsh0
        obtain ⟨htl, hok⟩ := hsh0
        simp only [callsOk_append, Bool.and_eq_true] at hc
        obtain ⟨ht, hrest⟩ := hc
        obtain ⟨t1, t2, t3⟩ := termsRun_sem hF sel (w.getD i 0) (nCols T) col ts cc.terms cst f htl hok
          (hl T rfl) ht
        obtain ⟨ih1, ih2, ih3, ih4⟩ := coordRun_sem hF zeta w sel kappa (some T) pubF col ζ hζ hk cds ccs (i + 1) k
          (termsRun os sel (w.getD i 0) ts cc.terms (cst, f)).2.1 (termsRun os sel (w.getD i 0) ts cc.terms (cst, f)).2.2
          hlen hsh' (fun T' hT' => by cases hT'; exact t2) hpub' hrest
        refine ⟨?_, fun T' hT' => ?_, ih3, by rw [ih4, t3]⟩
        · rw [ih1, CoordD.ts, blockKnown_terms, zero_add]
        · cases hT'
          rw [ih2 T rfl, t1, CoordD.ts, List.map_map]
          simp only [Function.comp_def]
          ring

/-- A block's share of the framework accumulator: its selector times its known part, and a framework block's `β`. -/
noncomputable def accPart {mu : ℕ} (ζ : Fin mu → E) (pubF : Bool → ℕ → ℕ → E) (wv : ℕ → E) (βv : E) (bd : BlockD) :
    E :=
  sel ζ bd.kappa bd.q * ((if bd.owner = none then βv else 0) + blockKnown ζ bd.kappa (bd.ts pubF wv))

/-- A block's share of table `T`'s form at columns `col`: its selector times its form, if it is `T`'s. -/
noncomputable def formPart {mu : ℕ} (ζ : Fin mu → E) (pubF : Bool → ℕ → ℕ → E) (wv : ℕ → E) (βv : E) (col : ℕ → E)
    (T : Table) (bd : BlockD) : E :=
  if bd.owner = some T then sel ζ bd.kappa bd.q * (blockQuad βv (bd.ts pubF wv)).eval col else 0

/-- A form's value at columns `col`. -/
noncomputable def FormSt.qv (val : Val) (n : ℕ) (col : ℕ → E) (f : FormSt) : E :=
  Model.ev val f.const + f.lv val n col

theorem blockRun_sem (hF : Facts cs rl os st val) (mu : ℕ) (zeta w : List ℕ) (beta : ℕ) (pubF : Bool → ℕ → ℕ → E)
    (ζ : Fin mu → E) (hζ : ∀ j : Fin mu, ζ j = Model.ev val (zeta.getD j 0)) (bd : BlockD) (bc : BlockCert)
    (s : SideSt) (hsh : bd.shapeOk mu w.length bc = true) (hl : ∀ T, (s.forms T).coeffs.length = nCols T)
    (hpub : ∀ p ∈ bd.coords.zip bc.coords, ∀ nx j, p.1 = .pub nx j →
      Model.ev val p.2.x = ∑ z ∈ range (2 ^ bd.kappa), rowEq ζ bd.kappa z * pubF nx j z)
    (hc : callsOk cs rl (blockRun os mu zeta w beta bd bc s).1 = true) :
    Model.ev val (blockRun os mu zeta w beta bd bc s).2.acc = Model.ev val s.acc +
        accPart ζ pubF (fun i => Model.ev val (w.getD i 0)) (Model.ev val beta) bd ∧
      Model.ev val (blockRun os mu zeta w beta bd bc s).2.selSum = Model.ev val s.selSum + sel ζ bd.kappa bd.q ∧
      (∀ T col, ((blockRun os mu zeta w beta bd bc s).2.forms T).qv val (nCols T) col =
        (s.forms T).qv val (nCols T) col +
          formPart ζ pubF (fun i => Model.ev val (w.getD i 0)) (Model.ev val beta) col T bd) ∧
      (∀ T, ((blockRun os mu zeta w beta bd bc s).2.forms T).coeffs.length = nCols T) := by
  simp only [BlockD.shapeOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at hsh
  obtain ⟨⟨⟨⟨⟨⟨⟨-, hk⟩, hst⟩, -⟩, -⟩, hlen⟩, -⟩, hcs⟩ := hsh
  have hz : ζ = fun j : Fin mu => Model.ev val (zeta.getD j 0) := funext hζ
  unfold blockRun at hc ⊢
  set sl := chainOut os (o os bc.one) bc.steps with hsl
  have hselL : callsOk cs rl ((bc.one, Call.one) :: selCalls os zeta bd.kappa bd.q (o os bc.one) mu bc.steps) = true →
      Model.ev val sl = sel ζ bd.kappa bd.q := fun h => by
    obtain ⟨h1, h2⟩ := callsOk_cons h
    have h0 : Model.ev val (o os bc.one) = 1 := holds_of_mem hF h1 (List.mem_singleton_self _)
    rw [hsl, selCalls_sem hF zeta bd.kappa bd.q bc.steps _ mu (by omega) h2, h0, one_mul, hz]
    exact (sel_eq_prod _ _ _).symm
  cases ho : bd.owner with
  | some T =>
    simp only [ho] at hc
    try dsimp only
    simp only [callsOk_append, Bool.and_eq_true] at hc
    obtain ⟨⟨⟨hs1, hs2⟩, hs3⟩, hs4⟩ := hc
    obtain ⟨hz0, hr⟩ := callsOk_cons hs3
    have hsv := hselL hs1
    have hsum : Model.ev val (o os bc.sumAt) = Model.ev val s.selSum + Model.ev val sl :=
      holds_of_mem hF hs2 (List.mem_singleton_self _)
    have h0 : Model.ev val (o os bc.zero) = 0 := holds_of_mem hF hz0 (List.mem_singleton_self _)
    have hca : Model.ev val (o os bc.constAt) = Model.ev val sl *
        Model.ev val (coordRun os zeta w sl 0 bd.coords bc.coords (o os bc.zero, beta, s.forms T)).2.2.1 +
          Model.ev val (s.forms T).const := holds_of_mem hF hs4 List.mem_cons_self
    have hac : Model.ev val (o os bc.accAt) = Model.ev val sl *
        Model.ev val (coordRun os zeta w sl 0 bd.coords bc.coords (o os bc.zero, beta, s.forms T)).2.1 +
          Model.ev val s.acc := holds_of_mem hF hs4 (List.mem_cons_of_mem _ List.mem_cons_self)
    have hcr := fun col => coordRun_sem hF zeta w sl bd.kappa (some T) pubF col ζ hζ hk bd.coords bc.coords 0
      (o os bc.zero) beta (s.forms T) hlen (fun p hp => by rw [← ho]; exact hcs p hp) (fun T' hT' => by cases hT'; exact hl T) hpub hr
    refine ⟨?_, ?_, fun T' col => ?_, fun T' => ?_⟩
    · rw [hac, (hcr fun _ => 0).1, h0, accPart, ho, hsv, if_neg (by simp)]
      simp only [BlockD.ts]
      ring
    · rw [hsum, hsv]
    · by_cases hT : T' = T
      · subst hT
        obtain ⟨-, h2, -, h4⟩ := hcr col
        simp only [if_true, FormSt.qv, formPart, ho, BlockD.ts]
        rw [blockQuad_eval, hca]
        have e := h2 T' rfl
        rw [← hsv]
        simp only [FormSt.lv] at e ⊢
        linear_combination e
      · simp only [hT, if_false, formPart, ho, Option.some.injEq]
        rw [if_neg (Ne.symm hT), add_zero]
    · by_cases hT : T' = T
      · subst hT
        simp only [if_true]
        exact (hcr fun _ => 0).2.2.1 T' rfl
      · simp only [hT, if_false]
        exact hl T'
  | none =>
    simp only [ho] at hc
    try dsimp only
    simp only [callsOk_append, Bool.and_eq_true] at hc
    obtain ⟨⟨⟨hs1, hs2⟩, hr⟩, hs4⟩ := hc
    have hsv := hselL hs1
    have hsum : Model.ev val (o os bc.sumAt) = Model.ev val s.selSum + Model.ev val sl :=
      holds_of_mem hF hs2 (List.mem_singleton_self _)
    have hac : Model.ev val (o os bc.accAt) = Model.ev val sl *
        Model.ev val (coordRun os zeta w sl 0 bd.coords bc.coords (beta, beta, default)).2.1 +
          Model.ev val s.acc := holds_of_mem hF hs4 (List.mem_singleton_self _)
    have hcr := coordRun_sem hF zeta w sl bd.kappa none pubF (fun _ => 0) ζ hζ hk bd.coords bc.coords 0 beta beta
      default hlen (fun p hp => by rw [← ho]; exact hcs p hp) (fun T' hT' => by cases hT') hpub hr
    refine ⟨?_, ?_, fun T' col => ?_, fun T' => hl T'⟩
    · rw [hac, hcr.1, accPart, ho, hsv, if_pos rfl]
      simp only [BlockD.ts]
      ring
    · rw [hsum, hsv]
    · simp [formPart, ho]

theorem sideRun_sem (hF : Facts cs rl os st val) (mu : ℕ) (zeta w : List ℕ) (beta : ℕ) (pubF : Bool → ℕ → ℕ → E)
    (ζ : Fin mu → E) (hζ : ∀ j : Fin mu, ζ j = Model.ev val (zeta.getD j 0)) :
    ∀ (bds : List BlockD) (bcs : List BlockCert) (s : SideSt), bds.length = bcs.length →
      (∀ p ∈ bds.zip bcs, p.1.shapeOk mu w.length p.2 = true) → (∀ T, (s.forms T).coeffs.length = nCols T) →
      (∀ p ∈ bds.zip bcs, ∀ q ∈ p.1.coords.zip p.2.coords, ∀ nx j, q.1 = .pub nx j →
        Model.ev val q.2.x = ∑ z ∈ range (2 ^ p.1.kappa), rowEq ζ p.1.kappa z * pubF nx j z) →
      callsOk cs rl (sideRun os mu zeta w beta bds bcs s).1 = true →
      Model.ev val (sideRun os mu zeta w beta bds bcs s).2.acc = Model.ev val s.acc +
          (bds.map (accPart ζ pubF (fun i => Model.ev val (w.getD i 0)) (Model.ev val beta))).sum ∧
        Model.ev val (sideRun os mu zeta w beta bds bcs s).2.selSum = Model.ev val s.selSum +
          (bds.map fun bd => sel ζ bd.kappa bd.q).sum ∧
        (∀ T col, ((sideRun os mu zeta w beta bds bcs s).2.forms T).qv val (nCols T) col =
          (s.forms T).qv val (nCols T) col +
            (bds.map (formPart ζ pubF (fun i => Model.ev val (w.getD i 0)) (Model.ev val beta) col T)).sum) ∧
        (∀ T, ((sideRun os mu zeta w beta bds bcs s).2.forms T).coeffs.length = nCols T)
  | [], bcs, s, _, _, hl, _, _ => by cases bcs <;> simp [sideRun, hl]
  | bd :: bds, [], s, h, _, _, _, _ => by simp at h
  | bd :: bds, bc :: bcs, s, h, hsh, hl, hpub, hc => by
    simp only [sideRun, callsOk_append, Bool.and_eq_true] at hc ⊢
    obtain ⟨hb, hr⟩ := hc
    obtain ⟨b1, b2, b3, b4⟩ := blockRun_sem hF mu zeta w beta pubF ζ hζ bd bc s (hsh _ List.mem_cons_self) hl
      (hpub _ List.mem_cons_self) hb
    obtain ⟨r1, r2, r3, r4⟩ := sideRun_sem hF mu zeta w beta pubF ζ hζ bds bcs _ (by simpa using h)
      (fun p hp => hsh p (List.mem_cons_of_mem _ hp)) b4 (fun p hp => hpub p (List.mem_cons_of_mem _ hp)) hr
    refine ⟨?_, ?_, fun T col => ?_, r4⟩
    · rw [r1, b1, List.map_cons, List.sum_cons]
      ring
    · rw [r2, b2, List.map_cons, List.sum_cons]
      ring
    · rw [r3, b3, List.map_cons, List.sum_cons]
      ring

/-- A form as a `Quad`: its constant, a coefficient per column, its products. -/
noncomputable def FormSt.quad (val : Val) (n : ℕ) (f : FormSt) : Quad where
  const := Model.ev val f.const
  lin := (List.range n).map fun c => (c, Model.ev val (f.coeffs.getD c 0))
  prods := f.prods.map fun p => (p.1, p.2.1, Model.ev val p.2.2)

theorem sum_range_list (n : ℕ) (h : ℕ → E) : ∑ i ∈ range n, h i = ((List.range n).map h).sum := by
  rw [Finset.sum_eq_multiset_sum, Finset.range_val, Multiset.range, Multiset.map_coe, Multiset.sum_coe]

theorem sum_fin_getElem {α : Type} (l : List α) (h : α → E) : ∑ i : Fin l.length, h l[i] = (l.map h).sum := by
  rw [← List.ofFn_getElem_eq_map, List.sum_ofFn]
  rfl

theorem FormSt.quad_eval (val : Val) (n : ℕ) (col : ℕ → E) (f : FormSt) :
    (f.quad val n).eval col = f.qv val n col := by
  simp only [FormSt.quad, Quad.eval, FormSt.qv, FormSt.lv, List.map_map, Function.comp_def, sum_range_list]
  ring

/-- A framework block's terms are its coordinates' values, which no form reads. -/
theorem coordsTs_dval {pubF : Bool → ℕ → ℕ → E} {wv : ℕ → E} (col : ℕ → E) :
    ∀ (i : ℕ) (cds : List CoordD), (∀ c ∈ cds, ∀ ts, c ≠ .terms ts) →
      ((coordsTs pubF wv i cds).map fun t => t.1 * dval col t.2).sum = 0
  | _, [], _ => by simp [coordsTs]
  | i, c :: cds, h => by
    have ih := coordsTs_dval (pubF := pubF) (wv := wv) col (i + 1) cds fun c' hc' => h c' (List.mem_cons_of_mem _ hc')
    simp only [coordsTs, List.map_append, List.sum_append, ih, add_zero]
    cases c with
    | idx b s => simp [CoordD.ts, dval]
    | pub nx j => simp [CoordD.ts, dval]
    | terms ts => exact absurd rfl (h _ List.mem_cons_self ts)

namespace SideCert

/-- The named point `ζ`. -/
noncomputable def zetaV (sc : SideCert) (val : Val) : Fin sc.mu → E := fun j => Model.ev val (sc.zeta.getD j 0)

/-- The named fingerprint weights. -/
noncomputable def wV (sc : SideCert) (val : Val) (i : ℕ) : E := Model.ev val (sc.w.getD i 0)

/-- Block `b`'s weighted terms. -/
noncomputable def tsOf (sc : SideCert) (val : Val) (pubF : Bool → ℕ → ℕ → E) (b : Fin sc.blocks.length) :
    List (E × DCoord) :=
  sc.blocks[b].ts pubF (sc.wV val)

/-- Block `b`'s leaves: `β + Σ_i w_i c_i(z)`, its columns none (a framework block reads none). -/
noncomputable def leafOf (sc : SideCert) (val : Val) (pubF : Bool → ℕ → ℕ → E) (b : Fin sc.blocks.length) (z : ℕ) :
    E :=
  blockLeaf (Model.ev val sc.beta) (sc.tsOf val pubF b) (fun _ => 0) z

/-- Each public coordinate's named value is its column's extension at `ζ[..κ]`: the premise for the fixed hints. -/
def PubTrue (sc : SideCert) (val : Val) (pubF : Bool → ℕ → ℕ → E) : Prop :=
  ∀ p ∈ sc.blocks.zip sc.certs, ∀ q ∈ p.1.coords.zip p.2.coords, ∀ nx j, q.1 = .pub nx j →
    Model.ev val q.2.x = ∑ z ∈ range (2 ^ p.1.kappa), rowEq (sc.zetaV val) p.1.kappa z * pubF nx j z

end SideCert

/-- The side as `AirLink`'s decomposition states it: where the calls hold, the certificate passes and each public
coordinate's named value is its column's extension at `ζ[..κ]`, the named share is `AirLink.framework` over the
recorded blocks at the named point, weights and `β`, and each table's form is `AirLink.sideForm`'s at every column
vector. -/
theorem SideCert.sem (hF : Facts cs rl os st val) {sc : SideCert} (h : sc.ok os cs rl = true)
    (pubF : Bool → ℕ → ℕ → E) (hpub : sc.PubTrue val pubF) :
    Model.ev val (sc.fw os) = framework (sc.zetaV val) (fun b => sc.blocks[b].kappa) (fun b => sc.blocks[b].q)
        (fun b => sc.blocks[b].owner) (sc.tsOf val pubF) (sc.leafOf val pubF) ∧
      ∀ T col, (((sc.final os).forms T).quad val (nCols T)).eval col =
        (sideForm (sc.zetaV val) (fun b => sc.blocks[b].kappa) (fun b => sc.blocks[b].q) (fun b => sc.blocks[b].owner)
          (Model.ev val sc.beta) (sc.tsOf val pubF) T).eval col := by
  simp only [SideCert.ok, SideCert.shapeOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hzl, hbl⟩, hsh⟩, -⟩, hc⟩ := h
  simp only [SideCert.calls, callsOk_append, Bool.and_eq_true] at hc
  obtain ⟨⟨hc0, hrun⟩, hfw⟩ := hc
  have hfz : Model.ev val (o os sc.formZero) = 0 := holds_of_mem hF hc0 List.mem_cons_self
  have hz0 : Model.ev val (o os sc.zeroAt) = 0 :=
    holds_of_mem hF hc0 (List.mem_cons_of_mem _ List.mem_cons_self)
  have ho1 : Model.ev val (o os sc.oneAt) = 1 :=
    holds_of_mem hF hc0 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  obtain ⟨r1, r2, r3, -⟩ := sideRun_sem hF sc.mu sc.zeta sc.w sc.beta pubF (sc.zetaV val) (fun _ => rfl) sc.blocks
    sc.certs (sc.init os) hbl hsh (fun T => by simp [SideCert.init]) hpub hrun
  have hblk : ∀ b : Fin sc.blocks.length, sc.blocks[b].kappa ≤ sc.mu ∧
      ∀ c ∈ sc.blocks[b].coords, sc.blocks[b].owner = none → ∀ ts, c ≠ .terms ts := by
    intro b
    have hb : (sc.blocks[b], sc.certs[b.val]'(hbl ▸ b.isLt)) ∈ sc.blocks.zip sc.certs := by
      have := List.getElem_mem (l := sc.blocks.zip sc.certs) (n := b.val)
        (by rw [List.length_zip, ← hbl, min_self]; exact b.isLt)
      rwa [List.getElem_zip] at this
    have hs := hsh _ hb
    simp only [BlockD.shapeOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at hs
    obtain ⟨⟨⟨⟨⟨⟨⟨-, hk⟩, -⟩, -⟩, -⟩, hlen⟩, -⟩, hcs⟩ := hs
    refine ⟨hk, fun c hc hown ts hct => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
    have hm : (sc.blocks[b].coords[i], (sc.certs[b.val]'(hbl ▸ b.isLt)).coords[i]'(hlen ▸ hi)) ∈
        sc.blocks[b].coords.zip (sc.certs[b.val]'(hbl ▸ b.isLt)).coords := by
      have := List.getElem_mem (l := sc.blocks[b].coords.zip (sc.certs[b.val]'(hbl ▸ b.isLt)).coords) (n := i)
        (by rw [List.length_zip, ← hlen, min_self]; exact hi)
      rwa [List.getElem_zip] at this
    have := hcs _ hm
    simp only at this
    rw [hct, hown] at this
    simp [CoordD.shapeOk] at this
  refine ⟨?_, fun T col => ?_⟩
  · have hfwv : Model.ev val (sc.fw os) = Model.ev val (sc.final os).acc + Model.ev val (sc.final os).selSum :=
      holds_of_mem hF hfw List.mem_cons_self
    rw [hfwv, SideCert.final, r1, r2]
    simp only [SideCert.init, hz0, ho1, zero_add]
    rw [framework, Finset.sum_filter, Finset.sum_filter, ← sum_fin_getElem, ← sum_fin_getElem, ← sum_add_distrib,
      one_sub_eq_one_add]
    have e : ∀ b : Fin sc.blocks.length,
        accPart (sc.zetaV val) pubF (sc.wV val) (Model.ev val sc.beta) sc.blocks[b] =
          (if sc.blocks[b].owner = none then sel (sc.zetaV val) sc.blocks[b].kappa sc.blocks[b].q *
            ∑ z ∈ range (2 ^ sc.blocks[b].kappa), rowEq (sc.zetaV val) sc.blocks[b].kappa z * sc.leafOf val pubF b z
            else 0) +
          (if sc.blocks[b].owner ≠ none then sel (sc.zetaV val) sc.blocks[b].kappa sc.blocks[b].q *
            blockKnown (sc.zetaV val) sc.blocks[b].kappa (sc.tsOf val pubF b) else 0) := by
      intro b
      obtain ⟨hk, hterms⟩ := hblk b
      rw [accPart]
      by_cases ho : sc.blocks[b].owner = none
      · simp only [SideCert.leafOf]
        rw [if_pos ho, if_pos ho, if_neg (not_not.mpr ho), add_zero,
          block_sum (sc.zetaV val) _ _ fun _ _ => 0, blockQuad_eval, ← sum_mul, sum_rowEq _ _ hk, one_mul,
          SideCert.tsOf, BlockD.ts, coordsTs_dval _ 0 _ fun c hc => hterms c hc ho, add_zero]
      · rw [if_neg ho, if_neg ho, if_pos ho, zero_add, zero_add]
        rfl
    have hw : (fun i => Model.ev val (sc.w.getD i 0)) = sc.wV val := rfl
    rw [hw, sum_congr rfl fun b _ => e b]
  · rw [FormSt.quad_eval, SideCert.final, r3, sideForm_eval, Finset.sum_filter, ← sum_fin_getElem]
    have hi : (sc.init os).forms T =
        (⟨o os sc.formZero, List.replicate (nCols T) (o os sc.formZero), []⟩ : FormSt) := rfl
    have h0 : ((sc.init os).forms T).qv val (nCols T) col = 0 := by
      rw [hi, FormSt.qv, FormSt.lv, hfz]
      simp only [List.map_nil, List.sum_nil, add_zero, zero_add]
      refine Finset.sum_eq_zero fun c hc => ?_
      rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos (mem_range.mp hc), Option.getD_some, hfz,
        zero_mul]
    rw [h0, zero_add]
    rfl

end Sem

/-! `BusBlocks::new` transcribed. -/

mutual
/-- A slot limb's terms (`Coord::Sum` flattened). -/
def formTerms : Form → List TermD
  | .const w => [.const w]
  | .col c => [.col c]
  | .prod a b => [.prod a b]
  | .sum ts => formTermsSum ts

def formTermsSum : List Form → List TermD
  | [] => []
  | t :: ts => formTerms t ++ formTermsSum ts
end

/-- A slot's key coordinate on a side: its key column on the pull side (`SlotKey::column`), its `Next` column on the
push side. -/
def keyCoord (pull : Bool) (slot : ℕ) : CoordD := if pull then .idx (slot * 2 ^ 32) 0 else .pub true slot

/-- `BusBlocks::new`'s blocks on a side, without their heights and offsets: the public table's slot, the framework's,
its four value columns (`Constant(j)`), then each owned table's slots in `Table::OWNED`'s order, its limbs the table's
forms (`AirLink.forms`). -/
def recCoords (pull : Bool) : List (Option Table × List CoordD) :=
  (none, keyCoord pull (firstSlot .pub) :: (List.range 4).map (CoordD.pub false)) ::
    ownedList.flatMap fun T => (List.range T.nSlots).map fun i =>
      (some T, keyCoord pull (firstSlot T + i) :: ((AirLink.forms T).getD i []).map fun f => .terms (formTerms f))

/-- Each owned table's first column (`RecLayout::TABLE_COLUMNS`): after the hash witness, the tables in order. -/
def colBase (T : Table) : ℕ := 1 + ((ownedList.take (ownedList.idxOf T)).map nCols).sum

/-! Reading the marks. -/

def parseTerm (base : ℕ) (w : String) : Option TermD :=
  match w.toList with
  | 'k' :: r => (String.ofList r).toNat?.map .const
  | 'c' :: r => (String.ofList r).toNat?.bind fun c => if base ≤ c then some (.col (c - base)) else none
  | 'x' :: r => match (String.ofList r).splitOn "." with
    | [a, b] => match a.toNat?, b.toNat? with
      | some a, some b => if base ≤ a && base ≤ b then some (.prod (a - base) (b - base)) else none
      | _, _ => none
    | _ => none
  | _ => none

def parseCoord (base : ℕ) (w : String) : Option CoordD :=
  match w.toList with
  | 'i' :: r => match (String.ofList r).splitOn "." with
    | [b, sh] => match b.toNat?, sh.toNat? with
      | some b, some sh => some (.idx b sh)
      | _, _ => none
    | _ => none
  | 'p' :: 'n' :: r => (String.ofList r).toNat?.map (.pub true)
  | 'p' :: 'c' :: r => (String.ofList r).toNat?.map (.pub false)
  | ['e'] => some (.terms [])
  | _ => ((w.splitOn "+").mapM (parseTerm base)).map .terms

/-- A `bus block kappa offset owner coords...` mark's words after `bus block`. -/
def parseBlock (ws : List String) : Option BlockD := do
  let k :: off :: own :: coords := ws | none
  let (owner, base) ← if own == "-" then some (none, 0) else match own.splitOn ":" with
    | [t, b] => do
      let T ← ownedList[← t.toNat?]?
      let b ← b.toNat?
      if b == colBase T then some (some T, b) else none
    | _ => none
  return { kappa := ← k.toNat?, off := ← off.toNat?, owner, coords := ← coords.mapM (parseCoord base) }

/-- A dump's bus marks: per verified child, the calls before its marks, the depth `μ`, and its push and pull blocks. -/
def busGroups (text : String) : List (ℕ × ℕ × List BlockD × List BlockD) := Id.run do
  let head := (text.splitOn "circuit\n").headD ""
  let mut n := 0
  let mut out : Array (ℕ × ℕ × List BlockD × List BlockD) := #[]
  let mut cur : Option (ℕ × ℕ × ℕ × Array BlockD × Array BlockD) := none
  for line in head.splitOn "\n" do
    let ws := line.splitOn " "
    match ws with
    | "bus" :: "side" :: si :: mu :: _ =>
      let some si := si.toNat? | continue
      let some mu := mu.toNat? | continue
      match cur with
      | some (p, m, _, a, b) => cur := some (p, m, si, a, b)
      | none => cur := some (n, mu, si, #[], #[])
    | "bus" :: "block" :: rest =>
      match cur, parseBlock rest with
      | some (p, m, si, a, b), some bd => cur := some (p, m, si, if si == 0 then a.push bd else a,
          if si == 1 then b.push bd else b)
      | _, _ => cur := none
    | _ =>
      if line == "" || Dump.isEdge line || Dump.isBus line then continue
      if let some (p, m, _, a, b) := cur then
        out := out.push (p, m, a.toList, b.toList)
        cur := none
      match Dump.parseLine line with
      | .ok (.call _) => n := n + 1
      | _ => pure ()
  return out.toList

/-! Finding a side's calls. -/

section Find

variable (calls : Array Call) (os : Array (List ℕ))

/-- The first call from `pos` that is `c`. -/
def findCall (pos : ℕ) (c : Call) : Option ℕ :=
  (List.range (calls.size - pos)).findSome? fun d => if calls[pos + d]? == some c then some (pos + d) else none

/-- A chain of calls from `pos`, each found after the last, its output read by the next (`mk acc`). -/
def findChain (pos : ℕ) (acc : ℕ) : List (ℕ → Call) → Option (List ℕ × ℕ × ℕ)
  | [] => some ([], acc, pos)
  | f :: rest => do
    let j ← findCall calls pos (f acc)
    let (js, out, p) ← findChain (j + 1) (o os j) rest
    return (j :: js, out, p)

/-- A side's certificate: `Side::decompose`'s calls from `pos`, at the point `zeta`, the weights `w` and `β`, the
forms' `zero` at `formZero` (side `0` finds its own, the first `zero` from `pos`), and the call after its share. -/
def sideOf (pos mu : ℕ) (zeta w : List ℕ) (beta : ℕ) (blocks : List BlockD) (formZero : Option ℕ) :
    Option (SideCert × ℕ) := do
  let fz ← match formZero with
    | some j => some j
    | none => findCall calls pos .zero
  let zeroAt ← findCall calls (max pos (fz + 1)) .zero
  let oneAt ← findCall calls (zeroAt + 1) .one
  let mut pos := oneAt + 1
  let mut st : SideSt := ⟨o os zeroAt, o os oneAt, fun T => ⟨o os fz, List.replicate (nCols T) (o os fz), []⟩⟩
  let mut certs : Array BlockCert := #[]
  for bd in blocks do
    let one ← findCall calls pos .one
    let (steps, sl, p) ← findChain calls os (one + 1) (o os one) ((List.range (mu - bd.kappa)).map fun d acc =>
      let j := mu - 1 - d
      if bd.q.testBit (j - bd.kappa) then .mul acc (zeta.getD j 0) else .mulAdd acc (zeta.getD j 0) acc)
    let sumAt ← findCall calls p (.add st.selSum sl)
    pos := sumAt + 1
    let zero ← match bd.owner with
      | some _ => findCall calls pos .zero
      | none => some 0
    if bd.owner.isSome then pos := zero + 1
    let f := match bd.owner with
      | some T => st.forms T
      | none => default
    let mut k := if bd.owner.isSome then o os zero else beta
    let mut cst := beta
    let mut form := f
    let mut ccs : Array CoordCert := #[]
    for (c, i) in bd.coords.zipIdx do
      let wi := w.getD i 0
      match c with
      | .idx base shift =>
        let e ← findCall calls pos (.eConst base 0 0)
        let (js, x, p) ← findChain calls os (e + 1) (o os e) ((List.range bd.kappa).map fun kk acc =>
          .mulConstAdd (zeta.getD kk 0) (2 ^ (kk + shift)) 0 0 acc)
        let a ← findCall calls p (.mulAdd wi x k)
        ccs := ccs.push { idx := e :: js, addAt := a }
        k := o os a
        pos := a + 1
      | .pub _ _ =>
        let a ← (List.range (calls.size - pos)).findSome? fun d => match calls[pos + d]? with
          | some (.mulAdd a' _ d') => if a' == wi && d' == k then some (pos + d) else none
          | _ => none
        let .mulAdd _ x _ := calls.getD a .zero | none
        ccs := ccs.push { x, addAt := a }
        k := o os a
        pos := a + 1
      | .terms ts =>
        let mut js : Array ℕ := #[]
        for t in ts do
          let call := match t with
            | .const v => Call.mulConstAdd wi v 0 0 cst
            | .col c => .mulAdd sl wi (form.coeffs.getD c 0)
            | .prod _ _ => .mul sl wi
          let j ← findCall calls pos call
          js := js.push j
          pos := j + 1
          match t with
          | .const _ => cst := o os j
          | .col c => form := { form with coeffs := form.coeffs.set c (o os j) }
          | .prod a b => form := { form with prods := form.prods ++ [(a, b, o os j)] }
        ccs := ccs.push { terms := js.toList }
    let (constAt, accAt) ← match bd.owner with
      | some _ => do
        let ca ← findCall calls pos (.mulAdd sl cst f.const)
        let aa ← findCall calls (ca + 1) (.mulAdd sl k st.acc)
        pure (ca, aa)
      | none => do pure (0, ← findCall calls pos (.mulAdd sl k st.acc))
    pos := accAt + 1
    let bc : BlockCert := { one, steps, sumAt, zero, coords := ccs.toList, constAt, accAt }
    certs := certs.push bc
    st := (blockRun os mu zeta w beta bd bc st).2
  let fwAt ← findCall calls pos (.add st.acc st.selSum)
  return ({ mu, zeta, w, beta, formZero := fz, zeroAt, oneAt, blocks, certs := certs.toList, fwAt }, fwAt + 1)

end Find

/-- The bus GKR's last point: its last layer's `[low, high]` and rounds' challenges. -/
def GkrCert.point (g : GkrCert) (scs : Array SumcheckCert) (tops : Array TopCert) (odds : Array OddCert)
    (os : Array (List ℕ)) : List ℕ :=
  match g.layers.getLast? with
  | some lc => [lc.layer.low.chal, lc.layer.high.chal] ++ ((scs[lc.sc]?.map fun sc => sc.rounds.map (·.chal)).getD [])
  | none => (g.start tops odds os).2.2

/-- A side's final form of `T` is the named form `f`: its constant, its coefficient per column and its products. -/
def FormCert.isFinal (f : FormCert) (n : ℕ) (st : FormSt) : Bool :=
  f.const == st.const && f.lin.map (fun t => (t.1, t.2.1)) == (List.range n).map (fun c => (c, st.coeffs.getD c 0)) &&
    f.prods.map (fun t => (t.1, t.2.1, t.2.2.1)) == st.prods

/-- Both sides of a table sumcheck's bus (`SideCert`s for push and pull) against its named certificates: each side's
certificate passes; its share is the GKR's named framework share; its point is the GKR's last point; the sides share
the weights and `β`; the table sumcheck's point is the bus point's first coordinates; each owned table's final forms are its residual term's named push and pull forms; its blocks are
`BusBlocks::new`'s (`recCoords`) with each owned table's height its residual term's `τ`. -/
def sidesOk (os : Array (List ℕ)) (cs : Array Call) (rl : Array Bool) (scs : Array SumcheckCert)
    (tops : Array TopCert) (odds : Array OddCert) (g : GkrCert) (rc : ResidCert) (s0 s1 : SideCert) : Bool :=
  s0.ok os cs rl && s1.ok os cs rl && s0.fw os == g.fw.1 && s1.fw os == g.fw.2 &&
    s0.zeta == g.point scs tops odds os && s1.zeta == s0.zeta && s0.mu == s0.zeta.length && s1.mu == s0.mu &&
    s1.w == s0.w && s1.beta == s0.beta && rc.zeta == s0.zeta.take rc.zeta.length &&
    ownedList.all (fun T => (rc.termOf T).push.isFinal (nCols T) ((s0.final os).forms T) &&
      (rc.termOf T).pull.isFinal (nCols T) ((s1.final os).forms T)) &&
    s0.blocks.map (fun b => (b.owner, b.coords)) == recCoords false &&
    s1.blocks.map (fun b => (b.owner, b.coords)) == recCoords true &&
    (s0.blocks ++ s1.blocks).all fun b => match b.owner with
      | some T => b.kappa == (rc.termOf T).tau
      | none => b.kappa == (s0.blocks.headD default).kappa

/-- The fingerprint weights and `β` a side reads, from its first block (the framework's): back from that block's
`mul_add(sel, leaf, acc)` through its coordinates' `mul_add(w_i, x_i, leaf)` to `β`. -/
def weightsOf (calls : Array Call) (os : Array (List ℕ)) (maker : Array ℕ) (pos mu : ℕ) (zeta : List ℕ)
    (bd : BlockD) : Option (List ℕ × ℕ) := do
  let fz ← findCall calls pos .zero
  let zeroAt ← findCall calls (fz + 1) .zero
  let oneAt ← findCall calls (zeroAt + 1) .one
  let one ← findCall calls (oneAt + 1) .one
  let (_, sl, p) ← findChain calls os (one + 1) (o os one) ((List.range (mu - bd.kappa)).map fun d acc =>
    let j := mu - 1 - d
    if bd.q.testBit (j - bd.kappa) then .mul acc (zeta.getD j 0) else .mulAdd acc (zeta.getD j 0) acc)
  let accAt ← (List.range (calls.size - p)).findSome? fun d => match calls[p + d]? with
    | some (.mulAdd a _ d') => if a == sl && d' == o os zeroAt then some (p + d) else none
    | _ => none
  let .mulAdd _ leaf _ := calls.getD accAt .zero | none
  let mut cur := leaf
  let mut ws : List ℕ := []
  for _ in bd.coords do
    let .mulAdd wi _ prev := calls.getD (maker.getD cur 0) .zero | none
    ws := wi :: ws
    cur := prev
  return (ws, cur)

/-! The side against the leaf layer: `balance_named`'s premise. -/

section Dec

variable {cs : Array Call} {rl : Array Bool} {os : Array (List ℕ)} {st : ℕ → Fin 4 → K} {val : Val}

theorem framework_congr {n m : ℕ} (ζ : Fin n → E) (κ q : Fin m → ℕ) (owner : Fin m → Option Table)
    (ts : Fin m → List (E × DCoord)) {leaf leaf' : Fin m → ℕ → E} (h : ∀ b, owner b = none → leaf b = leaf' b) :
    framework ζ κ q owner ts leaf = framework ζ κ q owner ts leaf' := by
  unfold framework
  congr 2
  exact Finset.sum_congr rfl fun b hb => by rw [h b (Finset.mem_filter.mp hb).2]

/-- Each recorded block's shape. -/
theorem SideCert.blockShape {sc : SideCert} (h : sc.shapeOk = true) (b : Fin sc.blocks.length) :
    ∃ bc, sc.blocks[b].shapeOk sc.mu sc.w.length bc = true := by
  simp only [SideCert.shapeOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨-, hbl⟩, hsh⟩, -⟩ := h
  have hb : (sc.blocks[b], sc.certs[b.val]'(hbl ▸ b.isLt)) ∈ sc.blocks.zip sc.certs := by
    have := List.getElem_mem (l := sc.blocks.zip sc.certs) (n := b.val)
      (by rw [List.length_zip, ← hbl, min_self]; exact b.isLt)
    rwa [List.getElem_zip] at this
  exact ⟨_, hsh _ hb⟩

/-- The recorded blocks fit the side's `2^μ` leaves, aligned, and do not overlap. -/
theorem SideCert.fits {sc : SideCert} (h : sc.shapeOk = true) :
    (∀ b : Fin sc.blocks.length, sc.blocks[b].kappa ≤ sc.mu ∧ (∀ T, sc.blocks[b].owner = some T → T ∈ owned) ∧
      2 ^ sc.blocks[b].kappa * sc.blocks[b].q + 2 ^ sc.blocks[b].kappa ≤ 2 ^ sc.mu) ∧
    ∀ b b' : Fin sc.blocks.length, b ≠ b' →
      Disjoint (Ico (2 ^ sc.blocks[b].kappa * sc.blocks[b].q) (2 ^ sc.blocks[b].kappa * sc.blocks[b].q +
        2 ^ sc.blocks[b].kappa))
      (Ico (2 ^ sc.blocks[b'].kappa * sc.blocks[b'].q) (2 ^ sc.blocks[b'].kappa * sc.blocks[b'].q +
        2 ^ sc.blocks[b'].kappa)) := by
  have hoff : ∀ b : Fin sc.blocks.length, 2 ^ sc.blocks[b].kappa * sc.blocks[b].q = sc.blocks[b].off := fun b => by
    obtain ⟨bc, hs⟩ := sc.blockShape h b
    simp only [BlockD.shapeOk, Bool.and_eq_true, beq_iff_eq] at hs
    exact Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hs.1.1.1.1.2)
  refine ⟨fun b => ?_, fun b b' hne => ?_⟩
  · obtain ⟨bc, hs⟩ := sc.blockShape h b
    simp only [BlockD.shapeOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hs
    obtain ⟨⟨⟨⟨⟨⟨⟨ho, hk⟩, -⟩, -⟩, hin⟩, -⟩, -⟩, -⟩ := hs
    refine ⟨hk, fun T hT => by rw [hT] at ho; simpa using ho, by rw [hoff]; exact hin⟩
  · simp only [SideCert.shapeOk, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
      beq_iff_eq] at h
    have hd := h.2 b b.isLt b' b'.isLt
    rw [hoff, hoff]
    rcases hd with hd | hd
    · exact absurd (Fin.ext hd) hne
    · have g1 : sc.blocks.getD b default = sc.blocks[b] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem b.isLt, Option.getD_some]
        rfl
      have g2 : sc.blocks.getD b' default = sc.blocks[b'] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem b'.isLt, Option.getD_some]
        rfl
      rw [g1, g2] at hd
      simp only [BlockD.disjoint, Bool.or_eq_true, decide_eq_true_eq] at hd
      rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [Finset.mem_Ico] at hx hx'
      rcases hd with hd | hd <;> omega

/-- A side against its leaf layer: where the calls hold, the certificate passes and its public coordinates' named
values are their columns' extensions, the named share plus the leaf claim of the stacked layer (`stackLeaf`: each
owned block's leaves `β + Σ_i w_i c_i` over its table's committed rows, the framework blocks' their public columns',
padding elsewhere) is the forms' sums at `ζ` (`formSums`), for any forms evaluating as the side's final forms, every
owned block of `T` at `T`'s height. -/
theorem SideCert.dec (hF : Facts cs rl os st val) {sc : SideCert} (h : sc.ok os cs rl = true)
    (pubF : Bool → ℕ → ℕ → E) (hpub : sc.PubTrue val pubF) (w : Witness)
    (hτ : ∀ b : Fin sc.blocks.length, ∀ T, sc.blocks[b].owner = some T → sc.blocks[b].kappa = tauOf w T)
    (forms : Table → Quad)
    (hforms : ∀ T ∈ owned, ∀ col, (forms T).eval col = (((sc.final os).forms T).quad val (nCols T)).eval col)
    (i : Fin 2) :
    Model.ev val (sc.fw os) + ∑ x ∈ range (2 ^ sc.mu), rowEq (sc.zetaV val) sc.mu x *
      stackLeaf (fun b => sc.blocks[b].kappa) (fun b => sc.blocks[b].q) (fun b z =>
        if sc.blocks[b].owner = none then sc.leafOf val pubF b z
        else blockLeaf (Model.ev val sc.beta) (sc.tsOf val pubF b)
          (fun c => emb (w.cols (sc.blocks[b].owner.getD .emul) z c)) z) x =
      formSums w (sc.zetaV val) (fun _ => forms) i := by
  have hsem := SideCert.sem hF h pubF hpub
  have hsh : sc.shapeOk = true := by
    simp only [SideCert.ok, Bool.and_eq_true] at h
    exact h.1
  obtain ⟨hfit, hdisj⟩ := SideCert.fits hsh
  set leaf : Fin sc.blocks.length → ℕ → E := fun b z =>
    if sc.blocks[b].owner = none then sc.leafOf val pubF b z
    else blockLeaf (Model.ev val sc.beta) (sc.tsOf val pubF b)
      (fun c => emb (w.cols (sc.blocks[b].owner.getD .emul) z c)) z with hleafdef
  have htot := totals_eq_formSums (sc.zetaV val) (fun b => sc.blocks[b].kappa) (fun b => sc.blocks[b].q)
    (fun b => sc.blocks[b].owner) (Model.ev val sc.beta) (sc.tsOf val pubF) w
    (stackLeaf (fun b => sc.blocks[b].kappa) (fun b => sc.blocks[b].q) leaf) leaf (fun b => (hfit b).1)
    (fun b => (hfit b).2.2) hdisj (stackLeaf_block _ _ _ hdisj) (stackLeaf_pad _ _ _)
    (fun b T hT => ⟨(hfit b).2.1 T hT, hτ b T hT, fun z => by
      have hT' : sc.blocks[b].owner = some T := hT
      simp only [hleafdef, hT', reduceCtorEq, if_false, Option.getD_some]⟩) i
  rw [hsem.1, framework_congr (sc.zetaV val) _ _ _ (sc.tsOf val pubF) (leaf' := leaf)
    (fun b hb => by
      have hb' : sc.blocks[b].owner = none := hb
      funext z
      simp only [hleafdef, hb', if_true]), htot]
  simp only [formSums]
  refine Finset.sum_congr rfl fun T hT => Finset.sum_congr rfl fun z _ => ?_
  rw [hforms T hT, hsem.2]

end Dec

/-! The recorded blocks' leaves as the bus's tuples: the GKR's leaf layer as those blocks. -/

mutual
theorem formTerms_val (r : ℕ → K) (z : ℕ) : ∀ f : Form,
    ((formTerms f).map fun t => (TermD.dc t).val (fun c => emb (r c)) z).sum = emb (f.eval r)
  | .const w => by simp [formTerms, TermD.dc, DCoord.val, Form.eval]
  | .col c => by simp [formTerms, TermD.dc, DCoord.val, Form.eval]
  | .prod a b => by simp [formTerms, TermD.dc, DCoord.val, Form.eval, emb_mul]
  | .sum ts => by rw [formTerms, Form.eval, formTermsSum_val r z ts]

theorem formTermsSum_val (r : ℕ → K) (z : ℕ) : ∀ ts : List Form,
    ((formTermsSum ts).map fun t => (TermD.dc t).val (fun c => emb (r c)) z).sum = emb (Form.evalSum r ts)
  | [] => by simp [formTermsSum, Form.evalSum, emb_zero]
  | t :: ts => by
    rw [formTermsSum, List.map_append, List.sum_append, formTerms_val r z t, formTermsSum_val r z ts, Form.evalSum,
      emb_add]
end

/-- A limb coordinate's terms at weight `w` sum to `w` times the limb's value. -/
theorem limb_leaf (pubF : Bool → ℕ → ℕ → E) (w : E) (r : ℕ → K) (z : ℕ) (f : Form) :
    (((CoordD.terms (formTerms f)).ts pubF w).map fun t => t.1 * t.2.val (fun c => emb (r c)) z).sum =
      w * emb (f.eval r) := by
  rw [CoordD.ts, List.map_map, ← formTerms_val r z f, ← List.sum_map_mul_left]
  rfl

/-- The fingerprint of a bus tuple: its key and four limbs at the first five weights. -/
theorem fpAt_busTuple (A : Fin 4 → E) (k : ℕ) (l : Fin 4 → K) :
    UnionSound.fpAt A (busTuple (k, l)) = UnionSound.eqAt A 0 * emb (ofWord k) +
      (UnionSound.eqAt A 1 * emb (l 0) + (UnionSound.eqAt A 2 * emb (l 1) + (UnionSound.eqAt A 3 * emb (l 2) +
        UnionSound.eqAt A 4 * emb (l 3)))) := by
  simp only [UnionSound.fpAt, Fin.sum_univ_succ, Fin.sum_univ_zero, busTuple]
  simp

/-- A slot's block leaf: `β` plus its key coordinate's value and its four limbs at the first five weights, the
weights `eq(A, k)`, is the bus tuple's `β + fp_A` (`AirLink.busTuple`), the key's value `kv`. -/
theorem slotLeaf (pubF : Bool → ℕ → ℕ → E) (wv : ℕ → E) (A : Fin 4 → E)
    (h0 : wv 0 = UnionSound.eqAt A 0) (h1 : wv 1 = UnionSound.eqAt A 1) (h2 : wv 2 = UnionSound.eqAt A 2)
    (h3 : wv 3 = UnionSound.eqAt A 3) (h4 : wv 4 = UnionSound.eqAt A 4) (β : E) (k : CoordD) (kv : ℕ) (fs : List Form)
    (hfs : fs.length = 4) (r : ℕ → K) (z : ℕ)
    (hk : ((k.ts pubF (wv 0)).map fun t => t.1 * t.2.val (fun c => emb (r c)) z).sum = wv 0 * emb (ofWord kv)) :
    blockLeaf β (coordsTs pubF wv 0 (k :: fs.map fun f => .terms (formTerms f))) (fun c => emb (r c)) z =
      β + UnionSound.fpAt A (busTuple (kv, fun j => (fs.getD j .zero).eval r)) := by
  match fs, hfs with
  | [f0, f1, f2, f3], _ =>
    simp only [blockLeaf, coordsTs, List.map_cons, List.map_nil, List.map_append, List.sum_append, hk,
      limb_leaf, List.sum_nil, add_zero, fpAt_busTuple]
    simp only [zero_add, Nat.reduceAdd, h0, h1, h2, h3, h4, List.getD_eq_getElem?_getD]
    rfl

/-- An index key coordinate's value at a row of a slot: `slot · 2^32 ^ z` is the slot's key (`SlotKey::new`). -/
theorem idxKey_val (pubF : Bool → ℕ → ℕ → E) (w : E) (row : ℕ → E) (slot z : ℕ) (hz : z < 2 ^ 32) :
    (((CoordD.idx (slot * 2 ^ 32) 0).ts pubF w).map fun t => t.1 * t.2.val row z).sum =
      w * emb (ofWord (slotKey slot z)) := by
  have hx : slot * 2 ^ 32 ^^^ z = slot * 2 ^ 32 + z := by
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_xor, show slot * 2 ^ 32 = 2 ^ 32 * slot + 0 by ring,
      Nat.testBit_two_pow_mul_add slot (by positivity : 0 < 2 ^ 32) j, Nat.add_zero,
      Nat.testBit_two_pow_mul_add slot hz j]
    by_cases hj : j < 32
    · rw [if_pos hj, if_pos hj, Nat.zero_testBit, Bool.false_xor]
    · rw [if_neg hj, if_neg hj, Nat.testBit_lt_two_pow (lt_of_lt_of_le hz
        (Nat.pow_le_pow_right (by norm_num) (by omega))), Bool.xor_false]
  simp only [CoordD.ts, DCoord.val, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    Nat.shiftLeft_zero]
  rw [hx, slotKey]

/-! The balance on the dumps' certificates. -/

theorem FormCert.isFinal_quad {f : FormCert} {n : ℕ} {st : FormSt} (h : f.isFinal n st = true) (val : Val) :
    f.quad val = st.quad val n := by
  simp only [FormCert.isFinal, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hc, hl⟩, hp⟩ := h
  have hl' := congrArg (List.map fun t : ℕ × ℕ => (t.1, Model.ev val t.2)) hl
  have hp' := congrArg (List.map fun t : ℕ × ℕ × ℕ => (t.1, t.2.1, Model.ev val t.2.2)) hp
  simp only [List.map_map, Function.comp_def] at hl' hp'
  simp only [FormCert.quad, FormSt.quad, hc, hl', hp']

/-- A side's leaf claim: its stacked layer (`stackLeaf`, each owned block's leaves over its table's committed rows,
the framework's over its public columns) at the bus point. -/
noncomputable def SideCert.leafClaim (sc : SideCert) (val : Val) (pubF : Bool → ℕ → ℕ → E) (w : Witness) : E :=
  ∑ x ∈ range (2 ^ sc.mu), rowEq (sc.zetaV val) sc.mu x *
    stackLeaf (fun b => sc.blocks[b].kappa) (fun b => sc.blocks[b].q) (fun b z =>
      if sc.blocks[b].owner = none then sc.leafOf val pubF b z
      else blockLeaf (Model.ev val sc.beta) (sc.tsOf val pubF b)
        (fun c => emb (w.cols (sc.blocks[b].owner.getD .emul) z c)) z) x

section Balance

variable {cs : Array Call} {rl : Array Bool} {os : Array (List ℕ)} {st : ℕ → Fin 4 → K} {val : Val}

/-- A side's share plus its leaf claim is the named forms' sums at the table sumcheck's point `ζ'`, the bus point's
first `N` coordinates. -/
theorem SideCert.dec_named (hF : Facts cs rl os st val) {sc : SideCert} (h : sc.ok os cs rl = true)
    (pubF : Bool → ℕ → ℕ → E) (hpub : sc.PubTrue val pubF) (w : Witness)
    (hτ : ∀ b : Fin sc.blocks.length, ∀ T, sc.blocks[b].owner = some T → sc.blocks[b].kappa = tauOf w T)
    (forms : Fin 2 → Table → Quad) (i : Fin 2)
    (hforms : ∀ T ∈ owned, ∀ col, (forms i T).eval col = (((sc.final os).forms T).quad val (nCols T)).eval col)
    {N : ℕ} (ζ' : Fin N → E) (hN : N ≤ sc.mu) (hζ' : ∀ j : Fin N, ζ' j = Model.ev val (sc.zeta.getD j 0))
    (htau : ∀ T ∈ owned, tauOf w T ≤ N) :
    Model.ev val (sc.fw os) + sc.leafClaim val pubF w = formSums w ζ' forms i := by
  rw [formSums_restrict w (sc.zetaV val) ζ' hN (fun j => hζ' j) htau, SideCert.leafClaim,
    SideCert.dec hF h pubF hpub w hτ (forms i) hforms i]
  rfl

/-- The balance on the dumps' certificates (`balance_named` with its premise from `sidesOk`): where the calls hold, the
table sumcheck `tc`, its bus GKR `g` and its residual `rc` pass and both sides `s0`, `s1` are certified against them
(`sidesOk`), each side's public coordinates' named values are their columns' extensions, each recorded owned block is
at its table's height, and the table sumcheck's input claim is its honest instance's sum at the named forms and point
`ζ'` (`table_part`'s output), the GKR's two last next claims are the sides' stacked leaf claims, off the balance's
draw event at the bus parts the forms' sums less the named totals. -/
theorem balance_sides {tc : TableCert} {g : GkrCert} {rc : ResidCert} {scs : Array SumcheckCert}
    {tops : Array TopCert} {odds : Array OddCert} {s0 s1 : SideCert}
    (hF : Facts cs rl os st val) (htc : tc.okIn scs tops odds cs rl os = true)
    (hg : g.okIn tc scs tops odds cs rl os = true) {sc : SumcheckCert} (hsc : scs[tc.sc]? = some sc)
    (hs : sidesOk os cs rl scs tops odds g rc s0 s1 = true) (pubF0 pubF1 : Bool → ℕ → ℕ → E)
    (hp0 : s0.PubTrue val pubF0) (hp1 : s1.PubTrue val pubF1) (w : Witness)
    (hτ0 : ∀ b : Fin s0.blocks.length, ∀ T, s0.blocks[b].owner = some T → s0.blocks[b].kappa = tauOf w T)
    (hτ1 : ∀ b : Fin s1.blocks.length, ∀ T, s1.blocks[b].owner = some T → s1.blocks[b].kappa = tauOf w T)
    {N : ℕ} (ζ' : Fin N → E) (hNl : N ≤ rc.zeta.length) (hζ' : ∀ j : Fin N, ζ' j = Model.ev val (rc.zeta.getD j 0))
    (htau : ∀ T ∈ owned, tauOf w T ≤ N) {a : (Fin N → E) → Fin 2 → E}
    (ha : a ζ' = fun i => formSums w ζ' (rc.formsV val) i - Model.ev val (if i = 0 then tc.tot0 else tc.tot1))
    (hin : Model.ev val sc.claim0 = (tableInst N w ζ' (rc.formsV val) (Model.ev val tc.xi)).sum)
    (hx : (ζ', Model.ev val tc.xi) ∉ balDraws w a) :
    ∃ v0 v1, LayerCert.chain scs cs rl os g.layers (g.start tops odds os).2.1 (g.start tops odds os).2.2 =
      some [v0, v1] ∧ Model.ev val v0 = s0.leafClaim val pubF0 w ∧ Model.ev val v1 = s1.leafClaim val pubF1 w := by
  simp only [sidesOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, hfw0⟩, hfw1⟩, -⟩, hz1⟩, hmu0⟩, hmu1⟩, -⟩, -⟩, hrz⟩, hfin⟩, -⟩, -⟩, -⟩ := hs
  have hz : ∀ j : Fin N, Model.ev val (rc.zeta.getD j 0) = Model.ev val (s0.zeta.getD j 0) := fun j => by
    rw [hrz, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt
      (lt_of_lt_of_le j.isLt hNl)]
  have hNmu : N ≤ s0.mu := by
    have := congrArg List.length hrz
    rw [List.length_take] at this
    omega
  have hmem : ∀ T ∈ owned, T ∈ ownedList := fun T hT => by
    simp only [owned, Finset.mem_insert, Finset.mem_singleton] at hT
    rcases hT with rfl | rfl | rfl | rfl | rfl <;> decide
  have hd0 := SideCert.dec_named hF h0 pubF0 hp0 w hτ0 (rc.formsV val) 0 (fun T hT col => by
    simp only [ResidCert.formsV, if_true]
    rw [FormCert.isFinal_quad ((hfin T (hmem T hT)).1)]) ζ' hNmu
    (fun j => (hζ' j).trans (hz j)) htau
  have hd1 := SideCert.dec_named hF h1 pubF1 hp1 w hτ1 (rc.formsV val) 1 (fun T hT col => by
    simp only [ResidCert.formsV, if_neg (by decide : (1 : Fin 2) ≠ 0)]
    rw [FormCert.isFinal_quad ((hfin T (hmem T hT)).2)]) ζ'
    (by rw [hmu1]; exact hNmu) (fun j => (hζ' j).trans ((hz j).trans (by rw [hz1]))) htau
  refine balance_named hF htc hg hsc htau ha (V := fun i => if i = 0 then s0.leafClaim val pubF0 w
    else s1.leafClaim val pubF1 w) (fun i => ?_) hin hx |>.imp fun v0 ⟨v1, hch, e0, e1⟩ => ⟨v1, hch, e0, e1⟩
  fin_cases i
  · simpa [hfw0] using hd0
  · simpa [hfw1] using hd1

end Balance

/-! The check on a small side, and mutations it rejects. -/

/-- One framework block of one row at depth one, its one coordinate a public one at weight wire `1`, `β` wire `2`,
value wire `3`. -/
def exCalls (sel : Call) : Array Call :=
  #[.freeE, .freeE, .freeE, .freeE, .zero, .zero, .one, .one, sel, .add 6 8, .mulAdd 1 3 2, .mulAdd 8 10 5,
    .add 11 9]

def exOuts : Array (List ℕ) := #[[0], [1], [2], [3], [4], [5], [6], [7], [8], [9], [10], [11], [12]]

def exCert (off : ℕ) : SideCert where
  mu := 1
  zeta := [0]
  w := [1]
  beta := 2
  formZero := 4
  zeroAt := 5
  oneAt := 6
  blocks := [⟨0, off, none, [.pub false 0]⟩]
  certs := [{ one := 7, steps := [8], sumAt := 9, coords := [{ x := 3, addAt := 10 }], accAt := 11 }]
  fwAt := 12

/-- The block at place `0`: its selector `eq_bits(0, ζ_0) = mul_add(1, ζ_0, 1)`. -/
example : (exCert 0).ok exOuts (exCalls (.mulAdd 7 0 7)) (Array.replicate 13 false) = true := by decide +kernel

/-- The block recorded at place `1` but the selector the circuit computes at place `0`: rejected. -/
example : (exCert 1).ok exOuts (exCalls (.mulAdd 7 0 7)) (Array.replicate 13 false) = false := by decide +kernel

/-- A selector computed at the wrong bit: rejected. -/
example : (exCert 0).ok exOuts (exCalls (.mul 7 0)) (Array.replicate 13 false) = false := by decide +kernel

/-- A block past the layer's end: rejected. -/
example : (exCert 2).ok exOuts (exCalls (.mulAdd 7 0 7)) (Array.replicate 13 false) = false := by decide +kernel

/-- `BusBlocks::new`'s first block on the push side: the public slot's `Next` then its four values; their order
swapped is rejected. -/
example : (recCoords false).head? = some (none, [.pub true 97, .pub false 0, .pub false 1, .pub false 2, .pub false 3]) :=
  by decide +kernel

example : (recCoords false).head? ≠ some (none, [.pub false 0, .pub true 97, .pub false 1, .pub false 2, .pub false 3]) :=
  by decide +kernel

/-- `BusBlocks::new` has the public slot and every owned slot. -/
example : (recCoords true).length = 1 + 97 := by decide +kernel

end LeanVMCircuits.Rec.Bind
