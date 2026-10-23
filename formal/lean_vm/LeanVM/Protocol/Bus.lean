/-
  LeanVM.Protocol.Bus

  The bus phase: the fingerprint challenges, the roots of the three product trees, the
  grand-product argument down to their leaves, and the boundary columns' values, after which the
  leaf claims are owed by the tables' forms. Definition and perfect completeness.
-/

module

public import LeanVM.Protocol.Fingerprint
public import LeanVM.Protocol.Spine.Errors
public import LeanVM.Protocol.Stack
public import LeanVM.Protocol.ToArkLib.GrandProduct
public import LeanVM.Protocol.ToArkLib.Typed.SendChecked
public import LeanVM.Protocol.ToArkLib.Typed.SampleChallenge
public import LeanVM.Protocol.Spine.Slots
import CompPoly.Multivariate.Operations
import CompPoly.Multivariate.MvPolyEquiv.Eval

/-!
# The bus phase

Specification §5.2 to §5.4 and §8.3 (`doc/leanvm/body/05-arithmetization.tex`,
`08-end-to-end-protocol.tex` at leanVM `3a37fb6e1c7423e36b67d1cac4eda70c3ad4dd45`), over an
abstract instance `I`.

The bus has three sides: the pushed tuples, the pulled tuples, and the count columns. Each side's
tuples come in *blocks*: a boundary block's `2 ^ κ` tuples, one flush of one table (a tuple per
row), one count column (a cell per row) (`Source`). A block's *leaves* are `β − π_α(t)` for its
tuples `t`, with `π_α` the fingerprint, and a count column's leaves are its cells; on a padding
row of a table (§8.3) a leaf is `φ(x) + 1 − φ(p)` instead, `φ` the executed leaf and `p` the
public padding row, so `1` on an honest one and in general the fingerprint of
`1 − t + t(p)`, a nonzero tuple when the separator is constant (`Conditions.separator`). The
verifier evaluates `(1 − φ(p))·pad_{rows}(z)` itself (`Source.padTerm`, part of
`Source.publicValue`), `pad_n` the extension of `[x ≥ n]` (`padWeight`). Each side's
blocks are stacked largest first at aligned offsets, ties in the order of `sources` (on the
push or pull side, its boundary blocks, then each table's flushes of that side; on the count
side, each table's count columns), and padded with `1` to the depth `μ_bus` of the push side
(`sideLeaves`; `pushLeaves`, `pullLeaves`, `countLeaves`). The product of a side's leaves is the
product of its blocks' leaves (`Blocks.prod_stackAt`), so the push and pull roots agree when the
bus balances, and the count root is nonzero when every count cell is.

The phase (`busPhase`), a typed front component at the slot `busSlot I`:

1. the verifier draws `(α, β)`;
2. the prover sends the roots `(R, R_c)`: one scalar for push and pull, which share their root,
   and the count root; the verifier rejects `R_c = 0`;
3. the grand-product argument `gkr` on the three leaf stacks, read off the stack and `(α, β)`,
   ends at a point `ζ` with one claim per side, `Ṽ_s(ζ) = v_s`;
4. the prover sends the values at `ζ` of the boundary columns (`I.boundaryColumns`), and the
   verifier hands on (`busOut`): the point `ζ_{<τ_max}`, the boundary columns' claims, and per
   side the *forms* and their *total*. By the stacking identity at `ζ` (`leaf_decomposition`,
   equation (2) of §5.4) a side's claim is the sum over its blocks of the selector weight
   `eq(sel_b, ζ_{≥κ_b})` times the block's leaf extension at `ζ_{<κ_b}`, plus the pad's weight.
   The verifier evaluates the boundary blocks' part from the values sent and subtracts it and the
   pad's from `v_s`: the remainder is the total, `rem_s` of §5.4. The tables' blocks are owed as
   forms, one per side and sumcheck table: for a flush block, the weight times `β` against the
   constant row polynomial `1` and the weight times `−eq(α, i)` against coordinate `i`'s flush
   polynomial; for a count column, the weight against the column's variable.

The grand-product argument carries the constraint polynomials of the tables as *riders*, tables
whose extension must vanish at the final point (`riders`): that is how the zerocheck of §5.5 is
paid inside the bus phase (`ζ` is drawn after the stack is committed). One more rider, on no
variable, is zero exactly when the public lines and the Flock predicate hold of the statement and
the stack (`linesRider`): the predicates the grand-product argument does not touch travel through
it this way.

The phase's side conditions (`Conditions`): the degree bound is at least one (a count column's
form is its variable); a table with a constraint fits in the leaf stacks' depth, so that `ζ` has
a point for it (the verifier reads `ζ` at every variable below the tallest table's height,
`crates/verifier/src/bus.rs:221-230`; its explicit rejection of a shorter `ζ`,
`crates/lean_vm/src/constraints.rs:250-253` at `a386121f`, is removed at `127510d1`); and the pull
and count sides fit in `2 ^ μ_bus`, the push side's depth, which the deployed prover asserts of
its layouts (`crates/leanvm_core/src/leaf.rs:115-130`, called at `:628`; the verifier's own call,
`leaf.rs:875` at `a386121f`, is removed at `127510d1`).

Perfect completeness (`busComplete`), from `Seam.commitHonest` to `Seam.bus`: on a stack
satisfying `M3Holds` with honest padding rows (their leaves `1`), the products of the push and
pull sides agree at every `(α, β)` (balance is a permutation), the count root is nonzero (counts
are nonzero), every rider is zero (constraints vanish, lines and Flock predicate hold), and at
the end the honest values make every claim true and the forms sum to the totals.

Written from the specification; the layout and its tie order, the count blocks and the order of
the messages are transcribed from `crates/leanvm_core/src/leaf.rs` at the pin (the layout
`:141-148`, the leaves `:179-255`, the decomposition `:381-451`), the verifier
`crates/verifier/src/bus.rs:107-209` (`verify_bus_balance`), the prover's grand product
`crates/leanvm_core/src/gkr.rs:299-418` and its verifier `crates/verifier/src/bus.rs:12-49`.
-/

namespace LeanVM.Protocol

open LeanVM.Parameters CompPoly CPoly CMlPolynomialEval OracleComp OracleSpec
open scoped NNReal

@[expose] public section

namespace Bus

variable (I : M3Instance)

/-! ## Blocks of leaves -/

/-- Where a block of leaves comes from: a boundary block, one flush of one table (its index among
the table's flushes), or one count column of one table. -/
inductive Source
  | boundary (b : BoundaryBlock I.toShape)
  | flush (j : Fin I.ntab) (f : Fin (I.flushes j).length)
  | count (j : Fin I.ntab) (c : Fin (I.width j))

variable {I}

/-- A block's log-height: its boundary block's, or its table's. -/
def Source.κ : Source I → ℕ
  | .boundary b => b.κ
  | .flush j _ => I.τ j
  | .count j _ => I.τ j

/-- The sixteen coordinate polynomials of flush `f` of table `j`. -/
abbrev flushPolys (j : Fin I.ntab) (f : Fin (I.flushes j).length) :
    Vector (CMvPolynomial (I.width j) K) 16 :=
  (I.flushes j)[f].2

/-- The tuple a block contributes at row `x`, read off the stack: the boundary block's
coordinates, or the flush's polynomials on the table's row. A count column's tuple, its cell then
zeros, is the deployed verifier's count block; no definition reads it, since a count leaf is the
cell itself. -/
def Source.tuple (q : Column I.μ) : (src : Source I) → Fin (2 ^ src.κ) → Vector K 16
  | .boundary b, x => b.coords.map fun co ↦ I.coordCell q co x
  | .flush j f, x => (flushPolys j f).map fun P ↦ P.eval (I.row q j x)
  | .count j c, x => Vector.ofFn fun i ↦ if i.val = 0 then (I.column q ⟨j, c⟩).values.get x else 0

/-- `[x ≥ rows j]`: `1` on a padding row of table `j`, `0` on an executed row. -/
def padInd (j : Fin I.ntab) (x : Fin (2 ^ I.τ j)) : E := if I.rows j ≤ x.val then 1 else 0

/-- The tuple flush `f` of table `j` emits on the table's public padding row. -/
def padTuple (j : Fin I.ntab) (f : Fin (I.flushes j).length) : Vector K 16 :=
  (flushPolys j f).map fun P ↦ P.eval (I.padRow j)

/-- A block's leaf at row `x` (§5.4, the leaves `L_b`): on an executed row, `φ(x) = β − π_α(t)` for
the row's tuple `t`, or the count cell; on a padding row of a table, `φ(x) + 1 − φ(p)` with `p` the
public padding row, whatever the row holds, so `1` on an honest one. -/
def Source.leaf (α : Fin 4 → E) (β : E) (q : Column I.μ) : (src : Source I) → Fin (2 ^ src.κ) → E
  | .boundary b, x => β - fingerprint α ((Source.boundary b).tuple q x)
  | .flush j f, x => β - fingerprint α ((Source.flush j f).tuple q x) +
    padInd j x * (1 - (β - fingerprint α (padTuple j f)))
  | .count j c, x => ofK ((I.column q ⟨j, c⟩).values.get x) +
    padInd j x * (1 - ofK (I.padRow j c))

variable (I)

/-- The blocks of a side of the bus (`Side.push` or `Side.pull`): the side's boundary blocks in
order, then every table's flushes of that side, table by table, in order. -/
def sideSources (s : Side) : List (Source I) :=
  (I.boundary.filter fun b ↦ decide (b.side = s)).map .boundary ++
    (List.finRange I.ntab).flatMap fun j ↦
      ((List.finRange (I.flushes j).length).filter fun f ↦ decide ((I.flushes j)[f].1 = s)).map
        (.flush j)

/-- The blocks of the count side: every table's count columns, table by table, in order. -/
def countSources : List (Source I) :=
  (List.finRange I.ntab).flatMap fun j ↦ (I.counts j).map (.count j)

/-- The blocks of the three sides: push, pull, count. -/
def sources (k : Fin 3) : List (Source I) :=
  ![sideSources I .push, sideSources I .pull, countSources I] k

/-- The number of leaves of a side, before padding. -/
def leafCount (k : Fin 3) : ℕ := ((sources I k).map fun src ↦ 2 ^ src.κ).sum

/-- The blocks of a side, largest first, ties in the order of `sources` (a stable sort). -/
def sorted (k : Fin 3) : List (Source I) :=
  (sources I k).mergeSort fun a b ↦ decide (b.κ ≤ a.κ)

/-- The sorted blocks are largest first. -/
theorem sorted_antitone (k : Fin 3) :
    Antitone fun b : Fin (sorted I k).length ↦ ((sorted I k)[b]).κ := by
  intro a b hab
  rcases eq_or_lt_of_le hab with h | h
  · rw [h]
  · have hp := List.pairwise_mergeSort (le := fun a b : Source I ↦ decide (b.κ ≤ a.κ))
      (fun a b c hab hbc ↦ by simp only [decide_eq_true_eq] at *; omega)
      (fun a b ↦ by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) (sources I k)
    exact of_decide_eq_true (List.pairwise_iff_getElem.mp hp a.val b.val a.isLt b.isLt h)

/-- The aligned layout of a side's blocks. -/
def blocks (k : Fin 3) : Blocks where
  n := (sorted I k).length
  size b := ((sorted I k)[b]).κ
  descending := sorted_antitone I k

/-- A side's blocks' leaves, one table per block. -/
def tables (k : Fin 3) (α : Fin 4 → E) (β : E) (q : Column I.μ) : (blocks I k).Tables E :=
  fun b ↦ Vector.ofFn (((sorted I k)[b]).leaf α β q)

/-- A side's leaf stack: its blocks stacked largest first at aligned offsets, padded with `1`,
on the push side's depth `μ_bus`. -/
def sideLeaves (k : Fin 3) (α : Fin 4 → E) (β : E) (q : Column I.μ) :
    CMlPolynomialEval E I.μBus :=
  (blocks I k).stackAt (tables I k α β q) I.μBus 1

/-- The bus phase's side conditions: the degree bound is at least one, a table with a constraint
fits in the leaf stacks' depth, and the pull and count sides fit in it. -/
structure Conditions : Prop where
  /-- A count column's form is its variable, of degree one. -/
  one_le_d : 1 ≤ I.d
  /-- A table with a constraint has a zerocheck point among the coordinates of `ζ`. -/
  constrained : ∀ j, I.constraints j ≠ [] → I.τ j ≤ I.μBus
  /-- The pull side fits in the push side's depth. -/
  pull_fits : leafCount I 1 ≤ 2 ^ I.μBus
  /-- The count side fits in the push side's depth. -/
  count_fits : leafCount I 2 ≤ 2 ^ I.μBus
  /-- A flush's first coordinate, its domain separator, takes one value on every row (§5.1): a
  padding row's leaf is then the fingerprint of a nonzero tuple (Proposition `prop:pad`). -/
  separator : ∀ j (f : Fin (I.flushes j).length) (r r' : Fin (I.width j) → K),
    ((flushPolys j f)[0]).eval r = ((flushPolys j f)[0]).eval r'

end Bus

/-- The push side's leaf stack (§5.3, §5.4). -/
abbrev pushLeaves (I : M3Instance) (α : Fin 4 → E) (β : E) (q : Column I.μ) :
    CMlPolynomialEval E I.μBus :=
  Bus.sideLeaves I 0 α β q

/-- The pull side's leaf stack. -/
abbrev pullLeaves (I : M3Instance) (α : Fin 4 → E) (β : E) (q : Column I.μ) :
    CMlPolynomialEval E I.μBus :=
  Bus.sideLeaves I 1 α β q

/-- The count side's leaf stack: the tables' count columns, padded with `1`. -/
abbrev countLeaves (I : M3Instance) (q : Column I.μ) : CMlPolynomialEval E I.μBus :=
  Bus.sideLeaves I 2 0 0 q

namespace Bus

variable (I : M3Instance)

/-! ## The layouts fit -/

/-- The log-heights of a side's blocks: its boundary blocks', then each table's, once per flush
of that side. -/
theorem sideSources_map_κ (s : Side) :
    (sideSources I s).map Source.κ =
      (I.boundary.filter fun b ↦ decide (b.side = s)).map (·.κ) ++
        (List.finRange I.ntab).flatMap fun j ↦
          List.replicate ((I.flushes j).filter fun f ↦ decide (f.1 = s)).length (I.τ j) := by
  rw [sideSources, List.map_append, List.map_map, List.map_flatMap]
  congr 1
  refine List.flatMap_congr fun j _ ↦ ?_
  rw [List.map_map]
  simp only [Function.comp_def, Source.κ, List.map_const']
  congr 1
  conv_rhs => rw [← List.map_getElem_finRange (I.flushes j)]
  rw [List.filter_map, List.length_map]
  rfl

/-- The log-heights of the count side's blocks: each table's, once per count column. -/
theorem countSources_map_κ :
    (countSources I).map Source.κ =
      (List.finRange I.ntab).flatMap fun j ↦ List.replicate (I.counts j).length (I.τ j) := by
  rw [countSources, List.map_flatMap]
  refine List.flatMap_congr fun j _ ↦ ?_
  simp only [List.map_map, Function.comp_def, Source.κ, List.map_const']

/-- A side's layout covers its leaves exactly. -/
theorem blocks_total (k : Fin 3) : (blocks I k).total = leafCount I k := by
  rw [Blocks.total_eq_sum]
  change ∑ b : Fin (sorted I k).length, 2 ^ ((sorted I k)[b.1]).κ = _
  rw [Fin.sum_univ_fun_getElem (sorted I k) fun src ↦ 2 ^ src.κ, leafCount]
  exact ((List.mergeSort_perm _ _).map _).sum_eq

private theorem length_filter_finRange {α : Type} (l : List α) (p : α → Bool) :
    ((List.finRange l.length).filter fun i ↦ p l[i]).length = (l.filter p).length := by
  conv_rhs => rw [← List.map_getElem_finRange l]
  rw [List.filter_map, List.length_map]
  rfl

private theorem sum_flatMap {α : Type} (l : List α) (f : α → List ℕ) :
    (l.flatMap f).sum = (l.map fun a ↦ (f a).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, List.sum_append, ih, List.map_cons, List.sum_cons]

/-- The push side's leaves are the instance's count of push leaves. -/
private theorem leafCount_push : leafCount I 0 = I.pushLeaves := by
  rw [leafCount, M3Instance.pushLeaves]
  change ((sideSources I .push).map _).sum = _
  rw [sideSources, List.map_append, List.sum_append, List.map_map]
  congr 1
  rw [List.map_flatMap, sum_flatMap]
  refine congrArg List.sum (List.map_congr_left fun j _ ↦ ?_)
  rw [List.map_map]
  simp only [Function.comp_def, Source.κ, List.map_const', List.sum_replicate, smul_eq_mul]
  rw [length_filter_finRange (I.flushes j) fun f ↦ decide (f.1 = Side.push)]

/-- The push side fits in its own depth. -/
theorem push_fits : (blocks I 0).total ≤ 2 ^ I.μBus := by
  rw [blocks_total, leafCount_push]
  exact Nat.le_pow_clog one_lt_two _

variable {I}

/-- Under the side conditions every side fits in the push side's depth. -/
theorem Conditions.fits (h : Conditions I) (k : Fin 3) : (blocks I k).total ≤ 2 ^ I.μBus := by
  fin_cases k
  · exact push_fits I
  · exact (blocks_total I 1).trans_le h.pull_fits
  · exact (blocks_total I 2).trans_le h.count_fits

/-- A block of a side that fits is no taller than the leaf stacks. -/
private theorem κ_le_of_mem {k : Fin 3} (hfit : leafCount I k ≤ 2 ^ I.μBus) {src : Source I}
    (hs : src ∈ sources I k) : src.κ ≤ I.μBus := by
  have h2 : 2 ^ src.κ ≤ leafCount I k :=
    List.le_sum_of_mem (List.mem_map_of_mem (f := fun src : Source I ↦ 2 ^ src.κ) hs)
  exact (Nat.pow_le_pow_iff_right one_lt_two).mp (h2.trans hfit)

/-- Under the side conditions every block of every side is no taller than the leaf stacks. -/
theorem Conditions.κ_le (h : Conditions I) {k : Fin 3} {src : Source I}
    (hs : src ∈ sources I k) : src.κ ≤ I.μBus :=
  κ_le_of_mem (by rw [← blocks_total]; exact h.fits k) hs

/-- Under the side conditions every sumcheck table is no taller than the leaf stacks: a table
with a constraint by hypothesis, one with a flush or a count column since its block fits. -/
theorem Conditions.τmax_le (h : Conditions I) : I.τmax ≤ I.μBus := by
  refine Finset.sup_le fun j _ ↦ ?_
  obtain ⟨j, hj⟩ := j
  rcases hj with hc | hf | hc
  · exact h.constrained j hc
  · obtain ⟨f, hfm⟩ := List.exists_mem_of_ne_nil _ hf
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hfm
    have hmem (s : Side) (hs : (I.flushes j)[i].1 = s) :
        Source.flush j ⟨i, hi⟩ ∈ sideSources I s := by
      simp only [sideSources, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_filter,
        List.mem_finRange, true_and, decide_eq_true_eq]
      exact Or.inr ⟨j, ⟨i, hi⟩, hs, rfl⟩
    cases hside : (I.flushes j)[i].1
    · exact h.κ_le (k := 0) (hmem .push hside)
    · exact h.κ_le (k := 1) (hmem .pull hside)
  · obtain ⟨c, hcm⟩ := List.exists_mem_of_ne_nil _ hc
    have hmem : Source.count j c ∈ sources I 2 := by
      change _ ∈ countSources I
      simp only [countSources, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and]
      exact ⟨j, c, hcm, rfl⟩
    exact h.κ_le hmem

/-- Under the side conditions every boundary column is no taller than the leaf stacks: it is a
coordinate of a boundary block of the push or pull side. -/
theorem Conditions.κ_le_of_boundaryColumn (h : Conditions I) {c : I.ColumnId}
    (hc : c ∈ I.boundaryColumns) : I.κ c ≤ I.μBus := by
  simp only [M3Instance.boundaryColumns, List.mem_eraseDups, List.mem_flatMap, List.mem_cons,
    List.not_mem_nil, or_false, List.mem_filter, decide_eq_true_eq, List.mem_filterMap] at hc
  obtain ⟨s, hs, b, ⟨hb, rfl⟩, co, -, hco⟩ := hc
  cases co with
  | const _ => cases hco
  | known _ => cases hco
  | committed c' hτ =>
    cases hco
    have hmem (k : Fin 3) (hk : sources I k = sideSources I b.side) :
        Source.boundary b ∈ sources I k := by
      rw [hk]
      simp only [sideSources, List.mem_append, List.mem_map, List.mem_filter,
        decide_eq_true_eq]
      exact Or.inl ⟨b, ⟨hb, rfl⟩, rfl⟩
    change I.τ _ ≤ I.μBus
    rw [hτ]
    rcases hs with hs | hs
    · exact h.κ_le (hmem 0 (by rw [hs]; rfl))
    · exact h.κ_le (hmem 1 (by rw [hs]; rfl))

/-! ## The leaves at a point -/

variable (I)

/-- Block `b` of side `k`, in the stacked order. -/
abbrev src (k : Fin 3) (b : Fin (blocks I k).n) : Source I := (sorted I k)[b.1]'b.isLt

variable {I}

/-- The extension at a point of a boundary block of one of its coordinates: a constant is itself,
a known column its extension, a committed column its extension read off the stack. -/
def coordEval (q : Column I.μ) {κ : ℕ} : Coord I.toShape κ → Vector E κ → E
  | .const c, _ => ofK c
  | .known col, z => eval₂Mle col.values (algebraMap K E) z
  | .committed c h, z => eval₂Mle (I.column q c).values (algebraMap K E) (Vector.cast h.symm z)

/-- The extension at `z` of `[x ≥ n]` on the cube of `z`'s length: `pad_n(z)` (Lemma
`lem:suffix`). -/
def padWeight {m : ℕ} (n : ℕ) (z : Vector E m) : E :=
  evalMle (Vector.ofFn fun x : Fin (2 ^ m) ↦ if n ≤ x.val then (1 : E) else 0) z

/-- The public part of a table block's leaf extension: the padding term
`(1 − φ(p))·pad_{rows}(z)` of equation `eq:pad_leaf`, `φ(p)` the leaf the padding row's tuple
would have. -/
def Source.padTerm (α : Fin 4 → E) (β : E) : (src : Source I) → Vector E src.κ → E
  | .boundary _, _ => 0
  | .flush j f, z => (1 - (β - fingerprint α (padTuple j f))) * padWeight (I.rows j) z
  | .count j c, z => (1 - ofK (I.padRow j c)) * padWeight (I.rows j) z

/-- The extension of a block's leaves at a point of the block, as the verifier writes it:
`β − Σ_i eq(α, i)·c̃_i(z)` with `c̃_i` the extension of coordinate `i`, or a count column's
extension, plus a table block's padding term. -/
def Source.leafEval (α : Fin 4 → E) (β : E) (q : Column I.μ) :
    (src : Source I) → Vector E src.κ → E
  | .boundary b, z =>
    let w := fingerprintWeights α
    β - ∑ i : Fin 16, w[i.val] * coordEval q b.coords[i] z
  | .flush j f, z =>
    let w := fingerprintWeights α
    β - ∑ i : Fin 16, w[i.val] * evalMle (I.virtualTable q j (flushPolys j f)[i]) z +
      (Source.flush j f).padTerm α β z
  | .count j c, z => eval₂Mle (I.column q ⟨j, c⟩).values (algebraMap K E) z +
    (Source.count j c).padTerm α β z

/-- The extension of `a + [x ≥ n]·c` is `ã + c·pad_n`. -/
private theorem evalMle_add_padInd {m : ℕ} (a : Fin (2 ^ m) → E) (n : ℕ) (c : E)
    (z : Vector E m) :
    evalMle (Vector.ofFn fun x ↦ a x + (if n ≤ x.val then (1 : E) else 0) * c) z =
      evalMle (Vector.ofFn a) z + c * padWeight n z := by
  simp only [padWeight, evalMle_eq_sum, Fin.getElem_fin, Vector.getElem_ofFn, add_mul,
    Finset.sum_add_distrib, Finset.mul_sum]
  exact congrArg _ (Finset.sum_congr rfl fun x _ ↦ by ring)

/-- The extension of `β − Σ_i w_i·g_i` is `β − Σ_i w_i·g̃_i`. -/
private theorem evalMle_affine {n : ℕ} (β : E) (w : Fin 16 → E) (g : Fin 16 → Fin (2 ^ n) → E)
    (z : Vector E n) :
    evalMle (Vector.ofFn fun x ↦ β - ∑ i, w i * g i x) z =
      β - ∑ i, w i * evalMle (Vector.ofFn (g i)) z := by
  simp only [evalMle_eq_sum, Fin.getElem_fin, Vector.getElem_ofFn, sub_mul, Finset.sum_sub_distrib,
    Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm (f := fun x i ↦ w i * (g i x * (lagrangeBasis z)[x.val]))]
  congr 1
  rw [← Finset.mul_sum]
  have h1 := sumCube_lagrangeBasis z
  simp only [sumCube, Fin.getElem_fin] at h1
  rw [h1, mul_one]

/-- A boundary coordinate's column, lifted to `E`, has the extension `coordEval`. -/
private theorem evalMle_coordCell (q : Column I.μ) {κ : ℕ} (co : Coord I.toShape κ)
    (z : Vector E κ) :
    evalMle (Vector.ofFn fun x ↦ ofK (I.coordCell q co x)) z = coordEval q co z := by
  cases co with
  | const c =>
    rw [show (Vector.ofFn fun x : Fin (2 ^ κ) ↦ ofK (I.coordCell q (.const c) x)) =
      Vector.replicate (2 ^ κ) (ofK c) from Vector.ext fun i hi ↦ by simp [M3Instance.coordCell]]
    exact evalMle_replicate _ z
  | known col =>
    refine congrArg (evalMle · z) (Vector.ext fun i hi ↦ ?_)
    simp [M3Instance.coordCell, CMlPolynomialEval.map, Extension.Ext.algebraMap_eq_ofBase,
      Vector.get_eq_getElem]
  | committed c h =>
    have ht : (Vector.ofFn fun x ↦ ofK (I.coordCell q (.committed c h) x)) =
        Vector.cast (congrArg (2 ^ ·) h)
          (CMlPolynomialEval.map (algebraMap K E) (I.column q c).values) :=
      Vector.ext fun i hi ↦ by
        simp [M3Instance.coordCell, CMlPolynomialEval.map, Extension.Ext.algebraMap_eq_ofBase,
          Vector.get_eq_getElem]
    rw [ht, coordEval, eval₂Mle, ← evalMle_cast h _ (Vector.cast h.symm z), Vector.cast_cast,
      Vector.cast_rfl]

private theorem evalMle_leaf_boundary (α : Fin 4 → E) (β : E) (q : Column I.μ)
    (b : BoundaryBlock I.toShape) (z : Vector E b.κ) :
    evalMle (n := b.κ) (Vector.ofFn ((Source.boundary b).leaf α β q)) z =
      β - ∑ i : Fin 16, (fingerprintWeights α)[i.val] * coordEval q b.coords[i] z := by
  show evalMle (Vector.ofFn fun x : Fin (2 ^ b.κ) ↦
    β - fingerprint α (b.coords.map fun co ↦ I.coordCell q co x)) z = _
  have ht : (Vector.ofFn fun x : Fin (2 ^ b.κ) ↦
      β - fingerprint α (b.coords.map fun co ↦ I.coordCell q co x)) =
      Vector.ofFn fun x ↦
        β - ∑ i : Fin 16, (fingerprintWeights α)[i.val] * ofK (I.coordCell q b.coords[i] x) :=
    congrArg Vector.ofFn (funext fun x ↦ congrArg (β - ·) (Finset.sum_congr rfl fun i _ ↦ by
      rw [Fin.getElem_fin, Vector.getElem_map]; rfl))
  rw [ht, evalMle_affine]
  exact congrArg (β - ·) (Finset.sum_congr rfl fun i _ ↦ by rw [evalMle_coordCell])

private theorem evalMle_leaf_flush (α : Fin 4 → E) (β : E) (q : Column I.μ) (j : Fin I.ntab)
    (f : Fin (I.flushes j).length) (z : Vector E (I.τ j)) :
    evalMle (n := I.τ j) (Vector.ofFn ((Source.flush j f).leaf α β q)) z =
      β - ∑ i : Fin 16,
        (fingerprintWeights α)[i.val] * evalMle (I.virtualTable q j (flushPolys j f)[i]) z +
        (Source.flush j f).padTerm α β z := by
  show evalMle (Vector.ofFn fun x : Fin (2 ^ I.τ j) ↦
    β - fingerprint α ((flushPolys j f).map fun P ↦ P.eval (I.row q j x)) +
      (if I.rows j ≤ x.val then (1 : E) else 0) * (1 - (β - fingerprint α (padTuple j f)))) z = _
  refine (evalMle_add_padInd _ _ _ z).trans (congrArg (· + _) ?_)
  have ht : (Vector.ofFn fun x : Fin (2 ^ I.τ j) ↦
      β - fingerprint α ((flushPolys j f).map fun P ↦ P.eval (I.row q j x))) =
      Vector.ofFn fun x ↦ β - ∑ i : Fin 16,
        (fingerprintWeights α)[i.val] * ofK ((flushPolys j f)[i].eval (I.row q j x)) :=
    congrArg Vector.ofFn (funext fun x ↦ congrArg (β - ·) (Finset.sum_congr rfl fun i _ ↦ by
      rw [Fin.getElem_fin, Vector.getElem_map]; rfl))
  rw [ht, evalMle_affine]
  rfl

private theorem evalMle_leaf_count (α : Fin 4 → E) (β : E) (q : Column I.μ) (j : Fin I.ntab)
    (c : Fin (I.width j)) (z : Vector E (I.τ j)) :
    evalMle (n := I.τ j) (Vector.ofFn ((Source.count j c).leaf α β q)) z =
      eval₂Mle (I.column q ⟨j, c⟩).values (algebraMap K E) z +
        (Source.count j c).padTerm α β z := by
  show evalMle (Vector.ofFn fun x : Fin (2 ^ I.τ j) ↦
    ofK ((I.column q ⟨j, c⟩).values.get x) +
      (if I.rows j ≤ x.val then (1 : E) else 0) * (1 - ofK (I.padRow j c))) z = _
  refine (evalMle_add_padInd _ _ _ z).trans (congrArg (· + _) ?_)
  refine congrArg (evalMle · z) (Vector.ext fun i hi ↦ ?_)
  simp [CMlPolynomialEval.map, Extension.Ext.algebraMap_eq_ofBase, Vector.get_eq_getElem]

/-- A block's leaves have the extension `leafEval`. -/
private theorem Source.evalMle_leaf (α : Fin 4 → E) (β : E) (q : Column I.μ) (src : Source I)
    (z : Vector E src.κ) :
    evalMle (Vector.ofFn (src.leaf α β q)) z = src.leafEval α β q z := by
  cases src with
  | boundary b => exact evalMle_leaf_boundary α β q b z
  | flush j f => exact evalMle_leaf_flush α β q j f z
  | count j c => exact evalMle_leaf_count α β q j c z

/-! ## The products of the sides -/

/-- The tuple flush `f` of table `j` emits on row `x`. -/
def flushTuple (q : Column I.μ) (j : Fin I.ntab) (f : Fin (I.flushes j).length)
    (x : Fin (2 ^ I.τ j)) : Vector K 16 :=
  (flushPolys j f).map fun P ↦ P.eval (I.row q j x)

/-- The tuples a block puts on the bus: every row of a boundary block, the executed rows of a
flush; none for a count column, whose leaves are its cells. -/
def Source.busTuples (q : Column I.μ) : Source I → List (Vector K 16)
  | .boundary b => (List.finRange (2 ^ b.κ)).map fun x ↦ b.coords.map fun co ↦ I.coordCell q co x
  | .flush j f => (I.executed j).map (flushTuple q j f)
  | .count _ _ => []

/-- The padding rows of table `j`, in order. -/
def padRows (j : Fin I.ntab) : List (Fin (2 ^ I.τ j)) :=
  (List.finRange (2 ^ I.τ j)).filter fun x ↦ decide (I.rows j ≤ x.val)

/-- The tuple whose fingerprint is a flush block's padding leaf at row `x`: `1 − t + t(p)` slot by
slot, `t` the row's tuple and `t(p)` the public padding row's (Proposition `prop:pad`). -/
def padDiff (q : Column I.μ) (j : Fin I.ntab) (f : Fin (I.flushes j).length)
    (x : Fin (2 ^ I.τ j)) : Vector K 16 :=
  Vector.ofFn fun i ↦ 1 - (flushTuple q j f x)[i] + (padTuple j f)[i]

/-- A flush block's padding leaves, as the tuples they fingerprint. -/
def Source.padTuples (q : Column I.μ) : Source I → List (Vector K 16)
  | .flush j f => (padRows j).map (padDiff q j f)
  | _ => []

variable (I)

/-- The tuples of a push or pull side, block by block. -/
def sideTuples (q : Column I.μ) (s : Side) : List (Vector K 16) :=
  (sideSources I s).flatMap (·.busTuples q)

/-- The padding tuples of a push or pull side, block by block. -/
def sidePadTuples (q : Column I.μ) (s : Side) : List (Vector K 16) :=
  (sideSources I s).flatMap (·.padTuples q)

variable {I}

private theorem prod_flatMap {M α β : Type} [CommMonoid M] (l : List α) (f : α → List β)
    (g : β → M) : ((l.flatMap f).map g).prod = (l.map fun a ↦ ((f a).map g).prod).prod := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.map_append, List.prod_append, ih, List.map_cons, List.prod_cons]

/-- A product over a list splits along a predicate. -/
private theorem prod_map_filter {M α : Type} [CommMonoid M] (l : List α) (p : α → Bool)
    (g : α → M) :
    (l.map g).prod = ((l.filter p).map g).prod * ((l.filter fun a ↦ !p a).map g).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases hp : p a <;> simp [hp, ih] <;> ac_rfl

/-- The padding rows are the rows that are not executed. -/
private theorem padRows_eq (j : Fin I.ntab) :
    padRows j = (List.finRange (2 ^ I.τ j)).filter fun x ↦ !decide (x.val < I.rows j) :=
  List.filter_congr fun x _ ↦ by
    by_cases h : x.val < I.rows j
    · simp [h, Nat.not_le.mpr h]
    · simp [h, Nat.le_of_not_lt h]

/-- The executed and padding rows of a table, together. -/
private theorem prod_rows {M : Type} [CommMonoid M] (j : Fin I.ntab) (g : Fin (2 ^ I.τ j) → M) :
    ∏ x, g x = ((I.executed j).map g).prod * ((padRows j).map g).prod := by
  rw [Fin.prod_univ_def, prod_map_filter _ fun x ↦ decide (x.val < I.rows j), padRows_eq]
  rfl

/-- A table has as many rows as executed and padding rows. -/
private theorem length_rows (j : Fin I.ntab) :
    (I.executed j).length + (padRows j).length = 2 ^ I.τ j := by
  have h := List.length_eq_length_filter_add (l := List.finRange (2 ^ I.τ j))
    (fun x ↦ decide (x.val < I.rows j))
  rw [List.length_finRange] at h
  rw [padRows_eq]
  exact h.symm

/-- A side's tuples, block by block, are its boundary tuples followed by its flushes'. -/
private theorem sideTuples_eq (q : Column I.μ) (s : Side) :
    sideTuples I q s = I.boundaryTuples q s ++ I.flushTuples q s := by
  rw [sideTuples, sideSources, List.flatMap_append, List.flatMap_map, List.flatMap_assoc]
  congr 1
  refine congrArg (List.flatMap · (List.finRange I.ntab)) (funext fun j ↦ ?_)
  conv_rhs => rw [← List.map_getElem_finRange (I.flushes j)]
  rw [List.flatMap_map, List.filter_map, List.flatMap_map]
  rfl

/-- The tuples of a side's blocks are the side's tuples of the instance, in another order. -/
theorem sideTuples_perm (q : Column I.μ) (s : Side) : (sideTuples I q s).Perm (I.tuples q s) := by
  rw [sideTuples_eq, M3Instance.tuples]
  exact List.perm_append_comm

/-- The product of a side's leaf stack is the product, block by block, of its blocks' leaves:
the pad is `1`. -/
theorem prod_sideLeaves (k : Fin 3) (α : Fin 4 → E) (β : E) (q : Column I.μ)
    (hfit : (blocks I k).total ≤ 2 ^ I.μBus) :
    ∏ x : Fin (2 ^ I.μBus), (sideLeaves I k α β q)[x] =
      ((sources I k).map fun src ↦ ∏ y, src.leaf α β q y).prod := by
  rw [sideLeaves, Blocks.prod_stackAt _ _ hfit, one_pow, mul_one,
    ← ((List.mergeSort_perm (sources I k) _).map _).prod_eq,
    ← Fin.prod_univ_fun_getElem]
  exact Finset.prod_congr rfl fun b _ ↦ Finset.prod_congr rfl fun y _ ↦ Vector.getElem_ofFn ..

private theorem prod_leaf_boundary (α : Fin 4 → E) (β : E) (q : Column I.μ)
    (b : BoundaryBlock I.toShape) :
    ∏ y : Fin (2 ^ b.κ), (β - fingerprint α (b.coords.map fun co ↦ I.coordCell q co y)) =
      (((List.finRange (2 ^ b.κ)).map fun x ↦ b.coords.map fun co ↦ I.coordCell q co x).map
        fun t ↦ β - fingerprint α t).prod * (([] : List (Vector K 16)).map (fingerprint α)).prod := by
  rw [Fin.prod_univ_def, List.map_map, List.map_nil, List.prod_nil, mul_one]
  rfl

private theorem prod_leaf_flush (α : Fin 4 → E) (β : E) (q : Column I.μ) (j : Fin I.ntab)
    (f : Fin (I.flushes j).length) :
    ∏ y : Fin (2 ^ I.τ j), (β - fingerprint α (flushTuple q j f y) +
        padInd j y * (1 - (β - fingerprint α (padTuple j f)))) =
      (((I.executed j).map (flushTuple q j f)).map fun t ↦ β - fingerprint α t).prod *
        (((padRows j).map (padDiff q j f)).map (fingerprint α)).prod := by
  rw [prod_rows, List.map_map, List.map_map]
  congr 1
  · refine congrArg List.prod (List.map_congr_left fun x hx ↦ ?_)
    have hx : x.val < I.rows j := of_decide_eq_true (List.mem_filter.mp hx).2
    simp [padInd, Nat.not_le.mpr hx]
  · refine congrArg List.prod (List.map_congr_left fun x hx ↦ ?_)
    have hx : I.rows j ≤ x.val := of_decide_eq_true (List.mem_filter.mp hx).2
    simp only [Function.comp_apply, padDiff, fingerprint_one_sub_add, padInd, hx, ite_true,
      one_mul]
    ring

/-- A block of a push or pull side multiplies `β − π_α(t)` over its tuples on the bus and the
fingerprints of its padding tuples. -/
private theorem prod_leaf_of_mem_sideSources {s : Side} {src : Source I}
    (hs : src ∈ sideSources I s) (α : Fin 4 → E) (β : E) (q : Column I.μ) :
    ∏ y, src.leaf α β q y = ((src.busTuples q).map fun t ↦ β - fingerprint α t).prod *
      ((src.padTuples q).map (fingerprint α)).prod := by
  cases src with
  | boundary b => exact prod_leaf_boundary α β q b
  | flush j f => exact prod_leaf_flush α β q j f
  | count j c => simp [sideSources] at hs

/-- The product of a push or pull side's leaves is the side's product at `(α, β)` (§5.2) times
the product of its padding leaves (Proposition `prop:pad`). -/
theorem prod_sideLeaves_eq {k : Fin 3} {s : Side} (hk : sources I k = sideSources I s)
    (α : Fin 4 → E) (β : E) (q : Column I.μ) (hfit : (blocks I k).total ≤ 2 ^ I.μBus) :
    ∏ x : Fin (2 ^ I.μBus), (sideLeaves I k α β q)[x] =
      sideProduct α β (I.tuples q s) * padProduct α (sidePadTuples I q s) := by
  rw [prod_sideLeaves k α β q hfit, hk, sideProduct,
    ← Multiset.coe_eq_coe.mpr (sideTuples_perm q s),
    Multiset.map_coe, Multiset.prod_coe, sideTuples, prod_flatMap, padProduct, sidePadTuples,
    Multiset.map_coe, Multiset.prod_coe, prod_flatMap, ← List.prod_map_mul]
  exact congrArg List.prod (List.map_congr_left fun src hs ↦
    prod_leaf_of_mem_sideSources hs α β q)

/-- The product of the push side's leaves. -/
theorem prod_pushLeaves (α : Fin 4 → E) (β : E) (q : Column I.μ) :
    ∏ x : Fin (2 ^ I.μBus), (pushLeaves I α β q)[x] =
      sideProduct α β (I.tuples q .push) * padProduct α (sidePadTuples I q .push) :=
  prod_sideLeaves_eq rfl α β q (push_fits I)

/-- The product of the pull side's leaves. -/
theorem prod_pullLeaves (h : Conditions I) (α : Fin 4 → E) (β : E) (q : Column I.μ) :
    ∏ x : Fin (2 ^ I.μBus), (pullLeaves I α β q)[x] =
      sideProduct α β (I.tuples q .pull) * padProduct α (sidePadTuples I q .pull) :=
  prod_sideLeaves_eq rfl α β q (h.fits 1)

/-- With honest padding rows, every padding leaf is `1`. -/
theorem padProduct_of_honest {q : Column I.μ} (hp : I.PaddingHonest q) (α : Fin 4 → E)
    (s : Side) : padProduct α (sidePadTuples I q s) = 1 := by
  rw [padProduct, sidePadTuples, Multiset.map_coe, Multiset.prod_coe]
  refine List.prod_eq_one fun e he ↦ ?_
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp he
  obtain ⟨src, -, hu⟩ := List.mem_flatMap.mp hu
  cases src with
  | flush j f =>
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hu
    have hrow := hp j x (of_decide_eq_true (List.mem_filter.mp hx).2)
    rw [padDiff, fingerprint_one_sub_add]
    simp only [flushTuple, hrow, padTuple]
    ring
  | boundary b => cases hu
  | count j c => cases hu

/-- A padding tuple is nonzero: its first slot, where both tuples hold the same separator, is
`1`. -/
theorem padTuple_ne_zero (h : Conditions I) {q : Column I.μ} {s : Side} {u : Vector K 16}
    (hu : u ∈ sidePadTuples I q s) : ∃ i : Fin 16, u[i] ≠ 0 := by
  obtain ⟨src, -, hu⟩ := List.mem_flatMap.mp hu
  cases src with
  | flush j f =>
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp hu
    refine ⟨0, ?_⟩
    simp only [padDiff, Fin.getElem_fin, Vector.getElem_ofFn, flushTuple, padTuple,
      Vector.getElem_map]
    rw [show ((flushPolys j f)[(0 : Fin 16).val]).eval (I.row q j x) =
      ((flushPolys j f)[(0 : Fin 16).val]).eval (I.padRow j) from h.separator j f _ _]
    simp
  | boundary b => cases hu
  | count j c => cases hu

/-- A push or pull side has as many tuples and padding tuples as leaves. -/
theorem length_side {k : Fin 3} {s : Side} (hk : sources I k = sideSources I s)
    (q : Column I.μ) :
    (sidePadTuples I q s).length + (I.tuples q s).length = leafCount I k := by
  rw [← (sideTuples_perm q s).length_eq, sidePadTuples, sideTuples, List.length_flatMap,
    List.length_flatMap, ← List.sum_map_add, leafCount, hk]
  refine congrArg List.sum (List.map_congr_left fun src hs ↦ ?_)
  cases src with
  | boundary b =>
    simp only [Source.padTuples, Source.busTuples, List.length_map, List.length_nil, zero_add,
      List.length_finRange]
    rfl
  | flush j f =>
    simp only [Source.padTuples, Source.busTuples, List.length_map]
    rw [add_comm]
    exact length_rows j
  | count j c => simp [sideSources] at hs

/-- The count side's product is zero when an executed count cell is (§6.2): a nonzero count root
makes every executed count cell nonzero. -/
theorem countsNonzero_of_prod (h : Conditions I) (α : Fin 4 → E) (β : E) (q : Column I.μ)
    (hnz : ∏ x : Fin (2 ^ I.μBus), (sideLeaves I 2 α β q)[x] ≠ 0) : I.CountsNonzero q := by
  rw [prod_sideLeaves 2 α β q (h.fits 2)] at hnz
  intro j c hc x hx h0
  refine hnz (List.prod_eq_zero (List.mem_map.mpr ⟨.count j c, ?_,
    Finset.prod_eq_zero (i := x) (Finset.mem_univ _) ?_⟩))
  · change _ ∈ countSources I
    simp only [countSources, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map]
    exact ⟨j, c, hc, rfl⟩
  · change ofK ((I.column q ⟨j, c⟩).values.get x) + padInd j x * (1 - ofK (I.padRow j c)) = 0
    have hi : padInd j x = 0 := by simp [padInd, Nat.not_le.mpr hx]
    rw [h0, hi, zero_mul, add_zero]
    exact _root_.map_zero (algebraMap K E)

/-- With honest padding rows and nonzero executed counts, the count side's product is nonzero. -/
theorem prod_countLeaves_ne_zero (h : Conditions I) (α : Fin 4 → E) (β : E) {q : Column I.μ}
    (hp : I.PaddingHonest q) (hn : I.CountsNonzero q) :
    ∏ x : Fin (2 ^ I.μBus), (sideLeaves I 2 α β q)[x] ≠ 0 := by
  rw [prod_sideLeaves 2 α β q (h.fits 2)]
  refine List.prod_ne_zero fun h0 ↦ ?_
  obtain ⟨src, hs, h0⟩ := List.mem_map.mp h0
  change src ∈ countSources I at hs
  simp only [countSources, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map] at hs
  obtain ⟨j, c, hc, rfl⟩ := hs
  obtain ⟨x, -, hx⟩ := Finset.prod_eq_zero_iff.mp h0
  change ofK ((I.column q ⟨j, c⟩).values.get x) + padInd j x * (1 - ofK (I.padRow j c)) = 0
    at hx
  by_cases hr : I.rows j ≤ x.val
  · have hcell : (I.column q ⟨j, c⟩).values.get x = I.padRow j c :=
      congrFun (hp j x hr) c
    have hi : padInd j x = 1 := by simp [padInd, hr]
    rw [hcell, hi, one_mul, add_sub_cancel] at hx
    exact one_ne_zero hx
  · have hi : padInd j x = 0 := by simp [padInd, hr]
    rw [hi, zero_mul, add_zero] at hx
    exact hn j c hc x (Nat.not_le.mp hr)
      ((map_eq_zero_iff (algebraMap K E) (algebraMap K E).injective).mp hx)

/-! ## Riders -/

variable (I)

/-- The constraints of the tables that fit in the leaf stacks' depth, as riders: each its
virtual table, which must vanish at the final point. -/
def constraintRiders (q : Column I.μ) : List (Σ τ : Fin (I.μBus + 1), CMlPolynomialEval E τ) :=
  (List.finRange I.ntab).flatMap fun j ↦
    if hj : I.τ j ≤ I.μBus then
      (I.constraints j).map fun C ↦ ⟨⟨I.τ j, Nat.lt_succ_of_le hj⟩, I.virtualTable q j C⟩
    else []

/-- The public lines and the Flock predicate as a rider on no variable: `0` exactly when they
hold. -/
def linesRider (input : I.Stmt) (q : Column I.μ) : Σ τ : Fin (I.μBus + 1), CMlPolynomialEval E τ :=
  ⟨⟨0, Nat.succ_pos _⟩, #v[if I.PublicLinesHold input q ∧ I.aux q then 0 else 1]⟩

/-- The public data of the grand-product argument: the statement and the fingerprint challenges
`(α, β)`. -/
abbrev Data : Type := I.Stmt × ((Fin 4 → E) × E)

/-- The leaves of the three trees, read off the stack at the challenges: push, pull, count. -/
def leaves (x : Data I) (o : ∀ i, TheOracle I i) : Fin 3 → CMlPolynomialEval E I.μBus :=
  fun k ↦ sideLeaves I k x.2.1 x.2.2 (theStack o)

/-- The riders: the constraints, and the public lines with the Flock predicate. -/
def riders (x : Data I) (o : ∀ i, TheOracle I i) :
    List (Σ τ : Fin (I.μBus + 1), CMlPolynomialEval E τ) :=
  constraintRiders I (theStack o) ++ [linesRider I x.1 (theStack o)]

variable {I}

/-- A constraint's virtual table is zero exactly when the constraint vanishes on every row. -/
private theorem virtualTable_zero_iff (q : Column I.μ) (j : Fin I.ntab)
    (C : CMvPolynomial (I.width j) K) :
    (∀ x : Fin (2 ^ I.τ j), (I.virtualTable q j C)[x] = 0) ↔ ∀ x, C.eval (I.row q j x) = 0 := by
  refine forall_congr' fun x ↦ ?_
  simp only [M3Instance.virtualTable, Fin.getElem_fin, Vector.getElem_ofFn]
  exact map_eq_zero_iff (algebraMap K E) (algebraMap K E).injective

/-- The lines' rider is zero exactly when the public lines and the Flock predicate hold. -/
private theorem linesRider_zero_iff (input : I.Stmt) (q : Column I.μ) :
    (∀ i : Fin (2 ^ ((linesRider I input q).1 : ℕ)), (linesRider I input q).2[i] = 0) ↔
      I.PublicLinesHold input q ∧ I.aux q := by
  by_cases hl : I.PublicLinesHold input q ∧ I.aux q
  · refine iff_of_true (fun i ↦ ?_) hl
    obtain ⟨i, hi⟩ := i
    have hi0 : i = 0 := by simpa [linesRider] using hi
    subst hi0
    simp only [linesRider, hl]
    rfl
  · refine iff_of_false (fun h0 ↦ ?_) hl
    have := h0 ⟨0, Nat.two_pow_pos _⟩
    simp only [linesRider, hl, ite_false] at this
    exact one_ne_zero this

/-- The lines' rider is its one value at any point. -/
private theorem evalMle_linesRider (input : I.Stmt) (q : Column I.μ) (ζ : Vector E I.μBus) :
    evalMle (linesRider I input q).2 (Gkr.lowPoint ζ (linesRider I input q).1) =
      if I.PublicLinesHold input q ∧ I.aux q then 0 else 1 :=
  rfl

/-- Every rider is zero exactly when the constraints vanish, the public lines hold and the
Flock predicate holds. -/
theorem ridersZero_iff (h : Conditions I) (x : Data I) (o : ∀ i, TheOracle I i) :
    Gkr.RidersZero I.μBus (riders I) x o ↔
      I.ConstraintsVanish (theStack o) ∧ I.PublicLinesHold x.1 (theStack o) ∧
        I.aux (theStack o) := by
  simp only [Gkr.RidersZero, riders, List.mem_append, List.mem_singleton, or_imp, forall_and,
    forall_eq]
  rw [linesRider_zero_iff]
  refine and_congr ⟨fun hz j C hC ↦ ?_, fun hc r hr ↦ ?_⟩ Iff.rfl
  · have hj : I.τ j ≤ I.μBus := h.constrained j (List.ne_nil_of_mem hC)
    refine (virtualTable_zero_iff _ j C).mp fun y ↦
      hz ⟨⟨I.τ j, Nat.lt_succ_of_le hj⟩, I.virtualTable (theStack o) j C⟩ ?_ y
    simp only [constraintRiders, List.mem_flatMap, List.mem_finRange, true_and]
    exact ⟨j, by rw [dite_eq_left hj]; exact List.mem_map_of_mem hC⟩
  · simp only [constraintRiders, List.mem_flatMap, List.mem_finRange, true_and] at hr
    obtain ⟨j, hr⟩ := hr
    split at hr
    · obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hr
      exact (virtualTable_zero_iff _ j C).mpr (hc j C hC)
    · cases hr

/-- Every rider vanishes at the low coordinates of a point exactly when every constraint of a
table that fits does, and the public lines and the Flock predicate hold. -/
theorem riders_vanish_iff (x : Data I) (o : ∀ i, TheOracle I i) (ζ : Vector E I.μBus) :
    (∀ r ∈ riders I x o, evalMle r.2 (Gkr.lowPoint ζ r.1) = 0) ↔
      (∀ j (hj : I.τ j ≤ I.μBus), ∀ C ∈ I.constraints j,
        evalMle (I.virtualTable (theStack o) j C) (Gkr.lowPoint ζ ⟨I.τ j, Nat.lt_succ_of_le hj⟩) =
          0) ∧ I.PublicLinesHold x.1 (theStack o) ∧ I.aux (theStack o) := by
  simp only [riders, List.mem_append, List.mem_singleton, or_imp, forall_and, forall_eq]
  rw [evalMle_linesRider]
  refine and_congr ⟨fun h j hj C hC ↦
    h ⟨⟨I.τ j, Nat.lt_succ_of_le hj⟩, I.virtualTable (theStack o) j C⟩ ?_, fun h r hr ↦ ?_⟩ ?_
  · simp only [constraintRiders, List.mem_flatMap, List.mem_finRange, true_and]
    exact ⟨j, by rw [dite_eq_left hj]; exact List.mem_map_of_mem hC⟩
  · simp only [constraintRiders, List.mem_flatMap, List.mem_finRange, true_and] at hr
    obtain ⟨j, hr⟩ := hr
    split at hr
    · obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hr
      exact h j ‹_› C hC
    · cases hr
  · by_cases hl : I.PublicLinesHold x.1 (theStack o) ∧ I.aux (theStack o)
    · simp [hl]
    · simp [hl]

variable (I)

/-! ## The verifier's last step -/

variable {I}

/-- The value sent for a committed boundary column: the message's entry at the column's place
among the boundary columns. -/
def valueOf (vals : Vector E I.busClaims) (c : I.ColumnId) : E :=
  match I.boundaryColumns.finIdxOf? c with
  | some i => vals[i]
  | none => 0

/-- A boundary coordinate's value as the verifier has it at a point: a constant, a known column's
extension, or the value sent for a committed column. -/
def coordValue (vals : Vector E I.busClaims) {κ : ℕ} : Coord I.toShape κ → Vector E κ → E
  | .const c, _ => ofK c
  | .known col, z => eval₂Mle col.values (algebraMap K E) z
  | .committed c _, _ => valueOf vals c

/-- The part of a block the verifier evaluates itself, from the values sent: a boundary block's
leaf extension, a table block's padding term (`padding_rows`, `verifier.py:594-601`). -/
def Source.publicValue (α : Fin 4 → E) (β : E) (vals : Vector E I.busClaims) :
    (src : Source I) → Vector E src.κ → E
  | .boundary b, z =>
    let w := fingerprintWeights α
    β - ∑ i : Fin 16, w[i.val] * coordValue vals b.coords[i] z
  | .flush j f, z => (Source.flush j f).padTerm α β z
  | .count j c, z => (Source.count j c).padTerm α β z

/-- The constant row polynomial `1`. -/
def oneRow (j : Fin I.ntab) : I.RowPoly j :=
  ⟨1, by rw [totalDegree_equiv (S := K), CPoly.map_one, MvPolynomial.totalDegree_one]; omega⟩

/-- A flush block's terms on its table, at the block's weight `w`: `w·β` against `1`, and
`−w·eq(α, i)` against coordinate `i`'s polynomial. -/
def flushForm (j : Fin I.ntab) (f : Fin (I.flushes j).length) (w : E) (α : Fin 4 → E) (β : E) :
    I.Form j :=
  let tw := fingerprintWeights α
  (w * β, oneRow j) :: (List.finRange 16).map fun i ↦ (-(w * tw[i.val]),
    ⟨(flushPolys j f)[i], by
      simpa [flushPolys, Vector.get_eq_getElem] using
        I.flushes_degree j _ (List.getElem_mem f.isLt) i⟩)

/-- A count column's term on its table, at the block's weight `w`: `w` against the column's
variable. -/
def countForm (hd : 1 ≤ I.d) (j : Fin I.ntab) (c : Fin (I.width j)) (w : E) : I.Form j :=
  [(w, ⟨CMvPolynomial.X c, by
    rw [totalDegree_equiv (S := K), CMvPolynomial.fromCMvPolynomial_X, MvPolynomial.totalDegree_X]
    exact hd⟩)]

/-- A block's terms on table `j`: its flush's or count column's if it is table `j`'s, none
otherwise. -/
def Source.form (hd : 1 ≤ I.d) (w : E) (α : Fin 4 → E) (β : E) (j : Fin I.ntab) :
    Source I → I.Form j
  | .boundary _ => []
  | .flush j' f => if h : j' = j then h ▸ flushForm j' f w α β else []
  | .count j' c => if h : j' = j then h ▸ countForm hd j' c w else []

/-- Block `b`'s selector weight at `ζ`: `eq(sel_b, ζ_{≥κ_b})`. -/
abbrev weight (h : Conditions I) (k : Fin 3) (b : Fin (blocks I k).n) (ζ : Vector E I.μBus) :
    E :=
  (blocks I k).selectorWeight (h.fits k) b ζ

/-- Block `b`'s point inside `ζ`: `ζ_{<κ_b}`. -/
abbrev lowAt (h : Conditions I) (k : Fin 3) (b : Fin (blocks I k).n) (ζ : Vector E I.μBus) :
    Vector E (src I k b).κ :=
  (blocks I k).lowPoint (h.fits k) b ζ

/-- Side `k`'s forms, per sumcheck table: its tables' blocks' terms. -/
def forms (h : Conditions I) (k : Fin 3) (α : Fin 4 → E) (β : E) (ζ : Vector E I.μBus)
    (j : I.SumcheckTables) : I.Form j.1 :=
  (List.finRange (blocks I k).n).flatMap fun b ↦
    (src I k b).form h.one_le_d (weight h k b ζ) α β j.1

/-- Side `k`'s total: its leaf claim `v`, less its blocks' public part (the boundary blocks',
evaluated from the values sent, and the table blocks' padding terms), and the pad's weight
`1 + Σ_b eq(sel_b, ζ_{≥κ_b})`. -/
def total (h : Conditions I) (k : Fin 3) (α : Fin 4 → E) (β : E) (ζ : Vector E I.μBus) (v : E)
    (vals : Vector E I.busClaims) : E :=
  v - ((∑ b, weight h k b ζ * (src I k b).publicValue α β vals (lowAt h k b ζ)) +
    (1 + ∑ b, weight h k b ζ))

/-- The table sumcheck's point: `ζ_{<τ_max}`. -/
def point (h : Conditions I) (ζ : Vector E I.μBus) : Vector E I.τmax :=
  Gkr.lowPoint ζ ⟨I.τmax, Nat.lt_succ_of_le h.τmax_le⟩

/-- The point of boundary column `i`'s claim: `ζ_{<κ}`, `κ` the column's log-height. -/
def columnPoint (h : Conditions I) (ζ : Vector E I.μBus) (i : Fin I.busClaims) :
    Vector E (I.κ I.boundaryColumns[i]) :=
  Gkr.lowPoint ζ ⟨_, Nat.lt_succ_of_le (h.κ_le_of_boundaryColumn (List.getElem_mem i.isLt))⟩

/-- What the bus phase hands on, from the grand-product argument's last statement (the
statement, `(α, β)`, `ζ` and the three leaf claims) and the values sent. -/
def busOut (h : Conditions I) (ℓ : Gkr.LayerStmt (Data I) E 3 I.μBus)
    (vals : Vector E I.busClaims) : BusOut I where
  point := point h ℓ.2.1
  forms k j := forms h k ℓ.1.2.1 ℓ.1.2.2 ℓ.2.1 j
  totals k := total h k ℓ.1.2.1 ℓ.1.2.2 ℓ.2.1 (ℓ.2.2 k) vals
  columns := Vector.ofFn fun i ↦ ⟨I.boundaryColumns[i], columnPoint h ℓ.2.1 i, vals[i]⟩

/-- The honest prover's values: each boundary column's extension at its point. -/
def honestValues (h : Conditions I) (q : Column I.μ) (ζ : Vector E I.μBus) :
    Vector E I.busClaims :=
  Vector.ofFn fun i ↦ eval₂Mle (I.column q I.boundaryColumns[i]).values (algebraMap K E)
    (columnPoint h ζ i)

/-! ## The phase's steps -/

variable (I)

/-- The honest roots: the push side's product, which is the pull side's on a balanced bus, and
the count side's. -/
def rootsHonest (p : (Data I × ∀ i, TheOracle I i) × Unit) : E × E :=
  (∏ x : Fin (2 ^ I.μBus), (leaves I p.1.1 p.1.2 0)[x],
    ∏ x : Fin (2 ^ I.μBus), (leaves I p.1.1 p.1.2 2)[x])

/-- The fingerprint challenges, as a typed component. -/
def challengeStep :
    Typed.Def (TheOracle I) I.Stmt Unit (Data I) Unit (Typed.drawSlot ((Fin 4 → E) × E)) :=
  Typed.sampleChallenge (TheOracle I) ((Fin 4 → E) × E) (fun _ ↦ true) fun s ab ↦ (s, ab)

/-- The roots, as a typed component. -/
def rootsStep :
    Typed.Def (TheOracle I) (Data I) Unit (Data I × (Fin 3 → E)) Unit (Typed.saySlot (E × E)) :=
  Typed.sendChecked (TheOracle I) (E × E) (rootsHonest I) (fun _ r ↦ decide (r.2 ≠ 0))
    fun x r ↦ (x, ![r.1, r.1, r.2])

/-- The boundary values, as a typed component. -/
def valuesStep (h : Conditions I) :
    Typed.Def (TheOracle I) (Gkr.LayerStmt (Data I) E 3 I.μBus) Unit (I.Stmt × BusOut I) Unit
      (Typed.saySlot (Vector E I.busClaims)) :=
  Typed.sendChecked (TheOracle I) (Vector E I.busClaims)
    (fun p ↦ honestValues h (theStack p.1.2) p.1.1.2.1) (fun _ _ ↦ true)
    fun ℓ vals ↦ (ℓ.1.1, busOut h ℓ vals)

end Bus

open Bus in
/-- **The leaves at a point** (§5.4, equation (2)): a side's leaf stack at `ζ` is the sum over
its blocks of the selector weight `eq(sel_b, ζ_{≥κ_b})` times the block's leaf extension at
`ζ_{<κ_b}`, plus the pad's weight `1 + Σ_b eq(sel_b, ζ_{≥κ_b})`. -/
theorem leaf_decomposition {I : M3Instance} (h : Conditions I) (k : Fin 3) (α : Fin 4 → E)
    (β : E) (q : Column I.μ) (ζ : Vector E I.μBus) :
    evalMle (sideLeaves I k α β q) ζ =
      (∑ b, (blocks I k).selectorWeight (h.fits k) b ζ *
        (src I k b).leafEval α β q ((blocks I k).lowPoint (h.fits k) b ζ)) +
      (1 + ∑ b, (blocks I k).selectorWeight (h.fits k) b ζ) := by
  rw [sideLeaves, Blocks.stack_eval_ambient_one]
  refine congrArg (· + _) (Finset.sum_congr rfl fun b _ ↦ ?_)
  exact congrArg _ (Source.evalMle_leaf α β q (src I k b) _)

namespace Bus

variable {I : M3Instance}

/-! ## Points inside `ζ` -/

/-- Block `b`'s point inside `ζ` is `ζ`'s first `κ_b` coordinates. -/
private theorem lowAt_eq (h : Conditions I) (k : Fin 3) (b : Fin (blocks I k).n)
    (ζ : Vector E I.μBus) :
    lowAt h k b ζ = Gkr.lowPoint ζ
      ⟨(src I k b).κ, Nat.lt_succ_of_le ((blocks I k).size_le (h.fits k) b)⟩ := by
  apply Vector.ext
  intro i hi
  simp only [lowAt, Blocks.lowPoint, lowVec, Gkr.lowPoint, Vector.getElem_cast,
    Vector.getElem_ofFn]
  erw [Vector.getElem_ofFn]

/-- A sumcheck table's point inside the table sumcheck's point is `ζ`'s first `τ_j`
coordinates. -/
theorem lowPoint_point (h : Conditions I) (ζ : Vector E I.μBus) (j : I.SumcheckTables) :
    I.lowPoint (point h ζ) j =
      Gkr.lowPoint ζ ⟨I.τ j.1, Nat.lt_succ_of_le ((I.τ_le_τmax j).trans h.τmax_le)⟩ := by
  apply Vector.ext
  intro i hi
  simp only [M3Instance.lowPoint, point, Gkr.lowPoint, Vector.getElem_cast, Vector.getElem_take,
    Vector.getElem_ofFn]

/-! ## The values sent and the boundary blocks -/

/-- A column's extension, read at an equal column. -/
private theorem eval_column_congr (q : Column I.μ) {c c' : I.ColumnId} (e : c = c')
    (z : Vector E (I.κ c)) :
    eval₂Mle (I.column q c).values (algebraMap K E) z =
      eval₂Mle (I.column q c').values (algebraMap K E) (Vector.cast (congrArg I.κ e) z) := by
  subst e
  rfl

/-- With the true values, the verifier's value of a boundary coordinate is its extension. -/
private theorem coordValue_eq (h : Conditions I) (q : Column I.μ) (ζ : Vector E I.μBus)
    (vals : Vector E I.busClaims)
    (hvals : ∀ i : Fin I.busClaims, vals[i] =
      eval₂Mle (I.column q I.boundaryColumns[i]).values (algebraMap K E) (columnPoint h ζ i))
    {κ : ℕ} (hκ : κ < I.μBus + 1) (co : Coord I.toShape κ)
    (hco : ∀ c, co.committed? = some c → c ∈ I.boundaryColumns) :
    coordValue vals co (Gkr.lowPoint ζ ⟨κ, hκ⟩) = coordEval q co (Gkr.lowPoint ζ ⟨κ, hκ⟩) := by
  cases co with
  | const c => rfl
  | known col => rfl
  | committed c hc =>
    have hmem := hco c rfl
    obtain ⟨i, hi⟩ : ∃ i, I.boundaryColumns.finIdxOf? c = some i := by
      cases hf : I.boundaryColumns.finIdxOf? c with
      | none => exact absurd hmem (List.finIdxOf?_eq_none_iff.mp hf)
      | some i => exact ⟨i, rfl⟩
    have hci : I.boundaryColumns[i] = c := (List.finIdxOf?_eq_some_iff.mp hi).1
    simp only [coordValue, valueOf, hi, coordEval]
    rw [hvals i, columnPoint, eval_column_congr q hci]
    congr 1
    apply Vector.ext
    intro n hn
    simp only [Vector.getElem_cast, Gkr.lowPoint]
    erw [Vector.getElem_ofFn, Vector.getElem_ofFn]

/-- A boundary block of a side is one of the instance's, of the push or pull side. -/
private theorem mem_boundary_of_mem {k : Fin 3} {b : BoundaryBlock I.toShape}
    (hs : Source.boundary b ∈ sources I k) :
    b ∈ I.boundary ∧ (b.side = .push ∨ b.side = .pull) := by
  fin_cases k <;>
    simp [sources, sideSources, countSources, List.mem_append, List.mem_map, List.mem_filter,
      List.mem_flatMap] at hs ⊢ <;> tauto

/-- A committed coordinate of a boundary block of a side is a boundary column. -/
private theorem mem_boundaryColumns_of_mem {k : Fin 3} {b : BoundaryBlock I.toShape}
    (hs : Source.boundary b ∈ sources I k) (i : Fin 16) (c : I.ColumnId)
    (hc : (b.coords[i]).committed? = some c) : c ∈ I.boundaryColumns := by
  obtain ⟨hb, hside⟩ := mem_boundary_of_mem hs
  simp only [M3Instance.boundaryColumns, List.mem_eraseDups, List.mem_flatMap, List.mem_cons,
    List.not_mem_nil, or_false, List.mem_filter, decide_eq_true_eq, List.mem_filterMap]
  exact ⟨b.side, by tauto, b, ⟨hb, rfl⟩, b.coords[i],
    Vector.mem_toList_iff.mpr (Vector.getElem_mem _), hc⟩

/-- A count column of a side is one of its table's count columns. -/
private theorem mem_counts_of_mem {k : Fin 3} {j : Fin I.ntab} {c : Fin (I.width j)}
    (hs : Source.count j c ∈ sources I k) : c ∈ I.counts j := by
  fin_cases k <;>
    simp [sources, sideSources, countSources, List.mem_append, List.mem_map, List.mem_filter,
      List.mem_flatMap] at hs
  obtain ⟨j', c', hc', rfl, he⟩ := hs
  cases he
  exact hc'

/-! ## The forms -/

private theorem sum_map_flatMap {M α β : Type} [AddCommMonoid M] (l : List α) (f : α → List β)
    (g : β → M) : ((l.flatMap f).map g).sum = (l.map fun a ↦ ((f a).map g).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons]

/-- A form built block by block has the sum of the blocks' values. -/
private theorem eval_flatMap {j : Fin I.ntab} {n : ℕ} (g : Fin n → I.Form j) (q : Column I.μ)
    (z : Vector E (I.τ j)) :
    M3Instance.Form.eval I ((List.finRange n).flatMap g) q z =
      ∑ b, M3Instance.Form.eval I (g b) q z := by
  rw [M3Instance.Form.eval, sum_map_flatMap, Fin.sum_univ_def]
  rfl

/-- A flush block's terms evaluate to its weight times its leaf extension, less the padding
term. -/
private theorem eval_flushForm (q : Column I.μ) (j : Fin I.ntab) (f : Fin (I.flushes j).length)
    (w : E) (α : Fin 4 → E) (β : E) (z : Vector E (I.τ j)) :
    M3Instance.Form.eval I (flushForm j f w α β) q z = w * (β - ∑ i : Fin 16,
      (fingerprintWeights α)[i.val] * evalMle (I.virtualTable q j (flushPolys j f)[i]) z) := by
  have hone : evalMle (I.virtualTable q j 1) z = 1 := by
    have h1 : I.virtualTable q j 1 = Vector.replicate _ 1 := Vector.ext fun x hx ↦ by
      simp only [M3Instance.virtualTable, Vector.getElem_ofFn, Vector.getElem_replicate]
      have h1 := (CMvPolynomial.eval₂Hom (RingHom.id K) (I.row q j ⟨x, hx⟩)).map_one
      rw [CMvPolynomial.eval₂Hom_apply] at h1
      rw [show (1 : CMvPolynomial (I.width j) K).eval (I.row q j ⟨x, hx⟩) = 1 from h1]
      exact _root_.map_one (algebraMap K E)
    rw [h1, evalMle_replicate]
  simp only [M3Instance.Form.eval, flushForm, List.map_cons, List.sum_cons, List.map_map,
    Function.comp_def, oneRow, hone]
  rw [← Fin.sum_univ_def, mul_one, mul_sub, Finset.mul_sum, sub_eq_add_neg,
    ← Finset.sum_neg_distrib]
  exact congrArg (w * β + ·) (Finset.sum_congr rfl fun i _ ↦ by ring)

/-- A count column's term evaluates to its weight times the column's extension. -/
private theorem eval_countForm (hd : 1 ≤ I.d) (q : Column I.μ) (j : Fin I.ntab)
    (c : Fin (I.width j)) (w : E) (z : Vector E (I.τ j)) :
    M3Instance.Form.eval I (countForm hd j c w) q z =
      w * eval₂Mle (I.column q ⟨j, c⟩).values (algebraMap K E) z := by
  simp only [M3Instance.Form.eval, countForm, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero]
  congr 1
  refine congrArg (evalMle · z) (Vector.ext fun x hx ↦ ?_)
  have hX : (CMvPolynomial.X c : CMvPolynomial (I.width j) K).eval (I.row q j ⟨x, hx⟩) =
      I.row q j ⟨x, hx⟩ c := by
    show CMvPolynomial.eval₂ (RingHom.id K) _ _ = _
    rw [CMvPolynomial.eval₂_X]
  rw [M3Instance.virtualTable, Vector.getElem_ofFn, hX, CMlPolynomialEval.map, Vector.getElem_map]
  show ofK ((I.column q ⟨j, c⟩).values.get ⟨x, hx⟩) = ofK ((I.column q ⟨j, c⟩).values[x])
  rw [Vector.get_eq_getElem]

/-- Block by block: a block's weighted leaf extension at its point is the part the verifier
evaluates from the true values plus its terms on the sumcheck tables at their points. -/
private theorem source_split (h : Conditions I) (k : Fin 3) (α : Fin 4 → E) (β : E)
    (q : Column I.μ) (ζ : Vector E I.μBus) (vals : Vector E I.busClaims)
    (hvals : ∀ i : Fin I.busClaims, vals[i] =
      eval₂Mle (I.column q I.boundaryColumns[i]).values (algebraMap K E) (columnPoint h ζ i))
    (src : Source I) (hs : src ∈ sources I k) (hκ : src.κ < I.μBus + 1) (w : E) :
    w * src.leafEval α β q (Gkr.lowPoint ζ ⟨src.κ, hκ⟩) =
      w * src.publicValue α β vals (Gkr.lowPoint ζ ⟨src.κ, hκ⟩) +
        ∑ j : I.SumcheckTables, M3Instance.Form.eval I (src.form h.one_le_d w α β j.1) q
          (I.lowPoint (point h ζ) j) := by
  cases src with
  | boundary b =>
    simp only [Source.form, M3Instance.Form.eval, List.map_nil, List.sum_nil,
      Finset.sum_const_zero, add_zero, Source.leafEval, Source.publicValue]
    exact congrArg (fun t ↦ w * (β - t)) (Finset.sum_congr rfl fun i _ ↦
      congrArg ((fingerprintWeights α)[i.val] * ·)
        (coordValue_eq h q ζ vals hvals hκ _ (mem_boundaryColumns_of_mem hs i)).symm)
  | flush j f =>
    have hst : I.SumcheckTable j :=
      Or.inr (Or.inl (List.ne_nil_of_length_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) f.isLt)))
    rw [Finset.sum_eq_single ⟨j, hst⟩]
    · rw [show (Source.flush j f).form h.one_le_d w α β j = flushForm j f w α β from
        dite_eq_left rfl,
        lowPoint_point, eval_flushForm]
      exact (mul_add _ _ _).trans (add_comm _ _)
    · intro j' _ hj'
      have hne : j ≠ j'.1 := fun he ↦ hj' (Subtype.ext he.symm)
      simp [Source.form, hne, M3Instance.Form.eval]
    · simp
  | count j c =>
    have hst : I.SumcheckTable j :=
      Or.inr (Or.inr (List.ne_nil_of_mem (mem_counts_of_mem hs)))
    rw [Finset.sum_eq_single ⟨j, hst⟩]
    · rw [show (Source.count j c).form h.one_le_d w α β j = countForm h.one_le_d j c w from
        dite_eq_left rfl, lowPoint_point, eval_countForm]
      exact (mul_add _ _ _).trans (add_comm _ _)
    · intro j' _ hj'
      have hne : j ≠ j'.1 := fun he ↦ hj' (Subtype.ext he.symm)
      simp [Source.form, hne, M3Instance.Form.eval]
    · simp

/-- Block `b` of side `k` is one of the side's blocks. -/
private theorem src_mem (k : Fin 3) (b : Fin (blocks I k).n) : src I k b ∈ sources I k :=
  (List.mergeSort_perm _ _).mem_iff.mp (List.getElem_mem _)

/-- **The leaf claims are owed by the forms.** With the true values of the boundary columns,
side `k`'s forms sum to its total exactly when its leaf claim `v` is its leaves' extension at
`ζ`. -/
theorem sum_forms_eq_total_iff (h : Conditions I) (k : Fin 3) (α : Fin 4 → E) (β : E)
    (q : Column I.μ) (ζ : Vector E I.μBus) (v : E) (vals : Vector E I.busClaims)
    (hvals : ∀ i : Fin I.busClaims, vals[i] =
      eval₂Mle (I.column q I.boundaryColumns[i]).values (algebraMap K E) (columnPoint h ζ i)) :
    (∑ j, M3Instance.Form.eval I (forms h k α β ζ j) q (I.lowPoint (point h ζ) j) =
        total h k α β ζ v vals) ↔
      evalMle (sideLeaves I k α β q) ζ = v := by
  have hsplit : ∑ b, weight h k b ζ * (src I k b).leafEval α β q (lowAt h k b ζ) =
      ∑ b, weight h k b ζ * (src I k b).publicValue α β vals (lowAt h k b ζ) +
        ∑ j, M3Instance.Form.eval I (forms h k α β ζ j) q (I.lowPoint (point h ζ) j) := by
    simp only [forms, eval_flatMap]
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [lowAt_eq]
    exact source_split h k α β q ζ vals hvals (src I k b) (src_mem k b) _ _
  rw [leaf_decomposition h k α β q ζ, total, eq_sub_iff_add_eq]
  change _ ↔ ∑ b, weight h k b ζ * (src I k b).leafEval α β q (lowAt h k b ζ) +
    (1 + ∑ b, weight h k b ζ) = v
  rw [hsplit]
  constructor <;> intro H <;> rw [← H] <;> ring

/-! ## Completeness -/

variable (I)

/-- After the challenges: the push and pull products agree, the count product is nonzero, every
constraint vanishes, and the public lines and the Flock predicate hold. -/
def afterChallenge : Set ((Data I × ∀ i, TheOracle I i) × Unit) :=
  {p | (∏ x : Fin (2 ^ I.μBus), (leaves I p.1.1 p.1.2 0)[x]) =
      ∏ x : Fin (2 ^ I.μBus), (leaves I p.1.1 p.1.2 1)[x] ∧
    (∏ x : Fin (2 ^ I.μBus), (leaves I p.1.1 p.1.2 2)[x]) ≠ 0 ∧
    I.ConstraintsVanish (theStack p.1.2) ∧
    I.PublicLinesHold p.1.1.1 (theStack p.1.2) ∧ I.aux (theStack p.1.2)}

variable {I}

/-- On a balanced bus with honest padding rows the two products agree at every `(α, β)`, and the
count product is nonzero. -/
theorem challenge_honest (h : Conditions I) (s : I.Stmt) (o : ∀ i, TheOracle I i) (w : Unit)
    (hin : ((s, o), w) ∈ Seam.commitHonest I) :
    (fun _ ↦ true) s = true ∧ ∀ ab : (Fin 4 → E) × E, (((s, ab), o), w) ∈ afterChallenge I := by
  obtain ⟨⟨hc, hb, hn, hl, ha⟩, hp⟩ := hin
  refine ⟨rfl, fun ab ↦ ⟨?_, prod_countLeaves_ne_zero h _ _ hp hn, hc, hl, ha⟩⟩
  change ∏ x : Fin (2 ^ I.μBus), (pushLeaves I ab.1 ab.2 (theStack o))[x] =
    ∏ x : Fin (2 ^ I.μBus), (pullLeaves I ab.1 ab.2 (theStack o))[x]
  rw [prod_pushLeaves, prod_pullLeaves h, padProduct_of_honest hp, padProduct_of_honest hp,
    Multiset.coe_eq_coe.mpr hb]

/-- The challenges' typed completeness. -/
theorem challengeComplete (h : Conditions I) :
    Typed.Complete (challengeStep I) (Seam.commitHonest I) (afterChallenge I) :=
  Typed.sampleChallengeComplete (challenge_honest h)

/-- The honest roots are the products, the count root is nonzero, and every rider is zero. -/
theorem roots_honest (h : Conditions I) (x : Data I) (o : ∀ i, TheOracle I i) (w : Unit)
    (hin : ((x, o), w) ∈ afterChallenge I) :
    decide ((rootsHonest I ((x, o), w)).2 ≠ 0) = true ∧
      (((x, ![(rootsHonest I ((x, o), w)).1, (rootsHonest I ((x, o), w)).1,
        (rootsHonest I ((x, o), w)).2]), o), w) ∈ Gkr.relIn 3 I.μBus (leaves I) (riders I) := by
  obtain ⟨hp, hn, hc, hl, ha⟩ := hin
  refine ⟨decide_eq_true hn,
    (ridersZero_iff h x o).mpr ⟨hc, hl, ha⟩, fun s ↦ ?_⟩
  fin_cases s
  · rfl
  · exact hp
  · rfl

/-- The roots' typed completeness. -/
theorem rootsComplete (h : Conditions I) :
    Typed.Complete (rootsStep I) (afterChallenge I) (Gkr.relIn 3 I.μBus (leaves I) (riders I)) :=
  Typed.sendCheckedComplete (roots_honest h)

/-- The honest values are the boundary columns' extensions. -/
theorem honestValues_getElem (h : Conditions I) (q : Column I.μ) (ζ : Vector E I.μBus)
    (i : Fin I.busClaims) :
    (honestValues h q ζ)[i] =
      eval₂Mle (I.column q I.boundaryColumns[i]).values (algebraMap K E) (columnPoint h ζ i) := by
  simp [honestValues]

/-- The honest values are the boundary columns' extensions: the leaf claims force the forms to
the totals, and the riders' vanishing gives the zerocheck clause. -/
theorem values_honest (h : Conditions I) (ℓ : Gkr.LayerStmt (Data I) E 3 I.μBus)
    (o : ∀ i, TheOracle I i) (w : Unit)
    (hout : ((ℓ, o), w) ∈ Gkr.relOut 3 I.μBus (leaves I) (riders I)) :
    (fun (_ : Gkr.LayerStmt (Data I) E 3 I.μBus) (_ : Vector E I.busClaims) ↦ true) ℓ
        (honestValues h (theStack o) ℓ.2.1) = true ∧
      (((ℓ.1.1, busOut h ℓ (honestValues h (theStack o) ℓ.2.1)), o), w) ∈ Seam.bus I := by
  obtain ⟨hleaf, hr⟩ := hout
  obtain ⟨hcons, hl, ha⟩ := (riders_vanish_iff ℓ.1 o ℓ.2.1).mp hr
  refine ⟨rfl, ?_, ?_, ?_, hl, ha⟩
  · intro j C hC
    rw [show (busOut h ℓ (honestValues h (theStack o) ℓ.2.1)).point = point h ℓ.2.1 from rfl,
      lowPoint_point]
    exact hcons j.1 ((I.τ_le_τmax j).trans h.τmax_le) C hC
  · intro side
    exact (sum_forms_eq_total_iff h side _ _ _ _ _ _
      (honestValues_getElem h (theStack o) ℓ.2.1)).mpr (hleaf side)
  · intro c hc
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (by simpa [busOut] using hc)
    exact (honestValues_getElem h (theStack o) ℓ.2.1 i).symm

/-- The values' typed completeness. -/
theorem valuesComplete (h : Conditions I) :
    Typed.Complete (valuesStep I h) (Gkr.relOut 3 I.μBus (leaves I) (riders I)) (Seam.bus I) :=
  Typed.sendCheckedComplete (values_honest h)

end Bus

/-- The bus phase on the typed framework, at its slot `busSlot I`. -/
def busPhase (I : M3Instance) (h : Bus.Conditions I) :
    Typed.Def (TheOracle I) I.Stmt Unit (I.Stmt × BusOut I) Unit (busSlot I) :=
  (((Bus.challengeStep I).append (Bus.rootsStep I)).append
    (gkr 3 I.μBus (Bus.leaves I))).append (Bus.valuesStep I h)

/-- **Perfect completeness of the bus phase on the typed framework**, from a stack whose padding
rows are honest. -/
theorem busComplete (I : M3Instance) (h : Bus.Conditions I) :
    Typed.Complete (busPhase I h) (Seam.commitHonest I) (Seam.bus I) :=
  (((Bus.challengeComplete h).append (Bus.rootsComplete h)).append
    (gkrComplete 3 I.μBus (Bus.leaves I) (Bus.riders I))).append (Bus.valuesComplete h)

end
end LeanVM.Protocol
