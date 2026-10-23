import LeanVM.Protocol.Bus
import LeanVM.Protocol.Spine.Toy
import CompPoly.Multivariate.Eval
import CompPoly.Multivariate.MvPolyEquiv.Eval
import CompPoly.Multivariate.Operations
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Bus phase tests

On an instance built for the bus (`busToy`): one table of height 2 with a value column `a` and a
count column `c`, one constraint (`a` is Boolean), one push flush `(0, a, c, 0, …)`, its slot 0 the
constant domain separator; a push boundary block of two constant tuples `(7, 0, …)`, a pull block
`(0, 1, c, 0, …)` whose third coordinate is the committed count column, and a pull block of two
constant tuples `(7, 0, …)`. Both rows are executed. The bus balances exactly when `a = [1, 1]`.
The push side has two blocks of equal height, so the tie order decides the offsets; the count
side has two leaves on a depth of two, so it is padded.

* **The side conditions** hold, the separator among them, and the instance's sizes: `μ_bus = 2`,
  one boundary column.
* **The tie order.** The push side keeps its boundary block before the table's flush (a stable
  sort): the boundary block at offset 0, the flush at offset 2.
* **The honest stack.** `M3Holds` holds; at a challenge `(α, β)` the push and pull products agree
  and the count product is nonzero, so the honest roots pass the check.
* **The leaves at a point** (`leaf_decomposition`) on all three sides at a point off the cube.
* **The last step.** With the leaf claims true at `ζ` and the honest values, every side's forms
  sum to its total, the boundary claim holds, and the forms carry each flush's terms.
* **The zero-count mutation.** A count cell `0` keeps the bus balanced but makes the count product
  `0`: the honest roots fail the check, and `M3Holds` fails at the counts alone. Without the
  check, the roots step has no security at any error (`roots_unchecked_no_security`, over any
  instance with such a stack and honest padding rows): the check is load-bearing.
* **The pad.** The count side padded with `0` instead of `1` has product `0`: the honest prover
  would be rejected.
* **The spine's toy** meets the side conditions too; its public line makes the lines rider `0` at
  the statement its stack satisfies and `1` at another; completeness has inhabitants on both.

The phase runs here by parts (the challenges and roots, the leaves at a point, the last step): the
grand-product argument between them is the one the grand-product tests run by hand, and the
composed honest run is `busComplete`.

A plain file, so `#guard` evaluates the compiled definitions. Values of `E` written with numerals
are named as definitions before a guard uses them.
-/

namespace LeanVMTests.Protocol.Bus

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Bus CompPoly CPoly
  CMlPolynomialEval OracleComp OracleSpec

/-! ## The instance -/

/-- One table of height two and width two. -/
abbrev shape : Shape := ⟨1, fun _ ↦ 1, fun _ ↦ 2⟩

/-- The two columns' blocks in the stack. -/
def colBlocks : Blocks := ⟨2, fun _ ↦ 1, fun _ _ _ ↦ le_rfl⟩

theorem colBlocks_total : colBlocks.total ≤ 2 ^ 2 := by
  simp [colBlocks, Blocks.total, Blocks.offsetNat]
  decide

/-- Column `i` is the aligned block `i`: cells `2i, 2i + 1`. -/
def layout : Layout 2 shape.ColumnId (fun c ↦ shape.τ c.1) :=
  (colBlocks.layout colBlocks_total).comap (fun c ↦ ⟨c.2.val, c.2.isLt⟩) fun _ ↦ rfl

/-- `a` is Boolean. -/
def constraint : CMvPolynomial 2 K := CMvPolynomial.X 0 * CMvPolynomial.X 0 - CMvPolynomial.X 0

private theorem constraint_totalDegree : constraint.totalDegree ≤ 2 := by
  rw [totalDegree_equiv (S := K), constraint]
  erw [CPoly.map_sub]
  rw [CPoly.map_mul, CMvPolynomial.fromCMvPolynomial_X]
  exact (MvPolynomial.totalDegree_sub _ _).trans
    (max_le ((MvPolynomial.totalDegree_mul _ _).trans (by simp)) (by simp))

/-- The push flush `(0, a, c, 0, …)`: slot 0, the domain separator, is constant. -/
def flush : Side × Vector (CMvPolynomial 2 K) 16 :=
  (.push, Vector.ofFn fun k ↦
    if k.val = 1 then CMvPolynomial.X 0 else if k.val = 2 then CMvPolynomial.X 1 else 0)

private theorem flush_totalDegree (k : Fin 16) : (flush.2.get k).totalDegree ≤ 1 := by
  rw [totalDegree_equiv (S := K)]
  simp only [flush, Vector.get_ofFn]
  split
  · simp [CMvPolynomial.fromCMvPolynomial_X]
  · split
    · simp [CMvPolynomial.fromCMvPolynomial_X]
    · simp

/-- Two constant tuples `(7, 0, …)` on a side. -/
def constBlock (s : Side) : BoundaryBlock shape where
  κ := 1
  side := s
  coords := Vector.ofFn fun k ↦ if k.val = 0 then .const (K.ofBits 7) else .const 0

/-- The pull block `(0, 1, c, 0, …)`: the flush's separator, a known column of ones and the
committed count column. -/
def countPull : BoundaryBlock shape where
  κ := 1
  side := .pull
  coords := Vector.ofFn fun k ↦
    if k.val = 1 then .known ⟨#v[1, 1]⟩ else if k.val = 2 then .committed ⟨0, 1⟩ rfl else .const 0

/-- The instance. -/
abbrev busToy : M3Instance where
  toShape := shape
  Stmt := Unit
  constraints := fun _ ↦ [constraint]
  flushes := fun _ ↦ [flush]
  d := 2
  constraints_degree := fun _ C h ↦ by
    rw [List.mem_singleton.mp h]; exact constraint_totalDegree
  flushes_degree := fun _ f h k ↦ by
    rw [List.mem_singleton.mp h]; exact (flush_totalDegree k).trans (by decide)
  counts := fun _ ↦ [1]
  rows := fun j ↦ 2 ^ shape.τ j
  rows_le := fun _ ↦ le_rfl
  padRow := fun _ _ ↦ 0
  boundary := [constBlock .push, countPull, constBlock .pull]
  μ := 2
  layout := layout
  nLines := 0
  publicLines := fun _ ↦ #v[]
  flock := none

/-! ## Sizes and side conditions -/

#guard busToy.μBus = 2
#guard busToy.busClaims = 1
#guard busToy.τmax = 1
#guard leafCount busToy 0 = 4 ∧ leafCount busToy 1 = 4 ∧ leafCount busToy 2 = 2

/-- Four push leaves: `μ_bus = 2`. -/
theorem μBus_eq : busToy.μBus = 2 := by
  change Nat.clog 2 busToy.pushLeaves = 2
  rw [show busToy.pushLeaves = 2 ^ 2 by decide, Nat.clog_pow _ _ one_lt_two]

/-- A flush whose slot 0 is the zero polynomial meets the separator condition. -/
theorem separator_of_zero {I : M3Instance}
    (h0 : ∀ j (f : Fin (I.flushes j).length), (flushPolys j f)[0] = 0) :
    ∀ j (f : Fin (I.flushes j).length) (r r' : Fin (I.width j) → K),
      ((flushPolys j f)[0]).eval r = ((flushPolys j f)[0]).eval r' := fun j f r r' ↦ by
  rw [h0 j f, CMvPolynomial.eval_zero, CMvPolynomial.eval_zero]

/-- The side conditions hold. -/
theorem conditions : Conditions busToy where
  one_le_d := by decide
  constrained := fun j _ ↦ by rw [μBus_eq]; fin_cases j; decide
  pull_fits := by rw [μBus_eq]; decide
  count_fits := by rw [μBus_eq]; decide
  separator := separator_of_zero fun _ f ↦ by
    obtain ⟨_ | _, hf⟩ := f
    · show (LeanVMTests.Protocol.Bus.flush.2)[0] = 0
      simp [LeanVMTests.Protocol.Bus.flush]
    · simp at hf

/-! ## The tie order -/

/-- The kind of a block, for the guards. -/
def kind {I : M3Instance} : Source I → String
  | .boundary _ => "boundary"
  | .flush _ _ => "flush"
  | .count _ _ => "count"

-- The push side's two blocks have the same height; the boundary block stays first.
#guard (sorted busToy 0).map kind = ["boundary", "flush"]
#guard (List.finRange (blocks busToy 0).n).map (blocks busToy 0).offset = [0, 2]
#guard (sorted busToy 1).map kind = ["boundary", "boundary"]
#guard (sorted busToy 2).map kind = ["count"]

/-! ## The honest stack -/

/-- `a = [1, 1]`, `c = [x, x + 1]`. -/
def honest : Column 2 := ⟨#v[1, 1, K.ofBits 2, K.ofBits 3]⟩

#guard M3Holds busToy () honest
#guard busToy.PaddingHonest honest

/-- Challenges off the cube. -/
def α : Fin 4 → E := ![y, y + 1, y * y, y * y + y]
def β : E := y * y * y + 1
def ζ : Vector E busToy.μBus := Vector.ofFn fun i ↦ if i.val = 0 then y + 1 else y * y
def e0 : E := 0

/-- The three leaf stacks of the honest stack at the challenges. -/
def pushHonest : CMlPolynomialEval E busToy.μBus := pushLeaves busToy α β honest
def pullHonest : CMlPolynomialEval E busToy.μBus := pullLeaves busToy α β honest
def countHonest : CMlPolynomialEval E busToy.μBus := countLeaves busToy honest

-- The push and pull products agree, and the count product is nonzero.
#guard (∏ x : Fin (2 ^ busToy.μBus), pushHonest[x]) = ∏ x : Fin (2 ^ busToy.μBus), pullHonest[x]
#guard (∏ x : Fin (2 ^ busToy.μBus), countHonest[x]) ≠ e0

/-- The oracles holding a stack. -/
def oracles (q : Column 2) : ∀ i, TheOracle busToy i := fun _ ↦ q

-- The honest roots pass the check.
#guard decide ((rootsHonest busToy ((((), (α, β)), oracles honest), ())).2 ≠ 0)

/-! ## The leaves at a point -/

#guard ∀ k : Fin 3, evalMle (sideLeaves busToy k α β honest) ζ =
  (∑ b, (blocks busToy k).selectorWeight (conditions.fits k) b ζ *
    (src busToy k b).leafEval α β honest ((blocks busToy k).lowPoint (conditions.fits k) b ζ)) +
  (1 + ∑ b, (blocks busToy k).selectorWeight (conditions.fits k) b ζ)

/-! ## The last step -/

/-- The leaf claims, true at `ζ`. -/
def v (k : Fin 3) : E := evalMle (sideLeaves busToy k α β honest) ζ

/-- The grand-product argument's last statement. -/
def last : Gkr.LayerStmt (Data busToy) E 3 busToy.μBus := (((), (α, β)), (ζ, v))

/-- What the bus phase hands on with the honest values. -/
def out : BusOut busToy := busOut conditions last (honestValues conditions honest ζ)

-- Every side's forms sum to its total.
#guard ∀ k : Fin 3, ∑ j, M3Instance.Form.eval busToy (out.forms k j) honest
  (busToy.lowPoint out.point j) = out.totals k
-- The boundary claim, on the count column, holds.
#guard ∀ c ∈ out.columns.toList,
  eval₂Mle (busToy.column honest c.col).values (algebraMap K E) c.point = c.value
-- A wrong leaf claim breaks its side's equation.
#guard ∑ j, M3Instance.Form.eval busToy
  ((busOut conditions (((), (α, β)), (ζ, fun k ↦ v k + 1)) (honestValues conditions honest ζ)).forms
    0 j) honest (busToy.lowPoint out.point j) ≠
  (busOut conditions (((), (α, β)), (ζ, fun k ↦ v k + 1))
    (honestValues conditions honest ζ)).totals 0
-- The push side's form on the table: `β` against `1` and seventeen terms in all, the pull side's
-- none (its blocks are boundary blocks), the count side's one.
#guard ∀ j, (out.forms 0 j).length = 17 ∧ (out.forms 1 j).length = 0 ∧ (out.forms 2 j).length = 1

/-! ## The zero-count mutation: the check `R_c ≠ 0` is load-bearing -/

/-- A count cell `0`. -/
def zeroCount : Column 2 := ⟨#v[1, 1, K.ofBits 2, 0]⟩

-- The bus still balances, and the constraint still holds; only the counts fail.
#guard busToy.Balanced zeroCount ∧ busToy.ConstraintsVanish zeroCount ∧
  busToy.PaddingHonest zeroCount
#guard ¬ busToy.CountsNonzero zeroCount
/-- The three leaf stacks of the zero-count stack. -/
def pushZero : CMlPolynomialEval E busToy.μBus := pushLeaves busToy α β zeroCount
def pullZero : CMlPolynomialEval E busToy.μBus := pullLeaves busToy α β zeroCount
def countZero : CMlPolynomialEval E busToy.μBus := countLeaves busToy zeroCount

#guard (∏ x : Fin (2 ^ busToy.μBus), pushZero[x]) = ∏ x : Fin (2 ^ busToy.μBus), pullZero[x]
-- The count product is `0`, so the roots fail the check.
#guard (∏ x : Fin (2 ^ busToy.μBus), countZero[x]) = e0
#guard ¬ decide ((rootsHonest busToy ((((), (α, β)), oracles zeroCount), ())).2 ≠ 0)

/-- Without the check `R_c ≠ 0`, the roots step has no security from `afterChallenge` to the
grand-product argument's input relation, at any error and whatever the extractor: a stack whose
bus balances, whose constraints vanish and whose lines and Flock predicate hold, but with a zero
count, has no witness, and its honest roots land in the argument's input relation, its padding
rows honest. `zeroCount` is such a stack, by the guards above; the kernel cannot evaluate a
constraint polynomial or the bus's permutation on a concrete stack, so the facts are hypotheses
here. -/
theorem roots_unchecked_no_security {I : M3Instance} (h : Conditions I) (s : I.Stmt)
    (q : Column I.μ) (hb : I.Balanced q) (hc : I.ConstraintsVanish q)
    (hl : I.PublicLinesHold s q) (ha : I.aux q) (hpad : I.PaddingHonest q)
    (hz : ¬ I.CountsNonzero q) (α : Fin 4 → E)
    (β : E) {hp : (Data I × ∀ i, TheOracle I i) × Unit → E × E}
    {err : Typed.Errors (Typed.sayTree (E × E)) (Typed.sayRoles _)}
    (S : Typed.Security (Typed.sendChecked (TheOracle I) (E × E) hp (fun _ _ ↦ true)
      fun (x : Data I) (r : E × E) ↦ (x, ![r.1, r.1, r.2]))
      (afterChallenge I) (Gkr.relIn 3 I.μBus (leaves I) (riders I)) err) : False := by
  let o : ∀ i, TheOracle I i := fun _ ↦ q
  refine Typed.sendChecked_no_security S (s, (α, β)) o
    (fun _ hw ↦ hz (countsNonzero_of_prod h α β q hw.2.1))
    (rootsHonest I (((s, (α, β)), o), ())) rfl ()
    ⟨(ridersZero_iff h _ o).mpr ⟨hc, hl, ha⟩, fun t ↦ ?_⟩
  fin_cases t
  · rfl
  · change ∏ x : Fin (2 ^ I.μBus), (pushLeaves I α β q)[x] =
      ∏ x : Fin (2 ^ I.μBus), (pullLeaves I α β q)[x]
    rw [prod_pushLeaves, prod_pullLeaves h, padProduct_of_honest hpad, padProduct_of_honest hpad,
      Multiset.coe_eq_coe.mpr hb]
  · rfl

/-! ## The pad -/

-- The count side padded with `0` has product `0`: the honest roots would fail the check.
#guard (∏ x : Fin (2 ^ busToy.μBus),
  ((blocks busToy 2).stackAt (tables busToy 2 α β honest) busToy.μBus 0)[x]) = e0

/-! ## Completeness -/

example : Typed.Complete (busPhase busToy conditions) (Seam.commitHonest busToy)
    (Seam.bus busToy) :=
  busComplete busToy conditions

/-- The spine's toy has two push leaves: `μ_bus = 1`. -/
theorem toy_μBus_eq : Toy.toy.μBus = 1 := by
  change Nat.clog 2 Toy.toy.pushLeaves = 1
  rw [show Toy.toy.pushLeaves = 2 ^ 1 by decide, Nat.clog_pow _ _ one_lt_two]

/-- The spine's toy meets the side conditions: its flush's slot 0 is the constant `0`. -/
theorem toyConditions : Conditions Toy.toy where
  one_le_d := by decide
  constrained := fun _ _ ↦ by rw [toy_μBus_eq]
  pull_fits := by rw [toy_μBus_eq]; decide
  count_fits := by rw [toy_μBus_eq]; decide
  separator := separator_of_zero fun _ f ↦ by
    obtain ⟨_ | _, hf⟩ := f
    · show (Toy.flush.2)[0] = 0
      simp [Toy.flush]
    · simp at hf

/-- `1` in `E`. -/
def e1 : E := 1

-- The spine's toy has a public line, cell 0 the statement: its rider is `0` at the honest
-- statement `1` and `1` at the statement `0`, which its stack fails.
#guard (linesRider Toy.toy (1 : K) Toy.honest).2.toList = [e0]
#guard (linesRider Toy.toy (0 : K) Toy.honest).2.toList = [e1]

example : Typed.Complete (busPhase Toy.toy toyConditions) (Seam.commitHonest Toy.toy)
    (Seam.bus Toy.toy) :=
  busComplete Toy.toy toyConditions

end LeanVMTests.Protocol.Bus
