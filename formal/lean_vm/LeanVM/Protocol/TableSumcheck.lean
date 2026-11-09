/-
  LeanVM.Protocol.TableSumcheck

  The table sumcheck phase: the batching challenge `ξ`, one plain sumcheck over the rows of the
  sumcheck tables, and the values of their columns at the final point. Definition, perfect
  completeness and round-by-round knowledge soundness.
-/

module

public import LeanVM.Protocol.Spine.Errors
public import LeanVM.Protocol.ToArkLib.Typed.Batch
public import LeanVM.Protocol.Spine.Slots
public import LeanVM.Protocol.ToArkLib.Sumcheck
import CompPoly.Multivariate.MvPolyEquiv.Eval
import Mathlib.Algebra.BigOperators.Fin

/-!
# The table sumcheck phase

Specification §5.5 (`doc/leanvm/body/05-arithmetization.tex:125-150` at leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`), over an abstract instance `I`.

The bus phase ends at a point `ζ` and leaves two kinds of claim on the rows of the *sumcheck
tables* (those with a constraint, a flush or a count column): every constraint `C_{t,i}` of table
`t` has extension zero at `ζ_{<τ_t}`, and for each side `s` of the bus the forms `B^s_t` of the
tables sum to the side's total at `ζ` (`Seam.bus`). Each is a sum over one table's rows weighted
by `eq(ζ_{<τ_t}, ·)` of a polynomial of degree at most `d` in the table's columns, and one
sumcheck proves them all:

1. the verifier draws `ξ` and batches the claims by its powers (`batchStep`, `Typed.batch`):
   constraint `i` of table `t` gets `ξ^{o_t + i}`, with the constraints numbered table by table
   (`constraintPos`), and side `s` gets `ξ^{B + s}`, the three powers shared by the tables, so the
   target `Σ_s ξ^{B+s} · total_s` is derived by the verifier and never sent;
2. a plain sumcheck of degree three on `τ_max` variables, highest first, of the virtual polynomial
   `tableSummand`: its tables are the sumcheck tables' columns, each read on `τ_max` variables as
   the same in every slice of the coordinates its table does not have (`table`), and its formula
   is §5.5's `F`, `Σ_t eq(ζ_{<τ_t}, X_{<τ_t}) · ∏_{k ≥ τ_t} X_k · (Σ_i ξ^{o_t+i} C_{t,i} +
   Σ_s ξ^{B+s} B^s_t)` at the tables' values (`formula`), the factor of table `t` the
   multilinear weight of its coordinates (`tableWeights`), `eq` below `τ_t` and the padding
   `X_k` above, so that table `t` joins at round `τ_max − τ_t`;
3. the prover sends one value per column of each sumcheck table, table by table (`columnPos`);
   the verifier checks the formula at the final point against the running claim, and hands on
   the bus phase's column claims followed by one claim per column at the final point's low
   coordinates (`tableOut`).

The sum of the summand over the cube is the batch of the true values, each constraint's extension
at `ζ` and each side's forms summed (`sum_tableSummand`), so it is the target exactly when the bus
seam's two claims hold (`tableSummand_target`). In characteristic two the factor
`(1 − r)(1 − ζ) + rζ` of `eq` is the deployed `1 + ζ + r`.

Perfect completeness (`tableSumcheckComplete`), from `Seam.bus` to `Seam.table`, needs the
degree bound `d ≤ 2`: the slot's rounds are cubic, and the summand has degree `d + 1` in each
variable (`tableSummand_degree`). The bus phase's column claims, the public lines and the Keccak
predicate ride through the sumcheck as its side condition (`side`), and the Keccak predicate holds
along every point (`M3Instance.auxAt_of_aux`), so at the final one.

Round-by-round knowledge soundness (`tableSumcheckSecurity`), between the same seams and under the
same bound, is at the slot's error: `(B + 2)/|E|` on `ξ`, since a false claim among the `B + 3`
batched survives only at a root of a nonzero polynomial of degree at most `B + 2` in `ξ`, the
true values being fixed before it (`trueValues`); `3/|E|` on each round's challenge; nothing on
the final values, which the table seam determines (`finalClaims_holds_iff`). The Keccak predicate
is not checked by any challenge of its own: the table seam asks it at the final point
(`M3Instance.auxAt`), and the rounds carry it as an invariant along the challenges
(`inv`, `M3Instance.auxStage`), the zero test of `Spine/KeccakZero.lean` with the high coordinates
bound first, as the rounds draw them. A round that restores a broken invariant does so at one
challenge at most (`inv_sound`), within the round's own `3/|E|`: a candidate alive after the round
had a true claim and a true invariant before it, or a challenge among the round polynomial's three
agreements with the honest one or the zero test's one root.

Written from the specification; the order of the powers, the shared side powers, the weights and
the order of the final values are checked against `crates/leanvm_core/src/cpu/mod.rs:388-406`,
`crates/verifier/src/lib.rs:231-249` and `crates/verifier/src/bus.rs:211-260` at the pin.
-/

namespace LeanVM.Protocol

open LeanVM.Parameters CompPoly CPoly CMlPolynomialEval OracleComp OracleSpec
open scoped NNReal

@[expose] public section

namespace TableSumcheck

variable (I : M3Instance)

/-! ## Positions, table by table -/

/-- A family of sizes over the tables, kept on the sumcheck tables and zero on the others. -/
def onSumcheck (f : Fin I.ntab → ℕ) (j : Fin I.ntab) : ℕ := if I.SumcheckTable j then f j else 0

/-- Summing the kept sizes over every table is summing the sizes over the sumcheck tables. -/
theorem sum_onSumcheck (f : Fin I.ntab → ℕ) :
    ∑ j, onSumcheck I f j = ∑ j : I.SumcheckTables, f j.1 := by
  simp only [onSumcheck]
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (fun j ↦ by simp) f

variable {I} in
/-- A position below a kept size is on a sumcheck table. -/
theorem sumcheckTable_of_lt {f : Fin I.ntab → ℕ} {j : Fin I.ntab} {i : ℕ}
    (hi : i < onSumcheck I f j) : I.SumcheckTable j := by
  by_contra h
  simp [onSumcheck, h] at hi

/-- The items of a family over the sumcheck tables are the items over every table of the kept
sizes. -/
def sigmaOnSumcheck (f : Fin I.ntab → ℕ) :
    (Σ j : I.SumcheckTables, Fin (f j.1)) ≃ Σ j : Fin I.ntab, Fin (onSumcheck I f j) where
  toFun p := ⟨p.1.1, Fin.cast (by simp [onSumcheck, p.1.2]) p.2⟩
  invFun p := ⟨⟨p.1, sumcheckTable_of_lt p.2.isLt⟩,
    Fin.cast (by simp [onSumcheck, sumcheckTable_of_lt p.2.isLt]) p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The position of each item of a family over the sumcheck tables, numbered table by table:
item `i` of table `t` is at `i` plus the sizes of the sumcheck tables before `t`
(`position_val`). -/
def position (f : Fin I.ntab → ℕ) :
    (Σ j : I.SumcheckTables, Fin (f j.1)) ≃ Fin (∑ j : I.SumcheckTables, f j.1) :=
  (sigmaOnSumcheck I f).trans (finSigmaFinEquiv.trans (finCongr (sum_onSumcheck I f)))

/-- Item `i` of table `t` is at `i` plus the sizes of the sumcheck tables before `t`. -/
theorem position_val (f : Fin I.ntab → ℕ) (p : Σ j : I.SumcheckTables, Fin (f j.1)) :
    (position I f p : ℕ) =
      ∑ j : Fin p.1.1.val, onSumcheck I f (Fin.castLE p.1.1.isLt.le j) + p.2 := by
  simp [position, sigmaOnSumcheck]

/-- The constraints of the sumcheck tables, table by table: the powers of `ξ` they take. -/
abbrev constraintPos :
    (Σ t : I.SumcheckTables, Fin (I.constraints t.1).length) ≃ Fin I.B :=
  position I fun j ↦ (I.constraints j).length

/-- The columns of the sumcheck tables, table by table: the order of the final values. -/
abbrev columnPos : (Σ t : I.SumcheckTables, Fin (I.width t.1)) ≃ Fin I.tableColumns :=
  position I I.width

/-! ## The virtual polynomial -/

/-- The public data of the sumcheck: the statement, the bus phase's output, and `ξ`. -/
abbrev Data : Type := (I.Stmt × BusOut I) × E

/-- Column `k` of the sumcheck tables, table by table, lifted to `E` and read on the sumcheck's
`τ_max` variables: the same in every slice of the coordinates its table does not have. -/
def table (q : Column I.μ) (k : Fin I.tableColumns) : CMlPolynomialEval E I.τmax :=
  repeatHigh (CMlPolynomialEval.map (algebraMap K E)
    (I.column q ⟨((columnPos I).symm k).1.1, ((columnPos I).symm k).2⟩).values)
    (I.τ_le_τmax ((columnPos I).symm k).1)

/-- The values of table `t`'s columns among the values of all the columns. -/
def tableValues (v : Vector E I.tableColumns) (t : I.SumcheckTables) : Fin (I.width t.1) → E :=
  fun i ↦ v[columnPos I ⟨t, i⟩]

variable {I} in
/-- A row polynomial at values in `E` of its table's columns. -/
def evalRow {j : Fin I.ntab} (P : CMvPolynomial (I.width j) K) (e : Fin (I.width j) → E) : E :=
  P.eval₂ (algebraMap K E) e

variable {I} in
/-- A form at values in `E` of its table's columns. -/
def formAt {j : Fin I.ntab} (f : I.Form j) (e : Fin (I.width j) → E) : E :=
  (f.map fun p ↦ p.1 * evalRow p.2.1 e).sum

/-- What table `t` owes at values `e` of its columns: constraint `i` weighted by `ξ` to its
position, and the form of side `s` weighted by `ξ^(B + s)`. -/
def rowValue (x : Data I) (t : I.SumcheckTables) (e : Fin (I.width t.1) → E) : E :=
  (∑ i : Fin (I.constraints t.1).length,
    x.2 ^ (constraintPos I ⟨t, i⟩ : ℕ) * evalRow (I.constraints t.1)[i] e) +
  ∑ s : Fin 3, x.2 ^ (I.B + s.val) * formAt (x.1.2.forms s t) e

/-- The weights of table `t`'s coordinates in the sumcheck: those of `eq(ζ_b, ·)` below its
log-height, and the padding's, `(0, 1)`, above it. -/
def tableWeights (ζ : Vector E I.τmax) (t : I.SumcheckTables) : Fin I.τmax → E × E :=
  fun b ↦ if b.val < I.τ t.1 then (1 - ζ[b], ζ[b]) else (0, 1)

/-- The formula of the table sumcheck, §5.5's `F` at a point and at the columns' values there:
table by table, the multilinear weight of its coordinates times what it owes. -/
def formula (x : Data I) (z : Vector E I.τmax) (v : Vector E I.tableColumns) : E :=
  ∑ t : I.SumcheckTables,
    prodWeight (tableWeights I x.1.2.point t) z * rowValue I x t (tableValues I v t)

/-- The virtual polynomial of the table sumcheck: the sumcheck tables' columns and the formula. -/
def tableSummand : Sumcheck.Virtual E (Data I) (TheOracle I) Unit I.τmax I.tableColumns where
  tables := fun ctx ↦ table I (theStack ctx.1.2)
  formula := formula I

/-! ## The phase -/

/-- The claimed values of the batch: zero for each constraint, then the three sides' totals. -/
def claimed (s : I.Stmt × BusOut I) : Fin (I.B + 3) → E := Fin.append (fun _ ↦ 0) s.2.totals

/-- The sumcheck's first statement: the data with `ξ`, no challenge yet, and the claim. -/
def start (s : I.Stmt × BusOut I) (ξ c : E) : SumcheckRound.Stmt (Data I) E 0 :=
  ((s, ξ), (#v[], c))

/-- The batching challenge `ξ`, as a typed component. -/
def batchStep : Typed.Def (TheOracle I) (I.Stmt × BusOut I) Unit
    (SumcheckRound.Stmt (Data I) E 0) Unit (Typed.drawSlot E) :=
  Typed.batch (TheOracle I) E (claimed I) (start I)

/-- Four distinct points of `E`, at which the honest prover interpolates its cubic round
polynomials. -/
def nodes : Fin 4 → E := ![0, 1, y, y + 1]

/-- The final claim on column `k` of the sumcheck tables: its value at the final point's low
coordinates is value `k`. -/
def finalClaim (r : Vector E I.τmax) (v : Vector E I.tableColumns) (k : Fin I.tableColumns) :
    ColumnClaim I :=
  ⟨⟨((columnPos I).symm k).1.1, ((columnPos I).symm k).2⟩, I.lowPoint r ((columnPos I).symm k).1,
    v[k]⟩

/-- The final claims: one per column of each sumcheck table, table by table. -/
def finalClaims (r : Vector E I.τmax) (v : Vector E I.tableColumns) :
    Vector (ColumnClaim I) I.tableColumns :=
  Vector.ofFn (finalClaim I r v)

/-- The phase's output: the bus phase's column claims carried forward, then the final claims at
the final point in coordinate order. -/
def tableOut (s : SumcheckRound.Stmt (Data I) E I.τmax) (v : Vector E I.tableColumns) :
    I.Stmt × TableOut I :=
  (s.1.1.1, ⟨s.1.1.2.columns ++ finalClaims I s.2.1.reverse v, s.2.1.reverse⟩)

/-! ## The columns -/

/-- Column `k`'s table at a point is its column's extension at the point's low coordinates. -/
private theorem evalMle_table (q : Column I.μ) (k : Fin I.tableColumns) (z : Vector E I.τmax) :
    evalMle (table I q k) z =
      eval₂Mle (I.column q ⟨((columnPos I).symm k).1.1, ((columnPos I).symm k).2⟩).values
        (algebraMap K E) (I.lowPoint z ((columnPos I).symm k).1) :=
  evalMle_repeatHigh _ _ z

/-- The values at a point of table `t`'s columns are their extensions at the point's low
coordinates. -/
private theorem tableValues_values (ctx : SumcheckRound.Ctx (Data I) (TheOracle I) Unit)
    (z : Vector E I.τmax) (t : I.SumcheckTables) (i : Fin (I.width t.1)) :
    tableValues I ((tableSummand I).values ctx z) t i =
      eval₂Mle (I.column (theStack ctx.1.2) ⟨t.1, i⟩).values (algebraMap K E) (I.lowPoint z t) := by
  simp only [tableValues, Sumcheck.Virtual.values, Fin.getElem_fin, Vector.getElem_ofFn,
    tableSummand]
  rw [evalMle_table, Equiv.symm_apply_apply]

/-! ## The sum over the cube -/

/-- Constraint `p` of its table: its extension at the bus point's low coordinates. -/
def constraintValue (s : I.Stmt × BusOut I) (q : Column I.μ)
    (p : Σ t : I.SumcheckTables, Fin (I.constraints t.1).length) : E :=
  evalMle (I.virtualTable q p.1.1 (I.constraints p.1.1)[p.2]) (I.lowPoint s.2.point p.1)

/-- A side's forms at the bus point, summed over the sumcheck tables. -/
def formTotal (s : I.Stmt × BusOut I) (q : Column I.μ) (side : Fin 3) : E :=
  ∑ t, M3Instance.Form.eval I (s.2.forms side t) q (I.lowPoint s.2.point t)

/-- The true values of the batched claims: each constraint's extension at the bus point, table by
table, then each side's forms summed. -/
def trueValues (s : I.Stmt × BusOut I) (q : Column I.μ) : Fin (I.B + 3) → E :=
  Fin.append (fun k ↦ constraintValue I s q ((constraintPos I).symm k)) (formTotal I s q)

variable {I} in
/-- A row polynomial at the lift of values in `K` is the lift of its value. -/
theorem evalRow_ofK {j : Fin I.ntab} (P : CMvPolynomial (I.width j) K)
    (r : Fin (I.width j) → K) : evalRow P (fun i ↦ ofK (r i)) = ofK (P.eval r) := by
  rw [evalRow, CPoly.eval₂_equiv, CMvPolynomial.eval, CPoly.eval₂_equiv]
  show _ = algebraMap K E _
  rw [MvPolynomial.eval₂_comp_left, RingHom.comp_id]
  rfl

/-- A virtual table's extension is the sum of its rows against the Lagrange basis. -/
private theorem evalMle_virtualTable (q : Column I.μ) (j : Fin I.ntab)
    (P : CMvPolynomial (I.width j) K) (z : Vector E (I.τ j)) :
    evalMle (I.virtualTable q j P) z = ∑ x, (lagrangeBasis z)[x] * ofK (P.eval (I.row q j x)) := by
  rw [evalMle_eq_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  simp [M3Instance.virtualTable, mul_comm]

/-- A form's value at the rows, summed against the Lagrange basis, is the form's value. -/
private theorem sum_formAt (q : Column I.μ) (j : Fin I.ntab) (f : I.Form j) (z : Vector E (I.τ j)) :
    ∑ x, (lagrangeBasis z)[x] * formAt f (fun i ↦ ofK (I.row q j x i)) =
      M3Instance.Form.eval I f q z := by
  induction f with
  | nil => simp [formAt, M3Instance.Form.eval]
  | cons p f ih =>
    simp only [formAt, M3Instance.Form.eval, List.map_cons, List.sum_cons] at ih ⊢
    rw [← ih, evalMle_virtualTable, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [evalRow_ofK]
    ring

/-- Table `t`'s share of the sum over the cube: its constraints' extensions and its forms at the
bus point, by their powers of `ξ`. The padding coordinates keep only their value `1`, and the
coordinates below `τ_t` weigh the rows by `eq(ζ_{<τ_t}, ·)`. -/
private theorem weightedCubeSum_table (x : Data I) (o : ∀ i, TheOracle I i) (t : I.SumcheckTables) :
    weightedCubeSum (fun _ ↦ ((1 : E), (1 : E))) (fun z ↦
        prodWeight (tableWeights I x.1.2.point t) z *
          rowValue I x t (tableValues I ((tableSummand I).values ((x, o), ()) z) t)) =
      (∑ i, x.2 ^ (constraintPos I ⟨t, i⟩ : ℕ) * constraintValue I x.1 (theStack o) ⟨t, i⟩) +
        ∑ s : Fin 3, x.2 ^ (I.B + s.val) *
          M3Instance.Form.eval I (x.1.2.forms s t) (theStack o) (I.lowPoint x.1.2.point t) := by
  rw [weightedCubeSum_one_prodWeight]
  have hv : (fun z ↦ rowValue I x t (tableValues I ((tableSummand I).values ((x, o), ()) z) t)) =
      fun z ↦ (fun y ↦ rowValue I x t fun i ↦
        eval₂Mle (I.column (theStack o) ⟨t.1, i⟩).values (algebraMap K E) y)
          (lowCoords (I.τ_le_τmax t) z) := by
    funext z
    congr 1
    funext i
    exact tableValues_values I _ z t i
  rw [hv, weightedCubeSum_lowCoords (I.τ_le_τmax t) _
    (fun b hb ↦ by simp [tableWeights, not_lt.mpr hb]) (fun y ↦ rowValue I x t fun i ↦
      eval₂Mle (I.column (theStack o) ⟨t.1, i⟩).values (algebraMap K E) y)]
  have hw : (fun a : Fin (I.τ t.1) ↦ tableWeights I x.1.2.point t (Fin.castLE (I.τ_le_τmax t) a)) =
      fun a : Fin (I.τ t.1) ↦
        (1 - (I.lowPoint x.1.2.point t)[a], (I.lowPoint x.1.2.point t)[a]) := by
    funext a
    have h : (I.lowPoint x.1.2.point t)[a] = x.1.2.point[a.val]'(a.isLt.trans_le (I.τ_le_τmax t)) :=
      getElem_lowCoords (I.τ_le_τmax t) _ a.isLt
    simp only [tableWeights, Fin.val_castLE, a.isLt, ite_true, Fin.getElem_fin, h]
  rw [hw, weightedCubeSum_eq]
  have hrow : ∀ (y : Fin (2 ^ I.τ t.1)) (i : Fin (I.width t.1)),
      eval₂Mle (I.column (theStack o) ⟨t.1, i⟩).values (algebraMap K E) (boolVec y) =
        ofK (I.row (theStack o) t.1 y i) := fun y i ↦ by
    rw [eval₂Mle, evalMle_boolVec]
    simp [CMlPolynomialEval.map, M3Instance.row, Vector.get_eq_getElem]
  simp only [hrow, rowValue, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [constraintValue, evalMle_virtualTable, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    rw [evalRow_ofK]
    ring
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [← sum_formAt I (theStack o) t.1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    ring

/-- The batch of a family of values with the three side values after the constraints' is the
constraints' part by their powers plus the sides' by `ξ^(B + s)`. -/
private theorem powerBatch_append (A : Fin I.B → E) (S : Fin 3 → E) (ξ : E) :
    powerBatch (Fin.append A S) ξ =
      (∑ k, A k * ξ ^ (k : ℕ)) + ∑ s : Fin 3, S s * ξ ^ (I.B + s.val) := by
  simp [powerBatch, Fin.sum_univ_add]

/-- **The sum of the table sumcheck's summand over the cube** is the true values batched by the
powers of `ξ`: each constraint's extension at the bus point by its power, each side's forms
summed by the side's. -/
theorem sum_tableSummand (x : Data I) (o : ∀ i, TheOracle I i) :
    Sumcheck.weightedSum (tableSummand I) Sumcheck.unitWeights ((x, o), ()) =
      powerBatch (trueValues I x.1 (theStack o)) x.2 := by
  have h : Sumcheck.weightedSum (tableSummand I) Sumcheck.unitWeights ((x, o), ()) =
      weightedCubeSum (fun _ ↦ ((1 : E), (1 : E))) fun z ↦ ∑ t : I.SumcheckTables,
        prodWeight (tableWeights I x.1.2.point t) z *
          rowValue I x t (tableValues I ((tableSummand I).values ((x, o), ()) z) t) := rfl
  rw [h, weightedCubeSum_finsetSum]
  simp only [weightedCubeSum_table]
  rw [trueValues, powerBatch_append, Finset.sum_add_distrib]
  congr 1
  · rw [← (constraintPos I).sum_comp, Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun t _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Equiv.symm_apply_apply, mul_comm]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [formTotal, Finset.sum_mul]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [mul_comm]

/-- The true values are the claimed ones exactly when the bus seam's two claims hold: every
constraint's extension is zero at the bus point, and each side's forms sum to its total. -/
theorem trueValues_eq_claimed_iff (s : I.Stmt × BusOut I) (q : Column I.μ) :
    trueValues I s q = claimed I s ↔
      (∀ j : I.SumcheckTables, ∀ C ∈ I.constraints j.1,
        evalMle (I.virtualTable q j.1 C) (I.lowPoint s.2.point j) = 0) ∧
      ∀ side, ∑ j : I.SumcheckTables,
        M3Instance.Form.eval I (s.2.forms side j) q (I.lowPoint s.2.point j) = s.2.totals side := by
  constructor
  · intro h
    refine ⟨fun j C hC ↦ ?_, fun side ↦ ?_⟩
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hC
      have := congrFun h (Fin.castAdd 3 (constraintPos I ⟨j, ⟨i, hi⟩⟩))
      simp only [trueValues, claimed, Fin.append_left] at this
      rw [Equiv.symm_apply_apply] at this
      exact this
    · have := congrFun h (Fin.natAdd I.B side)
      simpa [trueValues, claimed, formTotal] using this
  · rintro ⟨hc, hf⟩
    funext k
    cases k using Fin.addCases with
    | left k =>
      simp only [trueValues, claimed, Fin.append_left, constraintValue]
      exact hc _ _ (List.getElem_mem _)
    | right side =>
      simp only [trueValues, claimed, Fin.append_right]
      exact hf side

/-! ## The degree -/

/-- A form at values of degree at most one in a coordinate has degree at most `2` there, when
the instance's degree bound is. -/
private theorem degreeLEAt_formAt (hd : I.d ≤ 2) {j : Fin I.ntab} (f : I.Form j) {k : ℕ}
    {e : Fin (I.width j) → Vector E I.τmax → E} (he : ∀ i, DegreeLEAt (e i) k 1) :
    DegreeLEAt (fun z ↦ formAt f fun i ↦ e i z) k 2 := by
  induction f with
  | nil => simpa [formAt] using (DegreeLEAt.const (0 : E)).mono (Nat.zero_le 2)
  | cons p f ih =>
    simp only [formAt, List.map_cons, List.sum_cons] at ih ⊢
    exact (((DegreeLEAt.const p.1).mul
      (DegreeLEAt.cmvPolynomial_eval₂ (algebraMap K E) p.2.1 (p.2.2.trans hd) he)).mono
        (by omega)).add ih

/-- The summand has degree at most `3` in each variable when the instance's degree bound is at
most `2`: the weight of a table's coordinates has degree one in each, and what the table owes
is a polynomial of degree at most `d` in its columns' extensions, each of degree one. -/
theorem tableSummand_degree (hd : I.d ≤ 2) (ctx : SumcheckRound.Ctx (Data I) (TheOracle I) Unit) :
    IndividualDegreeLE ((tableSummand I).summand ctx) 3 := by
  intro k
  have hval : ∀ (t : I.SumcheckTables) (i : Fin (I.width t.1)),
      DegreeLEAt (fun z ↦ tableValues I ((tableSummand I).values ctx z) t i) k 1 := fun t i ↦ by
    have e : (fun z ↦ tableValues I ((tableSummand I).values ctx z) t i) =
        fun z ↦ evalMle ((tableSummand I).tables ctx (columnPos I ⟨t, i⟩)) z := by
      funext z
      simp [tableValues, Sumcheck.Virtual.values]
    rw [e]
    exact DegreeLEAt.evalMle _
  have hrow : ∀ t : I.SumcheckTables, DegreeLEAt
      (fun z ↦ rowValue I ctx.1.1 t (tableValues I ((tableSummand I).values ctx z) t)) k 2 :=
    fun t ↦ (DegreeLEAt.sum _ fun i _ ↦ ((DegreeLEAt.const _).mul
      (DegreeLEAt.cmvPolynomial_eval₂ (algebraMap K E) _
        ((I.constraints_degree t.1 _ (List.getElem_mem _)).trans hd) (hval t))).mono
          (by omega)).add
      (DegreeLEAt.sum _ fun s _ ↦ ((DegreeLEAt.const _).mul
        (degreeLEAt_formAt I hd _ (hval t))).mono (by omega))
  show DegreeLEAt (fun z ↦ ∑ t : I.SumcheckTables,
    prodWeight (tableWeights I ctx.1.1.1.2.point t) z *
      rowValue I ctx.1.1 t (tableValues I ((tableSummand I).values ctx z) t)) k (1 + 2)
  exact DegreeLEAt.sum _ fun t _ ↦ (DegreeLEAt.prodWeight _).mul (hrow t)

/-! ## Completeness -/

/-- The nodes are distinct. -/
theorem nodes_injective : Function.Injective nodes := by
  have y0 : y ≠ 0 := fun h ↦ by
    have h3 := y_pow_three
    rw [h] at h3
    simp at h3
  have y1 : y ≠ 1 := fun h ↦ by
    have h3 := y_pow_three
    rw [h] at h3
    simp at h3
  have y10 : y + 1 ≠ 0 := fun h ↦ by
    have h3 := y_pow_three
    rw [h] at h3
    exact y0 (pow_eq_zero_iff (by norm_num) |>.mp h3)
  have y11 : y + 1 ≠ 1 := fun h ↦ y0 (add_eq_right.mp h)
  have y1y : y + 1 ≠ y := fun h ↦ one_ne_zero (add_eq_left.mp h)
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [nodes, y0.symm, y1.symm, y10.symm, y11.symm, y1y.symm]

/-- What the sumcheck carries unchanged: the bus phase's column claims and the public lines. -/
def sideRest (ctx : SumcheckRound.Ctx (Data I) (TheOracle I) Unit) : Prop :=
  (∀ c ∈ ctx.1.1.1.2.columns.toList, c.Holds (theStack ctx.1.2)) ∧
    I.PublicLinesHold ctx.1.1.1.1 (theStack ctx.1.2)

/-- What the sumcheck's completeness carries unchanged: the bus phase's column claims, the public
lines and the Keccak predicate. -/
def side (ctx : SumcheckRound.Ctx (Data I) (TheOracle I) Unit) : Prop :=
  (∀ c ∈ ctx.1.1.1.2.columns.toList, c.Holds (theStack ctx.1.2)) ∧
    I.PublicLinesHold ctx.1.1.1.1 (theStack ctx.1.2) ∧ I.aux (theStack ctx.1.2)

/-- The rounds' invariant for soundness: the bus phase's column claims and the public lines,
unchanged, and the Keccak predicate along the challenges drawn so far
(`M3Instance.auxStage`), which each challenge may break or restore. -/
def inv (ctx : SumcheckRound.Ctx (Data I) (TheOracle I) Unit) (j : ℕ) (c : Vector E j) : Prop :=
  sideRest I ctx ∧ I.auxStage c.toList (theStack ctx.1.2)

/-- Before the first challenge, the invariant is the side condition. -/
theorem inv_zero (ctx : SumcheckRound.Ctx (Data I) (TheOracle I) Unit) :
    inv I ctx 0 #v[] ↔ side I ctx := by
  simp only [inv, sideRest, side, Vector.toList_mk, M3Instance.auxStage_nil, and_assoc]

/-- **A round restores a broken invariant at one challenge at most**: the bus claims and the
public lines do not move, and the Keccak predicate's zero test escapes at one value at most
(`M3Instance.card_auxStage_push_le`). -/
theorem inv_sound (ctx : SumcheckRound.Ctx (Data I) (TheOracle I) Unit) (j : ℕ) (c : Vector E j)
    (hj : j < I.τmax) (hne : ¬ inv I ctx j c) :
    Nat.card {x // inv I ctx (j + 1) (c.push x)} ≤ 3 := by
  by_cases hr : sideRest I ctx
  · have ha : ¬ I.auxStage c.toList (theStack ctx.1.2) := fun ha ↦ hne ⟨hr, ha⟩
    refine le_trans ?_ ((I.card_auxStage_push_le (theStack ctx.1.2)
      (by simpa using hj) ha).trans (by norm_num))
    have := Fintype.ofFinite E
    exact Nat.card_mono (Set.toFinite _) fun x hx ↦ by
      have h2 := hx.2
      rwa [Vector.toList_push] at h2
  · have : IsEmpty {x // inv I ctx (j + 1) (c.push x)} := ⟨fun x ↦ hr x.2.1⟩
    rw [Nat.card_of_isEmpty]
    exact Nat.zero_le _

/-- The final claims hold of the stack exactly when the values sent are the columns' extensions
at the final point. -/
theorem finalClaims_holds_iff (ctx : SumcheckRound.Ctx (Data I) (TheOracle I) Unit)
    (r : Vector E I.τmax) (v : Vector E I.tableColumns) :
    (∀ c ∈ (finalClaims I r v).toList, c.Holds (theStack ctx.1.2)) ↔
      (tableSummand I).values ctx r = v := by
  have hk : ∀ k : Fin I.tableColumns, (finalClaims I r v)[k].Holds (theStack ctx.1.2) ↔
      ((tableSummand I).values ctx r)[k] = v[k] := fun k ↦ by
    simp only [finalClaims, Fin.getElem_fin, Vector.getElem_ofFn, Sumcheck.Virtual.values,
      tableSummand]
    rw [evalMle_table]
    rfl
  constructor
  · intro h
    apply Vector.ext
    intro k hk'
    exact (hk ⟨k, hk'⟩).mp (h _ (Vector.mem_toList_iff.mpr (Vector.getElem_mem hk')))
  · rintro hv c hc
    obtain ⟨k, hk', rfl⟩ := Vector.getElem_of_mem (Vector.mem_toList_iff.mp hc)
    exact (hk ⟨k, hk'⟩).mpr (by rw [hv])

/-- The true values at the final point land in the table seam whenever the side condition holds:
the bus phase's claims carried forward hold, and so do the final claims. -/
theorem tableOut_mem_table (s : SumcheckRound.Stmt (Data I) E I.τmax) (o : ∀ i, TheOracle I i)
    (hside : side I ((s.1, o), ())) :
    ((tableOut I s ((tableSummand I).values ((s.1, o), ()) s.2.1.reverse), o), ()) ∈
      Seam.table I := by
  refine ⟨fun c hc ↦ ?_, hside.2.1, I.auxAt_of_aux hside.2.2 _⟩
  simp only [tableOut, Vector.toList_append, List.mem_append] at hc
  rcases hc with hc | hc
  · exact hside.1 c hc
  · exact (finalClaims_holds_iff I ((s.1, o), ()) _ _).mpr rfl c hc

/-! ## The phase -/

/-- From the bus seam, the combined claimed values are the combination of the true ones at every
challenge, and the side condition holds. -/
theorem batch_complete (s : I.Stmt × BusOut I) (o : ∀ i, TheOracle I i) (w : Unit)
    (hin : ((s, o), w) ∈ Seam.bus I) (ρ : E) :
    ((start I s ρ (powerBatch (claimed I s) ρ), o), w) ∈
      Sumcheck.relIn (tableSummand I) Sumcheck.unitWeights (side I) := by
  cases w
  simp only [Seam.bus, Seam.of, Set.mem_ofPred_eq] at hin
  refine ⟨?_, hin.2.2⟩
  show powerBatch (claimed I s) ρ = Sumcheck.weightedSum _ _ (((s, ρ), o), ())
  rw [sum_tableSummand, (trueValues_eq_claimed_iff I s (theStack o)).mpr ⟨hin.1, hin.2.1⟩]

/-- The batching challenge's hypothesis: the true values, fixed before the challenge, are what a
challenge carrying a statement outside the bus seam into the rounds' input relation makes the
combined claim the combination of, and they differ from the claimed values. -/
theorem xi_batch (s : I.Stmt × BusOut I) (o : ∀ i, TheOracle I i) :
    ∃ a : Fin (I.B + 3) → E, ∀ w ρ, ((s, o), w) ∉ Seam.bus I →
      ((start I s ρ (powerBatch (claimed I s) ρ), o), w) ∈
        Sumcheck.relIn (tableSummand I) Sumcheck.unitWeights (side I) →
        a ≠ claimed I s ∧ powerBatch (claimed I s) ρ = powerBatch a ρ :=
  ⟨trueValues I s (theStack o), fun w ρ hin hout ↦ by
    cases w
    obtain ⟨hsum, hside⟩ := hout
    have hsum : powerBatch (claimed I s) ρ = powerBatch (trueValues I s (theStack o)) ρ :=
      hsum.trans (sum_tableSummand I (s, ρ) o)
    refine ⟨fun heq ↦ hin ?_, hsum⟩
    obtain ⟨hzero, htotals⟩ := (trueValues_eq_claimed_iff I s (theStack o)).mp heq
    exact ⟨hzero, htotals, hside⟩⟩

/-- Values whose output is in the table seam are the tables' values at the final point, and the
invariant holds at the challenges. -/
theorem finalValues_reflect (s : SumcheckRound.Stmt (Data I) E I.τmax) (o : ∀ i, TheOracle I i)
    (w : Unit) (v : Vector E I.tableColumns) (h : ((tableOut I s v, o), w) ∈ Seam.table I) :
    (tableSummand I).values ((s.1, o), w) s.2.1.reverse = v ∧ inv I ((s.1, o), w) I.τmax s.2.1 := by
  cases w
  obtain ⟨hcols, hlines, haux⟩ := h
  simp only [tableOut, Vector.toList_append, List.mem_append] at hcols
  refine ⟨(finalClaims_holds_iff I ((s.1, o), ()) _ v).mp fun c hc ↦ hcols c (Or.inr hc),
    ⟨fun c hc ↦ hcols c (Or.inl hc), hlines⟩, ?_⟩
  rw [I.auxStage_full _ (by simp)]
  simpa [tableOut, Vector.toList_reverse] using haux

/-- The table sumcheck phase on the typed framework, at its slot `tableSlot I`: the batching
challenge, the rounds of the plain sumcheck, and the final values. -/
def tableSumcheck : Typed.Def (TheOracle I) (I.Stmt × BusOut I) Unit (I.Stmt × TableOut I) Unit
    (tableSlot I) :=
  ((batchStep I).append (Sumcheck.rounds (tableSummand I) Sumcheck.unitWeights nodes)).append
    (Sumcheck.final (tableSummand I) (tableOut I))

/-- **Completeness on the typed framework.** -/
theorem tableSumcheckComplete (hd : I.d ≤ 2) :
    Typed.Complete (tableSumcheck I) (Seam.bus I) (Seam.table I) :=
  ((Typed.batchComplete (batch_complete I)).append
    (Sumcheck.roundsComplete (tableSummand I) Sumcheck.unitWeights nodes (side I)
      (tableSummand_degree I hd) nodes_injective)).append
    (Sumcheck.finalComplete (tableSummand I) Sumcheck.unitWeights nodes (side I) (tableOut I)
      fun s o w hside ↦ by
        cases w
        exact tableOut_mem_table I s o hside)

/-- The batching challenge's security, the phase's first part, at `(B + 2)/|E|`. -/
def xiSecurity :
    Typed.Security (batchStep I) (Seam.bus I)
      (Sumcheck.relIn (tableSummand I) Sumcheck.unitWeights (side I))
      (Typed.drawErrors E (((I.B + 3 - 1 : ℕ) : ℝ≥0) / (Nat.card E : ℝ≥0))) :=
  Typed.batchSecurity (xi_batch I)

/-- The final values' security, the phase's last part, at no error. -/
def finalValuesSecurity :
    Typed.Security (Sumcheck.final (tableSummand I) (tableOut I))
      (SumcheckRound.rel (Sumcheck.familyInv (tableSummand I) Sumcheck.unitWeights nodes (inv I))
        I.τmax) (Seam.table I) (Typed.sayErrors _) :=
  Sumcheck.finalSecurityInv (tableSummand I) Sumcheck.unitWeights nodes (inv I) (tableOut I)
    (finalValues_reflect I)

/-- The rounds' input relation for soundness is the batching challenge's output relation. -/
theorem relIn_inv :
    Sumcheck.relIn (tableSummand I) Sumcheck.unitWeights (fun ctx ↦ inv I ctx 0 #v[]) =
      Sumcheck.relIn (tableSummand I) Sumcheck.unitWeights (side I) := by
  congr 1
  funext ctx
  exact propext (inv_zero I ctx)

/-- The rounds' security, with the Keccak predicate's escape absorbed, at `3/|E|` per round. -/
def roundsSecurity (hd : I.d ≤ 2) :
    Typed.Security (Sumcheck.rounds (tableSummand I) Sumcheck.unitWeights nodes)
      (Sumcheck.relIn (tableSummand I) Sumcheck.unitWeights (side I))
      (SumcheckRound.rel (Sumcheck.familyInv (tableSummand I) Sumcheck.unitWeights nodes (inv I))
        I.τmax)
      (Typed.roundsErrors E 3 (((3 : ℕ) : ℝ≥0) / (Nat.card E : ℝ≥0)) I.τmax) :=
  relIn_inv I ▸ Sumcheck.roundsSecurityInv (tableSummand I) Sumcheck.unitWeights nodes (inv I)
    (tableSummand_degree I hd) nodes_injective (inv_sound I)

/-- **Knowledge soundness on the typed framework**, at the slot's errors `tableErrors I`, with
the extractor that keeps the trivial witness. -/
def tableSumcheckSecurity (hd : I.d ≤ 2) :
    Typed.Security (tableSumcheck I) (Seam.bus I) (Seam.table I) (tableErrors I) :=
  (((xiSecurity I).append (roundsSecurity I hd)).append
    (finalValuesSecurity I)).mono (by
      refine Typed.Errors.Le.append ((Typed.drawSlot E).append (Typed.roundsSlot E 3 I.τmax)).tree
        ((Typed.drawSlot E).append (Typed.roundsSlot E 3 I.τmax)).roles
        (Typed.Errors.Le.append (Typed.drawSlot E).tree (Typed.drawSlot E).roles ?_ ?_)
        (Typed.Errors.Le.refl _ _ _)
      · exact ⟨le_of_eq (by rw [natCast_div_card_eq_overE]; rfl), fun _ ↦ trivial⟩
      · rw [natCast_div_card_eq_overE]
        exact Typed.Errors.Le.refl _ _ _)

end TableSumcheck

end
end LeanVM.Protocol
