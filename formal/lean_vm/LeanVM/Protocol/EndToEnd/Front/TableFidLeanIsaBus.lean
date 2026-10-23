/-
  LeanVM.Protocol.EndToEnd.Front.TableFidLeanIsaBus

  The bus phase's result on what it read, at the verifier's layout and the leanISA instance: the
  Python's per-table forms and per-side totals are the protocol's, evaluated at any values of the
  tables' columns in `E`.
-/

module

public import LeanVM.Protocol.EndToEnd.Front.TableFidLeanIsaRows
public import LeanVM.Protocol.EndToEnd.Front.TablePhase
public import LeanVM.Protocol.EndToEnd.Front.BusStack
public import LeanVM.Protocol.EndToEnd.Front.LayoutInstance
public import LeanVM.Protocol.EndToEnd.Complete.BusLayout
public import LeanVM.Protocol.EndToEnd.Front.FlockTerminal
public import LeanVM.Protocol.EndToEnd.Front.BusPadding

/-!
# The bus phase's forms and totals are the protocol's

The table phase's identities (`TableFid`, `LeanVM.Protocol.EndToEnd.Front.TablePhase`) compare
the verifier program's bus result, `BusWit.result` (`verify_bus_balance`,
`python-verifier/verifier.py:534-593` at leanVM `127510d14c98ade4e8a97646c44fa7f1ff5e752d`), with
the oracle protocol's output on the same reads, `Bus.busOut`. This module proves the two agree at
the leanISA instance and the verifier's layout, for every read whose GKR point has `μ_bus`
coordinates, whose memory values are three and whose fingerprint challenges are four:

* `formAt_busOut_forms`: the protocol's form of side `k` on opcode table `t`, evaluated at any
  values of the table's columns in `E`, is the Python's `forms[t][k]` evaluated there;
* `busOut_totals`: the protocol's total of side `k` is the Python's `totals[k]`.

**The blocks.** Both sides sum over the same blocks: the protocol over its sources sorted largest
first (`Bus.sorted`), at their selector weights, the Python over its framework and table blocks in
order, at `eq_above` of their `bus_layout` placements. `sum_weight_src` turns the first into the
second (`sum_selectorWeight_eq`, `LeanVM.Protocol.EndToEnd.Front.BusStack`), and the side's
sources are listed against the Python's blocks: the boundary blocks are the framework
(`sideSources_leanIsa`), and opcode table `t`'s flushes of a side are the Python's blocks of that
table and side, in order (`flushSrcs_map_κ`, `flushSrcs_map_arkG`, `pyFlush_evalE`); the count
columns likewise (`countSrcs_map_arkG`).

**The forms** (`formAt_busOut_forms`). A block's form is linear in its weight (`formAt_form`); at
weight one a flush of table `t` puts `β − Σ_i eq(α, i) · P_i(e)` on `t`, which is the Python's
`β + Σ_slot w_slot · coordinate_slot(e)` in characteristic two once the weights agree
(`fingerprintWeights_toAlpha`: the Python's `eq_kernel(α)` is the protocol's `lagrangeBasis` for
four `α`). The Python's three folds (`Complete.accFold_spec`) leave on each side exactly that
side's blocks owned by `t` (`result_form_eval`).

**The totals** (`busOut_totals`). The protocol's total subtracts from the leaf claim the boundary
blocks' values and the pad's weight; the Python's adds the framework's fingerprints and the pad's
weight. The boundary blocks are the framework, block for block (`bnd_push`, `bnd_pull`): the
separators (`channelSep_state`, …), `index_mle` against the index column (`indexMle_take`), the
values sent against the boundary columns (`valueOf_leanIsa`), and the bytecode entries against
`multilinear_eval` of the bytecode (`multilinearEval_bytecodeWords`).
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.TableSumcheck CompPoly CPoly CMlPolynomialEval
open Finset

@[expose] public section

/-! ## The sumcheck tables of the instance -/

/-- Every opcode table flushes. -/
theorem flushes_opIdx_length_pos : ∀ t : Fin 6, 0 < (LeanIsa.flushes (opIdx t)).length := by
  decide +kernel

/-- `JUMP` has two constraints, the other opcode tables none. -/
theorem constraints_opIdx_length :
    ∀ t : Fin 6, (LeanIsa.constraints (opIdx t)).length = if t = 4 then 2 else 0 := by
  decide +kernel

variable (F : FlockSpec) (prog : Program) (s : Sizes)

/-- The opcode tables are sumcheck tables. -/
theorem sumcheckTable_opIdx (t : Fin 6) : (leanIsaInstance F prog s).SumcheckTable (opIdx t) :=
  Or.inr (Or.inl (List.ne_nil_of_length_pos (flushes_opIdx_length_pos t)))

/-- The sumcheck tables are the opcode tables: the column groups have nothing to check. -/
theorem three_le_of_sumcheckTable (j : Fin 9) (h : (leanIsaInstance F prog s).SumcheckTable j) :
    3 ≤ j.val := by
  match j, h with
  | ⟨0, _⟩, h => rcases h with h | h | h <;> exact absurd rfl h
  | ⟨1, _⟩, h => rcases h with h | h | h <;> exact absurd rfl h
  | ⟨2, _⟩, h => rcases h with h | h | h <;> exact absurd rfl h
  | ⟨j + 3, _⟩, _ => show 3 ≤ j + 3; omega

/-- The six opcode tables are the instance's sumcheck tables, in order. -/
def stEquiv : Fin 6 ≃ (leanIsaInstance F prog s).SumcheckTables where
  toFun t := ⟨opIdx t, sumcheckTable_opIdx F prog s t⟩
  invFun j := ⟨j.1.val - 3, by have h9 : j.1.val < 9 := j.1.isLt; omega⟩
  left_inv t := Fin.ext (by simp [opIdx])
  right_inv j := by
    have h3 := three_le_of_sumcheckTable F prog s j.1 j.2
    refine Subtype.ext (Fin.ext ?_)
    show j.1.val - 3 + 3 = j.1.val
    omega

/-- The opcode table behind a sumcheck table. -/
@[simp] theorem stEquiv_apply_val (t : Fin 6) : (stEquiv F prog s t).1 = opIdx t := rfl

/-- A fold of `max` is below a bound above the start and every entry. -/
theorem foldl_max_le {b : ℕ} : ∀ (l : List ℕ) (init : ℕ), init ≤ b → (∀ x ∈ l, x ≤ b) →
    l.foldl max init ≤ b
  | [], _, h, _ => h
  | x :: l, init, h, hl =>
    foldl_max_le l _ (max_le h (hl x (by simp))) fun y hy ↦ hl y (by simp [hy])

/-- An entry is below the fold of `max`. -/
theorem le_foldl_max_of_mem {x : ℕ} : ∀ {l : List ℕ} {init : ℕ}, x ∈ l → x ≤ l.foldl max init
  | y :: l, init, h => by
    rw [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact (le_max_right _ _).trans (le_foldl_max_init l _)
    · exact le_foldl_max_of_mem h
where
  le_foldl_max_init : ∀ (l : List ℕ) (init : ℕ), init ≤ l.foldl max init
    | [], _ => le_rfl
    | y :: l, init => (le_max_left init y).trans (le_foldl_max_init l _)

/-- **The number of rounds**: `τ_max` is the largest announced log-height. -/
theorem τmax_leanIsa : (leanIsaInstance F prog s).τmax = (tableLogs s).foldl max 0 := by
  apply le_antisymm
  · refine Finset.sup_le fun j _ ↦ ?_
    obtain ⟨t, rfl⟩ := (stEquiv F prog s).surjective j
    exact le_foldl_max_of_mem (List.mem_ofFn.mpr ⟨t, rfl⟩)
  · refine foldl_max_le _ _ (Nat.zero_le _) fun x hx ↦ ?_
    simp only [tableLogs, List.mem_ofFn] at hx
    obtain ⟨t, rfl⟩ := hx
    exact (leanIsaInstance F prog s).τ_le_τmax (stEquiv F prog s t)

/-- **The number of constraints** of the sumcheck tables is two, `JUMP`'s. -/
theorem sumcheckB_leanIsa : (leanIsaInstance F prog s).B = 2 := by
  unfold M3Instance.B
  rw [← (stEquiv F prog s).sum_comp]
  simp only [stEquiv_apply_val]
  change ∑ t : Fin 6, (LeanIsa.constraints (opIdx t)).length = 2
  simp [constraints_opIdx_length]

/-- **The boundary columns**: the memory columns, then `BFCNT`. -/
theorem boundaryColumns_leanIsa : (leanIsaInstance F prog s).boundaryColumns =
    [memCol 0, memCol 1, memCol 2, memCol 3, bfcntCol] := by
  simp [M3Instance.boundaryColumns, LeanIsa.boundary, LeanIsa.coords, Vector.toList_ofFn,
    List.ofFn_succ, Coord.committed?]
  rfl

/-! ## Sums over a side's blocks -/

section Generic

variable {I : M3Instance} (h : Bus.Conditions I)

/-- The Python's placement of block `i` weighs the coordinates above it as `blockSel`. -/
theorem pyPlacements_eqAbove (sizes : List ℕ) (i : ℕ) (hi : i < (pyPlacements sizes).length)
    (p : List E) :
    ((pyPlacements sizes)[i]).eqAbove p = Complete.blockSel sizes p.length i p := by
  have hi' : i < sizes.length := by rwa [length_pyPlacements] at hi
  rw [show (pyPlacements sizes)[i] =
      { vars := sizes.getD i 0, index := Complete.blockOffset sizes i }
    from Complete.getElem_busPlacements sizes i hi', Complete.eqAbove_aligned]
  rfl

/-- **A sum over the protocol's sorted blocks is a sum over the side's blocks in order**, each at
the Python's selector of its placement. -/
theorem sum_weight_src (k : Fin 3) (x₀ : Bus.Source I) (G : Bus.Source I → E)
    (ζ : Vector E I.μBus) :
    ∑ b : Fin (Bus.blocks I k).n, Bus.weight h k b ζ * G (Bus.src I k b) =
      ∑ i ∈ range (Bus.sources I k).length,
        Complete.blockSel ((Bus.sources I k).map Bus.Source.κ) I.μBus i ζ.toList *
          ((Bus.sources I k).map G).getD i 0 := by
  refine Eq.trans (sum_selectorWeight_eq (Bus.sources I k) Bus.Source.κ x₀ (Bus.blocks I k) rfl
    (fun _ ↦ rfl) (h.fits k) ζ G) ?_
  rw [← Fin.sum_univ_eq_sum_range (fun i ↦
    Complete.blockSel ((Bus.sources I k).map Bus.Source.κ) I.μBus i ζ.toList *
      ((Bus.sources I k).map G).getD i 0)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [pyPlacements_eqAbove, Vector.length_toList, List.getD_eq_getElem _ _ (by simp),
    List.getElem_map]
  rfl

/-- `formAt` of a concatenation is the sum of the parts'. -/
theorem formAt_append {j : Fin I.ntab} (a b : I.Form j) (e : Fin (I.width j) → E) :
    formAt (a ++ b) e = formAt a e + formAt b e := by
  simp [formAt]

/-- `formAt` of a `flatMap` is the sum of the pieces'. -/
theorem formAt_flatMap {α : Type} {j : Fin I.ntab} (g : α → I.Form j) (e : Fin (I.width j) → E) :
    ∀ l : List α, formAt (l.flatMap g) e = (l.map fun x ↦ formAt (g x) e).sum
  | [] => by simp [formAt]
  | x :: l => by rw [List.flatMap_cons, formAt_append, formAt_flatMap g e l]; simp

/-- `eval₂` of `1`, at any `BEq` instance on the coefficients. -/
theorem eval₂_one' {n : ℕ} {R S : Type} [CommSemiring R] {_ : BEq R} {_ : LawfulBEq R}
    [CommSemiring S] (f : R →+* S) (e : Fin n → S) : (1 : CMvPolynomial n R).eval₂ f e = 1 :=
  (CMvPolynomial.eval₂Hom f e).map_one

/-- `eval₂` of a variable, at any `BEq` instance on the coefficients. -/
theorem eval₂_X' {n : ℕ} {R S : Type} [CommSemiring R] {_ : BEq R} {_ : LawfulBEq R}
    [CommSemiring S] (f : R →+* S) (e : Fin n → S) (i : Fin n) :
    (CMvPolynomial.X i : CMvPolynomial n R).eval₂ f e = e i :=
  CMvPolynomial.eval₂_X f e i

/-- The constant row `1` evaluates to `1`. -/
theorem evalRow_oneRow (j : Fin I.ntab) (e : Fin (I.width j) → E) :
    evalRow (Bus.oneRow j).1 e = 1 :=
  eval₂_one' _ e

/-- **A block's form is linear in its weight.** -/
theorem formAt_form (src : Bus.Source I) (hd : 1 ≤ I.d) (w : E) (α : Fin 4 → E) (β : E)
    (j : Fin I.ntab) (e : Fin (I.width j) → E) :
    formAt (src.form hd w α β j) e = w * formAt (src.form hd 1 α β j) e := by
  cases src with
  | boundary b => simp [Bus.Source.form, formAt]
  | flush j' f =>
    by_cases hj : j' = j
    · subst hj
      simp only [Bus.Source.form, dite_true, Bus.flushForm, formAt, List.map_cons, List.sum_cons,
        List.map_map, Function.comp_def]
      rw [mul_add, ← List.sum_map_mul_left]
      exact congrArg₂ (· + ·) (by ring) (congrArg List.sum (List.map_congr_left fun i _ ↦ by ring))
    · simp [Bus.Source.form, hj, formAt]
  | count j' c =>
    by_cases hj : j' = j
    · subst hj
      simp only [Bus.Source.form, dite_true, Bus.countForm, formAt, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil]
      ring
    · simp [Bus.Source.form, hj, formAt]

/-- **The protocol's form of a side and a sumcheck table**, evaluated, is the sum over the side's
blocks in order of the Python's selector times the block's form at weight `1`. -/
theorem formAt_forms (k : Fin 3) (x₀ : Bus.Source I) (α : Fin 4 → E) (β : E)
    (ζ : Vector E I.μBus) (j : I.SumcheckTables) (e : Fin (I.width j.1) → E) :
    formAt (Bus.forms h k α β ζ j) e =
      ∑ i ∈ range (Bus.sources I k).length,
        Complete.blockSel ((Bus.sources I k).map Bus.Source.κ) I.μBus i ζ.toList *
          ((Bus.sources I k).map fun src ↦ formAt (src.form h.one_le_d 1 α β j.1) e).getD i 0 := by
  rw [← sum_weight_src h k x₀, Bus.forms, formAt_flatMap, ← Fin.sum_univ_def]
  exact Finset.sum_congr rfl fun b _ ↦ formAt_form _ _ _ _ _ _ _

end Generic

/-! ## List helpers -/

/-- A filtered list is its filtered indices read back. -/
theorem filter_eq_map_finRange {α : Type} (l : List α) (p : α → Bool) :
    l.filter p = ((List.finRange l.length).filter fun i ↦ p l[i]).map (l[·]) := by
  conv_lhs => rw [← List.map_getElem_finRange l]
  rw [List.filter_map]
  rfl

/-- A sum over a list with its indices is a sum over the indices. -/
theorem sum_zipIdx {α : Type} (g : ℕ → α → E) (d : α) :
    ∀ (l : List α) (n : ℕ), ((l.zipIdx n).map fun x ↦ g x.2 x.1).sum =
      ∑ k ∈ range l.length, g (n + k) (l.getD k d)
  | [], _ => by simp
  | a :: l, n => by
    rw [List.zipIdx_cons, List.map_cons, List.sum_cons, sum_zipIdx g d l (n + 1),
      List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
    rw [add_comm]
    exact congrArg₂ (· + ·) (Finset.sum_congr rfl fun k _ ↦ by rw [add_assoc, add_comm 1 k])
      rfl

/-- `List.finRange 9`, the column groups first. -/
theorem finRange_nine' : List.finRange 9 = [0, 1, 2] ++ (List.finRange 6).map opIdx := by
  decide

/-- A `flatMap` over the instance's tables, the column groups first. -/
theorem flatMap_finRange_nine {X : Type} (g : Fin 9 → List X) :
    (List.finRange 9).flatMap g = g 0 ++ g 1 ++ g 2 ++ (List.finRange 6).flatMap (g ∘ opIdx) := by
  rw [finRange_nine', List.flatMap_append, List.flatMap_map]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
  rfl

/-! ## The sides of the bus at the leanISA instance -/

section Sides

variable (F : FlockSpec) (prog : Program) (s : Sizes)

/-- Opcode table `t` among the instance's tables. -/
def opI (t : Fin 6) : Fin (leanIsaInstance F prog s).ntab := opIdx t

/-- Opcode table `t`'s flushes of a side, as the protocol's blocks. -/
def flushSrcs (side : Side) (t : Fin 6) : List (Bus.Source (leanIsaInstance F prog s)) :=
  ((List.finRange ((leanIsaInstance F prog s).flushes (opI F prog s t)).length).filter fun f ↦
    decide (((leanIsaInstance F prog s).flushes (opI F prog s t))[f].1 = side)).map
      (Bus.Source.flush (opI F prog s t))

/-- Opcode table `t`'s count columns, as the protocol's blocks. -/
def countSrcs (t : Fin 6) : List (Bus.Source (leanIsaInstance F prog s)) :=
  ((leanIsaInstance F prog s).counts (opI F prog s t)).map (Bus.Source.count (opI F prog s t))

/-- The Python's blocks of opcode table `t` on a side. -/
def pyBlocks (side : Side) (t : Fin 6) : List BusBlock :=
  (Complete.pySide t side).map fun c ↦ ⟨s.τ t, s.rows t, c, t⟩

/-- The Python's count blocks of opcode table `t`. -/
def pyCountBlocks (t : Fin 6) : List BusBlock :=
  (tables.getD t default).countColumns.map fun l ↦ ⟨s.τ t, s.rows t, [Form.col l], t⟩

/-- **A side's blocks** at the instance: its boundary blocks, then the opcode tables' flushes of the
side, table by table. -/
theorem sideSources_leanIsa (side : Side) :
    Bus.sideSources (leanIsaInstance F prog s) side =
      ((boundary prog s).filter fun b ↦ decide (b.side = side)).map Bus.Source.boundary ++
        (List.finRange 6).flatMap (flushSrcs F prog s side) := by
  unfold Bus.sideSources
  refine congrArg (_ ++ ·) ((flatMap_finRange_nine _).trans ?_)
  show [] ++ [] ++ [] ++ _ = _
  simp only [List.nil_append]
  congr 1

/-- **The count side's blocks** at the instance: the opcode tables' count columns. -/
theorem countSources_leanIsa :
    Bus.countSources (leanIsaInstance F prog s) =
      (List.finRange 6).flatMap (countSrcs F prog s) := by
  unfold Bus.countSources
  exact flatMap_finRange_nine _

/-- The Python's push blocks, table by table. -/
theorem pushBlocks_eq : Complete.pushBlocks s = (List.finRange 6).flatMap (pyBlocks s .push) := by
  rw [Complete.pushBlocks, List.ofFn_eq_map, List.flatMap_def]
  rfl

/-- The Python's pull blocks, table by table. -/
theorem pullBlocks_eq : Complete.pullBlocks s = (List.finRange 6).flatMap (pyBlocks s .pull) := by
  rw [Complete.pullBlocks, List.ofFn_eq_map, List.flatMap_def]
  rfl

/-- The Python's count blocks, table by table. -/
theorem countBlocks_eq : Complete.countBlocks s = (List.finRange 6).flatMap (pyCountBlocks s) := by
  rw [Complete.countBlocks, List.ofFn_eq_map, List.flatMap_def]
  rfl

/-- Opcode table `t` has as many protocol flush blocks on a side as the Python. -/
theorem length_flushSrcs (side : Side) (t : Fin 6) :
    (flushSrcs F prog s side t).length = (pyBlocks s side t).length := by
  have h := congrArg List.length (pyFlush_evalE t side (fun _ ↦ 0))
  simp only [List.length_map] at h
  simp only [flushSrcs, pyBlocks, List.length_map]
  rw [h]
  show _ = (((leanIsaInstance F prog s).flushes (opI F prog s t)).filter fun f ↦
    decide (f.1 = side)).length
  rw [filter_eq_map_finRange ((leanIsaInstance F prog s).flushes (opI F prog s t)), List.length_map]

/-- The protocol's flush blocks of opcode table `t` have its height, as the Python's. -/
theorem flushSrcs_map_κ (side : Side) (t : Fin 6) :
    (flushSrcs F prog s side t).map Bus.Source.κ = (pyBlocks s side t).map (·.logRows) := by
  have hl := length_flushSrcs F prog s side t
  rw [show (flushSrcs F prog s side t).map Bus.Source.κ =
      (flushSrcs F prog s side t).map fun _ ↦ s.τ t from
      List.map_congr_left fun src hsrc ↦ by
        obtain ⟨f, -, rfl⟩ := List.mem_map.mp hsrc
        rfl,
    show (pyBlocks s side t).map (·.logRows) = (pyBlocks s side t).map fun _ ↦ s.τ t from
      List.map_congr_left fun b hb ↦ by
        obtain ⟨c, -, rfl⟩ := List.mem_map.mp hb
        rfl,
    List.map_const', List.map_const', hl]

/-- The protocol's count blocks of opcode table `t` have its height, as the Python's. -/
theorem countSrcs_map_κ (t : Fin 6) :
    (countSrcs F prog s t).map Bus.Source.κ = (pyCountBlocks s t).map (·.logRows) := by
  have h1 : (countSrcs F prog s t).map Bus.Source.κ =
      List.replicate ((leanIsaInstance F prog s).counts (opI F prog s t)).length (s.τ t) := by
    rw [countSrcs, List.map_map]
    exact (List.map_congr_left fun _ _ ↦ rfl).trans List.map_const'
  have h2 : (pyCountBlocks s t).map (·.logRows) =
      List.replicate (LeanIsa.counts (opIdx t)).length (s.τ t) := by
    rw [pyCountBlocks, Complete.pyCountColumns, List.map_map, List.map_map]
    exact (List.map_congr_left fun _ _ ↦ rfl).trans
      (List.map_const'.trans rfl)
  rw [h1, h2]
  rfl

end Sides

/-! ## The fingerprint weights -/

/-- The wire's weights are the protocol's fingerprint weights, for four `α`. -/
theorem fingerprintWeights_toAlpha {alphas : List E} (ha : alphas.length = 4) (k : Fin 16) :
    (fingerprintWeights (toAlpha alphas))[k.val] = (eqKernel alphas).getD k 0 := by
  have h := lagrangeBasis_toVec ha k
  rw [List.getD_eq_getElem _ _ (by rw [Whir.Complete.length_eqKernel, ha]; exact k.isLt)]
  exact h

/-! ## The forms, block by block -/

/-- The Python's weighted coordinates of a flush, as a sum over sixteen slots. -/
def wsum (w l : List E) : E := ∑ k ∈ range 16, w.getD k 0 * l.getD k 0

/-- A Python block's fingerprint of at most sixteen coordinates is `β` plus the weighted values of
its coordinates over sixteen slots. -/
theorem blockVal_eq_wsum (β : E) (w : List E) (b : BusBlock) (col : ℕ → E)
    (hb : b.coordinates.length ≤ 16) :
    Complete.blockVal β w b col =
      β + wsum w ((List.range 16).map fun k ↦ (b.coordinates.getD k {}).evaluate col) := by
  rw [Complete.blockVal, sum_zipIdx (fun k c ↦ w.getD k 0 * c.evaluate col) {} b.coordinates 0,
    wsum]
  refine congrArg (β + ·) ?_
  rw [← Finset.sum_range_add_sum_Ico _ hb]
  have hz : ∑ k ∈ Ico b.coordinates.length 16,
      w.getD k 0 * ((List.range 16).map fun k ↦ (b.coordinates.getD k {}).evaluate col).getD k 0 =
        0 := Finset.sum_eq_zero fun k hk ↦ by
    have hk' := Finset.mem_Ico.mp hk
    rw [List.getD_eq_getElem ((List.range 16).map _) _
        (by rw [List.length_map, List.length_range]; omega),
      List.getElem_map, List.getElem_range, List.getD_eq_default b.coordinates _ (by omega),
      Complete.evaluate_empty, mul_zero]
  rw [hz, add_zero]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk' := Finset.mem_range.mp hk
  rw [zero_add, List.getD_eq_getElem ((List.range 16).map _) _
      (by rw [List.length_map, List.length_range]; omega),
    List.getElem_map, List.getElem_range]

section Forms

variable (F : FlockSpec) (prog : Program) (s : Sizes) (α : Fin 4 → E) (β : E)

/-- The weight-one form a block of the instance puts on opcode table `t₀`, at values `e` of the
table's columns. -/
def arkG (t₀ : Fin 6) (e : Fin ((leanIsaInstance F prog s).width (opI F prog s t₀)) → E)
    (src : Bus.Source (leanIsaInstance F prog s)) : E :=
  formAt (src.form (by norm_num) 1 α β (opI F prog s t₀)) e

/-- The Python's block on opcode table `t₀`: its fingerprint if `t₀` owns it, nothing otherwise. -/
def pyG (t₀ : Fin 6) (w : List E) (col : ℕ → E) (b : BusBlock) : E :=
  if b.owner = t₀.val then Complete.blockVal β w b col else 0

/-- Distinct opcode tables are distinct tables of the instance. -/
theorem opI_injective : Function.Injective (opI F prog s) := fun a b h ↦ by
  have : (opI F prog s a).val = (opI F prog s b).val := congrArg Fin.val h
  simp only [opI, opIdx] at this
  exact Fin.ext (by omega)

/-- A flush of another table puts nothing on `t₀`. -/
theorem arkG_flush_ne {t t₀ : Fin 6} (ht : t ≠ t₀)
    (e : Fin ((leanIsaInstance F prog s).width (opI F prog s t₀)) → E)
    (f : Fin ((leanIsaInstance F prog s).flushes (opI F prog s t)).length) :
    arkG F prog s α β t₀ e (.flush (opI F prog s t) f) = 0 := by
  have hne : opI F prog s t ≠ opI F prog s t₀ := fun h ↦ ht (opI_injective F prog s h)
  simp [arkG, Bus.Source.form, hne, formAt]

/-- A flush of `t₀` puts its fingerprint at weight one: `β − Σ_i eq(α, i) · P_i(e)`. -/
theorem arkG_flush_self (t₀ : Fin 6)
    (e : Fin ((leanIsaInstance F prog s).width (opI F prog s t₀)) → E)
    (f : Fin ((leanIsaInstance F prog s).flushes (opI F prog s t₀)).length) :
    arkG F prog s α β t₀ e (.flush (opI F prog s t₀) f) =
      β - ∑ i : Fin 16, (fingerprintWeights α)[i.val] *
        evalRow ((leanIsaInstance F prog s).flushes (opI F prog s t₀))[f].2[i] e := by
  simp only [arkG, Bus.Source.form, dite_true, Bus.flushForm, formAt, List.map_cons,
    List.sum_cons, List.map_map, Function.comp_def, evalRow_oneRow, mul_one, one_mul]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib, Fin.sum_univ_def]
  refine congrArg (β + ·) ?_
  refine congrArg List.sum (List.map_congr_left fun i _ ↦ ?_)
  simp only [Fin.getElem_fin]
  ring

/-- The protocol's fingerprint of a flush at values in `E`, in the Python's weighted sum. -/
theorem flushValue_eq_wsum {alphas : List E} (ha : alphas.length = 4) (t₀ : Fin 6)
    (e : Fin ((leanIsaInstance F prog s).width (opI F prog s t₀)) → E)
    (fl : Side × Vector (CMvPolynomial ((leanIsaInstance F prog s).width (opI F prog s t₀)) K) 16) :
    β - ∑ i : Fin 16, (fingerprintWeights (toAlpha alphas))[i.val] * evalRow fl.2[i] e =
      β + wsum (eqKernel alphas) (fl.2.toList.map fun P ↦ P.eval₂ (algebraMap K E) e) := by
  rw [CharTwo.sub_eq_add, wsum, ← Fin.sum_univ_eq_sum_range]
  refine congrArg (β + ·) ?_
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [fingerprintWeights_toAlpha ha i, List.getD_eq_getElem (fl.2.toList.map _) _
      (by rw [List.length_map, Vector.length_toList]; exact i.isLt), List.getElem_map,
    Vector.getElem_toList]
  rfl

end Forms

/-! ## Sums over the indices -/

/-- A filtered sum over selectors zipped with blocks is a sum over the indices. -/
theorem sum_filter_zip (t : ℕ) (g : BusBlock → E) :
    ∀ (sels : List E) (bs : List BusBlock), sels.length = bs.length →
      (((List.zip sels bs).filter fun x ↦ decide (x.2.owner = t)).map fun x ↦ x.1 * g x.2).sum =
        ∑ i ∈ range bs.length,
          sels.getD i 0 * (bs.map fun b ↦ if b.owner = t then g b else 0).getD i 0
  | [], [], _ => by simp
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: sels, b :: bs, h => by
    rw [List.zip_cons_cons, List.filter_cons, List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, List.map_cons]
    rw [← sum_filter_zip t g sels bs (by simpa using h)]
    by_cases hb : b.owner = t
    · simp [hb, add_comm]
    · simp [hb]

/-- A sum over a framework of zeros followed by blocks is a sum over the blocks. -/
theorem sum_replicate_append (sel : ℕ → E) (m : ℕ) (l : List E) :
    ∑ i ∈ range (m + l.length), sel i * (List.replicate m 0 ++ l).getD i 0 =
      ∑ i ∈ range l.length, sel (m + i) * l.getD i 0 := by
  rw [Finset.sum_range_add]
  have h0 : ∑ i ∈ range m, sel i * (List.replicate m 0 ++ l).getD i 0 = 0 :=
    Finset.sum_eq_zero fun i hi ↦ by
      rw [List.getD_append _ _ _ _ (by simpa using hi),
        List.getD_eq_getElem _ _ (by simpa using hi),
        List.getElem_replicate, mul_zero]
  rw [h0, zero_add]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [List.getD_append_right _ _ _ _ (by simp), List.length_replicate, Nat.add_sub_cancel_left]

/-- **A side's sum over its blocks**, framework first, is the sum over its table blocks. -/
theorem side_sum_eq {X : Type} (L : List X) (κ : X → ℕ) (G : X → E) (fw : List ℕ)
    (blocks : List BusBlock) (pyv : BusBlock → E)
    (hκ : L.map κ = Complete.sideSizes fw blocks)
    (hG : L.map G = List.replicate fw.length 0 ++ blocks.map pyv) (D : ℕ) (p : List E) :
    ∑ i ∈ range L.length, Complete.blockSel (L.map κ) D i p * (L.map G).getD i 0 =
      ∑ i ∈ range blocks.length,
        Complete.blockSel (Complete.sideSizes fw blocks) D (fw.length + i) p *
          (blocks.map pyv).getD i 0 := by
  have hlen : L.length = fw.length + (blocks.map pyv).length := by
    rw [← List.length_map (f := κ), hκ, Complete.sideSizes, List.length_append, List.length_map,
      List.length_map]
  rw [hκ, hG, hlen, sum_replicate_append, List.length_map]

/-! ## The forms, table by table -/

section FormLists

variable (F : FlockSpec) (prog : Program) (s : Sizes) (β : E)

/-- A list of zeros as a constant map. -/
theorem map_eq_zeros {X : Type} (l : List X) (g : X → E) (h : ∀ x ∈ l, g x = 0) :
    l.map g = List.replicate l.length 0 :=
  (List.map_congr_left h).trans List.map_const'

/-- **Opcode table `t`'s flushes of a side put on table `t₀` what the Python's blocks put**, at
values `e` of `t₀`'s columns in `E`. -/
theorem flushSrcs_map_arkG {alphas : List E} (ha : alphas.length = 4) (side : Side) (t t₀ : Fin 6)
    (e : Fin ((leanIsaInstance F prog s).width (opI F prog s t₀)) → E) :
    (flushSrcs F prog s side t).map (arkG F prog s (toAlpha alphas) β t₀ e) =
      (pyBlocks s side t).map (pyG β t₀ (eqKernel alphas) (rowE e)) := by
  by_cases ht : t = t₀
  · subst ht
    have hL : (flushSrcs F prog s side t).map (arkG F prog s (toAlpha alphas) β t e) =
        ((((leanIsaInstance F prog s).flushes (opI F prog s t)).filter fun f ↦
          decide (f.1 = side)).map fun fl ↦
            fl.2.toList.map fun P ↦ P.eval₂ (algebraMap K E) e).map
          fun l ↦ β + wsum (eqKernel alphas) l := by
      rw [flushSrcs, List.map_map, filter_eq_map_finRange
        ((leanIsaInstance F prog s).flushes (opI F prog s t)), List.map_map, List.map_map]
      refine List.map_congr_left fun f _ ↦ ?_
      simp only [Function.comp_apply]
      rw [arkG_flush_self, flushValue_eq_wsum F prog s β ha]
    have hR : (pyBlocks s side t).map (pyG β t (eqKernel alphas) (rowE e)) =
        ((Complete.pySide t side).map fun coords ↦
          (List.range 16).map fun k ↦ (coords.getD k {}).evaluate (rowE e)).map
          fun l ↦ β + wsum (eqKernel alphas) l := by
      rw [pyBlocks, List.map_map, List.map_map]
      refine List.map_congr_left fun c hc ↦ ?_
      simp only [Function.comp_apply, pyG]
      refine blockVal_eq_wsum β _ _ _ ?_
      cases side
      · exact ((Complete.pyForm_terms t).1 c hc).1
      · exact ((Complete.pyForm_terms t).2 c hc).1
    rw [hL, hR]
    exact congrArg (List.map _) (pyFlush_evalE t side e).symm
  · rw [map_eq_zeros _ _ fun src hsrc ↦ ?_, map_eq_zeros _ _ fun b hb ↦ ?_,
      length_flushSrcs]
    · obtain ⟨c, -, rfl⟩ := List.mem_map.mp hb
      simp only [pyG]
      rw [ite_eq_right_iff]
      exact fun h ↦ absurd (Fin.ext h) ht
    · obtain ⟨f, -, rfl⟩ := List.mem_map.mp hsrc
      exact arkG_flush_ne F prog s _ β ht e f

/-- **Opcode table `t`'s count columns put on table `t₀` what the Python's count blocks put.** -/
theorem countSrcs_map_arkG (α : Fin 4 → E) (t t₀ : Fin 6)
    (e : Fin ((leanIsaInstance F prog s).width (opI F prog s t₀)) → E) :
    (countSrcs F prog s t).map (arkG F prog s α β t₀ e) =
      (pyCountBlocks s t).map (pyG 0 t₀ [1] (rowE e)) := by
  rw [pyCountBlocks, Complete.pyCountColumns, List.map_map, List.map_map, countSrcs, List.map_map]
  show ((leanIsaInstance F prog s).counts (opI F prog s t)).map (fun c ↦
      arkG F prog s α β t₀ e (Bus.Source.count (opI F prog s t) c)) =
    ((leanIsaInstance F prog s).counts (opI F prog s t)).map (fun c ↦
      pyG 0 t₀ [1] (rowE e) ⟨s.τ t, s.rows t, [Form.col c.val], t⟩)
  refine List.map_congr_left fun c _ ↦ ?_
  unfold pyG
  by_cases ht : t = t₀
  · subst ht
    rw [ite_eq_left_iff.mpr fun h ↦ absurd rfl h]
    simp only [arkG, Bus.Source.form, dite_true, Bus.countForm, formAt, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_mul, evalRow]
    rw [eval₂_X']
    simp [Complete.blockVal, Complete.evaluate_eq_sum, Form.col, Verifier.gpow, rowE, c.isLt]
  · rw [ite_eq_right_iff.mpr fun h ↦ absurd (Fin.ext h) ht]
    have hne : opI F prog s t ≠ opI F prog s t₀ := fun h ↦ ht (opI_injective F prog s h)
    simp [arkG, Bus.Source.form, hne, formAt]

end FormLists

/-! ## The sides' lists -/

section SideLists

variable (F : FlockSpec) (prog : Program) (s : Sizes) (β : E)

/-- The push side's blocks. -/
theorem sources_zero :
    Bus.sources (leanIsaInstance F prog s) 0 = Bus.sideSources (leanIsaInstance F prog s) .push :=
  rfl

/-- The pull side's blocks. -/
theorem sources_one :
    Bus.sources (leanIsaInstance F prog s) 1 = Bus.sideSources (leanIsaInstance F prog s) .pull :=
  rfl

/-- The heights of a side's blocks are the Python's, framework first. -/
theorem sideSources_map_κ (side : Side) (blocks : List BusBlock)
    (hb : blocks = (List.finRange 6).flatMap (pyBlocks s side)) :
    (Bus.sideSources (leanIsaInstance F prog s) side).map Bus.Source.κ =
      Complete.sideSizes (((boundary prog s).filter fun b ↦ decide (b.side = side)).map (·.κ))
        blocks := by
  rw [sideSources_leanIsa, List.map_append, List.map_map, Complete.sideSizes, hb,
    List.map_flatMap, List.map_flatMap]
  exact congrArg (_ ++ ·) (congrArg (fun g ↦ (List.finRange 6).flatMap g)
    (funext fun t ↦ flushSrcs_map_κ F prog s side t))

/-- The heights of the count side's blocks are the Python's count blocks'. -/
theorem countSources_map_κ :
    (Bus.countSources (leanIsaInstance F prog s)).map Bus.Source.κ =
      Complete.sideSizes [] (Complete.countBlocks s) := by
  rw [countSources_leanIsa, Complete.sideSizes, countBlocks_eq, List.map_flatMap,
    List.map_flatMap, List.nil_append]
  exact congrArg (fun g ↦ (List.finRange 6).flatMap g) (funext fun t ↦ countSrcs_map_κ F prog s t)

/-- The forms a side's blocks put on table `t₀`: nothing from the framework, then the Python's. -/
theorem sideSources_map_arkG {alphas : List E} (ha : alphas.length = 4) (side : Side)
    (blocks : List BusBlock) (hb : blocks = (List.finRange 6).flatMap (pyBlocks s side))
    (t₀ : Fin 6) (e : Fin ((leanIsaInstance F prog s).width (opI F prog s t₀)) → E) :
    (Bus.sideSources (leanIsaInstance F prog s) side).map
        (arkG F prog s (toAlpha alphas) β t₀ e) =
      List.replicate ((boundary prog s).filter fun b ↦ decide (b.side = side)).length 0 ++
        blocks.map (pyG β t₀ (eqKernel alphas) (rowE e)) := by
  rw [sideSources_leanIsa, List.map_append, List.map_map, hb, List.map_flatMap, List.map_flatMap]
  refine congrArg₂ (· ++ ·) ?_ (congrArg (fun g ↦ (List.finRange 6).flatMap g)
    (funext fun t ↦ flushSrcs_map_arkG F prog s β ha side t t₀ e))
  rw [map_eq_zeros _ _ fun b _ ↦ by simp [arkG, Bus.Source.form, formAt]]

/-- The forms the count side's blocks put on table `t₀` are the Python's. -/
theorem countSources_map_arkG (α : Fin 4 → E) (t₀ : Fin 6)
    (e : Fin ((leanIsaInstance F prog s).width (opI F prog s t₀)) → E) :
    (Bus.countSources (leanIsaInstance F prog s)).map (arkG F prog s α β t₀ e) =
      List.replicate ([] : List ℕ).length 0 ++
        (Complete.countBlocks s).map (pyG 0 t₀ [1] (rowE e)) := by
  rw [countSources_leanIsa, countBlocks_eq, List.map_flatMap, List.map_flatMap, List.length_nil,
    List.replicate_zero, List.nil_append]
  exact congrArg (fun g ↦ (List.finRange 6).flatMap g)
    (funext fun t ↦ countSrcs_map_arkG F prog s β α t t₀ e)

end SideLists

/-! ## The Python's forms -/

section PyForms

variable (prog : Program) (s : Sizes)

/-- The bus phase's result on what it read is the tail of `verify_bus_balance` on those reads. -/
theorem result_eq_busOut (L : Verifier.Layout) (w : BusWit) :
    w.result L = Complete.busOut L w.alphas w.beta w.point w.values w.memory w.mf w.bf := rfl

/-- **The Python's forms**: the three sides' folds over their blocks with their selectors. -/
theorem result_forms (w : BusWit) :
    (w.result (verifierLayout prog s)).forms =
      Complete.accFold 2 [1] 0 (List.zip (Complete.sideSels [] (Complete.countBlocks s) w.point 0
          (Complete.countBlocks s).length) (Complete.countBlocks s))
        (Complete.accFold 1 (eqKernel w.alphas) w.beta (List.zip (Complete.sideSels
            (Complete.fwLogs prog s) (Complete.pullBlocks s) w.point 3
            (Complete.pullBlocks s).length) (Complete.pullBlocks s))
          (Complete.accFold 0 (eqKernel w.alphas) w.beta (List.zip (Complete.sideSels
              (Complete.fwLogs prog s) (Complete.pushBlocks s) w.point 3
              (Complete.pushBlocks s).length) (Complete.pushBlocks s))
            (tables.map fun _ ↦ [{}, {}, {}]))) := by
  rw [result_eq_busOut]
  simp only [Complete.busOut, Complete.accumulateSide_fst]
  rw [Complete.layout_push, Complete.layout_pull, Complete.layout_count]
  rfl

/-- The sum a side's fold adds to table `t`'s form on that side. -/
def foldSum (w : List E) (β : E) (l : List (E × BusBlock)) (t : ℕ) (col : ℕ → E) : E :=
  ((l.filter fun x ↦ decide (x.2.owner = t)).map fun x ↦ x.1 * Complete.blockVal β w x.2 col).sum

/-- **The Python's forms, side by side**: table `t`'s form on each side is what that side's fold
adds. -/
theorem result_form_eval (w : BusWit) (t : Fin 6) (col : ℕ → E) :
    (((w.result (verifierLayout prog s)).forms.getD t []).getD 0 {}).evaluate col =
        foldSum (eqKernel w.alphas) w.beta (List.zip (Complete.sideSels (Complete.fwLogs prog s)
          (Complete.pushBlocks s) w.point 3 (Complete.pushBlocks s).length)
          (Complete.pushBlocks s)) t col ∧
      (((w.result (verifierLayout prog s)).forms.getD t []).getD 1 {}).evaluate col =
        foldSum (eqKernel w.alphas) w.beta (List.zip (Complete.sideSels (Complete.fwLogs prog s)
          (Complete.pullBlocks s) w.point 3 (Complete.pullBlocks s).length)
          (Complete.pullBlocks s)) t col ∧
      (((w.result (verifierLayout prog s)).forms.getD t []).getD 2 {}).evaluate col =
        foldSum [1] 0 (List.zip (Complete.sideSels [] (Complete.countBlocks s) w.point 0
          (Complete.countBlocks s).length) (Complete.countBlocks s)) t col := by
  rw [result_forms]
  obtain ⟨a1, a2, a3, a4⟩ := Complete.accFold_spec 0 (by norm_num) (eqKernel w.alphas) w.beta
    _ _ Complete.forms0_length Complete.forms0_row
    (Complete.owner_lt_six s (Complete.pushBlocks_owned s) _)
  obtain ⟨b1, b2, b3, b4⟩ := Complete.accFold_spec 1 (by norm_num) (eqKernel w.alphas) w.beta
    _ _ a1 a2 (Complete.owner_lt_six s (Complete.pullBlocks_owned s) _)
  obtain ⟨-, -, c3, c4⟩ := Complete.accFold_spec 2 (by norm_num) [1] 0
    _ _ b1 b2 (Complete.owner_lt_six s (Complete.countBlocks_owned s) _)
  refine ⟨?_, ?_, ?_⟩
  · rw [c3 _ 0 (by norm_num), b3 _ 0 (by norm_num), a4, Complete.forms0_entry,
      Complete.evaluate_empty, zero_add]
    rfl
  · rw [c3 _ 1 (by norm_num), b4, a3 _ 1 (by norm_num), Complete.forms0_entry,
      Complete.evaluate_empty, zero_add]
    rfl
  · rw [c4, b3 _ 2 (by norm_num), a3 _ 2 (by norm_num), Complete.forms0_entry,
      Complete.evaluate_empty, zero_add]
    rfl

/-- `foldSum` as a sum over the blocks' indices. -/
theorem foldSum_eq (w : List E) (β : E) (fw : List ℕ) (m : ℕ) (blocks : List BusBlock)
    (p : List E) (t : Fin 6) (col : ℕ → E) :
    foldSum w β (List.zip (Complete.sideSels fw blocks p m blocks.length) blocks) t col =
      ∑ i ∈ range blocks.length,
        Complete.blockSel (Complete.sideSizes fw blocks) p.length (m + i) p *
          (blocks.map (pyG β t w col)).getD i 0 := by
  rw [foldSum,
    sum_filter_zip t (Complete.blockVal β w · col) _ blocks (by simp [Complete.sideSels])]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [Complete.sideSels, Complete.getD_map_range _ _ _ (Finset.mem_range.mp hi)]
  rfl

end PyForms

/-! ## The forms are the Python's -/

section FormEq

variable (F : FlockSpec) (prog : Program) (s : Sizes) (input : PublicInput)

/-- A block of the instance, to read sums against. -/
def srcDefault : Bus.Source (leanIsaInstance F prog s) :=
  .boundary ⟨0, .push, Vector.replicate 16 (.const 0)⟩

/-- **The bus phase's forms are the Python's**: at the protocol's output on what the bus phase
read, the form of side `k` on opcode table `t₀`, evaluated at any values `e` of the table's
columns in `E`, is the Python's form `forms[t₀][k]` evaluated at `e`. -/
theorem formAt_busOut_forms (w : BusWit) (hp : w.point.length = (leanIsaInstance F prog s).μBus)
    (ha : w.alphas.length = 4) (k : Fin 3) (t₀ : Fin 6)
    (e : Fin ((leanIsaInstance F prog s).width (opI F prog s t₀)) → E) :
    formAt ((Bus.busOut (leanIsa_conditions F prog s) (w.layer (leanIsaInstance F prog s) input)
        (w.vals (leanIsaInstance F prog s))).forms k (stEquiv F prog s t₀)) e =
      (((w.result (verifierLayout prog s)).forms.getD t₀ []).getD k {}).evaluate (rowE e) := by
  have hf := formAt_forms (leanIsa_conditions F prog s) k (srcDefault F prog s)
    (toAlpha w.alphas) w.beta (vecOf _ w.point) (stEquiv F prog s t₀) e
  rw [toList_vecOf _ hp] at hf
  obtain ⟨h0, h1, h2⟩ := result_form_eval prog s w t₀ (rowE e)
  refine hf.trans ?_
  fin_cases k
  · have hκ : (Bus.sources (leanIsaInstance F prog s) 0).map Bus.Source.κ =
        Complete.sideSizes (Complete.fwLogs prog s) (Complete.pushBlocks s) :=
      sideSources_map_κ F prog s .push _ (pushBlocks_eq s)
    refine (side_sum_eq _ Bus.Source.κ _ (Complete.fwLogs prog s) (Complete.pushBlocks s) _ hκ
      (sideSources_map_arkG F prog s w.beta ha .push _ (pushBlocks_eq s) t₀ e) _ _).trans ?_
    refine Eq.trans ?_ h0.symm
    rw [foldSum_eq, hp]
    rfl
  · have hκ : (Bus.sources (leanIsaInstance F prog s) 1).map Bus.Source.κ =
        Complete.sideSizes (Complete.fwLogs prog s) (Complete.pullBlocks s) :=
      sideSources_map_κ F prog s .pull _ (pullBlocks_eq s)
    refine (side_sum_eq _ Bus.Source.κ _ (Complete.fwLogs prog s) (Complete.pullBlocks s) _ hκ
      (sideSources_map_arkG F prog s w.beta ha .pull _ (pullBlocks_eq s) t₀ e) _ _).trans ?_
    refine Eq.trans ?_ h1.symm
    rw [foldSum_eq, hp]
    rfl
  · refine (side_sum_eq _ Bus.Source.κ _ [] (Complete.countBlocks s) _
      (countSources_map_κ F prog s)
      (countSources_map_arkG F prog s w.beta (toAlpha w.alphas) t₀ e) _ _).trans ?_
    refine Eq.trans ?_ h2.symm
    rw [foldSum_eq, hp]
    rfl

end FormEq

/-! ## Boundary values -/

/-- `index_mle` as a product, from any power of the generator. -/
theorem indexMleFrom_prod : ∀ (z : List E) (m : ℕ) (acc : E),
    indexMleFrom (Verifier.gen ^ 2 ^ m) z acc =
      acc * ∏ i ∈ range z.length, (1 + z.getD i 0 * (1 + Verifier.gen ^ 2 ^ (m + i)))
  | [], _, acc => by simp [indexMleFrom]
  | r :: z, m, acc => by
    rw [indexMleFrom, ← pow_mul, ← pow_succ, indexMleFrom_prod z (m + 1), List.length_cons,
      Finset.prod_range_succ']
    have hp : ∏ i ∈ range z.length, (1 + z.getD i 0 * (1 + Verifier.gen ^ 2 ^ (m + 1 + i))) =
        ∏ i ∈ range z.length,
          (1 + (r :: z).getD (i + 1) 0 * (1 + Verifier.gen ^ 2 ^ (m + (i + 1)))) :=
      Finset.prod_congr rfl fun i _ ↦ by rw [List.getD_cons_succ, add_assoc, add_comm 1 i]
    rw [hp]
    simp only [List.getD_cons_zero, add_zero]
    ring

/-- **`index_mle` is the index column's extension**: at the low `κ` coordinates of a point. -/
theorem indexMle_take {κ : ℕ} (p : List E) (hκ : κ ≤ p.length) :
    indexMle (p.take κ) = eval₂Mle (idxColumn κ).values (algebraMap K E) (vecOf κ p) := by
  rw [idxColumn_eval, idxColumnEval_eq, indexMle, show Verifier.gen = Verifier.gen ^ 2 ^ 0 by simp,
    indexMleFrom_prod, one_mul, List.length_take, min_eq_left hκ,
    ← Fin.prod_univ_eq_prod_range]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  have ht : (p.take κ).getD k 0 = p.getD k 0 := by
    simp [List.getD_eq_getElem?_getD, k.isLt]
  rw [ht, zero_add, map_pow]
  simp only [vecOf, Fin.getElem_fin, Vector.getElem_ofFn]
  rfl

/-- The value sent for a boundary column is the entry at its place among the boundary columns. -/
theorem valueOf_eq {I : M3Instance} (vals : Vector E I.busClaims) {c : I.ColumnId}
    (hc : c ∈ I.boundaryColumns) :
    Bus.valueOf vals c = vals.toList.getD (I.boundaryColumns.idxOf c) 0 := by
  have hlt := List.idxOf_lt_length_of_mem hc
  have h : I.boundaryColumns.finIdxOf? c = some ⟨_, hlt⟩ :=
    List.finIdxOf?_eq_some_iff.mpr ⟨List.getElem_idxOf hlt, fun j hj ↦ by
      have := List.not_of_lt_findIdx (p := (· == c)) hj
      simpa using this⟩
  unfold Bus.valueOf
  rw [h]
  show vals[(⟨_, hlt⟩ : Fin _)] = _
  rw [List.getD_eq_getElem _ _ (by simpa using hlt), Vector.getElem_toList]
  rfl

/-- A side's sum against boundary values first and zeros after. -/
theorem sum_append_replicate (sel : ℕ → E) (A : List E) (n : ℕ) :
    ∑ i ∈ range (A.length + n), sel i * (A ++ List.replicate n 0).getD i 0 =
      ∑ i ∈ range A.length, sel i * A.getD i 0 := by
  rw [Finset.sum_range_add]
  have h0 : ∑ i ∈ range n, sel (A.length + i) * (A ++ List.replicate n 0).getD (A.length + i) 0 =
      0 := Finset.sum_eq_zero fun i hi ↦ by
    rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left,
      List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_replicate, mul_zero]
  rw [h0, add_zero]
  exact Finset.sum_congr rfl fun i hi ↦ by
    rw [List.getD_append _ _ _ _ (Finset.mem_range.mp hi)]

/-- A sum against ones. -/
theorem sum_map_one {X : Type} (sel : ℕ → E) (L : List X) :
    ∑ i ∈ range L.length, sel i * (L.map fun _ ↦ (1 : E)).getD i 0 = ∑ i ∈ range L.length, sel i :=
  Finset.sum_congr rfl fun i hi ↦ by
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, mul_one]

/-! ## The separators -/

/-- The state channels' separator is `g⁰`. -/
theorem channelSep_state :
    Arithmetization.channelSep Arithmetization.StatePush.toRaw = Parameters.gpow 0 ∧
      Arithmetization.channelSep Arithmetization.StatePull.toRaw = Parameters.gpow 0 := by
  decide +kernel

/-- The memory channels' separator is `g¹`. -/
theorem channelSep_mem :
    Arithmetization.channelSep Arithmetization.MemPush.toRaw = Parameters.gpow 1 ∧
      Arithmetization.channelSep Arithmetization.MemPull.toRaw = Parameters.gpow 1 := by
  decide +kernel

/-- The bytecode channels' separator is `g²`. -/
theorem channelSep_bytecode :
    Arithmetization.channelSep Arithmetization.BytecodePush.toRaw = Parameters.gpow 2 ∧
      Arithmetization.channelSep Arithmetization.BytecodePull.toRaw = Parameters.gpow 2 := by
  decide +kernel

/-! ## The boundary blocks' fingerprints -/

section Boundary

variable (F : FlockSpec) (prog : Program) (s : Sizes)

/-- A boundary block's value at the low coordinates of a point, as the verifier has it. -/
def arkB (α : Fin 4 → E) (β : E) (vals : Vector E (leanIsaInstance F prog s).busClaims)
    (p : List E) (src : Bus.Source (leanIsaInstance F prog s)) : E :=
  src.publicValue α β vals (vecOf src.κ p)

/-- The weighted coordinates of a boundary block written from a list. -/
theorem sum_coords {alphas : List E} (ha : alphas.length = 4) {κ : ℕ}
    (vals : Vector E (leanIsaInstance F prog s).busClaims)
    (cs : List (Coord (shape prog s) κ)) (z : Vector E κ) :
    ∑ i : Fin 16, (fingerprintWeights (toAlpha alphas))[i.val] *
        Bus.coordValue (I := leanIsaInstance F prog s) vals (LeanIsa.coords cs)[i] z =
      ∑ k ∈ range 16, (eqKernel alphas).getD k 0 *
        Bus.coordValue (I := leanIsaInstance F prog s) vals (cs.getD k (.const 0)) z := by
  rw [← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [fingerprintWeights_toAlpha ha i]
  simp only [LeanIsa.coords, Fin.getElem_fin, Vector.getElem_ofFn]

/-- The weighted coordinates of a boundary block of at most sixteen coordinates, as the Python's
`dot` of the weights against the coordinates' values. -/
theorem sum_coords_dot {alphas : List E} (ha : alphas.length = 4) {κ : ℕ}
    (vals : Vector E (leanIsaInstance F prog s).busClaims)
    (cs : List (Coord (shape prog s) κ)) (hcs : cs.length ≤ 16) (z : Vector E κ) :
    ∑ i : Fin 16, (fingerprintWeights (toAlpha alphas))[i.val] *
        Bus.coordValue (I := leanIsaInstance F prog s) vals (LeanIsa.coords cs)[i] z =
      dot ((eqKernel alphas).take cs.length)
        (cs.map fun c ↦ Bus.coordValue (I := leanIsaInstance F prog s) vals c z) := by
  rw [sum_coords F prog s ha, Complete.dot_take_eq _ _ cs.length (by simp)
    (by rw [Whir.Complete.length_eqKernel, ha]; norm_num; exact hcs),
    ← Finset.sum_range_add_sum_Ico _ hcs]
  have hz : ∑ k ∈ Ico cs.length 16, (eqKernel alphas).getD k 0 *
      Bus.coordValue (I := leanIsaInstance F prog s) vals (cs.getD k (.const 0)) z = 0 :=
    Finset.sum_eq_zero fun k hk ↦ by
      rw [List.getD_eq_default _ _ (Finset.mem_Ico.mp hk).1]
      simp [Bus.coordValue]
  rw [hz, add_zero]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk' := Finset.mem_range.mp hk
  rw [List.getD_eq_getElem cs _ hk', List.getD_eq_getElem (cs.map _) _ (by simpa using hk'),
    List.getElem_map]

/-- A list's low `κ` entries are the vector of its first `κ` coordinates. -/
theorem toList_vecOf_take {κ : ℕ} (p : List E) (hκ : κ ≤ p.length) :
    (vecOf κ p).toList = p.take κ := by
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp only [vecOf, Vector.getElem_toList, Vector.getElem_ofFn, List.getElem_take]
  simp at h1
  rw [List.getD_eq_getElem _ _ (by omega)]

/-- `dot` against a concatenation, the first part as a `dot`. -/
theorem dot_take_append (W a b : List E) (h : a.length + b.length ≤ W.length) :
    dot (W.take (a ++ b).length) (a ++ b) =
      dot (W.take a.length) a + ∑ k ∈ range b.length, W.getD (a.length + k) 0 * b.getD k 0 := by
  rw [Complete.dot_take_eq _ _ _ rfl (by simpa using h), Complete.dot_take_eq _ _ _ rfl (by omega),
    List.length_append, Finset.sum_range_add]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun k hk ↦ ?_)
    (Finset.sum_congr rfl fun k _ ↦ ?_)
  · rw [List.getD_append _ _ _ _ (Finset.mem_range.mp hk)]
  · rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]

/-- `dot` against a concatenation of mapped lists, the first part as a `dot`. -/
theorem dot_take_map_append {X : Type} (W : List E) (a b : List X) (f : X → E)
    (h : a.length + b.length ≤ W.length) :
    dot (W.take (a ++ b).length) ((a ++ b).map f) =
      dot (W.take a.length) (a.map f) +
        ∑ k ∈ range b.length, W.getD (a.length + k) 0 * (b.map f).getD k 0 := by
  have := dot_take_append W (a.map f) (b.map f) (by simpa using h)
  simp only [List.length_map, ← List.map_append, List.length_append] at this ⊢
  exact this

/-- The values sent for the boundary columns: the memory columns, `MFCNT`, `BFCNT`. -/
theorem valueOf_leanIsa (w : BusWit) (hm : w.memory.length = 3) :
    Bus.valueOf (w.vals (leanIsaInstance F prog s)) (memCol 0) = w.memory.getD 0 0 ∧
      Bus.valueOf (w.vals (leanIsaInstance F prog s)) (memCol 1) = w.memory.getD 1 0 ∧
      Bus.valueOf (w.vals (leanIsaInstance F prog s)) (memCol 2) = w.memory.getD 2 0 ∧
      Bus.valueOf (w.vals (leanIsaInstance F prog s)) (memCol 3) = w.mf ∧
      Bus.valueOf (w.vals (leanIsaInstance F prog s)) bfcntCol = w.bf := by
  have hl : (w.memory ++ [w.mf, w.bf]).length = (leanIsaInstance F prog s).busClaims := by
    show _ = (leanIsaInstance F prog s).boundaryColumns.length
    rw [boundaryColumns_leanIsa]
    simp [hm]
    rfl
  have ht : (w.vals (leanIsaInstance F prog s)).toList = w.memory ++ [w.mf, w.bf] :=
    toList_vecOf _ hl
  have hmem : ∀ c ∈ [memCol 0, memCol 1, memCol 2, memCol 3, bfcntCol],
      c ∈ (leanIsaInstance F prog s).boundaryColumns := fun c hc ↦ by
    rw [boundaryColumns_leanIsa]; exact hc
  have hidx : ∀ (c : Col) (i : ℕ),
      [memCol 0, memCol 1, memCol 2, memCol 3, bfcntCol].idxOf c = i →
      (leanIsaInstance F prog s).boundaryColumns.idxOf c = i := fun c i h ↦ by
    rw [boundaryColumns_leanIsa]; exact h
  have key : ∀ (c : Col) (i : ℕ), c ∈ [memCol 0, memCol 1, memCol 2, memCol 3, bfcntCol] →
      [memCol 0, memCol 1, memCol 2, memCol 3, bfcntCol].idxOf c = i →
      Bus.valueOf (w.vals (leanIsaInstance F prog s)) c = (w.memory ++ [w.mf, w.bf]).getD i 0 :=
    fun c i hc hi ↦ (valueOf_eq _ (hmem c hc)).trans (by
      rw [ht]; exact congrArg (fun j ↦ (w.memory ++ [w.mf, w.bf]).getD j 0) (hidx c i hi))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [key _ 0 (by simp) (by decide), List.getD_append _ _ _ _ (by omega)]
  · rw [key _ 1 (by simp) (by decide), List.getD_append _ _ _ _ (by omega)]
  · rw [key _ 2 (by simp) (by decide), List.getD_append _ _ _ _ (by omega)]
  · rw [key _ 3 (by simp) (by decide), List.getD_append_right _ _ _ _ (by omega), hm]
    rfl
  · rw [key _ 4 (by simp) (by decide), List.getD_append_right _ _ _ _ (by omega), hm]
    rfl

/-- The bytecode entries' weighted extensions: the Python's `multilinear_eval` of the bytecode at
`(low, α)`. -/
theorem bytecode_entries {alphas : List E} (ha : alphas.length = 4) (p : List E)
    (hp : prog.logSize ≤ p.length) :
    multilinearEval ((verifierLayout prog s).bytecode.map ofK) (p.take prog.logSize ++ alphas) =
      ∑ k ∈ range 8, (eqKernel alphas).getD (3 + k) 0 *
        ((List.finRange 8).map fun k ↦ Bus.coordValue (I := leanIsaInstance F prog s)
          (vals := 0) (.known (entryColumn prog k)) (vecOf prog.logSize p)).getD k 0 := by
  have hz : p.take prog.logSize = (vecOf prog.logSize p).toList := (toList_vecOf_take p hp).symm
  have hw : alphas = (Vector.ofFn (toAlpha alphas)).toList := by
    apply List.ext_getElem (by simp [ha])
    intro i h1 h2
    simp [toAlpha, List.getElem?_eq_getElem h1]
  rw [show p.take prog.logSize ++ alphas =
      (vecOf prog.logSize p).toList ++ (Vector.ofFn (toAlpha alphas)).toList by rw [← hz, ← hw],
    show (verifierLayout prog s).bytecode = bytecodeWords prog from rfl,
    multilinearEval_bytecodeWords, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [List.getD_eq_getElem ((List.finRange 8).map _) _ (by simp), List.getElem_map,
    List.getElem_finRange]
  have h3 := fingerprintWeights_toAlpha ha ⟨k.val + 3, by omega⟩
  simp only at h3
  rw [show 3 + k.val = k.val + 3 by omega, ← h3]
  rfl

/-- **The push side's boundary blocks are the Python's framework fingerprints.** -/
theorem bnd_push (w : BusWit) (ha : w.alphas.length = 4) (hm : w.memory.length = 3)
    (hlm : s.logMem ≤ w.point.length) (hls : prog.logSize ≤ w.point.length) :
    ((boundary prog s).filter fun b ↦ decide (b.side = Side.push)).map (fun b ↦
        arkB F prog s (toAlpha w.alphas) w.beta (w.vals _) w.point (.boundary b)) =
      (fingerprints (eqKernel w.alphas) w.memory (w.point.take s.logMem)
        (w.point.take prog.logSize)
        (multilinearEval ((verifierLayout prog s).bytecode.map ofK) (w.point.take prog.logSize ++ w.alphas)) (Verifier.gpow 0) 1 1).map
          (w.beta + ·) := by
  obtain ⟨v0, v1, v2, -, -⟩ := valueOf_leanIsa F prog s w hm
  obtain ⟨a, b, c, habc⟩ : ∃ a b c, w.memory = [a, b, c] := by
    match h : w.memory, hm with
    | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
  simp only [boundary, List.filter_cons, List.filter_nil, decide_true, decide_false, reduceCtorEq,
    ↓reduceIte, List.map_cons, List.map_nil, arkB, Bus.Source.publicValue, Bus.Source.κ,
    fingerprints]
  rw [sum_coords_dot F prog s ha _ _ (by simp), sum_coords_dot F prog s ha _ _ (by simp),
    sum_coords_dot F prog s ha _ _ (by simp)]
  simp only [List.cons.injEq, and_true, CharTwo.sub_eq_add]
  refine ⟨congrArg (w.beta + ·) ?_, congrArg (w.beta + ·) ?_, congrArg (w.beta + ·) ?_⟩
  · simp [Bus.coordValue, channelSep_state.1, sepState, Verifier.gpow]
  · simp [Bus.coordValue, channelSep_mem.1, v0, v1, v2, sepMem,
      ← indexMle_take w.point hlm, habc, ← Complete.gen_eq_ofK]
  · rw [dot_take_map_append _ _ _ _ (by simp [Whir.Complete.length_eqKernel, ha]),
      bytecode_entries F prog s ha w.point hls]
    refine congrArg₂ (· + ·) ?_ (Finset.sum_congr rfl fun k _ ↦ rfl)
    simp [Bus.coordValue, channelSep_bytecode.1, sepBytecode, ← indexMle_take w.point hls,
      Complete.ofK_gpow, Verifier.gpow]

/-- **The pull side's boundary blocks are the Python's framework fingerprints.** -/
theorem bnd_pull (w : BusWit) (ha : w.alphas.length = 4) (hm : w.memory.length = 3)
    (hlm : s.logMem ≤ w.point.length) (hls : prog.logSize ≤ w.point.length) :
    ((boundary prog s).filter fun b ↦ decide (b.side = Side.pull)).map (fun b ↦
        arkB F prog s (toAlpha w.alphas) w.beta (w.vals _) w.point (.boundary b)) =
      (fingerprints (eqKernel w.alphas) w.memory (w.point.take s.logMem)
        (w.point.take prog.logSize)
        (multilinearEval ((verifierLayout prog s).bytecode.map ofK) (w.point.take prog.logSize ++ w.alphas))
        (Verifier.gpow (2 ^ (verifierLayout prog s).logBytecode - 1)) w.mf w.bf).map
          (w.beta + ·) := by
  obtain ⟨v0, v1, v2, v3, v4⟩ := valueOf_leanIsa F prog s w hm
  obtain ⟨a, b, c, habc⟩ : ∃ a b c, w.memory = [a, b, c] := by
    match h : w.memory, hm with
    | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
  simp only [boundary, List.filter_cons, List.filter_nil, decide_true, decide_false, reduceCtorEq,
    ↓reduceIte, List.map_cons, List.map_nil, arkB, Bus.Source.publicValue, Bus.Source.κ,
    fingerprints]
  rw [sum_coords_dot F prog s ha _ _ (by simp), sum_coords_dot F prog s ha _ _ (by simp),
    sum_coords_dot F prog s ha _ _ (by simp)]
  simp only [List.cons.injEq, and_true, CharTwo.sub_eq_add]
  refine ⟨congrArg (w.beta + ·) ?_, congrArg (w.beta + ·) ?_, congrArg (w.beta + ·) ?_⟩
  · simp [Bus.coordValue, channelSep_state.2, sepState, Verifier.gpow, Program.finalPc,
      Complete.ofK_gpow]
    rfl
  · simp [Bus.coordValue, channelSep_mem.2, v0, v1, v2, v3, sepMem,
      ← indexMle_take w.point hlm, habc, ← Complete.gen_eq_ofK]
  · rw [dot_take_map_append _ _ _ _ (by simp [Whir.Complete.length_eqKernel, ha]),
      bytecode_entries F prog s ha w.point hls]
    refine congrArg₂ (· + ·) ?_ (Finset.sum_congr rfl fun k _ ↦ rfl)
    simp [Bus.coordValue, channelSep_bytecode.2, sepBytecode, ← indexMle_take w.point hls,
      Complete.ofK_gpow, Verifier.gpow, v4]

end Boundary

/-! ## The padding rows -/

section Padding

variable (F : FlockSpec) (prog : Program) (s : Sizes)

/-- The Python's padding term of a block (`padding_rows`, `verifier.py:601`): the padding weight of
its owner's rows times its form at the owner's padding row, plus one. -/
def pyPad (w : List E) (β : E) (p : List E) (b : BusBlock) : E :=
  paddingWeight (p.take b.logRows) b.rows *
    (Complete.blockVal β w b ((tables.getD b.owner default).padding.getD · 0) + 1)

/-- Opcode table `t`'s padding row, lifted to `E`. -/
def padE (t : Fin 6) : Fin ((leanIsaInstance F prog s).width (opI F prog s t)) → E :=
  fun i ↦ ofK ((leanIsaInstance F prog s).padRow (opI F prog s t) i)

/-- Lifting a list's entry is reading the lifted list. -/
private theorem ofK_getD : ∀ (l : List K) (i : ℕ), ofK (l.getD i 0) = (l.map ofK).getD i 0
  | [], _ => by
    simp only [List.getD_nil, List.map_nil]
    exact map_zero (algebraMap K E)
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => ofK_getD l i

/-- The padding row, as the Python reads columns, is the Python's `Table.padding`. -/
theorem rowE_padE (t : Fin 6) :
    rowE (padE F prog s t) = fun i ↦ (tables.getD t default).padding.getD i 0 := by
  funext i
  have hw : (padRowK (tables.getD t default)).length = width (opIdx t) := by
    rw [width_opIdx, padRowK, List.length_map]
    rfl
  have h3 : (opIdx t).val - 3 = t.val := by simp [opIdx]
  have hrow : ∀ j : Fin (width (opIdx t)),
      (leanIsaInstance F prog s).padRow (opI F prog s t) j =
        (padRowK (tables.getD t default)).getD j 0 := by
    intro j
    show (if 3 ≤ (opIdx t).val then
      (padRowK (tables.getD ((opIdx t).val - 3) default)).getD j 0 else 0) = _
    rw [ite_eq_left (by simp [opIdx]), h3]
  rw [padding_eq_map_ofK]
  unfold rowE
  split_ifs with h
  · rw [padE]
    exact (congrArg ofK (hrow ⟨i, h⟩)).trans (ofK_getD _ _)
  · rw [List.getD_eq_default ((padRowK (tables.getD t default)).map ofK) 0
      (by rw [List.length_map, hw]; exact Nat.le_of_not_lt h)]

/-- A table's rows fit in the bus point. -/
theorem tau_le_point (t : Fin 6) {p : List E} (hp : p.length = (leanIsaInstance F prog s).μBus) :
    s.τ t ≤ p.length :=
  hp ▸ ((leanIsaInstance F prog s).τ_le_τmax (stEquiv F prog s t)).trans
    (leanIsa_conditions F prog s).τmax_le

/-- The padding weight of a table's rows at the low coordinates of the bus point is the
Python's `padding_weight`. -/
theorem padWeight_vecOf (t : Fin 6) {p : List E} (hp : p.length = (leanIsaInstance F prog s).μBus) :
    Bus.padWeight (s.rows t) (vecOf (s.τ t) p) = paddingWeight (p.take (s.τ t)) (s.rows t) :=
  padWeight_ofFn_take p _ (tau_le_point F prog s t hp) (s.rows_le t)

/-- A flush block's public value is its padding term: one less its form at the padding row,
times the padding weight. -/
theorem arkB_flush (α : Fin 4 → E) (β : E)
    (vals : Vector E (leanIsaInstance F prog s).busClaims) (p : List E) (t : Fin 6)
    (f : Fin ((leanIsaInstance F prog s).flushes (opI F prog s t)).length) :
    arkB F prog s α β vals p (.flush (opI F prog s t) f) =
      (1 - arkG F prog s α β t (padE F prog s t) (.flush (opI F prog s t) f)) *
        Bus.padWeight (s.rows t) (vecOf (s.τ t) p) := by
  rw [arkG_flush_self]
  have hfp : fingerprint α (Bus.padTuple (opI F prog s t) f) = ∑ i : Fin 16,
      (fingerprintWeights α)[i.val] *
        evalRow ((leanIsaInstance F prog s).flushes (opI F prog s t))[f].2[i] (padE F prog s t) := by
    simp only [fingerprint, Bus.padTuple, Bus.flushPolys]
    refine Finset.sum_congr rfl fun i _ ↦ congrArg (_ * ·) ?_
    rw [Fin.getElem_fin, Vector.getElem_map]
    show _ = evalRow _ (fun j ↦ ofK ((leanIsaInstance F prog s).padRow (opI F prog s t) j))
    rw [TableSumcheck.evalRow_ofK]
    rfl
  rw [← hfp]
  rfl

/-- **A side's flush blocks' public values are the Python's padding terms.** -/
theorem flushSrcs_map_arkB {alphas : List E} (ha : alphas.length = 4) (side : Side) (β : E)
    (vals : Vector E (leanIsaInstance F prog s).busClaims) (p : List E)
    (hp : p.length = (leanIsaInstance F prog s).μBus) :
    ((List.finRange 6).flatMap (flushSrcs F prog s side)).map
        (arkB F prog s (toAlpha alphas) β vals p) =
      ((List.finRange 6).flatMap (pyBlocks s side)).map (pyPad (eqKernel alphas) β p) := by
  rw [List.map_flatMap, List.map_flatMap]
  refine congrArg (fun g ↦ (List.finRange 6).flatMap g) (funext fun t ↦ ?_)
  have h1 : (flushSrcs F prog s side t).map (arkB F prog s (toAlpha alphas) β vals p) =
      ((flushSrcs F prog s side t).map
        (arkG F prog s (toAlpha alphas) β t (padE F prog s t))).map
          fun a ↦ (1 - a) * Bus.padWeight (s.rows t) (vecOf (s.τ t) p) := by
    rw [List.map_map]
    refine List.map_congr_left fun src hsrc ↦ ?_
    obtain ⟨f, -, rfl⟩ := List.mem_map.mp hsrc
    exact arkB_flush F prog s _ β vals p t f
  rw [h1, flushSrcs_map_arkG F prog s β ha side t t, List.map_map]
  refine List.map_congr_left fun b hb ↦ ?_
  obtain ⟨c, -, rfl⟩ := List.mem_map.mp hb
  show (1 - pyG β t (eqKernel alphas) (rowE (padE F prog s t)) ⟨s.τ t, s.rows t, c, t⟩) *
      Bus.padWeight (s.rows t) (vecOf (s.τ t) p) = pyPad (eqKernel alphas) β p ⟨s.τ t, s.rows t, c, t⟩
  rw [pyG, ite_eq_left rfl, rowE_padE, pyPad, padWeight_vecOf F prog s t hp, CharTwo.sub_eq_add]
  ring

/-- **The count blocks' public values are the Python's padding terms.** -/
theorem countSources_map_arkB (α : Fin 4 → E) (β : E)
    (vals : Vector E (leanIsaInstance F prog s).busClaims) (p : List E)
    (hp : p.length = (leanIsaInstance F prog s).μBus) :
    (Bus.countSources (leanIsaInstance F prog s)).map (arkB F prog s α β vals p) =
      [] ++ (Complete.countBlocks s).map (pyPad [1] 0 p) := by
  rw [countSources_leanIsa, countBlocks_eq, List.nil_append, List.map_flatMap, List.map_flatMap]
  refine congrArg (fun g ↦ (List.finRange 6).flatMap g) (funext fun t ↦ ?_)
  rw [pyCountBlocks, Complete.pyCountColumns, List.map_map, List.map_map, countSrcs, List.map_map]
  refine List.map_congr_left fun c _ ↦ ?_
  show (1 - ofK ((leanIsaInstance F prog s).padRow (opI F prog s t) c)) *
      Bus.padWeight (s.rows t) (vecOf (s.τ t) p) =
    pyPad [1] 0 p ⟨s.τ t, s.rows t, [Form.col c.val], t⟩
  have hcol : (tables.getD t default).padding.getD c.val 0 =
      ofK ((leanIsaInstance F prog s).padRow (opI F prog s t) c) := by
    have h := congrFun (rowE_padE F prog s t) c.val
    simp only [rowE, c.isLt, dite_true, Fin.eta, padE] at h
    exact h.symm
  have hbv : Complete.blockVal 0 [1] ⟨s.τ t, s.rows t, [Form.col c.val], t⟩
      ((tables.getD t default).padding.getD · 0) = (tables.getD t default).padding.getD c.val 0 := by
    simp [Complete.blockVal, Complete.evaluate_eq_sum, Form.col, Verifier.gpow]
  rw [pyPad, hbv, hcol, padWeight_vecOf F prog s t hp, CharTwo.sub_eq_add]
  ring

end Padding

/-! ## The totals are the Python's -/

/-- A sum against a framework's values followed by the blocks'. -/
theorem sum_append_blocks (sel : ℕ → E) (A B : List E) :
    ∑ i ∈ range (A.length + B.length), sel i * (A ++ B).getD i 0 =
      ∑ i ∈ range A.length, sel i * A.getD i 0 +
        ∑ i ∈ range B.length, sel (A.length + i) * B.getD i 0 := by
  rw [Finset.sum_range_add]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i hi ↦ ?_)
    (Finset.sum_congr rfl fun i _ ↦ ?_)
  · rw [List.getD_append _ _ _ _ (Finset.mem_range.mp hi)]
  · rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]

/-- **A side's public sum**: the boundary values, then the table blocks' padding terms, summed
against the blocks' selectors. -/
theorem side_total_eq {X : Type} (L : List X) (κ : X → ℕ) (G : X → E) (fw : List ℕ)
    (blocks : List BusBlock) (A : List E) (pyv : BusBlock → E)
    (hκ : L.map κ = Complete.sideSizes fw blocks) (hA : A.length = fw.length)
    (hG : L.map G = A ++ blocks.map pyv) (D : ℕ) (p : List E) :
    ∑ i ∈ range L.length, Complete.blockSel (L.map κ) D i p * (L.map G).getD i 0 =
      ∑ i ∈ range fw.length,
        Complete.blockSel (Complete.sideSizes fw blocks) D i p * A.getD i 0 +
      ∑ i ∈ range blocks.length,
        Complete.blockSel (Complete.sideSizes fw blocks) D (fw.length + i) p *
          (blocks.map pyv).getD i 0 := by
  have hlen : L.length = A.length + (blocks.map pyv).length := by
    rw [← List.length_map (f := κ), hκ, Complete.sideSizes, List.length_append, List.length_map,
      List.length_map, hA]
  rw [hκ, hG, hlen, sum_append_blocks, hA, List.length_map]

/-- A side's selectors summed. -/
theorem side_ones_eq {X : Type} (L : List X) (κ : X → ℕ) (fw : List ℕ) (blocks : List BusBlock)
    (hκ : L.map κ = Complete.sideSizes fw blocks) (D : ℕ) (p : List E) :
    ∑ i ∈ range L.length, Complete.blockSel (L.map κ) D i p * (L.map fun _ ↦ (1 : E)).getD i 0 =
      ∑ i ∈ range (fw.length + blocks.length),
        Complete.blockSel (Complete.sideSizes fw blocks) D i p := by
  have hlen : L.length = fw.length + blocks.length := by
    rw [← List.length_map (f := κ), hκ, Complete.sideSizes, List.length_append, List.length_map]
  rw [sum_map_one, hκ, hlen]

/-- A sum over selectors zipped with blocks, as a sum over the indices. -/
theorem sum_zip_map (g : BusBlock → E) :
    ∀ (sels : List E) (bs : List BusBlock), sels.length = bs.length →
      ((List.zip sels bs).map fun x ↦ x.1 * g x.2).sum =
        ∑ i ∈ range bs.length, sels.getD i 0 * (bs.map g).getD i 0
  | [], [], _ => by simp
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: sels, b :: bs, h => by
    rw [List.zip_cons_cons, List.map_cons, List.sum_cons, List.length_cons,
      Finset.sum_range_succ', sum_zip_map g sels bs (by simpa using h)]
    simp only [List.getD_cons_succ, List.getD_cons_zero, List.map_cons]
    rw [add_comm]

/-- The Python's side total, as a sum over the framework, the selectors and the padding terms. -/
theorem accumulateSide_snd_eq (forms : List (List Form)) (side : ℕ) (fw : List ℕ)
    (blocks : List BusBlock) (fps w : List E) (β : E) (p : List E) (tv : E)
    (hfps : fps.length = fw.length) :
    (accumulateSide forms side blocks (busLayout fw blocks) fps w β p tv).2 =
      tv + ∑ i ∈ range fw.length, Complete.blockSel (Complete.sideSizes fw blocks) p.length i p *
          (fps.map (β + ·)).getD i 0 +
        (∑ i ∈ range (fw.length + blocks.length),
          Complete.blockSel (Complete.sideSizes fw blocks) p.length i p + 1) +
        ∑ i ∈ range blocks.length,
          Complete.blockSel (Complete.sideSizes fw blocks) p.length (fw.length + i) p *
            (blocks.map (pyPad w β p)).getD i 0 := by
  have h1 : dot (Complete.sideSels fw blocks p 0 fw.length) (fps.map (β + ·)) =
      ∑ i ∈ range fw.length, Complete.blockSel (Complete.sideSizes fw blocks) p.length i p *
        (fps.map (β + ·)).getD i 0 := by
    rw [Whir.Complete.dot_eq_sum _ _ (by simp [Complete.sideSels, hfps])]
    simp only [Complete.sideSels, List.length_map, List.length_range]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [Complete.getD_map_range _ _ _ (Finset.mem_range.mp hi), zero_add]
  have h2 : sumE (Complete.sideSels fw blocks p 0 fw.length ++
      Complete.sideSels fw blocks p fw.length blocks.length) =
      ∑ i ∈ range (fw.length + blocks.length),
        Complete.blockSel (Complete.sideSizes fw blocks) p.length i p := by
    rw [Whir.Complete.sumE_eq, List.sum_append, Complete.sideSels, Complete.sideSels,
      ← Complete.sum_range_eq_list, ← Complete.sum_range_eq_list, Finset.sum_range_add]
    simp only [zero_add]
  have h3 : Complete.padSum w β p
      (List.zip (Complete.sideSels fw blocks p fw.length blocks.length) blocks) =
      ∑ i ∈ range blocks.length,
        Complete.blockSel (Complete.sideSizes fw blocks) p.length (fw.length + i) p *
          (blocks.map (pyPad w β p)).getD i 0 := by
    unfold Complete.padSum
    rw [show (fun x : E × BusBlock ↦ x.1 * paddingWeight (p.take x.2.logRows) x.2.rows *
        (Complete.blockVal β w x.2 ((tables.getD x.2.owner default).padding.getD · 0) + 1)) =
        fun x ↦ x.1 * pyPad w β p x.2 from funext fun x ↦ by rw [pyPad, mul_assoc],
      sum_zip_map _ _ _ (by simp [Complete.sideSels])]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [Complete.sideSels, Complete.getD_map_range _ _ _ (Finset.mem_range.mp hi)]
  rw [Complete.accumulateSide_snd, h1, h2, h3]

section Totals

variable (F : FlockSpec) (prog : Program) (s : Sizes) (input : PublicInput)

/-- A block's low point is the vector of the point's first coordinates. -/
theorem lowAt_eq (k : Fin 3) (b : Fin (Bus.blocks (leanIsaInstance F prog s) k).n) (p : List E) :
    Bus.lowAt (leanIsa_conditions F prog s) k b (vecOf _ p) = vecOf _ p := by
  apply Vector.ext
  intro i hi
  simp only [Bus.lowAt, Blocks.lowPoint, lowVec, vecOf, Vector.getElem_ofFn, Vector.getElem_cast]
  exact Vector.getElem_ofFn hi

/-- The protocol's public sum of a side, read over the side's blocks in order. -/
theorem sum_weight_publicValue (k : Fin 3) (α : Fin 4 → E) (β : E)
    (vals : Vector E (leanIsaInstance F prog s).busClaims) (p : List E)
    (hp : p.length = (leanIsaInstance F prog s).μBus) :
    ∑ b : Fin (Bus.blocks (leanIsaInstance F prog s) k).n,
        Bus.weight (leanIsa_conditions F prog s) k b (vecOf _ p) *
          (Bus.src (leanIsaInstance F prog s) k b).publicValue α β vals
            (Bus.lowAt (leanIsa_conditions F prog s) k b (vecOf _ p)) =
      ∑ i ∈ range (Bus.sources (leanIsaInstance F prog s) k).length,
        Complete.blockSel ((Bus.sources (leanIsaInstance F prog s) k).map Bus.Source.κ)
          (leanIsaInstance F prog s).μBus i p *
          ((Bus.sources (leanIsaInstance F prog s) k).map (arkB F prog s α β vals p)).getD i 0 := by
  have h := sum_weight_src (leanIsa_conditions F prog s) k (srcDefault F prog s)
    (arkB F prog s α β vals p) (vecOf _ p)
  rw [toList_vecOf _ hp] at h
  rw [← h]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [lowAt_eq F prog s k b p]
  rfl

/-- A side's total, from its blocks' heights and public values over the Python's framework and
blocks. -/
theorem total_eq (k : Fin 3) (α : Fin 4 → E) (β v : E)
    (vals : Vector E (leanIsaInstance F prog s).busClaims) (p : List E)
    (hp : p.length = (leanIsaInstance F prog s).μBus) (fw : List ℕ) (blocks : List BusBlock)
    (A : List E) (pyv : BusBlock → E) (hκ : (Bus.sources (leanIsaInstance F prog s) k).map
      Bus.Source.κ = Complete.sideSizes fw blocks) (hA : A.length = fw.length)
    (hG : (Bus.sources (leanIsaInstance F prog s) k).map (arkB F prog s α β vals p) =
      A ++ blocks.map pyv) :
    Bus.total (leanIsa_conditions F prog s) k α β (vecOf _ p) v vals =
      v + ∑ i ∈ range fw.length, Complete.blockSel (Complete.sideSizes fw blocks) p.length i p *
          A.getD i 0 +
        (∑ i ∈ range (fw.length + blocks.length),
          Complete.blockSel (Complete.sideSizes fw blocks) p.length i p + 1) +
        ∑ i ∈ range blocks.length,
          Complete.blockSel (Complete.sideSizes fw blocks) p.length (fw.length + i) p *
            (blocks.map pyv).getD i 0 := by
  have hw1 := sum_weight_src (leanIsa_conditions F prog s) k (srcDefault F prog s)
    (fun _ ↦ (1 : E)) (vecOf _ p)
  simp only [mul_one] at hw1
  rw [toList_vecOf _ hp] at hw1
  unfold Bus.total
  rw [sum_weight_publicValue F prog s k _ _ _ _ hp, hw1, side_total_eq _ _ _ _ _ _ _ hκ hA hG,
    side_ones_eq _ _ _ _ hκ, hp, CharTwo.sub_eq_add]
  ring

/-- **The bus phase's totals are the Python's**: at the protocol's output on what the bus phase
read, the total of side `k` is the Python's `totals[k]`. -/
theorem busOut_totals (w : BusWit) (hp : w.point.length = (leanIsaInstance F prog s).μBus)
    (ha : w.alphas.length = 4) (hm : w.memory.length = 3) (k : Fin 3) :
    (Bus.busOut (leanIsa_conditions F prog s) (w.layer (leanIsaInstance F prog s) input)
        (w.vals (leanIsaInstance F prog s))).totals k =
      (w.result (verifierLayout prog s)).totals.getD k 0 := by
  have hlm : s.logMem ≤ w.point.length := hp ▸ (leanIsa_conditions F prog s).κ_le_of_boundaryColumn
    (c := memCol 0) (by rw [boundaryColumns_leanIsa]; exact List.mem_cons_self)
  have hls : prog.logSize ≤ w.point.length := hp ▸
    (leanIsa_conditions F prog s).κ_le_of_boundaryColumn
    (c := bfcntCol) (by
      rw [boundaryColumns_leanIsa]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self))))
  rw [result_eq_busOut]
  match k with
  | ⟨0, _⟩ =>
    have hG : (Bus.sources (leanIsaInstance F prog s) 0).map
        (arkB F prog s (toAlpha w.alphas) w.beta (w.vals _) w.point) =
        (fingerprints (eqKernel w.alphas) w.memory (w.point.take s.logMem)
          (w.point.take prog.logSize)
          (multilinearEval ((verifierLayout prog s).bytecode.map ofK) (w.point.take prog.logSize ++ w.alphas)) (Verifier.gpow 0) 1 1).map
            (w.beta + ·) ++ (Complete.pushBlocks s).map (pyPad (eqKernel w.alphas) w.beta w.point) := by
      rw [sources_zero, sideSources_leanIsa, List.map_append, List.map_map,
        flushSrcs_map_arkB F prog s ha .push w.beta _ _ hp, ← pushBlocks_eq]
      exact congrArg (· ++ _) (bnd_push F prog s w ha hm hlm hls)
    refine (total_eq F prog s 0 _ _ _ _ _ hp _ _ _ _
      (sideSources_map_κ F prog s .push _ (pushBlocks_eq s)) (by simp [fingerprints]; rfl)
      hG).trans ?_
    simp only [Complete.busOut, List.getD_cons_zero]
    rw [Complete.layout_push, accumulateSide_snd_eq _ _ _ _ _ _ _ _ _ (by simp [fingerprints])]
    rfl
  | ⟨1, _⟩ =>
    have hG : (Bus.sources (leanIsaInstance F prog s) 1).map
        (arkB F prog s (toAlpha w.alphas) w.beta (w.vals _) w.point) =
        (fingerprints (eqKernel w.alphas) w.memory (w.point.take s.logMem)
          (w.point.take prog.logSize)
          (multilinearEval ((verifierLayout prog s).bytecode.map ofK) (w.point.take prog.logSize ++ w.alphas))
          (Verifier.gpow (2 ^ (verifierLayout prog s).logBytecode - 1)) w.mf w.bf).map
            (w.beta + ·) ++ (Complete.pullBlocks s).map (pyPad (eqKernel w.alphas) w.beta w.point) := by
      rw [sources_one, sideSources_leanIsa, List.map_append, List.map_map,
        flushSrcs_map_arkB F prog s ha .pull w.beta _ _ hp, ← pullBlocks_eq]
      exact congrArg (· ++ _) (bnd_pull F prog s w ha hm hlm hls)
    refine (total_eq F prog s 1 _ _ _ _ _ hp _ _ _ _
      (sideSources_map_κ F prog s .pull _ (pullBlocks_eq s)) (by simp [fingerprints]; rfl)
      hG).trans ?_
    simp only [Complete.busOut, List.getD_cons_succ, List.getD_cons_zero]
    rw [Complete.layout_pull, accumulateSide_snd_eq _ _ _ _ _ _ _ _ _ (by simp [fingerprints])]
    rfl
  | ⟨2, _⟩ =>
    refine (total_eq F prog s 2 _ _ _ _ _ hp [] (Complete.countBlocks s) [] _
      (countSources_map_κ F prog s) rfl (countSources_map_arkB F prog s _ _ _ _ hp)).trans ?_
    simp only [Complete.busOut, List.getD_cons_succ, List.getD_cons_zero]
    rw [Complete.layout_count, accumulateSide_snd_eq _ _ _ _ _ _ _ _ _ rfl]
    rfl

end Totals

end
end LeanVM.Protocol.EndToEnd.Front
