/-
  LeanVM.Protocol.EndToEnd.Complete.Bus

  The honest prover of the bus phase: the fingerprint challenges, the batched GKR over the
  honest leaves of the three sides, the framework columns' values at the bus point, and the
  simulation of `verifyBusBalance` ending in a true bus result.
-/

module

public import LeanVM.Protocol.EndToEnd.Complete.BusLayout
public import LeanVM.Protocol.EndToEnd.Complete.BusShare
public import LeanVM.Protocol.EndToEnd.Complete.Gkr
public import LeanVM.Protocol.EndToEnd.Front.BusPadding

/-!
# The bus phase

The verifier program's bus phase (`verifyBusBalance`, `crates/verifier/src/bus.rs:130-247` at
leanVM at `leanvm-rev`), against the honest prover of a stack `q`
satisfying the leanISA instance's relation with honest padding (`M3Honest`). The prover passes
the grind for the push tree's depth, then receives the fingerprint: sixteen slot weights `w` and
`β`.

**The leaves.** Each side of the bus is a grand product over the cube of `2^D` leaves, `D` the
push side's depth (`busDepth`), every block placed where `bus_layout` places it (`stackLeaves`):

* push and pull: the framework blocks (`stateTab`, `memTab`, `bcTab`: `β` plus the fingerprint of
  the boundary tuple of each row) and one block per flush of every table (`tableTab`: `β` plus the
  fingerprint of the flushed tuple of each executed row, `blockVal`, and `1` on a padding row);
* count: one block per count column of every table, its executed cells, `1` on a padding row.

**The checks.** `prod_push_eq_pull`: the push and pull leaves multiply to the same root, since
they are the fingerprints of the instance's push and pull tuples (`prod_framework_push`,
`prod_tables`), which a balanced bus permutes. `prod_countLeaves_ne_zero`: the count root is
nonzero when every count cell is. The GKR is fork A's honest prover (`hGkr`,
`follows_verifyGkrGrandProducts`); after it the prover sends the memory limbs' and the two
finalize counts' extensions at the point (`memVals`, `mfVal`, `bfVal`), then proves the program's
share of the bytecode leaf (`hShare`, `Complete.BusShare`), whose value the deployed verifier
checks itself.

**The result** (`honestBus`, `busGood_honestBus`): its four framework claims are true, its forms
are the fold `accumulateSide` makes of the blocks, and each side's total, the tree value plus the
framework, the unused leaves and the padding rows' public term, is the stacking identity's table
part plus that term (`honestBus_totals`), which is the true total of the forms over every row,
padding rows included (`fold_trueTotal`): on a padding row, which holds the public padding row,
the honest leaf `1` and the public term `pad_n · (φ(p) + 1)` add up, in characteristic two, to the
row's own fingerprint `φ(p)` (`sum_block_true`, with `paddingWeight_eq_sum`).

`follows_verifyBusBalance`: the honest prover `hBus` follows `verifyBusBalance` at the verifier's
layout, ending in `BusGood`, for a push tree of depth below `64`. No `require` of the bus phase
fails on the honest prover.
-/

namespace LeanVM.Protocol.EndToEnd.Complete

open LeanVM.Prover (Script)

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.Whir.Complete Finset

@[expose] public section

/-! ## The honest leaves -/

section Honest

variable (prog : LeanIsaProgram) (s : Sizes) (q : Column (leanIsaμ prog s))

/-- The push side's leaf tables, in the side's block order: the framework, then the tables. -/
def pushTabs (β : E) (w : List E) : ℕ → List E
  | 0 => stateTab β w (Verifier.gpow 0)
  | 1 => memTab prog s q β w (onesList s.logMem)
  | 2 => bcTab prog β w (onesList prog.logSize)
  | b + 3 => tableTab prog s q β w ((pushBlocks s).getD b default)

/-- The pull side's leaf tables. -/
def pullTabs (β : E) (w : List E) : ℕ → List E
  | 0 => stateTab β w (Verifier.gpow (2 ^ prog.logSize - 1))
  | 1 => memTab prog s q β w (colList prog s q (memCol 2))
  | 2 => bcTab prog β w (colList prog s q bfcntCol)
  | b + 3 => tableTab prog s q β w ((pullBlocks s).getD b default)

/-- The count side's leaf tables: the count cells. -/
def countTabs : ℕ → List E := fun b ↦ tableTab prog s q 0 [1] ((countBlocks s).getD b default)

/-- The push side's leaves, at the slot weights `alphas`. -/
def pushLeaves (alphas : List E) (beta : E) : List E :=
  stackLeaves (sideSizes (fwLogs prog s) (pushBlocks s)) (pushTabs prog s q beta alphas)
    (busDepth prog s)

/-- The pull side's leaves, at the slot weights `alphas`. -/
def pullLeaves (alphas : List E) (beta : E) : List E :=
  stackLeaves (sideSizes (fwLogs prog s) (pullBlocks s)) (pullTabs prog s q beta alphas)
    (busDepth prog s)

/-- The count side's leaves. -/
def countLeaves : List E :=
  stackLeaves (sideSizes [] (countBlocks s)) (countTabs prog s q) (busDepth prog s)

theorem pushTabs_add_three (β : E) (w : List E) (i : ℕ) :
    pushTabs prog s q β w (3 + i) = tableTab prog s q β w ((pushBlocks s).getD i default) := by
  rw [Nat.add_comm]; rfl

theorem pullTabs_add_three (β : E) (w : List E) (i : ℕ) :
    pullTabs prog s q β w (3 + i) = tableTab prog s q β w ((pullBlocks s).getD i default) := by
  rw [Nat.add_comm]; rfl

theorem getD_sideSizes_table (fw : List ℕ) (blocks : List BusBlock) (i : ℕ)
    (hi : i < blocks.length) :
    (sideSizes fw blocks).getD (fw.length + i) 0 = (blocks.getD i default).logRows := by
  rw [sideSizes, List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left,
    List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
    List.getD_eq_getElem _ _ hi]

theorem length_pushTabs (β : E) (w : List E) :
    ∀ b < (sideSizes (fwLogs prog s) (pushBlocks s)).length,
      (pushTabs prog s q β w b).length = 2 ^ (sideSizes (fwLogs prog s) (pushBlocks s)).getD b 0
  | 0, _ => rfl
  | 1, _ => length_memTab ..
  | 2, _ => length_bcTab ..
  | b + 3, hb => by
    have hb' : b < (pushBlocks s).length := by simp [sideSizes, fwLogs] at hb; omega
    rw [show b + 3 = (fwLogs prog s).length + b by simp [fwLogs]; omega,
      getD_sideSizes_table _ _ _ hb', show (fwLogs prog s).length + b = 3 + b from rfl,
      pushTabs_add_three, length_tableTab]

theorem length_pullTabs (β : E) (w : List E) :
    ∀ b < (sideSizes (fwLogs prog s) (pullBlocks s)).length,
      (pullTabs prog s q β w b).length = 2 ^ (sideSizes (fwLogs prog s) (pullBlocks s)).getD b 0
  | 0, _ => rfl
  | 1, _ => length_memTab ..
  | 2, _ => length_bcTab ..
  | b + 3, hb => by
    have hb' : b < (pullBlocks s).length := by simp [sideSizes, fwLogs] at hb; omega
    rw [show b + 3 = (fwLogs prog s).length + b by simp [fwLogs]; omega,
      getD_sideSizes_table _ _ _ hb', show (fwLogs prog s).length + b = 3 + b from rfl,
      pullTabs_add_three, length_tableTab]

theorem length_countTabs :
    ∀ b < (sideSizes [] (countBlocks s)).length,
      (countTabs prog s q b).length = 2 ^ (sideSizes [] (countBlocks s)).getD b 0 := by
  intro b hb
  have hb' : b < (countBlocks s).length := by simpa [sideSizes] using hb
  have := getD_sideSizes_table [] (countBlocks s) b hb'
  simp only [List.length_nil, zero_add] at this
  rw [this, countTabs, length_tableTab]

theorem length_pushLeaves (alphas : List E) (beta : E) :
    (pushLeaves prog s q alphas beta).length = 2 ^ busDepth prog s :=
  length_stackLeaves _ _ _ (length_pushTabs prog s q _ _) (total_le_depth prog s)

theorem length_pullLeaves (alphas : List E) (beta : E) :
    (pullLeaves prog s q alphas beta).length = 2 ^ busDepth prog s :=
  length_stackLeaves _ _ _ (length_pullTabs prog s q _ _)
    ((total_pull prog s).le.trans (total_le_depth prog s))

theorem length_countLeaves : (countLeaves prog s q).length = 2 ^ busDepth prog s :=
  length_stackLeaves _ _ _ (length_countTabs prog s q)
    ((total_count_le prog s).trans (total_le_depth prog s))

/-- The product of a side's leaf tables, split into the framework's three and the tables'. -/
theorem prod_split (tabs : ℕ → List E) (m : ℕ) :
    ((List.range (3 + m)).map fun b ↦ (tabs b).prod).prod =
      (tabs 0).prod * (tabs 1).prod * (tabs 2).prod *
        ((List.range m).map fun i ↦ (tabs (3 + i)).prod).prod := by
  rw [List.range_add, List.map_append, List.prod_append, List.map_map]
  simp only [show List.range 3 = [0, 1, 2] from rfl, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, Function.comp_def, mul_assoc]

/-- **The push leaves' product** is the push tuples' fingerprint product. -/
theorem prod_pushLeaves (alphas : List E) (hw : alphas.length = 16) (beta : E) :
    (pushLeaves prog s q alphas beta).prod =
      (((inst prog s).tuples q .push).map (fpV beta alphas)).prod := by
  rw [pushLeaves, prod_stackLeaves, show (sideSizes (fwLogs prog s) (pushBlocks s)).length =
    3 + (pushBlocks s).length by simp [sideSizes, fwLogs]; omega, prod_split]
  simp only [pushTabs_add_three]
  rw [map_range_getD (pushBlocks s) default
    fun b ↦ (tableTab prog s q beta alphas b).prod]
  rw [M3Instance.tuples, List.map_append, List.prod_append]
  simp only [pushTabs]
  rw [prod_framework_push prog s q beta _ hw,
    show ((pushBlocks s).map fun b ↦
        (tableTab prog s q beta alphas b).prod).prod = _ from
      prod_tables prog s q beta _ hw .push, mul_comm]

/-- **The pull leaves' product** is the pull tuples' fingerprint product. -/
theorem prod_pullLeaves (alphas : List E) (hw : alphas.length = 16) (beta : E) :
    (pullLeaves prog s q alphas beta).prod =
      (((inst prog s).tuples q .pull).map (fpV beta alphas)).prod := by
  rw [pullLeaves, prod_stackLeaves, show (sideSizes (fwLogs prog s) (pullBlocks s)).length =
    3 + (pullBlocks s).length by simp [sideSizes, fwLogs]; omega, prod_split]
  simp only [pullTabs_add_three]
  rw [map_range_getD (pullBlocks s) default
    fun b ↦ (tableTab prog s q beta alphas b).prod]
  rw [M3Instance.tuples, List.map_append, List.prod_append]
  simp only [pullTabs]
  rw [prod_framework_pull prog s q beta _ hw,
    show ((pullBlocks s).map fun b ↦
        (tableTab prog s q beta alphas b).prod).prod = _ from
      prod_tables prog s q beta _ hw .pull, mul_comm]

/-- **The shared root**: a balanced bus makes the push and pull leaves' products equal. -/
theorem prod_push_eq_pull (hbal : (inst prog s).Balanced q) (alphas : List E)
    (halpha : alphas.length = 16) (beta : E) :
    (pushLeaves prog s q alphas beta).prod = (pullLeaves prog s q alphas beta).prod := by
  rw [prod_pushLeaves prog s q alphas halpha, prod_pullLeaves prog s q alphas halpha]
  exact (hbal.map _).prod_eq

/-- **The count root is nonzero** when every count cell is. -/
theorem prod_countLeaves_ne_zero (hcnt : (inst prog s).CountsNonzero q) :
    (countLeaves prog s q).prod ≠ 0 := by
  refine prod_countTabs_ne_zero prog s q hcnt _ (countBlocks s) (by simp [sideSizes]) ?_ _
  intro b hb
  obtain ⟨l, hl, hbl⟩ := List.mem_flatten.mp hb
  obtain ⟨t, rfl⟩ := List.mem_ofFn.mp hl
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hbl
  exact ⟨t, c, hc, rfl⟩

/-! ## The totals -/

theorem sum_map_filter_cons {α : Type} (p : α → Prop) [DecidablePred p] (g : α → E) (y : α)
    (l : List α) :
    (((y :: l).filter fun a ↦ decide (p a)).map g).sum =
      (if p y then g y else 0) + ((l.filter fun a ↦ decide (p a)).map g).sum := by
  by_cases h : p y <;> simp [h]

/-- `1 + 1 = 0` in `E`. -/
private theorem one_add_one_E : (1 : E) + 1 = 0 := by
  rw [one_add_one_eq_two]
  exact CharTwo.two_eq_zero

/-- The verifier's tables have the instance's widths. -/
theorem columns_length : ∀ t : Fin 6, (tables.getD t default).columns.length = width (opIdx t) := by
  decide +kernel

/-- The verifier's padding weight is the padding rows' share of the equality weight. -/
theorem paddingWeight_eq_sum (z : List E) (n : ℕ) (hn : n ≤ 2 ^ z.length) :
    paddingWeight z n =
      ∑ y ∈ range (2 ^ z.length), (if n ≤ y then 1 else 0) * eqEval (boolPoint z.length y) z := by
  rw [Front.paddingWeight_eq_padWeight z n hn, Bus.padWeight, ← Front.multilinearEval_eq_evalMle]
  have h1 : (Front.vecList z).toList = z := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp [List.getElem?_eq_getElem h2]
  have h2 : (Vector.ofFn fun x : Fin (2 ^ z.length) ↦ if n ≤ x.val then (1 : E) else 0).toList =
      (List.range (2 ^ z.length)).map fun y ↦ if n ≤ y then 1 else 0 := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp
  rw [h1, h2, multilinearEval_range _ _ _ rfl]

/-- A padding row of an honest stack reads, column by column, as the verifier's padding row. -/
theorem rowVal_padding (hP : (inst prog s).PaddingHonest q) (t : Fin 6) (x : Fin (2 ^ s.τ t))
    (hx : s.rows t ≤ x.val) :
    rowVal prog s q t x = fun i ↦ (tables.getD t default).padding.getD i 0 := by
  funext i
  rw [rowVal, padding_eq_map_ofK]
  split_ifs with hi
  · rw [hP (opIdx t) x hx]
    show ofK (padRow (opIdx t) ⟨i, hi⟩) = _
    simp only [padRow, opIdx, show 3 ≤ t.val + 3 by omega, ↓reduceIte, Nat.add_sub_cancel,
      List.getD_eq_getElem?_getD, List.getElem?_map]
    have h0 : ofK (0 : K) = 0 := map_zero (algebraMap K E)
    cases h : (padRowK (tables[(t : ℕ)]?.getD default))[i]? <;> simp [h0]
  · have hl : ((padRowK (tables.getD t default)).map ofK).length = width (opIdx t) := by
      rw [List.length_map, padRowK_length]
      exact columns_length t
    rw [List.getD_eq_default _ _ (by omega)]

/-- **One block's contribution to the true total**: its selector times its extension, and the
padding term the verifier adds, `pad_n · (φ(p) + 1)`: in characteristic two, the honest leaves `1`
of the padding rows and that term add up to the padding rows' fingerprints. -/
theorem sum_block_true (hP : (inst prog s).PaddingHonest q) (β : E) (w : List E) (p : List E)
    (sel : E) (t : Fin 6) (coords : List Form) (hp : s.τ t ≤ p.length) :
    ∑ x : Fin (2 ^ s.τ t), eqEval (p.take (s.τ t)) (boolPoint (s.τ t) x) *
        (sel * blockVal β w ⟨s.τ t, s.rows t, coords, t⟩ (rowVal prog s q t x)) =
      sel * multilinearEval (tableTab prog s q β w ⟨s.τ t, s.rows t, coords, t⟩)
          (p.take (s.τ t)) +
        sel * paddingWeight (p.take (s.τ t)) (s.rows t) *
          (blockVal β w ⟨s.τ t, s.rows t, coords, t⟩
            ((tables.getD t default).padding.getD · 0) + 1) := by
  have hz : (p.take (s.τ t)).length = s.τ t := by simp only [List.length_take]; omega
  rw [tableTab, multilinearEval_range _ _ _ hz,
    paddingWeight_eq_sum _ _ (by rw [hz]; exact s.rows_le t), hz, mul_sum, Finset.sum_range,
    Finset.sum_range, mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  simp only
  rw [eqEval_comm]
  by_cases hx : x.val < s.rows t
  · simp only [hx, ↓reduceIte, show ¬ s.rows t ≤ x.val by omega, rowAt_eq prog s q t x]
    ring
  · simp only [hx, ↓reduceIte, Nat.le_of_not_lt hx, rowVal_padding prog s q hP t x
      (Nat.le_of_not_lt hx)]
    linear_combination (-(sel * eqEval (boolPoint (s.τ t) x) (p.take (s.τ t)))) * one_add_one_E

/-- `padSum` of a cons. -/
theorem padSum_cons (w : List E) (β : E) (p : List E) (sel : E) (b : BusBlock)
    (l : List (E × BusBlock)) :
    padSum w β p ((sel, b) :: l) = sel * paddingWeight (p.take b.logRows) b.rows *
      (blockVal β w b ((tables.getD b.owner default).padding.getD · 0) + 1) + padSum w β p l := by
  simp only [padSum, List.map_cons, List.sum_cons]

/-- **The true total of a fold**: the forms a side's blocks accumulate, summed over every table's
rows against the point, are the blocks' selector-weighted extensions plus the padding terms, on an
honest stack. -/
theorem sum_owner_tables (hP : (inst prog s).PaddingHonest q) (β : E) (w : List E) (p : List E)
    (hp : ∀ t, s.τ t ≤ p.length) :
    ∀ l : List (E × BusBlock),
      (∀ y ∈ l, ∃ t : Fin 6, y.2 = ⟨s.τ t, s.rows t, y.2.coordinates, t⟩) →
      ∑ t : Fin 6, ∑ x : Fin (2 ^ s.τ t), eqEval (p.take (s.τ t)) (boolPoint (s.τ t) x) *
        ((l.filter fun y ↦ decide (y.2.owner = (t : ℕ))).map
          fun y ↦ y.1 * blockVal β w y.2 (rowVal prog s q t x)).sum =
      (l.map fun y ↦ y.1 * multilinearEval (tableTab prog s q β w y.2) (p.take y.2.logRows)).sum +
        padSum w β p l
  | [], _ => by simp [padSum]
  | (sel, b) :: l, hl => by
    obtain ⟨ty, hb⟩ := hl (sel, b) (by simp)
    simp only at hb
    rw [List.map_cons, List.sum_cons, padSum_cons, add_add_add_comm,
      ← sum_owner_tables hP β w p hp l fun y hy ↦ hl y (by simp [hy])]
    simp only [sum_map_filter_cons, mul_add, sum_add_distrib]
    refine congrArg (· + _) ?_
    have hcond : ∀ t : Fin 6, (b.owner = ↑t) ↔ (ty = t) := fun t ↦ by
      rw [hb]; simp [Fin.val_inj]
    simp only [hcond, mul_ite, mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, ↓reduceIte]
    rw [hb, sum_block_true prog s q hP β w p sel ty b.coordinates (hp ty)]
    dsimp only
    ring

/-- A list zipped with a function of its indices. -/
theorem sum_zip_range (l : List BusBlock) (f : ℕ → E) (g : E × BusBlock → E) :
    ((List.zip ((List.range l.length).map f) l).map g).sum =
      ∑ i ∈ range l.length, g (f i, l.getD i default) := by
  rw [sum_range_eq_list]
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.length_map, List.length_range] at h2
  simp [List.getElem?_eq_getElem h2]

/-! ## The framework's fingerprints -/

/-- The honest memory limbs at the bus point. -/
def memVals (point : List E) : List E :=
  [multilinearEval (colList prog s q (memCol 0)) (point.take s.logMem),
    multilinearEval (colList prog s q (memCol 1)) (point.take s.logMem)]

/-- The honest memory finalize counts at the bus point. -/
def mfVal (point : List E) : E :=
  multilinearEval (colList prog s q (memCol 2)) (point.take s.logMem)

/-- The honest bytecode finalize counts at the bus point. -/
def bfVal (point : List E) : E :=
  multilinearEval (colList prog s q bfcntCol) (point.take prog.logSize)

theorem multilinearEval_onesList (z : List E) (n : ℕ) (hz : z.length = n) :
    multilinearEval (onesList n) z = 1 := by
  subst hz; exact multilinearEval_replicate 1 z

/-- **The push framework blocks extend to the verifier's push fingerprints.** -/
theorem fw_push (w : List E) (hw : w.length = 16) (β : E) (p : List E)
    (hp : busDepth prog s ≤ p.length) :
    ∀ b < (fwLogs prog s).length,
      multilinearEval (pushTabs prog s q β w b)
          (p.take ((fwLogs prog s).getD b 0)) =
        β + (fingerprints w (memVals prog s q p) (p.take s.logMem)
          (p.take prog.logSize) (bcShare prog w (p.take prog.logSize)) (Verifier.gpow 0) 1
            1).getD b 0
  | 0, _ => rfl
  | 1, _ => by
    have hz := length_take_of_le ((logMem_le_busDepth prog s).trans hp)
    simp only [pushTabs, fwLogs, fingerprints, memVals, List.getD_cons_succ, List.getD_cons_zero]
    rw [multilinearEval_memTab prog s q β _ (by rw [hw]; norm_num) _
      (by simp [onesList]) _ hz, multilinearEval_onesList _ _ hz]
  | 2, _ => by
    have hz := length_take_of_le ((logSize_le_busDepth prog s).trans hp)
    simp only [pushTabs, fwLogs, fingerprints, List.getD_cons_succ, List.getD_cons_zero]
    rw [multilinearEval_bcTab prog β w (by rw [hw]; norm_num) _ (by simp [onesList]) _ hz,
      multilinearEval_onesList _ _ hz]
  | b + 3, hb => by simp [fwLogs] at hb

/-- **The pull framework blocks extend to the verifier's pull fingerprints.** -/
theorem fw_pull (L : Verifier.Layout) (hlb : L.logBytecode = prog.logSize) (w : List E)
    (hw : w.length = 16) (β : E) (p : List E) (hp : busDepth prog s ≤ p.length) :
    ∀ b < (fwLogs prog s).length,
      multilinearEval (pullTabs prog s q β w b)
          (p.take ((fwLogs prog s).getD b 0)) =
        β + (fingerprints w (memVals prog s q p) (p.take s.logMem)
          (p.take prog.logSize) (bcShare prog w (p.take prog.logSize))
          (Verifier.gpow (2 ^ L.logBytecode - 1)) (mfVal prog s q p) (bfVal prog s q p)).getD b 0
  | 0, _ => by rw [hlb]; rfl
  | 1, _ => by
    have hz := length_take_of_le ((logMem_le_busDepth prog s).trans hp)
    simp only [pullTabs, fwLogs, fingerprints, memVals, List.getD_cons_succ, List.getD_cons_zero]
    rw [multilinearEval_memTab prog s q β _ (by rw [hw]; norm_num) _
      (length_colList prog s q (memCol 2)) _ hz]
    rfl
  | 2, _ => by
    have hz := length_take_of_le ((logSize_le_busDepth prog s).trans hp)
    simp only [pullTabs, fwLogs, fingerprints, List.getD_cons_succ, List.getD_cons_zero]
    rw [multilinearEval_bcTab prog β w (by rw [hw]; norm_num) _ (length_colList prog s q bfcntCol)
      _ hz]
    rfl
  | b + 3, hb => by simp [fwLogs] at hb

/-! ## The bus's result is true -/

/-- The honest tree values: the three sides' leaves' extensions at the point. -/
def treeVals (alphas : List E) (β : E) (p : List E) : List E :=
  [multilinearEval (pushLeaves prog s q alphas β) p,
    multilinearEval (pullLeaves prog s q alphas β) p,
    multilinearEval (countLeaves prog s q) p]

/-- The honest bus result at the slot weights `alphas`, `β`, the GKR point `p` and the bytecode's
point `bp`. -/
def honestBus (alphas : List E) (β : E) (p bp : List E) : BusResult :=
  busOut (verifierLayout prog s) alphas β p (treeVals prog s q alphas β p) (memVals prog s q p)
    (mfVal prog s q p) (bfVal prog s q p) (bcShare prog alphas (p.take prog.logSize)) bp

theorem honestBus_point (alphas : List E) (β : E) (p bp : List E) :
    (honestBus prog s q alphas β p bp).point = p := rfl

theorem honestBus_forms (alphas : List E) (β : E) (p bp : List E) :
    (honestBus prog s q alphas β p bp).forms =
      accFold 2 [1] 0 (List.zip (sideSels [] (countBlocks s) p 0 (countBlocks s).length)
          (countBlocks s))
        (accFold 1 alphas β (List.zip (sideSels (fwLogs prog s) (pullBlocks s) p 3
            (pullBlocks s).length) (pullBlocks s))
          (accFold 0 alphas β (List.zip (sideSels (fwLogs prog s) (pushBlocks s) p 3
              (pushBlocks s).length) (pushBlocks s))
            (tables.map fun _ ↦ [{}, {}, {}]))) := by
  simp only [honestBus, busOut, accumulateSide_fst]
  rw [layout_push, layout_pull, layout_count]
  rfl

/-- A side's total as `accumulateSide` computes it from honest values. -/
def sideTotal (fw : List ℕ) (blocks : List BusBlock) (tabs : ℕ → List E) (p : List E) : E :=
  ∑ i ∈ range blocks.length, blockSel (sideSizes fw blocks) (busDepth prog s) (fw.length + i) p *
    multilinearEval (tabs (fw.length + i)) (p.take (blocks.getD i default).logRows)

theorem honestBus_totals (alphas : List E) (halpha : alphas.length = 16) (β : E) (p bp : List E)
    (hp : p.length = busDepth prog s) :
    (honestBus prog s q alphas β p bp).totals =
      [sideTotal prog s (fwLogs prog s) (pushBlocks s) (pushTabs prog s q β alphas) p +
          padSum alphas β p (List.zip (sideSels (fwLogs prog s) (pushBlocks s) p
            (fwLogs prog s).length (pushBlocks s).length) (pushBlocks s)),
        sideTotal prog s (fwLogs prog s) (pullBlocks s) (pullTabs prog s q β alphas) p +
          padSum alphas β p (List.zip (sideSels (fwLogs prog s) (pullBlocks s) p
            (fwLogs prog s).length (pullBlocks s).length) (pullBlocks s)),
        sideTotal prog s [] (countBlocks s) (countTabs prog s q) p +
          padSum [1] 0 p (List.zip (sideSels [] (countBlocks s) p 0 (countBlocks s).length)
            (countBlocks s))] := by
  simp only [honestBus, busOut, treeVals, List.getD_cons_zero, List.getD_cons_succ]
  rw [layout_push, layout_pull, layout_count]
  simp only [List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_⟩
  · exact accumulateSide_total _ 0 (fwLogs prog s) (pushBlocks s) _ _ β _ (busDepth prog s)
      (length_pushTabs prog s q _ _) (total_le_depth prog s) p hp rfl
      (fw_push prog s q alphas halpha β p hp.ge)
  · exact accumulateSide_total _ 1 (fwLogs prog s) (pullBlocks s) _ _ β _ (busDepth prog s)
      (length_pullTabs prog s q _ _) ((total_pull prog s).le.trans (total_le_depth prog s)) p hp
      rfl (fw_pull prog s q _ rfl alphas halpha β p hp.ge)
  · exact accumulateSide_total _ 2 [] (countBlocks s) [] [1] 0 _ (busDepth prog s)
      (length_countTabs prog s q) ((total_count_le prog s).trans (total_le_depth prog s)) p hp
      rfl fun b hb ↦ absurd hb (Nat.not_lt_zero b)

theorem trueTotal_congr (p : List E) {F G : List (List Form)} (side : ℕ)
    (h : ∀ t, (F.getD t []).getD side {} = (G.getD t []).getD side {}) :
    trueTotal prog s q p F side = trueTotal prog s q p G side := by
  simp only [trueTotal, h]

/-- **The true total of a side's fold** is the side's total with its padding terms, when the forms
start empty and the stack is honest. -/
theorem fold_trueTotal (hP : (inst prog s).PaddingHonest q) (side : ℕ) (hside : side < 3)
    (w : List E) (β : E) (blocks : List BusBlock)
    (hown : ∀ b ∈ blocks, ∃ t : Fin 6, b = ⟨s.τ t, s.rows t, b.coordinates, t⟩) (fw : List ℕ)
    (tabs : ℕ → List E)
    (htabs : ∀ i, tabs (fw.length + i) = tableTab prog s q β w (blocks.getD i default))
    (p : List E) (hp : p.length = busDepth prog s) (forms : List (List Form))
    (h6 : forms.length = 6) (h3 : ∀ t < 6, (forms.getD t []).length = 3)
    (hzero : ∀ t, (forms.getD t []).getD side {} = {}) :
    trueTotal prog s q p
        (accFold side w β (List.zip (sideSels fw blocks p fw.length blocks.length) blocks) forms)
        side =
      sideTotal prog s fw blocks tabs p +
        padSum w β p (List.zip (sideSels fw blocks p fw.length blocks.length) blocks) := by
  have hspec := (accFold_spec side hside w β
    (List.zip (sideSels fw blocks p fw.length blocks.length) blocks) forms h6 h3
    (owner_lt_six s hown _)).2.2.2
  unfold trueTotal
  simp only [hspec, hzero, evaluate_empty, zero_add]
  rw [sum_owner_tables prog s q hP β w p (fun t ↦ hp ▸ tau_le_busDepth prog s t) _
    (zip_owned s hown _)]
  refine congrArg (· + _) ?_
  rw [sideSels, sum_zip_range, sideTotal]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [htabs, hp]

/-- A claim on an instance column at a point of its variables, valued by the column's list,
is true. -/
theorem trueClaim_col (c : Col) (col : ℕ) (hcol : col = refCol c) (z : List E)
    (hz : z.length = kappa prog s c) :
    TrueClaim prog s q ⟨col, z, multilinearEval (colList prog s q c) z⟩ := by
  refine ⟨c, ⟨z.toArray, by simpa using hz⟩, ?_⟩
  have h := multilinearEval_colList prog s q c ⟨z.toArray, by simpa using hz⟩
  simp only [Vector.toList_mk] at h
  rw [hcol, h]
  rfl

/-- **The honest bus result's claims are true.** -/
theorem trueClaims_honestBus (alphas : List E) (β : E) (p bp : List E)
    (hp : p.length = busDepth prog s) :
    TrueClaims prog s q (honestBus prog s q alphas β p bp).claims := by
  have hm : (p.take s.logMem).length = s.logMem :=
    length_take_of_le (hp ▸ logMem_le_busDepth prog s)
  have hb : (p.take prog.logSize).length = prog.logSize :=
    length_take_of_le (hp ▸ logSize_le_busDepth prog s)
  intro cl hcl
  simp only [honestBus, busOut, memVals, mfVal, bfVal, List.zipWith_cons_cons,
    List.zipWith_nil_left,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hcl
  rcases hcl with rfl | rfl | rfl | rfl
  · exact trueClaim_col prog s q (memCol 0) _ (refCol_memCol 0).symm _ hm
  · exact trueClaim_col prog s q (memCol 1) _ (refCol_memCol 1).symm _ hm
  · exact trueClaim_col prog s q (memCol 2) _ (refCol_memCol 2).symm _ hm
  · exact trueClaim_col prog s q bfcntCol _ refCol_bfcntCol.symm _ hb

/-- The table blocks' coordinates have degree at most two. -/
theorem blocks_deg2 (side : Side) (sels : List E) :
    ∀ x ∈ List.zip sels ((List.ofFn fun t : Fin 6 ↦
      (refSide t side).map fun c ↦ (⟨s.τ t, s.rows t, c, t⟩ : BusBlock)).flatten),
      ∀ c ∈ x.2.coordinates, Deg2 c := by
  intro x hx c hc
  obtain ⟨l, hl, hbl⟩ := List.mem_flatten.mp (List.of_mem_zip hx).2
  obtain ⟨t, rfl⟩ := List.mem_ofFn.mp hl
  obtain ⟨cs, hcs, hx2⟩ := List.mem_map.mp hbl
  rw [← hx2] at hc
  intro term hterm
  cases side
  · exact (((refForm_terms t).1 cs hcs).2 c hc term hterm).1
  · exact (((refForm_terms t).2 cs hcs).2 c hc term hterm).1

theorem countBlocks_deg2 (sels : List E) :
    ∀ x ∈ List.zip sels (countBlocks s), ∀ c ∈ x.2.coordinates, Deg2 c := by
  intro x hx c hc
  obtain ⟨l, hl, hbl⟩ := List.mem_flatten.mp (List.of_mem_zip hx).2
  obtain ⟨t, rfl⟩ := List.mem_ofFn.mp hl
  obtain ⟨col, -, hx2⟩ := List.mem_map.mp hbl
  rw [← hx2] at hc
  simp only [List.mem_singleton] at hc
  subst hc
  intro term hterm
  simp [Form.col] at hterm
  rw [hterm]; simp

/-- **The honest bus result is true.** -/
theorem busGood_honestBus (hP : (inst prog s).PaddingHonest q) (alphas : List E)
    (halpha : alphas.length = 16) (β : E) (p bp : List E) (hp : p.length = busDepth prog s) :
    BusGood prog s q (honestBus prog s q alphas β p bp) := by
  set w := alphas
  set F0 : List (List Form) := tables.map fun _ ↦ [{}, {}, {}]
  set l1 := List.zip (sideSels (fwLogs prog s) (pushBlocks s) p 3 (pushBlocks s).length)
    (pushBlocks s)
  set l2 := List.zip (sideSels (fwLogs prog s) (pullBlocks s) p 3 (pullBlocks s).length)
    (pullBlocks s)
  set l3 := List.zip (sideSels [] (countBlocks s) p 0 (countBlocks s).length) (countBlocks s)
  set F1 := accFold 0 w β l1 F0
  set F2 := accFold 1 w β l2 F1
  set F3 := accFold 2 [1] 0 l3 F2
  have hF : (honestBus prog s q alphas β p bp).forms = F3 :=
    honestBus_forms prog s q alphas β p bp
  obtain ⟨a1, b1, c1, -⟩ := accFold_spec 0 (by norm_num) w β l1 F0 forms0_length forms0_row
    (owner_lt_six s (pushBlocks_owned s) _)
  obtain ⟨a2, b2, c2, -⟩ := accFold_spec 1 (by norm_num) w β l2 F1 a1 b1
    (owner_lt_six s (pullBlocks_owned s) _)
  obtain ⟨a3, b3, c3, -⟩ := accFold_spec 2 (by norm_num) [1] 0 l3 F2 a2 b2
    (owner_lt_six s (countBlocks_owned s) _)
  refine ⟨trueClaims_honestBus prog s q alphas β p bp hp, rfl, fun t ↦ ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [honestBus_point, hp]; exact tau_le_busDepth prog s t
  · rw [hF]; exact a3
  · rw [hF]; exact b3
  · rw [hF]
    exact accFold_deg2 _ _ _ _ _ (accFold_deg2 _ _ _ _ _ (accFold_deg2 _ _ _ _ _ forms0_deg
      (blocks_deg2 s .push _)) (blocks_deg2 s .pull _)) (countBlocks_deg2 s _)
  · rw [honestBus_totals prog s q alphas halpha β p bp hp]; rfl
  · intro side hside
    rw [honestBus_totals prog s q alphas halpha β p bp hp, hF, honestBus_point]
    rcases side with _ | _ | _ | side
    · rw [trueTotal_congr prog s q p 0 fun t ↦ c3 t 0 (by norm_num),
        trueTotal_congr prog s q p 0 fun t ↦ c2 t 0 (by norm_num)]
      exact (fold_trueTotal prog s q hP 0 (by norm_num) w β (pushBlocks s) (pushBlocks_owned s)
        (fwLogs prog s) _ (fun i ↦ pushTabs_add_three prog s q β w i) p hp F0 forms0_length
        forms0_row fun t ↦ forms0_entry t 0).symm
    · rw [trueTotal_congr prog s q p 1 fun t ↦ c3 t 1 (by norm_num)]
      exact (fold_trueTotal prog s q hP 1 (by norm_num) w β (pullBlocks s) (pullBlocks_owned s)
        (fwLogs prog s) _ (fun i ↦ pullTabs_add_three prog s q β w i) p hp F1 a1 b1
        fun t ↦ (c1 t 1 (by norm_num)).trans (forms0_entry t 1)).symm
    · exact (fold_trueTotal prog s q hP 2 (by norm_num) [1] 0 (countBlocks s) (countBlocks_owned s)
        [] _ (fun i ↦ by simp [countTabs]) p hp F2 a2 b2
        fun t ↦ (c2 t 2 (by norm_num)).trans ((c1 t 2 (by norm_num)).trans
          (forms0_entry t 2))).symm
    · omega

end Honest

/-! ## The honest prover -/

/-- **The honest prover of the bus phase**: pass the grind for the push tree's depth, receive the
sixteen slot weights `w` and `β`, run the honest GKR over the three sides' leaves, send the memory
limbs' and the two finalize counts' extensions at the bus point, then prove the program's share of
the bytecode leaf; return the verifier's bus result. -/
noncomputable def hBus (prog : LeanIsaProgram) (s : Sizes) (q : Column (leanIsaμ prog s)) :
    Script BusResult :=
  (Script.grindBits (busGrindingBits (busDepth prog s))).bind fun _ ↦
  (Script.sampleN (2 ^ busBits)).bind fun w ↦ Script.sampleE.bind fun beta ↦
  (hGkr (busDepth prog s) (pushLeaves prog s q w beta) (pullLeaves prog s q w beta)
    (countLeaves prog s q)).bind fun g ↦
  (Script.sendList (memVals prog s q g.2.1)).bind fun _ ↦
  (Script.sendE (mfVal prog s q g.2.1)).bind fun _ ↦
  (Script.sendE (bfVal prog s q g.2.1)).bind fun _ ↦
  (hShare prog w (g.2.1.take prog.logSize)).bind fun sh ↦
  .ret (honestBus prog s q w beta g.2.1 sh.2.1)

attribute [local irreducible] Follows in
/-- **Perfect completeness of the bus phase.** For a stack satisfying the leanISA instance's
relation, whose push tree has depth below `64`, the honest prover follows the verifier program's
bus phase at the verifier's layout: every `require` holds (the depth, the shared root, the nonzero
count root, the bytecode share's last round and its value), and the result is true (`BusGood`):
true framework claims, and totals that are the true totals of the forms. -/
theorem follows_verifyBusBalance {prog : LeanIsaProgram} {s : Sizes} {input : PublicInput}
    {q : Column (leanIsaμ prog s)} (hD : busDepth prog s < 64)
    (hq : M3Honest (inst prog s) input q) (cs : Commits) :
    Follows (fun cs' a b ↦ cs' = cs ∧ a = b ∧ BusGood prog s q b) (hBus prog s q)
      (verifyBusBalance computedBytecodeValue (verifierLayout prog s)) cs := by
  obtain ⟨⟨-, hbal, hcnt, -, -⟩, hP⟩ := hq
  rw [verifyBusBalance_eq, busLayout_depth_verifier, hBus]
  simp only [VerifierProgram.require, hD, ↓reduceIte, VerifierProgram.ret_bind,
    VerifierProgram.bind_eq]
  refine Follows.bind (fun cs₀ _ _ h ↦ ?_) _ _ _ (Follows.grindBits_grindP _ cs)
  subst h
  refine Follows.bind (fun cs₁ a b h ↦ ?_) _ _ _ (Follows.sampleN_sampleN _ (2 ^ busBits))
  obtain ⟨rfl, rfl, hlen⟩ := h
  have hlen' : a.length = 16 := hlen
  refine Follows.bind (fun cs₂ c c' h ↦ ?_) _ _ _ (Follows.sampleE_sampleE cs₁)
  obtain ⟨rfl, rfl⟩ := h
  refine Follows.bind (fun cs₃ g g' h ↦ ?_) _ _ _
    (follows_verifyGkrGrandProducts (busDepth prog s) _ _ _ (length_pushLeaves prog s q a c)
      (length_pullLeaves prog s q a c) (length_countLeaves prog s q)
      (prod_push_eq_pull prog s q hbal a hlen' c) cs₂)
  obtain ⟨rfl, rfl, hcr, hpl, htv⟩ := h
  have hne : g.1 ≠ 0 := hcr ▸ prod_countLeaves_ne_zero prog s q hcnt
  simp only [hne, ne_eq, not_false_eq_true, ↓reduceIte, VerifierProgram.ret_bind]
  refine Follows.bind (fun cs₄ _ mem h ↦ ?_) _ _ _
    (Follows.sendList_readN cs₃ (memVals prog s q g.2.1))
  obtain ⟨rfl, rfl⟩ := h
  refine Follows.bind (fun cs₅ _ mf h ↦ ?_) _ _ _ (Follows.sendE_readE _ cs₄)
  obtain ⟨rfl, rfl⟩ := h
  refine Follows.bind (fun cs₆ _ bf h ↦ ?_) _ _ _ (Follows.sendE_readE _ cs₅)
  obtain ⟨rfl, rfl⟩ := h
  have hz : (g.2.1.take prog.logSize).length = prog.logSize :=
    length_take_of_le (hpl ▸ logSize_le_busDepth prog s)
  change Follows _ _ ((bytecodeShare a (g.2.1.take prog.logSize)).bind _) cs₆
  refine Follows.bind (fun cs₇ sh sh' h ↦ ?_) _ _ _
    (follows_bytecodeShare prog a _ hlen' hz cs₆)
  obtain ⟨rfl, rfl, hsh, hval⟩ := h
  obtain ⟨share, bp, value⟩ := sh
  simp only at hsh hval ⊢
  subst hsh
  change Follows _ _ ((VerifierProgram.require
    (multilinearEval ((bytecodeWords prog).map ofK) bp = value)).bind _) cs₇
  simp only [← hval, VerifierProgram.require, ↓reduceIte, VerifierProgram.ret_bind]
  have heq : honestBus prog s q a c g.2.1 bp = busOut (verifierLayout prog s) a c g.2.1 g.2.2
      (memVals prog s q g.2.1) (mfVal prog s q g.2.1) (bfVal prog s q g.2.1)
      (bcShare prog a (g.2.1.take prog.logSize)) bp := by
    rw [honestBus, htv]
    rfl
  exact Follows.ret_ret ⟨rfl, heq, heq ▸ busGood_honestBus prog s q hP a hlen' c g.2.1 bp hpl⟩

end
end LeanVM.Protocol.EndToEnd.Complete
