/-
  LeanVM.Protocol.EndToEnd.Complete.BusTables

  The table blocks of the bus, honestly: the leaves of every block the Python's `bus_layout` gives
  a table (one per flush of a side, one per count column), their product, which is the instance's
  flush tuples' fingerprint product, and the count leaves, which are nonzero.
-/

module

public import LeanVM.Protocol.EndToEnd.Complete.BusFramework
public import LeanVM.Protocol.EndToEnd.Complete.Flushes

/-!
# The table blocks

The verifier program's bus blocks (`busBlocks`, `python-verifier/verifier.py:888-898` at leanVM
`3a37fb6e1c7423e36b67d1cac4eda70c3ad4dd45`) are, per table in opcode order, one block per pushed
tuple, one per pulled tuple, and one per count column, each of the table's height and row count.
Their honest leaves are, on an executed row, `β` plus the fingerprint of the flushed tuple
(`tableTab`, through `blockVal`, the value `accumulate_side` gives the block's forms at the row),
and `1` on a padding row.

* `accumulateSide_fst`, `accumulateSide_snd`: `accumulate_side`'s fold is the forms' fold
  (`accFold`) and the padding term (`padSum`);

* `busBlocks_eq`: the blocks, table by table;
* `prod_tables`: the product of a side's table leaves is the product of the fingerprints of the
  instance's flush tuples of that side (its executed rows') (`M3Instance.flushTuples`), by the flush fidelity
  `pyFlush_eval`;
* `zero_not_mem_countTab`: no count leaf is zero, when the instance's count cells are nonzero
  (`CountsNonzero`), by `pyCountColumns`.
-/

namespace LeanVM.Protocol.EndToEnd.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier LeanVM.Protocol.LeanIsa
open LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.Whir.Complete
open Finset

@[expose] public section

/-! ## The blocks -/

/-- Each table's opcode is its index. -/
theorem opcode_tables : ∀ t : Fin 6, (tables.getD t default).opcode = t := by decide

/-- The rows `busBlocks` walks: the tables with their heights and row counts. -/
theorem zip_tables_tableLogs (s : Sizes) :
    List.zip tables (List.zip (tableLogs s) (tableRows s)) =
      List.ofFn fun t : Fin 6 ↦ (tables.getD t default, s.τ t, s.rows t) := by
  apply List.ext_getElem
  · simp [tableLogs, tableRows, tables]
  · intro i h1 h2
    simp only [List.getElem_zip, List.getElem_ofFn, tableLogs, tableRows]
    rw [List.getD_eq_getElem _ _ (by simp at h2; simp [tables]; omega)]

/-- A side's table blocks, table by table. -/
theorem busBlocks_eq (s : Sizes) :
    busBlocks (tableLogs s) (tableRows s) =
      ((List.ofFn fun t : Fin 6 ↦
          (pySide t .push).map fun c ↦ (⟨s.τ t, s.rows t, c, t⟩ : BusBlock)).flatten,
        (List.ofFn fun t : Fin 6 ↦
          (pySide t .pull).map fun c ↦ (⟨s.τ t, s.rows t, c, t⟩ : BusBlock)).flatten,
        (List.ofFn fun t : Fin 6 ↦ (tables.getD t default).countColumns.map fun l ↦
          (⟨s.τ t, s.rows t, [Form.col l], t⟩ : BusBlock)).flatten) := by
  simp only [busBlocks, zip_tables_tableLogs, List.flatMap, List.map_ofFn]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> congr 1

/-- Every block of a flattened table-by-table list is owned by a table, at its height. -/
theorem mem_flatten_ofFn {α : Type} (s : Sizes) (f : Fin 6 → List α) (g : Fin 6 → α → BusBlock)
    (hg : ∀ t a, (g t a).owner = t ∧ (g t a).logRows = s.τ t) (b : BusBlock)
    (hb : b ∈ (List.ofFn fun t ↦ (f t).map (g t)).flatten) :
    ∃ t : Fin 6, b.owner = t ∧ b.logRows = s.τ t := by
  obtain ⟨l, hl, hbl⟩ := List.mem_flatten.mp hb
  obtain ⟨t, rfl⟩ := List.mem_ofFn.mp hl
  obtain ⟨a, -, rfl⟩ := List.mem_map.mp hbl
  exact ⟨t, hg t a⟩

/-! ## A side's decomposition -/

theorem getD_map_range (n j : ℕ) (F : ℕ → E) (hj : j < n) :
    ((List.range n).map F).getD j 0 = F j := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  simp


/-- The selectors of a side's blocks at a point. -/
def sideSels (fw : List ℕ) (blocks : List BusBlock) (p : List E) (k n : ℕ) : List E :=
  (List.range n).map fun i ↦ blockSel (sideSizes fw blocks) p.length (k + i) p

/-- A fold whose step updates a pair componentwise is the pair of the two folds. -/
theorem foldl_pair {α β' γ : Type} (F : α × β' → γ → α × β') (f : α → γ → α) (g : β' → γ → β')
    (hF : ∀ a b x, F (a, b) x = (f a x, g b x)) :
    ∀ (l : List γ) (a : α) (b : β'), l.foldl F (a, b) = (l.foldl f a, l.foldl g b)
  | [], _, _ => rfl
  | x :: l, a, b => by rw [List.foldl_cons, hF, foldl_pair F f g hF l]; rfl

/-- A fold that adds a term per item adds their sum. -/
theorem foldl_add_map {γ : Type} (h : γ → E) :
    ∀ (l : List γ) (a : E), l.foldl (fun acc x ↦ acc + h x) a = a + (l.map h).sum
  | [], a => by simp
  | x :: l, a => by rw [List.foldl_cons, foldl_add_map h l, List.map_cons, List.sum_cons]; ring

/-- The forms' step of `accumulate_side`. -/
private abbrev formStep (side : ℕ) (w : List E) (β : E) (forms : List (List Form))
    (x : E × BusBlock) : List (List Form) :=
  forms.modify x.2.owner fun row ↦ row.modify side fun f ↦ f.addScaled (blockForm x.2 w β) x.1

/-- The padding term's step of `accumulate_side`. -/
private abbrev padStep (w : List E) (β : E) (p : List E) (pr : E) (x : E × BusBlock) : E :=
  pr + x.1 * paddingWeight (p.take x.2.logRows) x.2.rows *
    ((blockForm x.2 w β).evaluate (((tables.getD x.2.owner default).padding).getD · 0) + 1)

private theorem foldl_formStep (side : ℕ) (w : List E) (β : E) (l : List (E × BusBlock))
    (forms : List (List Form)) : l.foldl (formStep side w β) forms = accFold side w β l forms :=
  rfl

private theorem foldl_padStep (w : List E) (β : E) (p : List E) (l : List (E × BusBlock)) :
    l.foldl (padStep w β p) 0 = padSum w β p l := by
  rw [foldl_add_map, zero_add, padSum]
  simp only [evaluate_blockForm]

/-- `accumulate_side`'s forms: the fold over the side's blocks with their selectors. -/
theorem accumulateSide_fst (forms : List (List Form)) (side : ℕ) (fw : List ℕ)
    (blocks : List BusBlock) (fps w : List E) (β : E) (p : List E) (tv : E) :
    (accumulateSide forms side blocks (busLayout fw blocks) fps w β p tv).1 =
      accFold side w β (List.zip (sideSels fw blocks p fw.length blocks.length) blocks) forms := by
  unfold accumulateSide
  dsimp only
  rw [busLayout_tables, foldl_pair _ (formStep side w β) (padStep w β p)]
  · rfl
  · intro a b x
    obtain ⟨sel, blk⟩ := x
    rfl

/-- `accumulate_side`'s total: the tree value, the framework, the unused leaves, and the padding
rows. -/
theorem accumulateSide_snd (forms : List (List Form)) (side : ℕ) (fw : List ℕ)
    (blocks : List BusBlock) (fps w : List E) (β : E) (p : List E) (tv : E) :
    (accumulateSide forms side blocks (busLayout fw blocks) fps w β p tv).2 =
      tv + dot (sideSels fw blocks p 0 fw.length) (fps.map (β + ·)) +
        (sumE (sideSels fw blocks p 0 fw.length ++
          sideSels fw blocks p fw.length blocks.length) + 1) +
        padSum w β p (List.zip (sideSels fw blocks p fw.length blocks.length) blocks) := by
  unfold accumulateSide
  dsimp only
  rw [busLayout_framework, busLayout_tables, foldl_pair _ (formStep side w β) (padStep w β p)]
  · simp only [sideSels, zero_add, foldl_padStep]
  · intro a b x
    obtain ⟨sel, blk⟩ := x
    rfl

/-- **A side's total is its table blocks' selector-weighted extensions**, when the tree value is
the honest leaves' extension and every framework block extends to `β` plus the verifier's
fingerprint. -/
theorem accumulateSide_total (forms : List (List Form)) (side : ℕ) (fw : List ℕ)
    (blocks : List BusBlock) (fps w : List E) (β : E) (tabs : ℕ → List E) (D : ℕ)
    (htab : ∀ b < (sideSizes fw blocks).length,
      (tabs b).length = 2 ^ (sideSizes fw blocks).getD b 0)
    (hD : blockTotal (sideSizes fw blocks) ≤ 2 ^ D) (p : List E) (hp : p.length = D)
    (hfps : fps.length = fw.length)
    (hfw : ∀ b < fw.length,
      multilinearEval (tabs b) (p.take (fw.getD b 0)) = β + fps.getD b 0) :
    (accumulateSide forms side blocks (busLayout fw blocks) fps w β p
        (multilinearEval (stackLeaves (sideSizes fw blocks) tabs D) p)).2 =
      ∑ i ∈ range blocks.length, blockSel (sideSizes fw blocks) D (fw.length + i) p *
        multilinearEval (tabs (fw.length + i)) (p.take (blocks.getD i default).logRows) +
      padSum w β p (List.zip (sideSels fw blocks p fw.length blocks.length) blocks) := by
  have hn : (sideSizes fw blocks).length = fw.length + blocks.length := by simp [sideSizes]
  rw [accumulateSide_snd, multilinearEval_stackLeaves _ tabs D htab hD p hp, hn, sum_range_add,
    sum_range_add]
  have hfwsz : ∀ b < fw.length, (sideSizes fw blocks).getD b 0 = fw.getD b 0 := fun b hb ↦ by
    rw [sideSizes, List.getD_append _ _ _ _ hb]
  have hblsz : ∀ i < blocks.length,
      (sideSizes fw blocks).getD (fw.length + i) 0 = (blocks.getD i default).logRows := by
    intro i hi
    rw [sideSizes, List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left,
      List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
      List.getD_eq_getElem _ _ hi]
  have hknown : dot (sideSels fw blocks p 0 fw.length) (fps.map (β + ·)) =
      ∑ b ∈ range fw.length, blockSel (sideSizes fw blocks) D b p * (β + fps.getD b 0) := by
    rw [dot_eq_sum _ _ (by simp [sideSels, hfps])]
    simp only [sideSels, List.length_map, List.length_range]
    refine sum_congr rfl fun b hb ↦ ?_
    have hb' := mem_range.mp hb
    rw [getD_map_range _ _ _ hb', zero_add, hp, List.getD_eq_getElem _ _ (by simp [hfps, hb'])]
    simp [List.getElem?_eq_getElem (show b < fps.length by omega)]
  have hpad : sumE (sideSels fw blocks p 0 fw.length ++
      sideSels fw blocks p fw.length blocks.length) =
      ∑ b ∈ range fw.length, blockSel (sideSizes fw blocks) D b p +
        ∑ i ∈ range blocks.length, blockSel (sideSizes fw blocks) D (fw.length + i) p := by
    rw [sumE_eq, List.sum_append, sideSels, sideSels, ← sum_range_eq_list,
      ← sum_range_eq_list, hp]
    simp only [zero_add]
  have hfw' : ∑ b ∈ range fw.length, blockSel (sideSizes fw blocks) D b p *
      multilinearEval (tabs b) (p.take ((sideSizes fw blocks).getD b 0)) =
      ∑ b ∈ range fw.length, blockSel (sideSizes fw blocks) D b p * (β + fps.getD b 0) :=
    sum_congr rfl fun b hb ↦ by rw [hfwsz b (mem_range.mp hb), hfw b (mem_range.mp hb)]
  have htab' : ∑ i ∈ range blocks.length, blockSel (sideSizes fw blocks) D (fw.length + i) p *
      multilinearEval (tabs (fw.length + i))
        (p.take ((sideSizes fw blocks).getD (fw.length + i) 0)) =
      ∑ i ∈ range blocks.length, blockSel (sideSizes fw blocks) D (fw.length + i) p *
        multilinearEval (tabs (fw.length + i)) (p.take (blocks.getD i default).logRows) :=
    sum_congr rfl fun i hi ↦ by rw [hblsz i (mem_range.mp hi)]
  rw [hknown, hpad, hfw', htab', add_left_inj]
  linear_combination (∑ b ∈ range fw.length, blockSel (sideSizes fw blocks) D b p *
    (β + fps.getD b 0) + 1) * two_eq_zero_E

/-! ## The leaves -/

section Leaves

variable (prog : Program) (s : Sizes) (q : Column (leanIsaμ prog s))

/-- Row `x` of table `t`, for natural-number indices: `rowVal`, `0` outside the tables. -/
def rowAt (t x : ℕ) : ℕ → E :=
  if h : t < 6 then
    if hx : x < 2 ^ s.τ ⟨t, h⟩ then rowVal prog s q ⟨t, h⟩ ⟨x, hx⟩ else fun _ ↦ 0
  else fun _ ↦ 0

theorem rowAt_eq (t : Fin 6) (x : Fin (2 ^ s.τ t)) :
    rowAt prog s q t x = rowVal prog s q t x := by
  simp [rowAt, t.isLt, x.isLt]

/-- A table block's honest leaves: `β` plus the block's fingerprint at every executed row of its
owner, `1` at a padding row. -/
def tableTab (β : E) (w : List E) (b : BusBlock) : List E :=
  (List.range (2 ^ b.logRows)).map fun x ↦
    if x < b.rows then blockVal β w b (rowAt prog s q b.owner x) else 1

/-- Ones past the first `n` entries leave the product of the first `n`. -/
theorem prod_range_ite (f : ℕ → E) {n : ℕ} : ∀ {N : ℕ}, n ≤ N →
    ((List.range N).map fun x ↦ if x < n then f x else 1).prod = ((List.range n).map f).prod
  | 0, h => by obtain rfl : n = 0 := by omega
               rfl
  | N + 1, h => by
    rcases Nat.lt_or_ge N n with hN | hN
    · obtain rfl : n = N + 1 := by omega
      exact congrArg List.prod (List.map_congr_left fun x hx ↦ by simp [List.mem_range.mp hx])
    · rw [List.range_succ, List.map_append, List.prod_append, prod_range_ite f hN]
      simp [Nat.not_lt.mpr hN]

theorem length_tableTab (β : E) (w : List E) (b : BusBlock) :
    (tableTab prog s q β w b).length = 2 ^ b.logRows := by simp [tableTab]

/-- A product over a flattened list of lists of the tables. -/
theorem prod_flatten_ofFn {α : Type} (f : Fin 6 → List α) (T : α → E) :
    (((List.ofFn f).flatten).map T).prod = ∏ t : Fin 6, ((f t).map T).prod := by
  rw [List.map_flatten, List.prod_flatten, List.map_ofFn, List.map_ofFn, List.prod_ofFn]
  rfl

/-- Products over a list and over a finite type commute. -/
theorem prod_map_prod_comm {α ι : Type} [Fintype ι] (l : List α) (f : α → ι → E) :
    (l.map fun a ↦ ∏ x, f a x).prod = ∏ x, (l.map fun a ↦ f a x).prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, prod_mul_distrib]

/-- The block's fingerprint at a row is `β` plus the weights against its sixteen coordinates. -/
theorem blockVal_eq (β : E) (w : List E) (hw : w.length = 16) (b : BusBlock)
    (hb : b.coordinates.length ≤ 16) (r : ℕ → E) :
    blockVal β w b r =
      β + dot w ((List.range 16).map fun k ↦ (b.coordinates.getD k {}).evaluate r) := by
  rw [blockVal, dot_eq_sum _ _ (by simp [hw]), hw]
  refine congrArg (β + ·) ?_
  rw [show 16 = b.coordinates.length + (16 - b.coordinates.length) by omega, sum_range_add]
  have hz : ∑ x ∈ range (16 - b.coordinates.length),
      w.getD (b.coordinates.length + x) 0 *
        ((List.range (b.coordinates.length + (16 - b.coordinates.length))).map
          fun k ↦ (b.coordinates.getD k {}).evaluate r).getD (b.coordinates.length + x) 0 = 0 := by
    refine sum_eq_zero fun x hx ↦ ?_
    rw [getD_map_range _ _ _ (by have := mem_range.mp hx; omega),
      List.getD_eq_default b.coordinates _ (by omega), evaluate_empty, mul_zero]
  rw [hz, add_zero]
  have hl : (b.coordinates.zipIdx.map fun cs ↦ w.getD cs.2 0 * cs.1.evaluate r) =
      (List.range b.coordinates.length).map fun k ↦
        w.getD k 0 * (b.coordinates.getD k {}).evaluate r := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.length_map, List.length_zipIdx] at h1
    simp [List.getElem_zipIdx, List.getElem?_eq_getElem h1]
  rw [hl, ← sum_range_eq_list]
  refine sum_congr rfl fun k hk ↦ ?_
  rw [getD_map_range _ _ _ (by have := mem_range.mp hk; omega)]

/-- A finite product over the range is the list product. -/
theorem prod_range_eq_list (n : ℕ) (H : ℕ → E) :
    ∏ b ∈ range n, H b = ((List.range n).map H).prod := by
  rw [← List.toFinset_range, List.prod_toFinset _ (List.nodup_range)]

/-- A table block's product: the fingerprints of its tuple at every executed row of its table. -/
theorem prod_tableTab (β : E) (w : List E) (hw : w.length = 16) (t : Fin 6) (c : List Form)
    (hc : c.length ≤ 16) :
    (tableTab prog s q β w ⟨s.τ t, s.rows t, c, t⟩).prod =
      ∏ x : Fin (s.rows t), (β + dot w ((List.range 16).map fun k ↦
        (c.getD k {}).evaluate (rowVal prog s q t (Fin.castLE (s.rows_le t) x)))) := by
  rw [tableTab, prod_range_ite _ (s.rows_le t), ← prod_range_eq_list, Finset.prod_range]
  refine Finset.prod_congr rfl fun x _ ↦ ?_
  simp only
  rw [show (x : ℕ) = (Fin.castLE (s.rows_le t) x : ℕ) from rfl, rowAt_eq prog s q t,
    blockVal_eq β w hw _ hc]

/-- A product over the listed rows of every listed item. -/
theorem prod_flatMap_rows {α β' γ : Type} (L : List α) (rs : List γ) (v : α → γ → β')
    (φ : β' → E) :
    ((L.flatMap fun f ↦ rs.map (v f)).map φ).prod =
      (rs.map fun x ↦ (L.map fun f ↦ φ (v f x)).prod).prod := by
  rw [List.map_flatMap, prod_flatMap_E, ← prod_map_prod_comm_list]
  refine congrArg List.prod (List.map_congr_left fun f _ ↦ ?_)
  rw [List.map_map]
  rfl
where
  prod_map_prod_comm_list (l : List α) (f : α → γ → E) :
      (l.map fun a ↦ (rs.map (f a)).prod).prod = (rs.map fun x ↦ (l.map fun a ↦ f a x).prod).prod := by
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons, List.prod_cons, ih]
      clear ih
      induction rs with
      | nil => simp
      | cons x rs ihr => simp only [List.map_cons, List.prod_cons, ← ihr]; ring

/-- The instance's flush tuples of a side, fingerprinted, table by table and executed row by
executed row. -/
theorem prod_flushTuples (β : E) (w : List E) (side : Side) :
    (((inst prog s).flushTuples q side).map (fpV β w)).prod =
      ∏ t : Fin 6, ∏ x : Fin (s.rows t),
        (((LeanIsa.flushes (opIdx t)).filter fun f ↦ decide (f.1 = side)).map fun f ↦
          β + dot w (f.2.toList.map fun P ↦
            ofK (P.eval ((inst prog s).row q (opIdx t) (Fin.castLE (s.rows_le t) x))))).prod := by
  rw [M3Instance.flushTuples, List.map_flatMap, prod_flatMap_E, ← Fin.prod_univ_def]
  set G : Fin 9 → E := fun j ↦
    ((((inst prog s).flushes j).filter fun f ↦ decide (f.1 = side)).flatMap
    fun f ↦ ((inst prog s).executed j).map fun x ↦
      f.2.map fun P ↦ P.eval ((inst prog s).row q j x)).map (fpV β w) |>.prod with hG
  show ∏ j : Fin 9, G j = _
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_succ]
  have e0 : G 0 = 1 := rfl
  have e1 : G (Fin.succ 0) = 1 := rfl
  have e2 : G (Fin.succ (Fin.succ 0)) = 1 := rfl
  rw [e0, e1, e2, one_mul, one_mul, one_mul]
  refine Finset.prod_congr rfl fun t _ ↦ ?_
  have ht : t.succ.succ.succ = opIdx t := Fin.ext (by simp [opIdx])
  rw [ht]
  have he : (inst prog s).executed (opIdx t) =
      (List.finRange (s.rows t)).map (Fin.castLE (s.rows_le t)) := M3Instance.executed_eq _ _
  simp only [hG]
  rw [prod_flatMap_rows, he, Fin.prod_univ_def]
  refine congrArg List.prod ((List.map_map ..).trans (List.map_congr_left fun x _ ↦
    congrArg List.prod (List.map_congr_left fun f _ ↦ ?_)))
  simp only [fpV, Vector.toList_map, List.map_map]
  rfl

/-- **A side's table leaves multiply to the instance's flush tuples' fingerprints.** -/
theorem prod_tables (β : E) (w : List E) (hw : w.length = 16) (side : Side) :
    (((List.ofFn fun t : Fin 6 ↦
        (pySide t side).map fun c ↦ (⟨s.τ t, s.rows t, c, t⟩ : BusBlock)).flatten).map
        fun b ↦ (tableTab prog s q β w b).prod).prod =
      (((inst prog s).flushTuples q side).map (fpV β w)).prod := by
  rw [prod_flatten_ofFn, prod_flushTuples]
  refine Finset.prod_congr rfl fun t _ ↦ ?_
  have hc : ∀ c ∈ pySide t side, c.length ≤ 16 := by
    intro c hc
    cases side
    · exact ((pyForm_terms t).1 c hc).1
    · exact ((pyForm_terms t).2 c hc).1
  simp only [List.map_map, Function.comp_def]
  rw [List.map_congr_left fun c hc' ↦ prod_tableTab prog s q β w hw t c (hc c hc')]
  rw [prod_map_prod_comm]
  refine Finset.prod_congr rfl fun x _ ↦ ?_
  have h := congrArg (List.map fun l ↦ β + dot w l)
    (pyFlush_eval t side ((inst prog s).row q (opIdx t) (Fin.castLE (s.rows_le t) x)))
  simp only [List.map_map] at h
  exact congrArg List.prod h

/-- **No count leaf is zero**: a count block's leaves are its count column's executed cells and
ones. -/
theorem zero_not_mem_countTab (hcnt : (inst prog s).CountsNonzero q) (t : Fin 6) (l : ℕ)
    (hl : l ∈ (tables.getD t default).countColumns) :
    (0 : E) ∉ tableTab prog s q 0 [1] ⟨s.τ t, s.rows t, [Form.col l], t⟩ := by
  rw [pyCountColumns t] at hl
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hl
  intro h0
  obtain ⟨x, hx, hx0⟩ := List.mem_map.mp h0
  have hx' : x < 2 ^ s.τ t := by simpa using hx
  split_ifs at hx0 with hr
  · rw [rowAt_eq prog s q t ⟨x, hx'⟩] at hx0
    simp [blockVal, Form.col, evaluate_eq_sum, rowVal, Verifier.gpow] at hx0
    have hne := hcnt (opIdx t) i hi ⟨x, hx'⟩ hr
    exact hne (ofK_injective (hx0.trans (map_zero (algebraMap K E)).symm))
  · exact one_ne_zero hx0

/-- The count side's leaves multiply to a nonzero root. -/
theorem prod_countTabs_ne_zero (hcnt : (inst prog s).CountsNonzero q) (sizes : List ℕ)
    (blocks : List BusBlock) (hsz : sizes.length = blocks.length)
    (hb : ∀ b ∈ blocks, ∃ t : Fin 6, ∃ l ∈ (tables.getD t default).countColumns,
      b = ⟨s.τ t, s.rows t, [Form.col l], t⟩) (D : ℕ) :
    (stackLeaves sizes (fun b ↦ tableTab prog s q 0 [1] (blocks.getD b default)) D).prod ≠ 0 := by
  rw [prod_stackLeaves]
  refine List.prod_ne_zero fun h0 ↦ ?_
  obtain ⟨b, hbr, hb0⟩ := List.mem_map.mp h0
  have hbl : b < blocks.length := by rw [← hsz]; exact List.mem_range.mp hbr
  rw [List.getD_eq_getElem _ _ hbl] at hb0
  obtain ⟨t, l, hl, he⟩ := hb _ (List.getElem_mem hbl)
  rw [he] at hb0
  exact zero_not_mem_countTab prog s q hcnt t l hl (List.prod_eq_zero_iff.mp hb0)

end Leaves

end
end LeanVM.Protocol.EndToEnd.Complete
