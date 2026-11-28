/-
  LeanVM.Prover.Complete.Link.TailOut

  What the link's tail returns on the honest message holds (`LinkOut`).
-/

module

public import LeanVM.Prover.Complete.Link.TailIndex
import LeanVM.Parameters.Field

/-!
# The link's tail: what it returns holds

`tailVia`'s end on the honest message: its column claims are the sent extensions, its memory term
`M_1`, its ring claim the pointer columns' bit slices under `eq(q*, ·)`.

* `tailView_rowSideOf`: `rowSideOf`'s fold keeps, of its accumulator, each table's row point and
  sent values (`columns`), one ring piece per pointer column (`pieces`, its scale `eq(q*, q)` for
  the column's place `q`), the count `q` and the unread values, in closed form;
* `honestTail_end`: on the honest message, each table's sent values are its non-pointer columns'
  extensions at its row point, the pieces one per pointer column, the slices the message's, the
  memory term `M_1` at `r`'s low coordinates;
* `sliceHolds_columnSlices`: a pointer column's slices (`columnSlices`) are the extensions of its
  bit slices; `ringHolds_honestTail`: the ring claim holds of the stack;
* `linkOut_honestTail`: `LinkOut`; `linkTailHolds_of_value`: `LinkTailHolds` from the summand
  alone.
-/

@[expose] public section

namespace LeanVM.Prover.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Prover LeanVM.Protocol.Hotwire LeanVM.Protocol.Verifier.Defers Finset

/-! ## `rowSideOf`'s columns and pieces -/

/-- What `rowSideOf`'s fold keeps that the end reads: the columns, the ring pieces, the pointer
count and the unread values. -/
abbrev TailView : Type := List (List E × List (ℕ × E)) × List RingPiece × ℕ × List E

/-- A row side's view. -/
def tailView (rs : LinkRowSide) : TailView := (rs.columns, rs.pieces, rs.q, rs.sent)

/-- The ring piece of table `t`'s pointer column `pk.1`, at place `pk.2`. -/
def tailPiece (layout : Layout) (point eqQ : List E) (t : ℕ) (pk : ℕ × ℕ) : RingPiece :=
  { placement :=
      some ((layout.placements.getD (globalColumnBases.getD t 0 + pk.1) none).getD default)
    point := point
    scale := eqQ.getD pk.2 0 }

/-- One table's step of the view. -/
def tailOuterView (layout : Layout) (chi eqQ : List E) (v : TailView) (tt : Table × ℕ) : TailView :=
  let ptrs := (tables.map (·.links.pointers)).getD tt.2 []
  let cols := (List.range tt.1.width).filter fun c ↦ !ptrs.contains c
  let point := chi.take (layout.tableLogHeights.getD tt.2 0)
  (v.1 ++ [(point, cols.zip (v.2.2.2.take cols.length))],
    v.2.1 ++ (ptrs.zipIdx v.2.2.1).map (tailPiece layout point eqQ tt.2),
    v.2.2.1 + ptrs.length, v.2.2.2.drop cols.length)

theorem foldl_view {α β γ : Type} (π : β → γ) (G : γ → α → γ) {F : β → α → β}
    (hF : ∀ b a, π (F b a) = G (π b) a) : ∀ (L : List α) (b : β), π (L.foldl F b) = L.foldl G (π b)
  | [], _ => rfl
  | a :: L, b => by rw [List.foldl_cons, List.foldl_cons, foldl_view π G hF L, hF]

/-- One pointer column's step of the view. -/
def tailInnerView (layout : Layout) (point eqQ : List E) (t : ℕ) (v : TailView) (pk : ℕ × ℕ) :
    TailView :=
  (v.1, v.2.1 ++ [tailPiece layout point eqQ t (pk.1, v.2.2.1)], v.2.2.1 + 1, v.2.2.2)

theorem foldl_tailInnerView (layout : Layout) (point eqQ : List E) (t : ℕ) :
    ∀ (L : List (ℕ × ℕ)) (c : List (List E × List (ℕ × E))) (p : List RingPiece) (q : ℕ)
      (s : List E), L.foldl (tailInnerView layout point eqQ t) (c, p, q, s) =
        (c, p ++ ((L.map Prod.fst).zipIdx q).map (tailPiece layout point eqQ t), q + L.length, s)
  | [], c, p, q, s => by simp
  | pk :: L, c, p, q, s => by
    rw [List.foldl_cons, tailInnerView, foldl_tailInnerView layout point eqQ t L]
    simp only [List.map_cons, List.zipIdx_cons, List.length_cons, List.append_assoc,
      List.singleton_append, Prod.mk.injEq, true_and]
    exact ⟨by omega, trivial⟩

theorem map_fst_zipIdx {α : Type} (L : List α) : (L.zipIdx.map Prod.fst) = L := by
  simp

/-- `rowSideOf`'s fold, viewed. -/
theorem tailView_rowSideOf (layout : Layout) (htab : layout.tables = tables) (ch : LinkChallenges)
    (chi jump : List E) (eqZetaR shiftZetaR xBc pFp yMem m1 eq0R : E) (eqQ : List E)
    (maxShift : ℕ) (sent0 : List E) :
    tailView (rowSideOf layout ch chi jump eqZetaR shiftZetaR xBc pFp yMem m1 eq0R eqQ maxShift sent0) =
      tables.zipIdx.foldl (tailOuterView layout chi eqQ) ([], [], 0, sent0) := by
  unfold rowSideOf
  rw [htab]
  refine (foldl_view tailView (tailOuterView layout chi eqQ) (fun acc tt ↦ ?_) _ _).trans rfl
  obtain ⟨table, t⟩ := tt
  dsimp only [tailView]
  generalize hI : List.foldl (α := LinkRowSide) (β := ℕ × ℕ) _ _ _ = I
  have hv := congrArg tailView hI
  rw [foldl_view tailView (tailInnerView layout (chi.take (layout.tableLogHeights.getD t 0)) eqQ t)
    (fun b pk ↦ ?_)] at hv
  · dsimp only [tailView] at hv
    rw [foldl_tailInnerView, map_fst_zipIdx] at hv
    simp only [Prod.mk.injEq, List.length_zipIdx] at hv
    obtain ⟨h1, h2, h3, h4⟩ := hv
    rw [← h1, ← h2, ← h3, ← h4]
    rfl
  · obtain ⟨pointer, k⟩ := pk
    dsimp only [tailView]
    rfl

/-- Table `t`'s pointer columns. -/
abbrev tailPtrs (t : ℕ) : List ℕ := (tables.map (·.links.pointers)).getD t []

/-- Table `t`'s non-pointer columns, in order: the values the message sends for it. -/
def tailNP (t : ℕ) : List ℕ :=
  (List.range (tables.getD t default).width).filter fun c ↦ !(tailPtrs t).contains c

/-- The non-pointer values of the tables before `m`. -/
def tailNVBefore (m : ℕ) : ℕ := ((List.range m).map fun t ↦ (tailNP t).length).sum

/-- The pointer columns of the tables before `m`. -/
def tailQBefore (m : ℕ) : ℕ := ((List.range m).map fun t ↦ (tailPtrs t).length).sum

/-- **The view after the first `m` tables**, in closed form. -/
theorem foldl_tailOuterView (layout : Layout) (chi eqQ sent0 : List E) : ∀ m ≤ nTables,
    ((tables.zipIdx).take m).foldl (tailOuterView layout chi eqQ) ([], [], 0, sent0) =
      ((List.range m).map fun t ↦ (chi.take (layout.tableLogHeights.getD t 0),
          (tailNP t).zip ((sent0.drop (tailNVBefore t)).take (tailNP t).length)),
        (List.range m).flatMap (fun t ↦ ((tailPtrs t).zipIdx (tailQBefore t)).map
          (tailPiece layout (chi.take (layout.tableLogHeights.getD t 0)) eqQ t)),
        tailQBefore m, sent0.drop (tailNVBefore m))
  | 0, _ => by simp [tailQBefore, tailNVBefore]
  | m + 1, hm => by
    have hl : tables.length = nTables := by decide +kernel
    have hm' : m < tables.length := by rw [hl]; omega
    rw [List.take_add_one, List.foldl_append, foldl_tailOuterView layout chi eqQ sent0 m (by omega),
      List.getElem?_zipIdx, List.getElem?_eq_getElem hm']
    simp only [Option.map_some, Option.toList_some, List.foldl_cons, List.foldl_nil, tailOuterView,
      List.range_succ, List.map_append, List.map_cons, List.map_nil, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, List.drop_drop, zero_add, Prod.mk.injEq]
    have hg : tables.getD m default = tables[m] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm', Option.getD_some]
    have hNP : (List.range tables[m].width).filter
        (fun c ↦ !((List.map (fun x ↦ x.links.pointers) tables).getD m []).contains c) = tailNP m := by
      simp only [tailNP, tailPtrs, hg]
    rw [hNP]
    refine ⟨rfl, trivial, ?_, ?_⟩
    · simp only [tailQBefore, List.range_succ, List.map_append, List.map_cons, List.map_nil,
        List.sum_append, List.sum_cons, List.sum_nil, add_zero, tailPtrs]
    · simp only [tailNVBefore, List.range_succ, List.map_append, List.map_cons, List.map_nil,
        List.sum_append, List.sum_cons, List.sum_nil, add_zero]

theorem tailPtrs_eq : ∀ t < nTables, tailPtrs t = (tables.getD t default).links.pointers := by
  decide +kernel

theorem tailNValues_eq (layout : Layout) (htab : layout.tables = tables) :
    tailNValues layout = tailNVBefore nTables := by
  rw [tailNValues, htab]
  decide +kernel

/-- A block of a concatenation over `range n`, read at its offset. -/
theorem take_drop_flatMap {α : Type} (f : ℕ → List α) (n t : ℕ) (h : t < n) :
    (((List.range n).flatMap f).drop ((List.range t).map fun i ↦ (f i).length).sum).take
      (f t).length = f t := by
  obtain ⟨k, rfl⟩ : ∃ k, n = t + (k + 1) := ⟨n - t - 1, by omega⟩
  rw [List.range_add, List.flatMap_append, List.range_succ_eq_map]
  simp only [List.map_cons, List.flatMap_cons, add_zero]
  rw [List.drop_left' (by rw [List.length_flatMap]), List.take_left' rfl]

/-! ## The honest message -/

/-- Table `t`'s sent values: its non-pointer columns' extensions at its row point. -/
def tailVals (W : Witness) (chi : List E) (t : ℕ) : List E :=
  (tailNP t).map fun c ↦ mleK ((W.tableCols t).getD c #[]) (chi.take (W.layout.tableLogHeights.getD t 0))

/-- The honest message's slices: the pointer columns' slices under `eq(q*, ·)`. -/
def tailSlices (W : Witness) (x : LinkProverPre) (chi qPoint : List E) (st : RowState) : List E :=
  (List.range 64).map fun b ↦
    sumE ((linkColumns W x chi st).zipIdx.map fun (c, q) ↦ (eqTable qPoint).getD q 0 * c.slices.getD b 0)

theorem flatMap_congr_range {α : Type} {n : ℕ} {f g : ℕ → List α} (h : ∀ t < n, f t = g t) :
    (List.range n).flatMap f = (List.range n).flatMap g := by
  simp only [List.flatMap, List.map_congr_left fun t ht ↦ h t (List.mem_range.mp ht)]

theorem linkMessage_eq (W : Witness) (x : LinkProverPre) (chi qPoint : List E) (st : RowState) :
    linkMessage W x chi qPoint st =
      (List.range nTables).flatMap (tailVals W chi) ++ tailSlices W x chi qPoint st := by
  unfold linkMessage tailSlices
  congr 1

theorem length_tailVals (W : Witness) (chi : List E) :
    ((List.range nTables).flatMap (tailVals W chi)).length = tailNVBefore nTables := by
  simp [List.length_flatMap, tailVals, tailNVBefore]

/-- **The honest tail's end**: its columns, its ring pieces and slices, its memory term. -/
theorem honestTail_end {prog : LeanIsaProgram} {input : PublicInput} {ex : Execution prog}
    {W : Witness} (hW : witness? prog input ex = some W) (y : LinkPre) (x : LinkProverPre)
    (chi qPoint : List E) :
    let st := chi.foldl rowFold (linkRowStart W x)
    let e := (honestTail W y x chi qPoint).2
    e.columns = (List.range nTables).map (fun t ↦ (chi.take (W.layout.tableLogHeights.getD t 0),
        (tailNP t).zip (tailVals W chi t))) ∧
      e.ring.pieces = (List.range nTables).flatMap (fun t ↦ ((tailPtrs t).zipIdx (tailQBefore t)).map
        (tailPiece W.layout (chi.take (W.layout.tableLogHeights.getD t 0)) (eqKernel qPoint) t)) ∧
      e.ring.slices = tailSlices W x chi qPoint st ∧
      e.memoryPoint = y.r.take W.layout.logMemory ∧
      e.memoryScales = (prodE ((y.r.drop (min W.layout.logMemory y.chunks.width)).map (1 + ·)),
        eY * prodE ((y.r.drop (min W.layout.logMemory y.chunks.width)).map (1 + ·))) ∧
      e.memoryValue = y.m1 := by
  intro st e
  have htab := (linkSizes hW).1
  have hl : tables.zipIdx.length ≤ nTables := by rw [List.length_zipIdx]; decide +kernel
  have hmsg := linkMessage_eq W x chi qPoint st
  have hnv := tailNValues_eq W.layout htab
  have hview := tailView_rowSideOf W.layout htab (verCh W.layout y) chi (y.fresh.drop 1)
    (eqEval (verCh W.layout y).zeta y.r) (linkShiftEq (verCh W.layout y).zeta y.r)
    ((verCh W.layout y).etaBc * (verCh W.layout y).slot.getD 1 0 * indexMle y.r +
      prodE ((y.r.drop (min W.layout.logBytecode y.chunks.width)).map (1 + ·)) *
        ((verCh W.layout y).etaBc * (verCh W.layout y).slot.getD 2 0 + (honestProgramSide W y).1))
    (prodE ((y.r.drop (min W.layout.logBytecode y.chunks.width)).map (1 + ·)) *
      (honestProgramSide W y).2)
    ((verCh W.layout y).gammaMem.getD 0 0 * indexMle y.r + (verCh W.layout y).gammaMem.getD 3 0 *
      prodE ((y.r.drop (min W.layout.logMemory y.chunks.width)).map (1 + ·)) +
      (verCh W.layout y).gammaMem.getD 1 0 * y.m1)
    y.m1 (prodE ((y.r.drop (min 0 y.chunks.width)).map (1 + ·))) (eqKernel qPoint)
    (W.layout.tables.foldl (fun m t ↦ max m t.links.maxShift) 0)
    ((linkMessage W x chi qPoint st).take (tailNValues W.layout))
  conv at hview =>
    rhs
    rw [← List.take_of_length_le hl, foldl_tailOuterView _ _ _ _ _ le_rfl, hmsg, hnv,
      List.take_left' (length_tailVals W chi)]
  simp only [tailView, Prod.mk.injEq] at hview
  obtain ⟨hc, hpc, -, -⟩ := hview
  refine ⟨?_, ?_, ?_, rfl, rfl, rfl⟩
  · refine (show e.columns = _ from hc).trans (List.map_congr_left fun t ht ↦ ?_)
    have h := take_drop_flatMap (tailVals W chi) nTables t (List.mem_range.mp ht)
    simp only [tailVals, List.length_map] at h
    simp only [tailNVBefore, tailVals, h]
  · exact hpc
  · show (linkMessage W x chi qPoint st).drop (tailNValues W.layout) = _
    rw [hmsg, hnv, List.drop_left' (length_tailVals W chi)]

/-! ## The honest witness's tables -/

theorem tail_le_foldl_max : ∀ (l : List ℕ) (a t : ℕ), a ≤ l.foldl max a ∧ l.getD t 0 ≤ l.foldl max a
  | [], a, t => by simp
  | b :: l, a, t => by
    rw [List.foldl_cons]
    obtain ⟨h1, -⟩ := tail_le_foldl_max l (max a b) 0
    refine ⟨le_trans (le_max_left a b) h1, ?_⟩
    cases t with
    | zero => exact le_trans (le_max_right a b) h1
    | succ t => exact (tail_le_foldl_max l (max a b) t).2

theorem tail_tableCols_getD {prog : LeanIsaProgram} {input : PublicInput} {ex : Execution prog}
    {W : Witness} (hW : witness? prog input ex = some W) {t c : ℕ} (ht : t < nTables)
    (hc : c < tableWidths.getD t 0) :
    (W.tableCols t).getD c #[] = W.cols.getD (globalColumnBases.getD t 0 + c) #[] := by
  obtain ⟨-, steps, -, -, -, -, -, hcols, -⟩ := witness?_spec hW
  obtain ⟨-, -, h3⟩ := tableOf_base t ht c hc
  have hsize : W.cols.size = nColumns := by rw [hcols]; simp [colsOf]
  have hlt : c < min (globalColumnBases.getD t 0 + tableWidths.getD t 0) W.cols.size -
      globalColumnBases.getD t 0 := by rw [hsize]; omega
  simp only [Witness.tableCols, Array.getD_eq_getD_getElem?, Array.getElem?_extract, hlt,
    ↓reduceIte]

/-- A table column's placement has the table's row variables. -/
theorem tail_variableCount {prog : LeanIsaProgram} {input : PublicInput} {ex : Execution prog}
    {W : Witness} (hW : witness? prog input ex = some W) {t c : ℕ} (ht : t < nTables)
    (hc : c < tableWidths.getD t 0) {p : Placement}
    (hp : W.layout.placements.getD (globalColumnBases.getD t 0 + c) none = some p) :
    p.variableCount = W.layout.tableLogHeights.getD t 0 := by
  have h1 := (placement_witness hW hp).2.1
  rw [← tail_tableCols_getD hW ht hc, size_tableCols_getD hW ht hc] at h1
  exact (Nat.pow_right_injective le_rfl h1).symm

theorem tailNP_lt : ∀ t < nTables, ∀ c ∈ tailNP t, c < tableWidths.getD t 0 := by
  decide +kernel

theorem tailPtrs_lt : ∀ t < nTables, ∀ c ∈ tailPtrs t, c < tableWidths.getD t 0 ∧
    globalColumnBases.getD t 0 + c < 116 ∧
    ¬(globalColumnBases.getD opKeccak 0 + keccakOut ≤ globalColumnBases.getD t 0 + c ∧
      globalColumnBases.getD t 0 + c < globalColumnBases.getD opKeccak 0 + keccakOut + keccakStateLanes) := by
  decide +kernel

/-- **A pointer column has a placement.** -/
theorem tail_ptr_placement {prog : LeanIsaProgram} {input : PublicInput} {ex : Execution prog}
    {W : Witness} (hW : witness? prog input ex = some W) {t c : ℕ} (ht : t < nTables)
    (hc : c ∈ tailPtrs t) :
    ∃ p, W.layout.placements.getD (globalColumnBases.getD t 0 + c) none = some p ∧
      p.variableCount = W.layout.tableLogHeights.getD t 0 := by
  obtain ⟨-, steps, -, -, hl, -⟩ := witness?_spec hW
  obtain ⟨hw, h116, hk⟩ := tailPtrs_lt t ht c hc
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (LeanVM.Protocol.Verifier.placement_isSome hl h116 hk)
  exact ⟨p, hp, tail_variableCount hW ht hw hp⟩

/-! ## The pointer columns' slices -/

/-- **A column's slices at a point are the extensions of its bit slices.** -/
theorem sliceHolds_columnSlices (words : Array K) (pt : List E) (hw : words.size = 2 ^ pt.length) :
    SlicesHoldIn words pt (columnSlices words pt) := by
  refine ⟨length_columnSlices words pt, fun i hi ↦ ?_⟩
  rw [getD_columnSlices words pt hw hi, mleA_eq_sum _ _ (by rw [bitSlice, Array.size_map, hw])]
  refine sum_congr rfl fun u hu ↦ ?_
  have hu' : u < words.size := hw ▸ mem_range.mp hu
  have hb : (kToNat (words.getD u 0) >>> i) % 2 = 1 ↔ (words.getD u 0).toBitVec.getLsbD i = true := by
    rw [shiftRight_mod_two, kToNat, BitVec.testBit_toNat]
  simp only [bitSlice, Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_eq_getElem hu',
    Option.map_some, Option.getD_some] at hb ⊢
  by_cases h : words[u].toBitVec.getLsbD i = true
  · rw [ite_eq_left (hb.mpr h), ite_eq_left h, mul_one]
  · rw [ite_eq_right (fun h' ↦ h (hb.mp h')), ite_eq_right h, mul_zero]

theorem foldl_append_map {α β : Type} (g : α → β) : ∀ (L : List (α × ℕ)) (v : List β),
    L.foldl (fun v pk ↦ v ++ [g pk.1]) v = v ++ (L.map Prod.fst).map g
  | [], v => by simp
  | pk :: L, v => by
    rw [List.foldl_cons, foldl_append_map g L]
    simp

/-- The slices `columnsAt` keeps: one per pointer column, in order. -/
theorem slices_columnsAt (W : Witness) (inp : RowInputs) (t q₀ : ℕ) (rt : RowTable) (chi : List E) :
    (columnsAt W inp t q₀ rt chi).map (·.slices) =
      (tables.getD t default).links.pointers.map fun p ↦
        columnSlices ((W.tableCols t).getD p #[]) (chi.take rt.height) := by
  unfold columnsAt
  refine (foldl_view (fun acc : List ColumnAt × ℕ ↦ acc.1.map (·.slices))
    (fun v pk ↦ v ++ [columnSlices ((W.tableCols t).getD pk.1 #[]) (chi.take rt.height)])
    (fun acc pk ↦ ?_) _ _).trans ?_
  · obtain ⟨out, pos⟩ := acc
    obtain ⟨pointer, k⟩ := pk
    simp
  · refine (foldl_append_map (fun p ↦ columnSlices ((W.tableCols t).getD p #[]) (chi.take rt.height))
      _ _).trans ?_
    simp

/-! ## The ring claim -/

theorem zipIdx_flatMap_range {α : Type} (f : ℕ → List α) : ∀ n,
    ((List.range n).flatMap f).zipIdx =
      (List.range n).flatMap fun t ↦ (f t).zipIdx (((List.range t).map fun i ↦ (f i).length).sum)
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append, List.zipIdx_append, zipIdx_flatMap_range f n,
      List.flatMap_append]
    simp [List.length_flatMap]

/-- After the row rounds a table keeps its height. -/
theorem height_rowState (W : Witness) (x : LinkProverPre) (chi : List E) {t : ℕ} (ht : t < nTables) :
    ((chi.foldl rowFold (linkRowStart W x)).getD t default).height =
      W.layout.tableLogHeights.getD t 0 := by
  unfold linkRowStart
  rw [foldl_rowFold_ofFn]
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, show t < nTables from ht,
    ↓reduceDIte, Option.getD_some]
  rw [foldl_rowTableFold _ _ (Nat.zero_le _)]

theorem map_zipIdx_slices (C : List ColumnAt) (S : List (List E)) (h : C.map (·.slices) = S)
    (F : List E → ℕ → E) (s : ℕ) :
    (C.zipIdx s).map (fun x ↦ F x.1.slices x.2) = (S.zipIdx s).map (fun x ↦ F x.1 x.2) := by
  subst h
  rw [List.zipIdx_map, List.map_map]
  rfl

/-- **The honest ring claim holds of the stack**: the pointer columns' slices under `eq(q*, ·)`. -/
theorem ringHolds_honestTail {prog : LeanIsaProgram} {input : PublicInput} {ex : Execution prog}
    {W : Witness} (hW : witness? prog input ex = some W) (y : LinkPre) (x : LinkProverPre)
    (chi qPoint : List E) (hchi : chi.length = linkNRows W) :
    (honestTail W y x chi qPoint).2.ring.HoldsOn W.stack := by
  obtain ⟨-, hpieces, hslices, -⟩ := honestTail_end hW y x chi qPoint
  refine ⟨by rw [hslices, tailSlices, List.length_map, List.length_range], fun i hi ↦ ?_⟩
  rw [hslices, hpieces, tailSlices, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hi, Option.map_some, Option.getD_some]
  refine congrArg sumE ?_
  unfold linkColumns
  rw [zipIdx_flatMap_range, List.map_flatMap, List.map_flatMap]
  refine flatMap_congr_range fun t ht ↦ ?_
  have hlen : ∀ j < nTables, (columnsAt W (linkRowInputs W x) j (pointerStarts.getD j 0)
      ((chi.foldl rowFold (linkRowStart W x)).getD j default) chi).length = (tailPtrs j).length := by
    intro j hj
    rw [← List.length_map (f := (·.slices)), slices_columnsAt, List.length_map, tailPtrs_eq j hj]
  have hs : ((List.range t).map fun j ↦ (columnsAt W (linkRowInputs W x) j (pointerStarts.getD j 0)
      ((chi.foldl rowFold (linkRowStart W x)).getD j default) chi).length).sum = tailQBefore t := by
    rw [tailQBefore, List.map_congr_left fun j hj ↦ hlen j (by have := List.mem_range.mp hj; omega)]
  rw [hs]
  have hsl := slices_columnsAt W (linkRowInputs W x) t (pointerStarts.getD t 0)
    ((chi.foldl rowFold (linkRowStart W x)).getD t default) chi
  rw [height_rowState W x chi ht, ← tailPtrs_eq t ht] at hsl
  refine (map_zipIdx_slices _ _ hsl (fun sl q ↦ (eqTable qPoint).getD q 0 * sl.getD i 0) _).trans ?_
  rw [List.zipIdx_map, List.map_map, List.map_map]
  refine List.map_congr_left fun pk hpk ↦ ?_
  obtain ⟨-, hlt, hfst⟩ := List.mem_zipIdx hpk
  have hmem : pk.1 ∈ tailPtrs t := by rw [hfst]; exact List.getElem_mem _
  obtain ⟨p, hp, hvc⟩ := tail_ptr_placement hW ht hmem
  have hht : W.layout.tableLogHeights.getD t 0 ≤ chi.length := by
    rw [hchi]; exact (tail_le_foldl_max _ 0 t).2
  have hpt : (chi.take (W.layout.tableLogHeights.getD t 0)).length =
      W.layout.tableLogHeights.getD t 0 := by rw [List.length_take, min_eq_left hht]
  have hw := (tailPtrs_lt t ht pk.1 hmem).1
  have hslices := sliceHolds_columnSlices (W.cols.getD (globalColumnBases.getD t 0 + pk.1) #[])
    (chi.take (W.layout.tableLogHeights.getD t 0))
    (by rw [hpt, ← tail_tableCols_getD hW ht hw, size_tableCols_getD hW ht hw])
  simp only [Function.comp_def, Prod.map, id, tailPiece, hp, Option.getD_some]
  rw [sliceValue_witness hW hp hslices _ hi, tail_tableCols_getD hW ht hw, Keccak.getD_toList,
    Keccak.toList_eqTable]

/-! ## `LinkOut` -/

theorem zip_map_self (l : List ℕ) (F : ℕ → E) : l.zip (l.map F) = l.map fun c ↦ (c, F c) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem globalColumnBases_getD {t : ℕ} (ht : t < nTables) :
    globalColumnBases.getD t 0 = numGlobalColumns + (tableWidths.take t).sum := by
  simp [globalColumnBases, List.getD_eq_getElem?_getD, ht]

theorem tailNVBefore_le : tailNVBefore nTables ≤ 116 := by decide +kernel

theorem keccakOut_mem_tailNP : ∀ lane < keccakStateLanes, keccakOut + lane ∈ tailNP opKeccak := by
  decide +kernel

/-- **The honest tail's column claims**, each a table's non-pointer column at its row point. -/
theorem linkColumnClaims_honestTail {prog : LeanIsaProgram} {input : PublicInput}
    {ex : Execution prog} {W : Witness} (hW : witness? prog input ex = some W) (y : LinkPre)
    (x : LinkProverPre) (chi qPoint : List E) :
    linkColumnClaims (honestTail W y x chi qPoint).2 = (List.range nTables).flatMap fun t ↦
      (tailNP t).map fun c ↦ (⟨globalColumnBases.getD t 0 + c,
        chi.take (W.layout.tableLogHeights.getD t 0),
        mleK ((W.tableCols t).getD c #[]) (chi.take (W.layout.tableLogHeights.getD t 0))⟩ : ColumnClaim) := by
  obtain ⟨hcols, -⟩ := honestTail_end hW y x chi qPoint
  rw [linkColumnClaims, hcols]
  conv_lhs => rw [globalColumnBases]
  rw [List.zip_map', List.flatMap_map]
  refine flatMap_congr_range fun t ht ↦ ?_
  simp only [tailVals, zip_map_self, List.map_map, Function.comp_def, globalColumnBases_getD ht]

/-- **`LinkOut` of the honest tail.** -/
theorem linkOut_honestTail {prog : LeanIsaProgram} {input : PublicInput} {ex : Execution prog}
    {W : Witness} (hW : witness? prog input ex = some W) {y : LinkPre} {x : LinkProverPre}
    (hp : HonestPre W y x) (chi qPoint : List E) (hchi : chi.length = linkNRows W) :
    LinkOut W (honestTail W y x chi qPoint).2 := by
  obtain ⟨hcols, hpieces, -, hmp, hms, hmv⟩ := honestTail_end hW y x chi qPoint
  have hclaims := linkColumnClaims_honestTail hW y x chi qPoint
  have hht : ∀ t, W.layout.tableLogHeights.getD t 0 ≤ chi.length := fun t ↦ by
    rw [hchi]; exact (tail_le_foldl_max _ 0 t).2
  have hpt : ∀ t, (chi.take (W.layout.tableLogHeights.getD t 0)).length =
      W.layout.tableLogHeights.getD t 0 := fun t ↦ by rw [List.length_take, min_eq_left (hht t)]
  have hκ := tail_logMemory_le_width hW
  refine ⟨?_, ?_, ringHolds_honestTail hW y x chi qPoint hchi, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc
    rw [hclaims] at hc
    obtain ⟨t, ht, hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨col, hcol, rfl⟩ := List.mem_map.mp hc
    have ht' := List.mem_range.mp ht
    simp only [ColumnClaim.HoldsIn]
    rw [tail_tableCols_getD hW ht' (tailNP_lt t ht' col hcol)]
  · rw [hmv, hms, hmp, hp.m1, hp.m1eq, honestM1, hp.chunks, hp.r]
    ring
  · intro t ht
    rw [hcols, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht]
    exact hpt t
  · intro c hc p hpl
    rw [hclaims] at hc
    obtain ⟨t, ht, hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨col, hcol, rfl⟩ := List.mem_map.mp hc
    have ht' := List.mem_range.mp ht
    rw [hpt, tail_variableCount hW ht' (tailNP_lt t ht' col hcol) hpl]
  · rw [hmp, List.length_take, hp.r, hp.rlen, min_eq_left hκ]
  · intro piece hpc
    rw [hpieces] at hpc
    obtain ⟨t, ht, hpc⟩ := List.mem_flatMap.mp hpc
    obtain ⟨pk, hpk, rfl⟩ := List.mem_map.mp hpc
    have ht' := List.mem_range.mp ht
    obtain ⟨-, -, hfst⟩ := List.mem_zipIdx hpk
    have hmem : pk.1 ∈ tailPtrs t := by rw [hfst]; exact List.getElem_mem _
    obtain ⟨p, hpl, hvc⟩ := tail_ptr_placement hW ht' hmem
    exact ⟨_, p, hpl, by simp only [tailPiece, hpl, Option.getD_some], by rw [tailPiece, hpt, hvc]⟩
  · intro lane hl
    rw [hcols, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (show opKeccak < nTables by decide), Option.map_some, Option.getD_some]
    simp only [tailVals, zip_map_self]
    exact ⟨_, List.mem_map.mpr ⟨_, keccakOut_mem_tailNP lane hl, rfl⟩⟩
  · rw [hclaims, List.length_flatMap]
    simpa [tailNVBefore] using tailNVBefore_le

/-- **`LinkTailHolds` from the terminal summand**: `LinkOut` holds of the honest tail. -/
theorem linkTailHolds_of_value {prog : LeanIsaProgram} {input : PublicInput} {ex : Execution prog}
    {W : Witness} (hW : witness? prog input ex = some W)
    (h : ∀ y x, HonestPre W y x → ∀ chi qPoint : List E, chi.length = linkNRows W →
      qPoint.length = log2Ceil (linkNPointers W.layout) →
      (honestTail W y x chi qPoint).1 = (qPoint.foldl Prods.fold
          (linkColumnProds W x chi (chi.foldl rowFold (linkRowStart W x)))).value) :
    LinkTailHolds W :=
  linkTailHolds_of_tail fun y x hp chi qPoint hchi hq ↦
    ⟨h y x hp chi qPoint hchi hq, linkOut_honestTail hW hp chi qPoint hchi⟩

end LeanVM.Prover.Complete

end
