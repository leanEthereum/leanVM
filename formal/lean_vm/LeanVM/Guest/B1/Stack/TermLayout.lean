/-
  LeanVM.Guest.B1.Stack.TermLayout

  The columns the terminal weighs: the link's sent and pointer columns, their kinds and placements.
-/

module

public import LeanVM.Guest.B1.Stack.TermRing
public import LeanVM.Guest.B1.Stack.Placed

/-!
# The terminal's columns

The link sends each table's non-pointer columns (`sentCols`, in `linkColumnClaims`' order) and
ring-switches its pointer columns (`ptrCols`, in `pointerPieces`' order). Each column is of a kind
(`sentKinds`, `ptrKinds`, the guest's `SENT_TARGET` and `PTR_BLOCK`): a stack block `b < 52`, a
`q_keccak` slot `52 + s`, or none (`1000`, a `KECCAK` output lane); `sent_ok`, `ptr_ok` check
each kind against `stackBlocks` and `qkeccakSlot` (`KindOk`). In a layout `buildLayout` returns,
a block's column has its block's placement, a slot's column `q_keccak`'s offset plus `s·2^h`
(`layout_slot`), a column of neither no placement (`layout_none`), and a table's column the
table's height as kappa (`layout_kappa`).
-/

namespace LeanVM.Guest.B1.Stack

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The columns and their kinds -/

/-- The link's sent columns, table and global column, in `linkColumnClaims`' order. -/
def sentCols : List (ℕ × ℕ) :=
  tables.zipIdx.flatMap fun (table, t) ↦ (nonPointerColumns table).map fun c ↦ (t, globalColumnBases.getD t 0 + c)

/-- The link's pointer columns, table and global column, in `pointerPieces`' order. -/
def ptrCols : List (ℕ × ℕ) :=
  tables.zipIdx.flatMap fun (table, t) ↦ table.links.pointers.map fun p ↦ (t, globalColumnBases.getD t 0 + p)

/-- The sent columns' kinds, the guest's `SENT_TARGET`. -/
def sentKinds : List ℕ := [3, 4, 10, 11, 12, 13, 19, 20, 24, 25, 26, 27, 28, 34, 35, 36, 37, 38, 39, 40, 41, 42,
  102, 103, 104, 105, 106, 107, 108, 109, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68,
  69, 70, 71, 72, 73, 74, 75, 76, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000,
  1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000]

/-- The pointer columns' kinds, the guest's `PTR_BLOCK`. -/
def ptrKinds : List ℕ := [9, 8, 5, 6, 7, 18, 17, 14, 15, 16, 23, 22, 21, 33, 32, 29, 30, 31, 47, 46, 43, 44, 45,
  51, 50, 110, 111, 112, 113, 114, 115, 48, 49]

/-- What a column `col` of table `t` and kind `k` is. -/
def KindOk (t col k : ℕ) : Prop :=
  t < 6 ∧ col < colSrc.length ∧ colSrc.getD col (0, 0) = (2 + t, 0) ∧
    (k < 52 → blockColumn k = col) ∧
    (52 ≤ k → k < 1000 → qkeccakSlot col = some (k - 52) ∧ k < 116 ∧ t = 5) ∧
    (k = 1000 → qkeccakSlot col = none ∧ col ∉ stackBlocks.map (·.column)) ∧ (k < 116 ∨ k = 1000)

instance (t col k : ℕ) : Decidable (KindOk t col k) := by unfold KindOk; infer_instance

set_option maxRecDepth 100000 in
theorem sent_ok : sentCols.length = 80 ∧ ∀ z ∈ sentCols.zip sentKinds, KindOk z.1.1 z.1.2 z.2 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ptr_ok : ptrCols.length = 33 ∧ ∀ q < 33,
    KindOk (ptrCols.getD q (0, 0)).1 (ptrCols.getD q (0, 0)).2 (ptrKinds.getD q 0) ∧ ptrKinds.getD q 0 ≠ 1000 := by
  decide +kernel

/-- Each pointer's table. -/
def ptrTab : List ℕ := [0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5,
  5, 5, 5]

set_option maxRecDepth 100000 in
theorem ptr_tab : ptrCols.map (·.1) = ptrTab := by decide +kernel

/-- Per table, a stack block of its own (`h_t ≤ stackLog`). -/
theorem table_block : ∀ t < 6, ∃ b < 52, colSrc.getD (blockColumn b) (0, 0) = (2 + t, 0) ∧
    blockColumn b < colSrc.length := by
  intro t ht
  interval_cases t
  · exact ⟨3, by decide, by decide +kernel, by decide +kernel⟩
  · exact ⟨10, by decide, by decide +kernel, by decide +kernel⟩
  · exact ⟨19, by decide, by decide +kernel, by decide +kernel⟩
  · exact ⟨24, by decide, by decide +kernel, by decide +kernel⟩
  · exact ⟨34, by decide, by decide +kernel, by decide +kernel⟩
  · exact ⟨48, by decide, by decide +kernel, by decide +kernel⟩

theorem block2_column : blockColumn 2 = qkeccak := by decide +kernel

theorem block01_column : blockColumn 0 = memory0 ∧ blockColumn 1 = memory1 := by decide +kernel

theorem qkeccak_facts : qkeccak < colSrc.length ∧ qkeccakSlot qkeccak = none := by decide +kernel

/-! ## Placements -/

theorem colSrc_length_eq (lm : ℕ) (hs : List ℕ) : (columnKappas tables lm hs).length = colSrc.length := by
  rw [columnKappas_eq, List.length_map]

/-- **A table column's kappa** is its table's height. -/
theorem layout_kappa (lm : ℕ) (hs : List ℕ) {col t : ℕ} (hc : col < colSrc.length)
    (hsrc : colSrc.getD col (0, 0) = (2 + t, 0)) :
    (columnKappas tables lm hs).getD col 0 = hs.getD t 0 := by
  rw [columnKappas_eq, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hc]
  simp only [Option.map_some, Option.getD_some]
  rw [List.getD_eq_getElem _ _ hc] at hsrc
  rw [hsrc]
  simp [kvOf, show 2 + t ≠ 1 by omega]

/-- A column's placement, from `buildLayout`'s formula. -/
theorem layout_placement {bytecode : List K} {lm : ℕ} {rows : List ℕ} {layout : Layout}
    (hbl : buildLayout bytecode lm rows = some layout) {col : ℕ} (hc : col < colSrc.length) :
    layout.placements.getD col none =
      (match qkeccakSlot col with
        | some slot => ((stack (columnKappas tables layout.logMemory layout.tableLogHeights)).1.lookup qkeccak).map
            (· + (slot <<< (columnKappas tables layout.logMemory layout.tableLogHeights).getD col 0))
        | none => (stack (columnKappas tables layout.logMemory layout.tableLogHeights)).1.lookup col).map
        fun index ↦ (⟨(columnKappas tables layout.logMemory layout.tableLogHeights).getD col 0, index⟩ : Placement) := by
  obtain ⟨hlm, -, -, -, -, -, hpl⟩ := buildLayout_some hbl
  rw [← hlm] at hpl
  have hcl : col < (columnKappas tables layout.logMemory layout.tableLogHeights).length := by
    rw [colSrc_length_eq]; exact hc
  rw [hpl, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_zipIdx, List.getElem?_eq_getElem hcl]
  simp only [Option.map_some, Option.getD_some, Nat.zero_add]
  rw [List.getD_eq_getElem _ _ hcl]
  rfl

theorem lookup_zip_none (c : ℕ) : ∀ (ks vs : List ℕ), c ∉ ks → (ks.zip vs).lookup c = none
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | k :: ks, v :: vs, h => by
    have hne : c ≠ k := fun e ↦ h (e ▸ List.mem_cons_self)
    have ih := lookup_zip_none c ks vs (fun hm ↦ h (List.mem_cons_of_mem _ hm))
    have hb : (c == k) = false := by simpa using hne
    simp [List.zip_cons_cons, List.lookup, hb, ih]

/-- **A column of no kind has no placement.** -/
theorem layout_none {bytecode : List K} {lm : ℕ} {rows : List ℕ} {layout : Layout}
    (hbl : buildLayout bytecode lm rows = some layout) {col : ℕ} (hc : col < colSrc.length)
    (hs : qkeccakSlot col = none) (hnb : col ∉ stackBlocks.map (·.column)) :
    layout.placements.getD col none = none := by
  rw [layout_placement hbl hc, hs, stack_eq]
  simp [lookup_zip_none col (stackBlocks.map (·.column)) _ hnb]

/-- **A slot's column**: `q_keccak`'s offset plus `s · 2^kappa`. -/
theorem layout_slot {bytecode : List K} {lm : ℕ} {rows : List ℕ} {layout : Layout}
    (hbl : buildLayout bytecode lm rows = some layout) {col s : ℕ} (hc : col < colSrc.length)
    (hs : qkeccakSlot col = some s) :
    ∃ p2 : Placement, layout.placements.getD qkeccak none = some p2 ∧
      layout.placements.getD col none = some ⟨(columnKappas tables layout.logMemory layout.tableLogHeights).getD col 0,
        p2.index + (s <<< (columnKappas tables layout.logMemory layout.tableLogHeights).getD col 0)⟩ := by
  obtain ⟨p2, hp2, -⟩ := layout_block hbl (b := 2) (by decide)
  rw [block2_column] at hp2
  refine ⟨p2, hp2, ?_⟩
  have hq := layout_placement hbl qkeccak_facts.1
  rw [qkeccak_facts.2, hp2] at hq
  simp only at hq
  rw [layout_placement hbl hc, hs]
  simp only
  rcases hl : (stack (columnKappas tables layout.logMemory layout.tableLogHeights)).1.lookup qkeccak with _ | i
  · rw [hl] at hq; simp at hq
  · rw [hl] at hq
    simp only [Option.map_some, Option.some.injEq] at hq
    subst hq
    simp

/-! ## The link's claims and pieces, as lists -/

theorem fold_ptr_inner (mk : ℕ → ℕ → ℕ → RingPiece) (t : ℕ) : ∀ (ps : List ℕ) (l : List RingPiece) (n : ℕ),
    ps.foldl (fun (acc : List RingPiece × ℕ) pointer ↦
        (acc.1 ++ [mk t (globalColumnBases.getD t 0 + pointer) acc.2], acc.2 + 1)) (l, n) =
      (l ++ ((ps.map fun p ↦ (t, globalColumnBases.getD t 0 + p)).zipIdx n).map (fun e ↦ mk e.1.1 e.1.2 e.2),
        n + ps.length)
  | [], l, n => by simp
  | p :: ps, l, n => by
    rw [List.foldl_cons, fold_ptr_inner mk t ps, List.map_cons, List.zipIdx_cons, List.map_cons,
      List.append_assoc, List.singleton_append, List.length_cons]
    simp only [Prod.mk.injEq, true_and]
    omega

theorem fold_ptr (mk : ℕ → ℕ → ℕ → RingPiece) : ∀ (T : List (Table × ℕ)) (l : List RingPiece) (n : ℕ),
    (T.foldl (fun (acc : List RingPiece × ℕ) (tt : Table × ℕ) ↦ tt.1.links.pointers.foldl
        (fun (acc : List RingPiece × ℕ) pointer ↦
          (acc.1 ++ [mk tt.2 (globalColumnBases.getD tt.2 0 + pointer) acc.2], acc.2 + 1)) acc) (l, n)).1 =
      l ++ ((T.flatMap fun tt ↦ tt.1.links.pointers.map fun p ↦ (tt.2, globalColumnBases.getD tt.2 0 + p)).zipIdx n).map
        (fun e ↦ mk e.1.1 e.1.2 e.2)
  | [], l, n => by simp
  | tt :: T, l, n => by
    rw [List.foldl_cons, fold_ptr_inner, fold_ptr mk T, List.flatMap_cons, List.zipIdx_append,
      List.map_append, List.append_assoc, List.length_map]

/-- Pointer `q`'s piece, of table `t` and global column `col`. -/
def ptrPiece (layout : Layout) (chi qPoint : List E) (t col q : ℕ) : RingPiece :=
  ⟨some ((layout.placements.getD col none).getD default), chi.take (layout.tableLogHeights.getD t 0),
    (eqKernel qPoint).getD q 0⟩

/-- **The link's pointer pieces**, one per pointer column. -/
theorem pointerPieces_eq (layout : Layout) (chi qPoint : List E) :
    pointerPieces layout chi qPoint = ptrCols.zipIdx.map (fun e ↦ ptrPiece layout chi qPoint e.1.1 e.1.2 e.2) := by
  have := fold_ptr (ptrPiece layout chi qPoint) tables.zipIdx [] 0
  rw [List.nil_append] at this
  exact this

theorem claims_colPts : ∀ (bases : List ℕ) (cols : List (List E × List (ℕ × E))),
    ((bases.zip cols).flatMap fun (bpv : ℕ × List E × List (ℕ × E)) ↦
        bpv.2.2.map fun cv ↦ (⟨bpv.1 + cv.1, bpv.2.1, cv.2⟩ : ColumnClaim)).map (fun c ↦ (c.column, c.point)) =
      (bases.zip (cols.map fun c ↦ (c.1, c.2.map (·.1)))).flatMap
        (fun (bpc : ℕ × List E × List ℕ) ↦ bpc.2.2.map fun c ↦ (bpc.1 + c, bpc.2.1))
  | [], _ => rfl
  | _ :: _, [] => rfl
  | b :: bases, c :: cols => by
    rw [List.zip_cons_cons, List.flatMap_cons, List.map_append, claims_colPts bases cols, List.map_cons,
      List.zip_cons_cons, List.flatMap_cons, List.map_map, List.map_map]
    rfl

set_option maxRecDepth 100000 in
theorem sentCols_zip (P : ℕ → List E) :
    (globalColumnBases.zip (tables.zipIdx.map fun (table, t) ↦ (P t, nonPointerColumns table))).flatMap
      (fun (bpc : ℕ × List E × List ℕ) ↦ bpc.2.2.map fun c ↦ (bpc.1 + c, bpc.2.1)) =
    sentCols.map fun e ↦ (e.2, P e.1) := by
  rfl

/-- **The link's column claims**: their columns and points, `sentCols` at their tables' row points. -/
theorem linkColumnClaims_colPts (link : LinkEnd) (P : ℕ → List E)
    (h : link.columns.map (fun c ↦ (c.1, c.2.map (·.1))) =
      tables.zipIdx.map (fun (table, t) ↦ (P t, nonPointerColumns table))) :
    (linkColumnClaims link).map (fun c ↦ (c.column, c.point)) = sentCols.map fun e ↦ (e.2, P e.1) := by
  unfold linkColumnClaims
  rw [← sentCols_zip, ← h]
  exact claims_colPts globalColumnBases link.columns

end
end LeanVM.Guest.B1.Stack
