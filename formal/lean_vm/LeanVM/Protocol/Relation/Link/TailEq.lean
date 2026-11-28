/-
  LeanVM.Protocol.Relation.Link.TailEq

  The terminal check on the stack: under `LinkEndHolds` the packed message and the memory term are
  the stack's own, so the check compares the claim with the row summand at the final point.
-/

module

public import LeanVM.Protocol.Relation.Link.Summand

/-!
# The terminal check

`tail_of_summand` is `LinkSummandFacts.tail`. The link's end (`tailValuesF`) carries the memory term
`m1` at the memory point, each table's row point with the values it read (`(column, value)` pairs,
`linkColumnClaims`), and the bit-slices with the ring pieces. When it holds of the stack
(`LinkEndHolds`):

* `m1` is `honestM1`;
* the row side's fold hands table `t` the next `|nonPointer_t|` values of the message
  (`gCol`, `gCol_fold`), each a column claim, so the values are `honestValues` (`take_values_eq`);
* the pieces depend on the points alone (`gPiece`, `rowSideOf_pieces`), so the slices are
  `honestSlices`.

So the message is `honestMessage` and `last` is `rowSummand` at `χ ++ q_point`, the row side's table
there (`cube_full`).
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier LeanVM.Protocol.Link Finset

@[expose] public section

/-! ## Folds through a projection -/

theorem foldl_proj {α β γ : Type} (π : β → γ) (f : β → α → β) (g : γ → α → γ)
    (h : ∀ b x, π (f b x) = g (π b) x) : ∀ (l : List α) (b : β), π (l.foldl f b) = l.foldl g (π b)
  | [], _ => rfl
  | x :: l, b => by
    simp only [List.foldl_cons]
    rw [foldl_proj π f g h l, h]

theorem foldl_const_self {α γ : Type} : ∀ (l : List α) (s : γ), l.foldl (fun s _ ↦ s) s = s
  | [], _ => rfl
  | _ :: l, s => foldl_const_self l s

/-! ## The pieces -/

/-- What a pointer column adds to the pieces and their count. -/
def gPiece (layout : Layout) (eqQ point : List E) (t : ℕ) (s : List RingPiece × ℕ) (x : ℕ × ℕ) :
    List RingPiece × ℕ :=
  let piece : RingPiece :=
    { placement := some ((layout.placements.getD (globalColumnBases.getD t 0 + x.1) none).getD default)
      point := point
      scale := eqQ.getD s.2 0 }
  (s.1 ++ [piece], s.2 + 1)

/-- What a table adds to the pieces and their count. -/
def gRow (layout : Layout) (eqQ chi : List E) (s : List RingPiece × ℕ) (x : Table × ℕ) :
    List RingPiece × ℕ :=
  (((layout.tables.map (·.links.pointers)).getD x.2 []).zipIdx).foldl
    (gPiece layout eqQ (chi.take (layout.tableLogHeights.getD x.2 0)) x.2) s

theorem ptrStep_pieces (layout : Layout) (ch : LinkCh) (a : IdxAt) (eqQ point : List E)
    (corner omega act sHat sNext : E) (table : Table) (t : ℕ) (col : ℕ → E) (acc : LinkRowSide)
    (x : ℕ × ℕ) :
    ((ptrStep layout ch a eqQ point corner omega act sHat sNext table t col acc x).pieces,
      (ptrStep layout ch a eqQ point corner omega act sHat sNext table t col acc x).q) =
      gPiece layout eqQ point t (acc.pieces, acc.q) x := by
  obtain ⟨pointer, k⟩ := x
  rfl

theorem rowStep_pieces (layout : Layout) (ch : LinkCh) (a : IdxAt) (jump eqQ chi : List E)
    (acc : LinkRowSide) (x : Table × ℕ) :
    ((rowStep layout ch a jump eqQ chi acc x).pieces, (rowStep layout ch a jump eqQ chi acc x).q) =
      gRow layout eqQ chi (acc.pieces, acc.q) x := by
  obtain ⟨table, t⟩ := x
  exact foldl_proj (fun acc : LinkRowSide ↦ (acc.pieces, acc.q)) _ _
    (fun b y ↦ ptrStep_pieces _ _ _ _ _ _ _ _ _ _ _ _ _ b y) _ _

/-- **The pieces depend on the points alone.** -/
theorem rowSideOf_pieces (layout : Layout) (ch : LinkCh) (a : IdxAt) (jump chi qPoint message : List E) :
    (rowSideOf layout ch a jump (eqKernel qPoint) chi message).pieces = piecesOf layout chi qPoint := by
  have h1 := foldl_proj (fun acc : LinkRowSide ↦ (acc.pieces, acc.q)) _ _
    (rowStep_pieces layout ch a jump (eqKernel qPoint) chi) layout.tables.zipIdx (rowStart layout message)
  have h2 := foldl_proj (fun acc : LinkRowSide ↦ (acc.pieces, acc.q)) _ _
    (rowStep_pieces layout ⟨[], [], [], [], [], 0, 0, [], [], [], []⟩ ⟨0, 0, 0, 0, 0, 0, 0⟩ []
      (eqKernel qPoint) chi) layout.tables.zipIdx (rowStart layout [])
  exact (congrArg Prod.fst h1).trans (congrArg Prod.fst h2).symm

/-! ## The values -/

/-- What a table adds to the columns, and the values it leaves. -/
def gCol (layout : Layout) (chi : List E) (s : List (List E × List (ℕ × E)) × List E)
    (x : Table × ℕ) : List (List E × List (ℕ × E)) × List E :=
  (s.1 ++ [(chi.take (layout.tableLogHeights.getD x.2 0),
    (nonPointerOf layout x.2 x.1).zip (s.2.take (nonPointerOf layout x.2 x.1).length))],
    s.2.drop (nonPointerOf layout x.2 x.1).length)

theorem foldl_ptrStep_cols (layout : Layout) (ch : LinkCh) (a : IdxAt) (eqQ point : List E)
    (corner omega act sHat sNext : E) (table : Table) (t : ℕ) (col : ℕ → E) (l : List (ℕ × ℕ))
    (b : LinkRowSide) :
    ((l.foldl (ptrStep layout ch a eqQ point corner omega act sHat sNext table t col) b).columns,
      (l.foldl (ptrStep layout ch a eqQ point corner omega act sHat sNext table t col) b).sent) =
      (b.columns, b.sent) := by
  rw [foldl_proj (fun acc : LinkRowSide ↦ (acc.columns, acc.sent)) _ (fun s _ ↦ s)
    (fun b y ↦ by obtain ⟨p, k⟩ := y; rfl) l b, foldl_const_self]

theorem foldl_ptrStep_columns (layout : Layout) (ch : LinkCh) (a : IdxAt) (eqQ point : List E)
    (corner omega act sHat sNext : E) (table : Table) (t : ℕ) (col : ℕ → E) (l : List (ℕ × ℕ))
    (b : LinkRowSide) :
    (l.foldl (ptrStep layout ch a eqQ point corner omega act sHat sNext table t col) b).columns =
      b.columns :=
  congrArg Prod.fst (foldl_ptrStep_cols layout ch a eqQ point corner omega act sHat sNext table t col l b)

theorem foldl_ptrStep_sent (layout : Layout) (ch : LinkCh) (a : IdxAt) (eqQ point : List E)
    (corner omega act sHat sNext : E) (table : Table) (t : ℕ) (col : ℕ → E) (l : List (ℕ × ℕ))
    (b : LinkRowSide) :
    (l.foldl (ptrStep layout ch a eqQ point corner omega act sHat sNext table t col) b).sent =
      b.sent :=
  congrArg Prod.snd (foldl_ptrStep_cols layout ch a eqQ point corner omega act sHat sNext table t col l b)

theorem rowStep_cols (layout : Layout) (ch : LinkCh) (a : IdxAt) (jump eqQ chi : List E)
    (acc : LinkRowSide) (x : Table × ℕ) :
    ((rowStep layout ch a jump eqQ chi acc x).columns, (rowStep layout ch a jump eqQ chi acc x).sent) =
      gCol layout chi (acc.columns, acc.sent) x := by
  obtain ⟨table, t⟩ := x
  simp only [rowStep, gCol, foldl_ptrStep_columns, foldl_ptrStep_sent]

theorem rowSideOf_cols (layout : Layout) (ch : LinkCh) (a : IdxAt) (jump eqQ chi message : List E) :
    ((rowSideOf layout ch a jump eqQ chi message).columns,
      (rowSideOf layout ch a jump eqQ chi message).sent) =
      layout.tables.zipIdx.foldl (gCol layout chi) ([], message.take (nValuesOf layout)) :=
  foldl_proj (fun acc : LinkRowSide ↦ (acc.columns, acc.sent)) _ _
    (rowStep_cols layout ch a jump eqQ chi) _ _

/-- **The fold splits the values among the tables**, in order. -/
theorem gCol_fold (layout : Layout) (chi : List E) : ∀ (L : List (Table × ℕ))
    (cs : List (List E × List (ℕ × E))) (s : List E),
    (L.map fun x ↦ (nonPointerOf layout x.2 x.1).length).sum ≤ s.length →
    ∃ S : List (List E), S.length = L.length ∧
      (∀ i (h1 : i < S.length) (h2 : i < L.length),
        S[i].length = (nonPointerOf layout L[i].2 L[i].1).length) ∧
      S.flatten ++ (L.foldl (gCol layout chi) (cs, s)).2 = s ∧
      (L.foldl (gCol layout chi) (cs, s)).1 = cs ++ List.zipWith (fun x sv ↦
        (chi.take (layout.tableLogHeights.getD x.2 0), (nonPointerOf layout x.2 x.1).zip sv)) L S
  | [], cs, s, _ => ⟨[], rfl, fun i h1 ↦ absurd h1 (by simp), by simp, by simp⟩
  | x :: L, cs, s, hs => by
    simp only [List.map_cons, List.sum_cons] at hs
    set k := (nonPointerOf layout x.2 x.1).length
    obtain ⟨S, h1, h2, h3, h4⟩ := gCol_fold layout chi L
      (cs ++ [(chi.take (layout.tableLogHeights.getD x.2 0),
        (nonPointerOf layout x.2 x.1).zip (s.take k))]) (s.drop k) (by simp; omega)
    refine ⟨s.take k :: S, by simp [h1], fun i hi1 hi2 ↦ ?_, ?_, ?_⟩
    · cases i with
      | zero => simp; omega
      | succ i => simpa using h2 i (by simpa using hi1) (by simpa using hi2)
    · rw [List.foldl_cons, List.flatten_cons, List.append_assoc]
      exact (congrArg (s.take k ++ ·) h3).trans (List.take_append_drop k s)
    · rw [List.foldl_cons]
      exact h4.trans (by simp)

/-- Two lists whose pairs are `(a, f a)` are a list and its image. -/
theorem eq_map_of_zip {α β : Type} (f : α → β) : ∀ (l₁ : List α) (l₂ : List β),
    l₂.length = l₁.length → (∀ p ∈ l₁.zip l₂, p.2 = f p.1) → l₂ = l₁.map f
  | [], [], _, _ => rfl
  | a :: l₁, b :: l₂, hl, h => by
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨h (a, b) (by simp), eq_map_of_zip f l₁ l₂ (by simpa using hl)
      fun p hp ↦ h p (by simp [hp])⟩
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

/-- A table's value on the stack: its column's extension at its row point. -/
def honestValue (layout : Layout) {μ : ℕ} (q : Column μ) (chi : List E) (t c : ℕ) : E :=
  rowMle (chi.take (layout.tableLogHeights.getD t 0))
    (columnValue layout q (globalColumnBases.getD t 0 + c))

theorem honestValues_eq (layout : Layout) {μ : ℕ} (q : Column μ) (chi : List E) :
    honestValues layout q chi = (layout.tables.zipIdx.map fun x ↦
      (nonPointerOf layout x.2 x.1).map (honestValue layout q chi x.2)).flatten := rfl

theorem nValuesOf_eq (layout : Layout) :
    nValuesOf layout = (layout.tables.zipIdx.map fun x ↦ (nonPointerOf layout x.2 x.1).length).sum :=
  rfl

/-- **The values are the stack's** when every column claim of the end holds. -/
theorem take_values_eq (layout : Layout) {μ : ℕ} (q : Column μ) (chi : List E)
    (hB : layout.tables.length ≤ globalColumnBases.length) (message : List E)
    (hl : nValuesOf layout ≤ message.length) (cols : List (List E × List (ℕ × E)))
    (hc : cols = (layout.tables.zipIdx.foldl (gCol layout chi) ([], message.take (nValuesOf layout))).1)
    (hcl : ∀ i (hi : i < cols.length) (hb : i < globalColumnBases.length), ∀ p ∈ cols[i].2,
      p.2 = rowMle cols[i].1 (columnValue layout q (globalColumnBases[i] + p.1))) :
    message.take (nValuesOf layout) = honestValues layout q chi := by
  set L := layout.tables.zipIdx
  obtain ⟨S, h1, h2, h3, h4⟩ := gCol_fold layout chi L [] (message.take (nValuesOf layout))
    (by rw [← nValuesOf_eq]; simp; omega)
  rw [← hc, List.nil_append] at h4
  have hS : S = L.map fun x ↦ (nonPointerOf layout x.2 x.1).map (honestValue layout q chi x.2) := by
    refine List.ext_getElem (by simp [h1]) fun i hi1 hi2 ↦ ?_
    have hiL : i < L.length := h1 ▸ hi1
    have hiT : i < layout.tables.length := by simpa [L] using hiL
    have hci : i < cols.length := by rw [h4]; simp [h1, hiL]
    have hcol : cols[i] = (chi.take (layout.tableLogHeights.getD L[i].2 0),
        (nonPointerOf layout L[i].2 L[i].1).zip S[i]) := by
      simp only [h4, List.getElem_zipWith]
    have hLi : L[i].2 = i := by simp [L]
    rw [List.getElem_map]
    refine eq_map_of_zip _ _ _ (h2 i hi1 hiL) fun p hp ↦ ?_
    have := hcl i hci (by omega) p (by rw [hcol]; exact hp)
    rw [this, hcol, honestValue, hLi]
    simp only
    rw [List.getD_eq_getElem (l := globalColumnBases) (d := 0) (by omega)]
  have hlen : S.flatten.length = nValuesOf layout := by
    rw [hS, nValuesOf_eq, List.length_flatten, List.map_map]
    congr 1
    refine List.map_congr_left fun x _ ↦ ?_
    simp
  have hrest : (L.foldl (gCol layout chi) ([], message.take (nValuesOf layout))).2 = [] := by
    have := congrArg List.length h3
    rw [List.length_append, hlen, List.length_take, min_eq_left hl] at this
    exact List.eq_nil_of_length_eq_zero (by omega)
  rw [← h3, hrest, List.append_nil, hS, honestValues_eq]

/-! ## The terminal check -/

theorem mem_linkColumnClaims_at (e : LinkEnd) (i : ℕ) (hi : i < e.columns.length)
    (hb : i < globalColumnBases.length) (p : ℕ × E) (hp : p ∈ e.columns[i].2) :
    (⟨globalColumnBases[i] + p.1, e.columns[i].1, p.2⟩ : ColumnClaim) ∈ linkColumnClaims e := by
  unfold linkColumnClaims
  refine List.mem_flatMap.2 ⟨(globalColumnBases[i], e.columns[i]), ?_, ?_⟩
  · have := List.getElem_mem (l := globalColumnBases.zip e.columns) (n := i) (by simp; omega)
    simpa using this
  · simp only [List.mem_map]
    exact ⟨p, hp, rfl⟩

/-- **The terminal check on the stack** (`LinkSummandFacts.tail`). -/
theorem tail_of_summand (layout : Layout) {μ : ℕ} (q : Column μ) (chunks : Chunks)
    (hB : layout.tables.length ≤ globalColumnBases.length) :
    ∀ theta0 drawn r m1 fresh chi qPoint message, message.length = tailLen layout →
    chi.length = linkRows layout → qPoint.length = linkQVars layout →
    (tailValues layout chunks theta0 drawn r m1 fresh (linkSplit layout r) chi qPoint message).1 ≠
      linkRow layout chunks q theta0 drawn r fresh (chi ++ qPoint) →
    ¬ LinkEndHolds layout q
      (tailValues layout chunks theta0 drawn r m1 fresh (linkSplit layout r) chi qPoint message).2 := by
  intro theta0 drawn r m1 fresh chi qPoint message hl hchi hq hne hE
  apply hne
  rw [tailValues_eq_F] at hE ⊢
  obtain ⟨hmem, hcols, hring⟩ := hE
  have hl' : message.length = nValuesOf layout + kBits := hl
  -- The memory term.
  have hm1 : m1 = honestM1 layout chunks q r := hmem
  -- The bit-slices.
  have hsl : message.drop (nValuesOf layout) = honestSlices layout q chi qPoint := by
    obtain ⟨hlen, hval⟩ := hring
    change (message.drop (nValuesOf layout)).length = kBits at hlen
    refine List.ext_getElem (by simp [honestSlices, hlen]) fun b hb1 hb2 ↦ ?_
    have := hval b (hlen ▸ hb1)
    change (message.drop (nValuesOf layout)).getD b 0 = sumE
      (((rowSideOf layout _ _ _ (eqKernel qPoint) chi message).pieces).map _) at this
    rw [rowSideOf_pieces, List.getD_eq_getElem _ _ hb1] at this
    rw [this]
    simp [honestSlices]
  -- The values.
  have hv : message.take (nValuesOf layout) = honestValues layout q chi := by
    refine take_values_eq layout q chi hB message (by omega)
      (rowSideOf layout (linkCh layout chunks theta0 drawn)
        (idxAt layout chunks (linkCh layout chunks theta0 drawn) r m1 (linkSplit layout r))
        (fresh.drop 1) (eqKernel qPoint) chi message).columns
      (congrArg Prod.fst (rowSideOf_cols layout _ _ _ _ chi message)) fun i hi hb p hp ↦ ?_
    exact hcols _ (mem_linkColumnClaims_at _ i hi hb p hp)
  have hmsg : message = honestMessage layout q chi qPoint := by
    rw [honestMessage, ← hv, ← hsl, List.take_append_drop]
  subst hm1 hmsg
  rw [linkRow, cube_full (by simp [linkRowVars, hchi, hq]), rowSummand]
  simp only [List.take_left' hchi, List.drop_left' hchi]

end

end LeanVM.Protocol.Relation
