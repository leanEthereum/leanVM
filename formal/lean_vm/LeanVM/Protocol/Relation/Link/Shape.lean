/-
  LeanVM.Protocol.Relation.Link.Shape

  The shape of what `verify_link` returns.
-/

module

public import LeanVM.Protocol.Relation.Iface
public import LeanVM.Protocol.Relation.Link.Tail
public import LeanVM.Protocol.Relation.Placement
public import LeanVM.Protocol.Relation.Link.Spec
import LeanVM.Protocol.Relation.Link.Valid

/-!
# The link's end has its shape

`linkShape`: what `verifyLink computedSplit` returns at an announced layout has `LinkShape`. The
run's challenges have their lengths (`returns_sumcheck`), and the end is `tailValues`' (`linkTail_eq`):
its memory point is the index point's first `log_memory` coordinates, its columns one entry per
table, the row point's first log-height coordinates and a prefix of the table's non-pointer
columns (`rowSide_inv`), and each ring piece at its pointer column's placement
(`placement_isSome`, `placement_variableCount`).
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier LeanVM.Protocol.Compile
open LeanVM.Protocol.Link

@[expose] public section

/-! ## Folds -/

theorem foldl_zipIdx_inv {α β : Type} (P : ℕ → β → Prop) (f : β → α × ℕ → β) :
    ∀ (L : List α) (n : ℕ) (b : β), P n b →
      (∀ k (hk : k < L.length) acc, P (n + k) acc → P (n + k + 1) (f acc (L[k], n + k))) →
      P (n + L.length) ((L.zipIdx n).foldl f b)
  | [], n, b, h0, _ => by simpa using h0
  | a :: L, n, b, h0, hs => by
    rw [List.zipIdx_cons, List.foldl_cons]
    have h1 : P (n + 1) (f b (a, n)) := hs 0 (by simp) b (by simpa using h0)
    have := foldl_zipIdx_inv P f L (n + 1) (f b (a, n)) h1 fun k hk acc hacc ↦ by
      have := hs (k + 1) (by simp; omega) acc (by rwa [show n + (k + 1) = n + 1 + k by omega])
      simpa [show n + (k + 1) = n + 1 + k by omega] using this
    simpa [show n + (L.length + 1) = n + 1 + L.length by omega] using this

theorem foldl_inv {α β : Type} (P : β → Prop) (f : β → α → β) :
    ∀ (L : List α) (b : β), P b → (∀ acc x, x ∈ L → P acc → P (f acc x)) → P (L.foldl f b)
  | [], _, h0, _ => h0
  | a :: L, b, h0, hs => foldl_inv P f L (f b a) (hs b a (by simp) h0)
      fun acc x hx hacc ↦ hs acc x (by simp [hx]) hacc


theorem map_fst_zip_prefix {α β : Type} : ∀ (l₁ : List α) (l₂ : List β), (l₁.zip l₂).map Prod.fst <+: l₁
  | [], _ => by simp
  | _ :: _, [] => by simp
  | a :: l₁, _ :: l₂ => by simpa using map_fst_zip_prefix l₁ l₂

/-! ## The row side's fold -/

/-- Table `t`'s non-pointer columns, in order (`verify_link`'s `nonPointer`). -/
def nonPointerCols (layout : Layout) (t : ℕ) (table : Table) : List ℕ :=
  (List.range table.width).filter fun c ↦ !((layout.tables.map (·.links.pointers)).getD t []).contains c

/-- A ring piece at table `t`'s pointer column's placement and the table's row point. -/
def GoodPiece (layout : Layout) (chi : List E) (t : ℕ) (piece : RingPiece) : Prop :=
  ∃ ptr ∈ ((layout.tables.map (·.links.pointers)).getD t []),
    piece.placement = some ((layout.placements.getD (globalColumnBases.getD t 0 + ptr) none).getD
      default) ∧ piece.point = chi.take (layout.tableLogHeights.getD t 0)

/-- What the row side's step does to the columns and the pieces. -/
def StepOK (layout : Layout) (chi : List E) (F : LinkRowSide → Table × ℕ → LinkRowSide) : Prop :=
  ∀ acc table t, (∃ s : List (ℕ × E), (F acc (table, t)).columns =
      acc.columns ++ [(chi.take (layout.tableLogHeights.getD t 0), s)] ∧
      s.map Prod.fst <+: nonPointerCols layout t table) ∧
    ∀ pc ∈ (F acc (table, t)).pieces, pc ∈ acc.pieces ∨ GoodPiece layout chi t pc

/-- The row side's invariant after `k` tables. -/
def RowInv (layout : Layout) (chi : List E) (k : ℕ) (acc : LinkRowSide) : Prop :=
  acc.columns.length = k ∧ (∀ t < k, (acc.columns.getD t ([], [])).1 =
      chi.take (layout.tableLogHeights.getD t 0) ∧
      ((acc.columns.getD t ([], [])).2.map Prod.fst) <+:
        nonPointerCols layout t (layout.tables.getD t default)) ∧
    ∀ pc ∈ acc.pieces, ∃ t < k, GoodPiece layout chi t pc

theorem rowInv_fold (layout : Layout) (chi : List E) (F : LinkRowSide → Table × ℕ → LinkRowSide)
    (hF : StepOK layout chi F) (b : LinkRowSide) (hb : b.columns = [] ∧ b.pieces = []) :
    RowInv layout chi layout.tables.length (layout.tables.zipIdx.foldl F b) := by
  have := foldl_zipIdx_inv (RowInv layout chi) F layout.tables 0 b
    ⟨by simp [hb.1], fun t ht ↦ absurd ht (by omega), fun pc hpc ↦ by simp [hb.2] at hpc⟩
    fun k hk acc ⟨hlen, hcols, hpcs⟩ ↦ by
      obtain ⟨⟨s, hs, hpre⟩, hp⟩ := hF acc layout.tables[k] (0 + k)
      simp only [zero_add] at hs hpre hp hlen hcols ⊢
      refine ⟨by simp [hs, hlen], fun t ht ↦ ?_, fun pc hpc ↦ ?_⟩
      · rw [hs]
        by_cases htk : t < k
        · rw [List.getD_append _ _ _ _ (by omega)]
          exact hcols t htk
        · obtain rfl : t = k := by omega
          rw [List.getD_append_right _ _ _ _ (by omega), hlen, Nat.sub_self]
          simp only [List.getD_cons_zero]
          refine ⟨by trivial, ?_⟩
          rwa [List.getD_eq_getElem _ _ hk]
      · rcases hp pc hpc with h | h
        · obtain ⟨t, ht, h⟩ := hpcs pc h
          exact ⟨t, by omega, h⟩
        · exact ⟨k, by omega, h⟩
  simpa using this


theorem foldl_columns {α : Type} (F : LinkRowSide → α → LinkRowSide)
    (hF : ∀ a x, (F a x).columns = a.columns) : ∀ (L : List α) (b : LinkRowSide),
    (L.foldl F b).columns = b.columns
  | [], _ => rfl
  | x :: L, b => (foldl_columns F hF L (F b x)).trans (hF b x)

theorem foldl_pieces {α : Type} (F : LinkRowSide → α → LinkRowSide) (Q : RingPiece → Prop) :
    ∀ (L : List α), (∀ a x, x ∈ L → ∀ pc ∈ (F a x).pieces, pc ∈ a.pieces ∨ Q pc) →
    ∀ (b : LinkRowSide), ∀ pc ∈ (L.foldl F b).pieces, pc ∈ b.pieces ∨ Q pc
  | [], _, _, _, h => .inl h
  | x :: L, hF, b, pc, h => by
    rcases foldl_pieces F Q L (fun a y hy ↦ hF a y (by simp [hy])) (F b x) pc h with h' | h'
    · exact hF b x (by simp) pc h'
    · exact .inr h'

theorem fst_mem_of_mem_zipIdx {α : Type} : ∀ (l : List α) (n : ℕ) (x : α × ℕ), x ∈ l.zipIdx n →
    x.1 ∈ l
  | [], _, _, h => by simp at h
  | a :: l, n, x, h => by
    rw [List.zipIdx_cons, List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · exact List.mem_cons_of_mem _ (fst_mem_of_mem_zipIdx l (n + 1) x h)

/-! ## The layout's tables -/

/-- Every table's pointer columns: placed, no `KECCAK` output lane, inside the table. -/
theorem pointers_placed : ∀ t < nTables, ∀ ptr ∈ (tables.getD t default).links.pointers,
    globalColumnBases.getD t 0 + ptr < 116 ∧
      ¬ (globalColumnBases.getD opKeccak 0 + keccakOut ≤ globalColumnBases.getD t 0 + ptr ∧
        globalColumnBases.getD t 0 + ptr < globalColumnBases.getD opKeccak 0 + keccakOut +
          keccakStateLanes) ∧
      ptr < tableWidths.getD t 0 := by
  decide +kernel

theorem tables_width : ∀ t < nTables, (tables.getD t default).width = tableWidths.getD t 0 := by
  decide +kernel

theorem tables_length : tables.length = nTables := by decide +kernel

/-- An announced layout is `buildLayout`'s. -/
theorem announced_build {bytecode : List K} {layout : Layout} {ρ : ℕ}
    (h : Announced bytecode layout ρ) : ∃ lm rows, buildLayout bytecode lm rows = some layout := by
  unfold Announced readAnnouncedSizes at h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨l, hl, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  have he := VerifierProgram.returns_ret h
  simp only [Prod.mk.injEq] at he
  exact ⟨_, _, he.1 ▸ returns_liftOption hl⟩

/-! ## The shape -/

/-- **The link's end from a row side with the invariant** has its shape. -/
theorem linkShape_of_rowSide {bytecode : List K} {layout : Layout} {ρ : ℕ}
    (hA : Announced bytecode layout ρ) {chi : List E} (hchi : chi.length = linkRows layout)
    {r : List E} (hr : layout.logMemory ≤ r.length) (R : LinkRowSide)
    (hR : RowInv layout chi layout.tables.length R) (ms : E × E) (mv : E) (sl bp : List E)
    (hsl : sl.length = kBits) :
    LinkShape layout (LinkEnd.mk (r.take layout.logMemory) ms mv R.columns ⟨R.pieces, sl⟩ bp) := by
  obtain ⟨-, hT, -⟩ := announced_facts hA
  obtain ⟨lm, rows, hB⟩ := announced_build hA
  obtain ⟨hlen, hcols, hpcs⟩ := hR
  rw [hT, tables_length] at hlen
  have hheight : ∀ t, (chi.take (layout.tableLogHeights.getD t 0)).length =
      layout.tableLogHeights.getD t 0 := fun t ↦ by
    rw [List.length_take, hchi]
    exact min_eq_left (getD_le_foldl_max _ _ _)
  have hptr : ∀ t < tables.length, (layout.tables.map (·.links.pointers)).getD t [] =
      (tables.getD t default).links.pointers := fun t ht ↦ by
    rw [hT]
    simp [List.getD_eq_getElem?_getD, ht]
  refine ⟨by simp [hr], hlen, fun t ht ↦ ?_, fun t ht ↦ ?_, fun pc hpc ↦ ?_, hsl⟩
  · rw [(hcols t (by rwa [hT, tables_length])).1, hheight]
  · have hpre := (hcols t (by rwa [hT, tables_length])).2
    rw [hT] at hpre
    have hnd : (nonPointerCols layout t (tables.getD t default)).Nodup :=
      List.nodup_range.filter _
    refine ⟨hnd.sublist hpre.sublist, fun x hx ↦ ?_⟩
    have hx' := hpre.subset (List.mem_map_of_mem (f := Prod.fst) hx)
    simp only [nonPointerCols, List.mem_filter, List.mem_range] at hx'
    rw [← tables_width t ht]
    exact hx'.1
  · obtain ⟨t, ht, ptr, hptrt, hplace, hpoint⟩ := hpcs pc hpc
    rw [hT, tables_length] at ht
    rw [hptr t (by rw [tables_length]; exact ht)] at hptrt
    obtain ⟨hc, hk, hw⟩ := pointers_placed t ht ptr hptrt
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (placement_isSome hB hc hk)
    refine ⟨_, p, hp, by rw [hplace, hp]; rfl, ?_⟩
    rw [hpoint, hheight, placement_variableCount hB hp]
    exact (columnKappas_table _ _ ht hw).symm


/-- **`tailValues`' end has the link's shape.** -/
theorem tailValues_shape {bytecode : List K} {layout : Layout} {ρ : ℕ}
    (hA : Announced bytecode layout ρ) (chunks : Chunks) (theta0 : E) (drawn r : List E) (m1 : E)
    (fresh : List E) (split : Split) (chi qPoint message : List E)
    (hchi : chi.length = linkRows layout) (hr : layout.logMemory ≤ r.length)
    (hm : message.length = tailLen layout) :
    LinkShape layout (tailValues layout chunks theta0 drawn r m1 fresh split chi qPoint message).2 := by
  unfold tailValues
  dsimp only
  refine linkShape_of_rowSide hA hchi hr _ (rowInv_fold layout chi _ ?_ _ ⟨rfl, rfl⟩) _ _ _ _
    (by rw [List.length_drop, hm]; exact Nat.add_sub_cancel_left _ _)
  intro acc table t
  dsimp only
  refine ⟨⟨(nonPointerCols layout t table).zip
    (acc.sent.take (nonPointerCols layout t table).length), ?_, map_fst_zip_prefix _ _⟩, ?_⟩
  · rw [foldl_columns]
    · rfl
    · intro a x
      obtain ⟨p, k⟩ := x
      rfl
  · intro pc hpc
    have key := foldl_pieces _ (GoodPiece layout chi t) _ ?_ _ pc hpc
    · exact key
    intro a x hx pc' hpc'
    obtain ⟨p, k⟩ := x
    simp only [List.mem_append, List.mem_singleton] at hpc'
    rcases hpc' with h | rfl
    · exact .inl h
    · exact .inr ⟨p, fst_mem_of_mem_zipIdx _ _ _ hx, rfl, rfl⟩

/-- What `verifyLink` returns is `tailValues`' end, at challenges of their lengths. -/
theorem returns_verifyLink {layout : Layout} {e : LinkEnd}
    (h : VerifierProgram.Returns (verifyLink computedSplit layout) e) :
    ∃ chunks theta0 drawn r m1 fresh chi qPoint message,
      Chunks.new (linkWidth layout) = some chunks ∧ r.length = chunks.width ∧
      chi.length = linkRows layout ∧ message.length = tailLen layout ∧
      e = (tailValues layout chunks theta0 drawn r m1 fresh
        (splitAt layout.bytecode (r.take layout.logBytecode) (pcSlots layout.tables)) chi qPoint
        message).2 := by
  cases hch : Chunks.new (linkWidth layout) with
  | none =>
    have hfail : verifyLink computedSplit layout = VerifierProgram.fail := by
      rw [verifyLink_eq_linkSkeleton]
      unfold linkSkeleton
      rw [hch]
      rfl
    rw [hfail] at h
    cases h
  | some chunks =>
    rw [verifyLink_eq_of_chunks hch] at h
    obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
    obtain ⟨x, -, h⟩ := VerifierProgram.returns_bind h
    obtain ⟨y, hy, h⟩ := VerifierProgram.returns_bind h
    unfold linkRowPhase at h
    obtain ⟨m1, -, h⟩ := VerifierProgram.returns_bind h
    obtain ⟨fresh, -, h⟩ := VerifierProgram.returns_bind h
    obtain ⟨split, hs, h⟩ := VerifierProgram.returns_bind h
    obtain ⟨⟨chi, c1⟩, hz, h⟩ := VerifierProgram.returns_bind h
    dsimp only at h
    obtain ⟨⟨qPoint, c2⟩, -, h⟩ := VerifierProgram.returns_bind h
    dsimp only at h
    rw [linkTail_eq] at h
    obtain ⟨message, hmsg, h⟩ := VerifierProgram.returns_bind h
    obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
    have he := VerifierProgram.returns_ret h
    rw [computedSplit_eq] at hs
    obtain ⟨_, -, hs⟩ := VerifierProgram.returns_bind hs
    have hs' := VerifierProgram.returns_ret hs
    subst hs'
    refine ⟨chunks, x.1, x.2, y.1, m1, fresh, chi, qPoint, message, rfl, ?_, ?_, ?_, he⟩
    · simpa using returns_sumcheck hy
    · simpa [linkRows] using returns_sumcheck hz
    · cases hmsg with
      | readPacked _ xs hl hr => cases hr; exact hl

/-- **The link's end has its shape** (`LinkIface.linkShape`). -/
theorem linkShape_holds (bytecode : List K) (layout : Layout) (ρ : ℕ)
    (hA : Announced bytecode layout ρ) (e : LinkEnd)
    (h : VerifierProgram.Returns (verifyLink computedSplit layout) e) : LinkShape layout e := by
  obtain ⟨chunks, theta0, drawn, r, m1, fresh, chi, qPoint, message, hch, hr, hchi, hm, rfl⟩ :=
    returns_verifyLink h
  refine tailValues_shape hA chunks theta0 drawn r m1 fresh _ chi qPoint message hchi ?_ hm
  rw [hr, Chunks.new_width hch, linkWidth, pointerWidth]
  omega

end

end LeanVM.Protocol.Relation
