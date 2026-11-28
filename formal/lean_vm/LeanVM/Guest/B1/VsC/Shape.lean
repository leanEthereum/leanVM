/-
  LeanVM.Guest.B1.VsC.Shape

  The shape of an accepted child's layout: what the deferring verifier's acceptance gives of the
  sizes the guest's `verify_sub` range-checks.
-/

module

public import LeanVM.Guest.B1.VsC.Announced
public import LeanVM.Facts.Stack

/-!
# An accepted child's shape

`VsShape layout r`: the facts of the announced layout and rate that `verify_sub`'s checks of the
sizes need, read off the checks the deferring verifier makes: the rate in `1 ..= 4` and the stack
log in `16 ..= 30` (`readAnnouncedSizes`), the layout `buildLayout`'s (the memory at least
`MIN_LOG_MEMORY`, one row count per table, each height the least power of two holding the rows, at
least the floor), and the pointer width in `1 ..= MAX_WIDTH = 24` (`verify_link`'s `Chunks::new`).

`vsShape_of_verifyDeferred`: an accepted child's announced layout and rate have the shape.
The consequences `verify_sub`'s range checks read: the memory's log, the cycles' bit length and
every table's height at most `24` (`VsShape.logMemory_le`, `cycles_lt`, `height_le`), every
height at least its floor and its rows at most `2^height` (`height_ge_floor`, `rows_le`).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

/-- The cycles of a layout, `verify_link`'s: its tables' row counts summed. -/
def cyclesOf (layout : Layout) : ℕ := layout.tableRows.foldl (· + ·) 0

/-- The pointer width of a layout, `verify_link`'s. -/
def widthOf (layout : Layout) : ℕ := pointerWidth layout.logMemory layout.logBytecode (cyclesOf layout)

/-- **The shape of an accepted child's layout and rate.** -/
structure VsShape (bytecode : List K) (layout : Layout) (r : ℕ) : Prop where
  bytecode_eq : layout.bytecode = bytecode
  logBytecode_eq : bytecode.length >>> bytecodeSlotBits = 2 ^ layout.logBytecode
  rate_ge : 1 ≤ r
  rate_le : r ≤ 4
  stack_ge : Whir.minLogStack ≤ layout.stackLog
  stack_le : layout.stackLog ≤ Whir.maxLogStack
  logMemory_ge : minLogMemory ≤ layout.logMemory
  rows_length : layout.tableRows.length = nTables
  heights : layout.tableLogHeights =
    List.zipWith (fun rows floor ↦ max (log2Ceil rows) floor) layout.tableRows tableLogFloors
  width_ge : 1 ≤ widthOf layout
  width_le : widthOf layout ≤ maxPointerWidth

/-- The fields of a layout `buildLayout` gives. -/
theorem buildLayout_fields {bytecode : List K} {logMemory : ℕ} {tableRows : List ℕ}
    {layout : Layout} (h : buildLayout bytecode logMemory tableRows = some layout) :
    layout.logMemory = logMemory ∧ layout.tableRows = tableRows ∧
      layout.tableLogHeights =
        List.zipWith (fun rows floor ↦ max (log2Ceil rows) floor) tableRows tableLogFloors ∧
      minLogMemory ≤ logMemory ∧ tableRows.length = nTables := by
  unfold buildLayout at h
  split at h
  · cases h
  · split at h
    · next hc =>
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨rfl, rfl, rfl, hc.1, hc.2.2.2.2.2⟩
    · cases h

/-- What `sizesOf` checks of the layout and rate it gives. -/
theorem sizesOf_facts {bytecode : List K} {a : List E} {layout : Layout} {r : ℕ}
    (h : sizesOf bytecode a = some (layout, r)) :
    1 ≤ r ∧ r ≤ 4 ∧ Whir.minLogStack ≤ layout.stackLog ∧ layout.stackLog ≤ Whir.maxLogStack ∧
      ∃ logMemory tableRows, buildLayout bytecode logMemory tableRows = some layout := by
  unfold sizesOf at h
  split at h
  · simp only at h
    split at h
    · next h2 =>
      obtain ⟨l, hl, h⟩ := Option.bind_eq_some_iff.mp h
      split at h
      · next h3 =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨h2.1, h2.2, h3.1, h3.2, _, _, hl⟩
      · cases h
    · cases h
  · cases h

/-- **The rest of an accepted run chunks the pointer width**: `Chunks::new` accepts it. -/
theorem rest_chunks {bytecodeSplit : List K → List E → List (ℕ × ℕ) → VerifierProgram Split}
    {publicInput : Digest} {layout : Layout} {r : ℕ}
    (h : VerifierProgram.Returns (verifyRest bytecodeSplit publicInput (layout, r)) ()) :
    ∃ c, Chunks.new (widthOf layout) = some c := by
  unfold verifyRest at h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨_, hl, -⟩ := VerifierProgram.returns_bind h
  unfold verifyLink at hl
  obtain ⟨c, hc, -⟩ := VerifierProgram.returns_bind hl
  exact ⟨c, returns_liftOption hc⟩

/-- A width `Chunks::new` accepts is in `1 ..= MAX_WIDTH`. -/
theorem width_of_chunks {w : ℕ} {c : Chunks} (h : Chunks.new w = some c) :
    1 ≤ w ∧ w ≤ maxPointerWidth := by
  unfold Chunks.new at h
  split at h
  · assumption
  · cases h

/-- **An accepted child's announced layout and rate have the shape `verify_sub` checks.** -/
theorem vsShape_of_verifyDeferred {bytecode : List K} {iv publicInput : Digest} {fresh : FreshClaim}
    {proof : Proof} (h : verifyDeferred bytecode iv publicInput fresh proof = true) :
    ∃ layout r, announcedLayoutAndRate bytecode proof.stream = some (layout, r) ∧
      VsShape bytecode layout r := by
  obtain ⟨⟨layout, r⟩, hann, hrest⟩ := accepted_rest h
  refine ⟨layout, r, hann, ?_⟩
  have hs := announced_eq_run (fun _ ↦ default) (fun _ ↦ default) bytecode
    (s := ⟨⟨default, [], none⟩, proof.stream, [], []⟩) rfl
  have hsz : sizesOf bytecode (proof.stream.take (2 + nTables)) = some (layout, r) := by
    have e := hs.symm.trans hann
    rw [run_readSizes _ _ bytecode rfl] at e
    split at e
    · exact e
    · cases e
  obtain ⟨hr1, hr4, hs1, hs2, lm, rows, hb⟩ := sizesOf_facts hsz
  obtain ⟨hlm, hrows, hh, hmin, hlen⟩ := buildLayout_fields hb
  obtain ⟨c, hc⟩ := rest_chunks hrest
  obtain ⟨hw1, hw2⟩ := width_of_chunks hc
  obtain ⟨hbc, -, hlb, -⟩ := buildLayout_facts hb
  exact ⟨hbc, hlb, hr1, hr4, hs1, hs2, hlm ▸ hmin, hrows ▸ hlen, hrows ▸ hh, hw1, hw2⟩

theorem lt_pow_bitLength (n : ℕ) : n < 2 ^ bitLength n := by
  unfold bitLength
  split
  · omega
  · exact Nat.lt_log2_self

theorem pow_pred_bitLength_le {n : ℕ} (h : n ≠ 0) : 2 ^ (bitLength n - 1) ≤ n := by
  unfold bitLength
  simp only [h, ↓reduceIte, Nat.add_sub_cancel]
  exact Nat.log2_self_le h

theorem foldl_add_eq (l : List ℕ) : ∀ acc, l.foldl (· + ·) acc = acc + l.sum := by
  induction l with
  | nil => intro acc; simp
  | cons a l ih => intro acc; simp only [List.foldl_cons, List.sum_cons, ih]; omega

theorem getD_le_sum (l : List ℕ) (t : ℕ) : l.getD t 0 ≤ l.sum := by
  rw [List.getD_eq_getElem?_getD]
  cases h : l[t]? with
  | none => simp
  | some a => exact List.le_sum_of_mem (List.mem_of_getElem? h)

theorem cycles_lt (layout : Layout) : cyclesOf layout < 2 ^ widthOf layout := by
  have h1 := lt_pow_bitLength (cyclesOf layout)
  have h2 : bitLength (cyclesOf layout) ≤ widthOf layout := by unfold widthOf pointerWidth; omega
  exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) h2)

/-- The width is the cycles' bit length, the memory's log or the program's. -/
theorem width_cases (layout : Layout) : widthOf layout = bitLength (cyclesOf layout) ∨
    widthOf layout = layout.logMemory ∨ widthOf layout = layout.logBytecode ∨ widthOf layout = 1 := by
  unfold widthOf pointerWidth; omega

theorem rows_le_cycles (layout : Layout) (t : ℕ) : layout.tableRows.getD t 0 ≤ cyclesOf layout := by
  unfold cyclesOf
  rw [foldl_add_eq, Nat.zero_add]
  exact getD_le_sum _ t

theorem floors_le : ∀ t < nTables, tableLogFloors.getD t 0 ≤ 9 := by decide

namespace VsShape

variable {bytecode : List K} {layout : Layout} {r : ℕ} (S : VsShape bytecode layout r)
include S

theorem logMemory_le : layout.logMemory ≤ 24 := by
  have := S.width_le
  unfold widthOf pointerWidth maxPointerWidth at this
  omega

theorem logBytecode_le : layout.logBytecode ≤ 24 := by
  have := S.width_le
  unfold widthOf pointerWidth maxPointerWidth at this
  omega

theorem bitLength_cycles_le : bitLength (cyclesOf layout) ≤ 24 := by
  have := S.width_le
  unfold widthOf pointerWidth maxPointerWidth at this
  omega

theorem cycles_lt_24 : cyclesOf layout < 2 ^ 24 :=
  lt_of_lt_of_le (cycles_lt layout) (Nat.pow_le_pow_right (by norm_num) S.width_le)

/-- Table `t`'s height: the least power of two holding its rows, at least its floor. -/
theorem height_eq {t : ℕ} (ht : t < nTables) : layout.tableLogHeights.getD t 0 =
    max (log2Ceil (layout.tableRows.getD t 0)) (tableLogFloors.getD t 0) := by
  have hl := S.rows_length
  have hf : tableLogFloors.length = nTables := rfl
  rw [S.heights, List.getD_eq_getElem?_getD, List.getElem?_zipWith,
    List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)]
  rfl

theorem height_le {t : ℕ} (ht : t < nTables) : layout.tableLogHeights.getD t 0 ≤ 24 := by
  rw [S.height_eq ht]
  have h1 : log2Ceil (layout.tableRows.getD t 0) ≤ 24 :=
    (log2Ceil_le_iff _ _).mpr (le_of_lt (lt_of_le_of_lt (rows_le_cycles layout t) S.cycles_lt_24))
  have h2 := floors_le t ht
  omega

theorem height_ge_floor {t : ℕ} (ht : t < nTables) :
    tableLogFloors.getD t 0 ≤ layout.tableLogHeights.getD t 0 := by
  rw [S.height_eq ht]; omega

theorem rows_le {t : ℕ} (ht : t < nTables) :
    layout.tableRows.getD t 0 ≤ 2 ^ layout.tableLogHeights.getD t 0 :=
  (log2Ceil_le_iff _ _).mp (by rw [S.height_eq ht]; omega)

/-- A height above its floor is the least: its rows exceed half of it. -/
theorem height_least {t : ℕ} (ht : t < nTables) :
    layout.tableLogHeights.getD t 0 = tableLogFloors.getD t 0 ∨
      2 ^ (layout.tableLogHeights.getD t 0 - 1) < layout.tableRows.getD t 0 := by
  rw [S.height_eq ht]
  by_cases h : log2Ceil (layout.tableRows.getD t 0) ≤ tableLogFloors.getD t 0
  · left; omega
  · right
    rw [Nat.max_eq_left (by omega)]
    by_contra hc
    have := (log2Ceil_le_iff (layout.tableRows.getD t 0)
      (log2Ceil (layout.tableRows.getD t 0) - 1)).mpr (by omega)
    omega

end VsShape

end
end LeanVM.Guest.B1.VsC
