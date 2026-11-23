module

public import NativeRustcVmArm.Spec.Layout
public import NativeRustcVm.MemLemmas

/-!
# `ladder`'s values

Inside the window (`Whir.Admissible μ r`), `Whir.ladder μ r` has `nOf μ` levels, level `i` folding
`foldAt i` variables at rate `r + 3 i` with `qAt μ r i` queries (`ladderW`, `ladder_eq`), the
entry `(r - 1, μ - 16)` of `QUERY_TABLE`, and `QUERY_LEVELS` holds `nOf μ` there (`levels_eq`):
both checked on the window by `decide +kernel`. The data's words in memory: `QUERY_LEVELS`'
entry (`levels_word`) and `QUERY_TABLE`'s `i`th count of the entry (`table_word`).
-/

namespace NativeRustcVmArm.Layout.Ladder

open LeanVM.Parameters NativeRustcVm

@[expose] public section

/-- The level count of a `μ`-variable stack. -/
def nOf (μ : Nat) : Nat := if μ < 20 then 3 else if μ < 24 then 4 else if μ < 28 then 5 else 6

/-- `QUERY_TABLE`'s `i`th query count of the entry `(r - 1, μ - 16)`. -/
def qAt (μ r i : Nat) : Nat := Data.queryTable.flatten.flatten.getD (90 * (r - 1) + 6 * (μ - 16) + i) 0

/-- Level `i`'s fold. -/
def foldAt (i : Nat) : Nat := if i = 0 then 6 else 4

/-- The ladder of the window. -/
def ladderW (μ r : Nat) : List Whir.Level :=
  (List.range (nOf μ)).map fun i ↦ ⟨foldAt i, r + 3 * i, qAt μ r i⟩

end

public section

theorem ladder_table : ∀ μ < 31, ∀ r < 5, Whir.Admissible μ r →
    Whir.ladder μ r = some (ladderW μ r) := by
  decide +kernel

theorem levels_table : ∀ μ < 31, ∀ r < 5, Whir.Admissible μ r →
    Data.queryLevels.flatten.getD (15 * (r - 1) + (μ - 16)) 0 = nOf μ := by
  decide +kernel

theorem queries_le : ∀ j < 360, Data.queryTable.flatten.flatten.getD j 0 ≤ 230 := by
  decide +kernel

theorem length_levels : Data.queryLevels.flatten.length = 60 := by decide +kernel

theorem length_table : Data.queryTable.flatten.flatten.length = 360 := by decide +kernel

theorem admissible_iff {μ r : Nat} : Whir.Admissible μ r ↔ 16 ≤ μ ∧ μ ≤ 30 ∧ 1 ≤ r ∧ r ≤ 4 :=
  Iff.rfl

theorem ladder_eq {μ r : Nat} (h : Whir.Admissible μ r) : Whir.ladder μ r = some (ladderW μ r) := by
  have := admissible_iff.mp h
  exact ladder_table μ (by omega) r (by omega) h

theorem ladder_none {μ r : Nat} (h : ¬Whir.Admissible μ r) : Whir.ladder μ r = none := by
  simp [Whir.ladder, h]

theorem levels_eq {μ r : Nat} (h : Whir.Admissible μ r) :
    Data.queryLevels.flatten.getD (15 * (r - 1) + (μ - 16)) 0 = nOf μ := by
  have := admissible_iff.mp h
  exact levels_table μ (by omega) r (by omega) h

theorem qAt_le (μ r i : Nat) : qAt μ r i ≤ 230 := by
  unfold qAt
  rcases Nat.lt_or_ge (90 * (r - 1) + 6 * (μ - 16) + i) 360 with h | h
  · exact queries_le _ h
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [length_table]; exact h)]
    simp

theorem nOf_le (μ : Nat) : 3 ≤ nOf μ ∧ nOf μ ≤ 6 := by
  unfold nOf; split_ifs <;> omega

theorem length_ladderW (μ r : Nat) : (ladderW μ r).length = nOf μ := by
  simp [ladderW]

theorem length_natBytes (xs : List Nat) : (xs.flatMap Data.natBytes).length = 8 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.flatMap_cons, List.length_append, ih, List.length_cons]
    simp only [Data.natBytes, length_wordBytes]
    omega

theorem length_levels_bytes : Data.Item.queryLevels.bytes.length = 480 := by
  show (Data.queryLevels.flatten.flatMap Data.natBytes).length = 480
  rw [length_natBytes, length_levels]

theorem length_table_bytes : Data.Item.queryTable.bytes.length = 2880 := by
  show (Data.queryTable.flatten.flatten.flatMap Data.natBytes).length = 2880
  rw [length_natBytes, length_table]

/-- Number `j` of numbers in memory. -/
theorem wordAt_nats {d : Mem 64} {a : BitVec 64} {xs : List Nat}
    (h : BytesAt d a (xs.flatMap Data.natBytes)) {j : Nat} (hj : j < xs.length) :
    WordAt d (a + BitVec.ofNat 64 (8 * j)) (xs.getD j 0).toUInt64 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  have := BytesAt.flatMap_getElem (f := Data.natBytes) (k := 8)
    (fun x ↦ length_wordBytes x.toUInt64) h hj
  exact this

/-- **`QUERY_LEVELS`' entry** `(r - 1, μ - 16)`: `nOf μ`. -/
theorem levels_word {d : Mem 64} {a : BitVec 64} (h : BytesAt d a Data.Item.queryLevels.bytes)
    {μ r : Nat} (hadm : Whir.Admissible μ r) :
    WordAt d (a + BitVec.ofNat 64 (120 * (r - 1)) + BitVec.ofNat 64 (8 * (μ - 16)))
      (nOf μ).toUInt64 := by
  have hb := admissible_iff.mp hadm
  have := wordAt_nats (xs := Data.queryLevels.flatten) h
    (j := 15 * (r - 1) + (μ - 16)) (by rw [length_levels]; omega)
  rw [levels_eq hadm] at this
  rw [addr_add_add, show 120 * (r - 1) + 8 * (μ - 16) = 8 * (15 * (r - 1) + (μ - 16)) by omega]
  exact this

/-- **`QUERY_TABLE`'s entry** `(r - 1, μ - 16)`: its `i`th count. -/
theorem table_word {d : Mem 64} {a : BitVec 64} (h : BytesAt d a Data.Item.queryTable.bytes)
    {μ r : Nat} (hadm : Whir.Admissible μ r) {i : Nat} (hi : i < 6) :
    WordAt d (a + BitVec.ofNat 64 (720 * (r - 1)) + BitVec.ofNat 64 (8 * i + 48 * (μ - 16)))
      (qAt μ r i).toUInt64 := by
  have hb := admissible_iff.mp hadm
  have := wordAt_nats (xs := Data.queryTable.flatten.flatten) h
    (j := 90 * (r - 1) + 6 * (μ - 16) + i) (by rw [length_table]; omega)
  rw [addr_add_add,
    show 720 * (r - 1) + (8 * i + 48 * (μ - 16)) = 8 * (90 * (r - 1) + 6 * (μ - 16) + i) by omega]
  exact this

end

end NativeRustcVmArm.Layout.Ladder
