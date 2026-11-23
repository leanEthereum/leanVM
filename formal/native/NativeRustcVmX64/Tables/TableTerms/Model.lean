module

public import NativeVm.Math.Tables.Rows
public import NativeRustcVm.Rodata
public import NativeRustcVm.Arrays.ReadLemmas
public import NativeRustcVm.MemLemmas
public import NativeRustcVm.Sumcheck.RoundPoly

/-!
# `table_terms`: the model's side

`TABLES` as words (`tablesWords`, five per table: opcode, width, constraint count, padding span),
each table's words the model's (`tw_opcode`, `tw_width`, `tw_nc`); the widths at most `92`; the
constraint cursor before table `i` (`cursorAt i`) with the table's constraints at most `2`;
`constraintsW` of at most two elements; the fold over the first `i + 1` rows from the first `i`
(`foldlM_take_succ`); the elements a slice's prefix and sub-slice read (`ewsOf_take`,
`ewsOf_sub`).
-/

namespace NativeRustcVmX64.Tables.TableTerms

open NativeVm.Model NativeRustcVm

@[expose] public section

/-- A `TABLES` entry's five words. -/
def tableWords (t : Data.Table) : List UInt64 :=
  [t.opcode.toUInt64, t.width.toUInt64, t.nConstraints.toUInt64, t.padding.start.toUInt64,
    t.padding.len.toUInt64]

/-- `TABLES` as words. -/
def tablesWords : List UInt64 := Data.tables.flatMap tableWords

/-- Table `i`. -/
abbrev tb (i : Nat) : TableW := tablesW.getD i default

/-- The constraint cursor before table `i`. -/
def cursorAt (i : Nat) : Nat := ((List.range i).map fun j ↦ (tb j).nConstraints).sum

end

public section

theorem tables_bytes : Data.Item.bytes .tables = tablesWords.flatMap wordBytes := by
  simp only [Data.Item.bytes, tablesWords, List.flatMap_assoc]
  congr 1

theorem tablesWords_length : tablesWords.length = 30 := by decide

theorem tb_eq (i : Nat) :
    tb i = (LeanVM.Protocol.Verifier.tables.map TableW.ofTable).getD i default :=
  NativeVm.Math.Tables.tablesW_get i

theorem tw_opcode {i : Nat} (hi : i < 6) : (tablesWords.getD (5 * i) 0).toNat = (tb i).opcode := by
  rw [tb_eq]
  interval_cases i <;> decide

theorem tw_width {i : Nat} (hi : i < 6) :
    (tablesWords.getD (5 * i + 1) 0).toNat = (tb i).width := by
  rw [tb_eq]
  interval_cases i <;> decide

theorem tw_nc {i : Nat} (hi : i < 6) :
    (tablesWords.getD (5 * i + 2) 0).toNat = (tb i).nConstraints := by
  rw [tb_eq]
  interval_cases i <;> decide

theorem width_le {i : Nat} (hi : i < 6) : (tb i).width ≤ 92 := by
  rw [tb_eq]
  interval_cases i <;> decide

theorem cursor_le {i : Nat} (hi : i < 6) : cursorAt i + (tb i).nConstraints ≤ 2 := by
  simp only [cursorAt, tb_eq]
  interval_cases i <;> decide

theorem cursorAt_zero : cursorAt 0 = 0 := rfl

theorem cursorAt_succ (i : Nat) : cursorAt (i + 1) = cursorAt i + (tb i).nConstraints := by
  simp [cursorAt, List.range_succ]

/-- `constraintsW` has at most two elements. -/
theorem constraintsW_size (op : Nat) (row : Array EW) : (constraintsW op row).size ≤ 2 := by
  unfold constraintsW
  split <;> simp

/-- **The fold over the first `i + 1` elements**: the first `i`'s, then element `i`. -/
theorem foldlM_take_succ {α β : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : β → α → m β) (b : β) (L : List α) {i : Nat} (hi : i < L.length) :
    (L.take (i + 1)).foldlM f b = (L.take i).foldlM f b >>= fun acc ↦ f acc L[i] := by
  rw [List.take_succ_eq_append_getElem hi, List.foldlM_append]
  simp

/-- The whole fold from a prefix's. -/
theorem foldlM_take_drop {α β : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : β → α → m β) (b : β) (L : List α) (i : Nat) :
    L.foldlM f b = (L.take i).foldlM f b >>= fun acc ↦ (L.drop i).foldlM f acc := by
  conv_lhs => rw [← List.take_append_drop i L]
  rw [List.foldlM_append]

/-- A prefix of a slice. -/
theorem ewsOf_take (d : Mem 64) (a : BitVec 64) (n h : Nat) :
    ewsOf d a (min h n) = (ewsOf d a n).take h := by
  unfold ewsOf
  rw [← List.map_take, List.take_range]

/-- A part of a slice. -/
theorem ewsOf_sub (d : Mem 64) (a : BitVec 64) {n c k : Nat} (hck : c + k ≤ n) :
    ewsOf d (a + BitVec.ofNat 64 (16 * c)) k = ((ewsOf d a n).drop c).take k := by
  apply List.ext_getElem
  · simp only [ewsOf, List.length_map, List.length_range, List.length_take, List.length_drop]
    omega
  · intro j h1 h2
    simp only [ewsOf, List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range]
    rw [addr_add_add, ← Nat.mul_add]

end

end NativeRustcVmX64.Tables.TableTerms
