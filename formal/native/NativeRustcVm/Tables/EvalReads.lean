module

public import NativeRustcVm.Tables.Rep
public import NativeRustcVm.Arrays.ReadLemmas
public import NativeRustcVm.MemLemmas

/-!
# Reading the tables' entries

Table `i`'s point (`ptOf`) and values (`valsOf`) in its `TableEvalW` at `e + 1968 i`: their
counts (`ptCount_at`, `count_at`), the point's elements (`pt_at`), value `j` (`val_at`), the
bounds (`pt_le`, `vals_le`).
-/

namespace NativeRustcVm.Tables

open NativeVm.Model

@[expose] public section

/-- Table `i`'s point. -/
def ptOf (ev : Array (Array EW × Array EW)) (i : Nat) : Array EW := (ev.getD i (#[], #[])).1
/-- Table `i`'s values. -/
def valsOf (ev : Array (Array EW × Array EW)) (i : Nat) : Array EW := (ev.getD i (#[], #[])).2

end

public section

variable {d : Mem 64} {e : BitVec 64} {ev : Array (Array EW × Array EW)} {i : Nat}

theorem entry_at (h : TableEvalsAt d e ev) (hi : i < 6) :
    TableEvalAt d (e + BitVec.ofNat 64 (1968 * i)) (ptOf ev i, valsOf ev i) := by
  have hs : i < ev.size := by rw [h.1]; exact hi
  have := h.2 i hs
  simp only [ptOf, valsOf, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hs,
    Option.getD_some]
  exact this

theorem pt_le (h : TableEvalsAt d e ev) (hi : i < 6) : (ptOf ev i).size ≤ 30 := by
  have := (entry_at h hi).1.1; simpa [tablePointCap] using this

theorem vals_le (h : TableEvalsAt d e ev) (hi : i < 6) : (valsOf ev i).size ≤ 92 := by
  have := (entry_at h hi).2.1; simpa [widthCap] using this

theorem ptCount_at (h : TableEvalsAt d e ev) (hi : i < 6) :
    WordAt d (e + BitVec.ofNat 64 (1968 * i)) (ptOf ev i).size.toUInt64 := by
  have := (entry_at h hi).1.2.1; simpa using this

theorem count_at (h : TableEvalsAt d e ev) (hi : i < 6) :
    WordAt d (e + BitVec.ofNat 64 (1968 * i + 488)) (valsOf ev i).size.toUInt64 := by
  have := (entry_at h hi).2.2.1
  rw [addr_add_add] at this
  simpa [valuesOff] using this

theorem pt_at (h : TableEvalsAt d e ev) (hi : i < 6) :
    EWsAt d (e + BitVec.ofNat 64 (1968 * i + 8)) (ptOf ev i).toList := by
  have := (entry_at h hi).1.2.2
  rwa [show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, addr_add_add] at this

theorem val_at (h : TableEvalsAt d e ev) (hi : i < 6) {j : Nat} (hj : j < (valsOf ev i).size) :
    EWAt d (e + BitVec.ofNat 64 (1968 * i + 496 + 16 * j)) (valsOf ev i)[j] := by
  have h2 := (entry_at h hi).2.2.2
  have := ewsAt_getElem h2 (i := j) (by simpa using hj)
  rw [show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, addr_add_add, addr_add_add,
    addr_add_add] at this
  simp only [valuesOff, Array.getElem_toList] at this
  rwa [show 1968 * i + (488 + (8 + 16 * j)) = 1968 * i + 496 + 16 * j by omega] at this

end

end NativeRustcVm.Tables
