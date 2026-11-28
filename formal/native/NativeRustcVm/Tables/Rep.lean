module

public import NativeRustcVm.Bus.Rep
public import NativeVm.Model.Tables

/-!
# Phase 4's result in memory

`table_phase` (`rustc/vm/src/tables.rs`) writes each table's point and evaluations into an array
`[TableEvalW; N_TABLES]` (`#[repr(C)]`, `1968` bytes each), the model's `tablePhase` result
`Array (Array EW × Array EW)`:

| offset | field | holds |
|---|---|---|
| `0` | `point` | `Buf<EW, 30>` (`488` bytes): the table's point, its first log-height coordinates |
| `488` | `values` | `Buf<EW, 92>` (`1480` bytes): the table's evaluations, its width many |

Table `i`'s entry is at `1968 i` (`TableEvalsAt`); phase 6 reads `KECCAK`'s, `tableColumnClaims`
every table's.

Phase 4 reads besides the tables' log-heights, six words (`HeightsAt`: the layout's
`table_log_heights`, each at most `30`), and the bus's forms (`NativeRustcVm.Bus.FormsAt`).
-/

namespace NativeRustcVm.Tables

open NativeVm.Model NativeRustcVm.Layout NativeRustcVm.Bus
open NativeRustcVm.Transcript (off)

@[expose] public section

/-- `TABLE_POINT_CAP`: a table's point holds at most `30` coordinates. -/
def tablePointCap : Nat := 30

/-- `WIDTH_CAP`: the widest table, `KECCAK`'s, `92` columns. -/
def widthCap : Nat := 92

/-- A `TableEvalW`'s bytes. -/
def tableEvalBytes : Nat := 1968

/-- The bytes of the `N_TABLES` entries. -/
def tableEvalsBytes : Nat := nTables * tableEvalBytes

/-- The offset of a `TableEvalW`'s `values`. -/
def valuesOff : Nat := 488

/-- The `TableEvalW` at `p` holds the table's point `e.1` and evaluations `e.2`. -/
def TableEvalAt (d : Mem 64) (p : BitVec 64) (e : Array EW × Array EW) : Prop :=
  BufEWAt d p tablePointCap e.1.toList ∧
    BufEWAt d (p + BitVec.ofNat 64 valuesOff) widthCap e.2.toList

/-- **Phase 4's result**: the `N_TABLES` entries from `p` hold the tables' points and
evaluations, `evals`. -/
def TableEvalsAt (d : Mem 64) (p : BitVec 64) (evals : Array (Array EW × Array EW)) : Prop :=
  evals.size = nTables ∧
    ∀ i (h : i < evals.size), TableEvalAt d (p + BitVec.ofNat 64 (tableEvalBytes * i)) evals[i]

/-- The tables' log-heights at `a`: six words, each at most `30` (`table_log_heights`). -/
def HeightsAt (d : Mem 64) (a : BitVec 64) (heights : Array Nat) : Prop :=
  heights.size = nTables ∧ (∀ h ∈ heights, h ≤ 30) ∧
    WordsAt d a (heights.toList.map Nat.toUInt64)

end

public section

/-- The layout's log-heights. -/
theorem _root_.NativeRustcVm.Layout.LayoutWAt.heightsAt {d : Mem 64} {a : BitVec 64}
    {L : LayoutW} (h : LayoutWAt d a L) : HeightsAt d (off a 24) L.tableLogHeights :=
  ⟨h.heights_size, h.heights_le, h.heights⟩
end

end NativeRustcVm.Tables
