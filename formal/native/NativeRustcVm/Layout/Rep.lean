module

public import NativeRustcVm.Arrays.Read
public import NativeRustcVm.Transcript.Rep
public import NativeVm.Model.Claims

/-!
# The layout, the forms and the column claims in memory

The crate's `#[repr(C)]` structs of `layout.rs` and `stack.rs` (offsets: `offset_of!`) represent
the model's values (`NativeVm/Model/Layout.lean`, `Claims.lean`):

| struct | bytes | fields | represents |
|---|---|---|---|
| `TermW` | `40` | `degree` `0`, `cols[2]` `8`, `coeff` `24` | `TermW` (`TermWAt`): the monomial's columns, at most two |
| `FormBuf` | `5928` | `len` `0`, `terms[148]` `8` | `FormW` (`FormBufAt`), at most `formCap` terms |
| `PlacementAt` | `24` | `present` `0`, `variable_count` `8`, `index` `16` | `Option Placement` (`PlacementWAt`) |
| `LayoutW` | `3912` | `log_memory` `0`, `log_bytecode` `8`, `stack_log` `16`, `table_log_heights[6]` `24`, `rows[6]` `72`, `placements[158]` `120` | `LayoutW` (`LayoutWAt`) |
| `ColumnClaimW` | `608` | `column` `0`, `point: Buf<EW, 36>` `8`, `value` `592` | `ColumnClaimW` (`ColumnClaimAt`) |
| `ClaimsW = Buf<ColumnClaimW, 160>` | `97288` | `len` `0`, `items` `8` | `Array ColumnClaimW` (`ClaimsWAt`) |
| `EqClaimW` | `504` | `z: Buf<EW, 30>` `0`, `value` `488` | the stack claim `⟨.eq z, value⟩` (`EqClaimAt`) |

The Rust's `LayoutW` keeps the tables' row counts in place of the model's bus blocks, which are
`busBlocks` of the heights and those rows (`LayoutWAt.rows`); it does not hold the bytecode, which
`LayoutWAt` says nothing of (the caller's input area holds it). A term's unused `cols` words, a
`none` placement's coordinates and the entries past a buffer's count are unconstrained.
-/

namespace NativeRustcVm.Layout

open NativeVm.Model LeanVM.Protocol.Verifier
open NativeRustcVm.Transcript (off)

@[expose] public section

/-! ## Sizes -/

/-- `TermW`'s bytes. -/
def termBytes : Nat := 40
/-- `FORM_CAP`: the most terms of a `FormBuf`. -/
def formCap : Nat := 148
/-- `FormBuf`'s bytes. -/
def formBufBytes : Nat := 8 + termBytes * formCap
/-- `PlacementAt`'s bytes. -/
def placementBytes : Nat := 24
/-- `COLUMN_COUNT`. -/
def columnCountW : Nat := 158
/-- `LayoutW`'s bytes. -/
def layoutBytes : Nat := 120 + placementBytes * columnCountW
/-- `POINT_CAP`: a column claim's point. -/
def pointCap : Nat := 36
/-- `CLAIM_CAP`: the most column claims. -/
def claimCap : Nat := 160
/-- `ColumnClaimW`'s bytes. -/
def columnClaimBytes : Nat := 608
/-- `ClaimsW`'s bytes. -/
def claimsBytes : Nat := 8 + columnClaimBytes * claimCap
/-- `STACK_CAP`: a point on the stack. -/
def stackCap : Nat := 30
/-- `EqClaimW`'s bytes. -/
def eqClaimBytes : Nat := 504

theorem formBufBytes_eq : formBufBytes = 5928 := rfl
theorem layoutBytes_eq : layoutBytes = 3912 := rfl
theorem claimsBytes_eq : claimsBytes = 97288 := rfl

/-- The model's `columnCount` is `COLUMN_COUNT`. -/
theorem columnCount_eq : columnCount = columnCountW := by decide

/-! ## Forms -/

/-- **A term** at `a` (`TermW`, 40 bytes): its degree (the monomial's column count, at most `2`),
its columns from byte `8`, its coefficient at byte `24`. -/
structure TermWAt (d : Mem 64) (a : BitVec 64) (t : TermW) : Prop where
  degree_le : t.cols.size ≤ 2
  degree : WordAt d a t.cols.size.toUInt64
  cols_lt : ∀ i (h : i < t.cols.size), t.cols[i] < 2 ^ 64
  cols : ∀ i (h : i < t.cols.size), WordAt d (off a (8 + 8 * i)) t.cols[i].toUInt64
  coeff : EWAt d (off a 24) t.coeff

/-- The terms from `a`, end to end (a `&[TermW]` slice, or a `FormBuf`'s entries). -/
def TermsAt (d : Mem 64) (a : BitVec 64) (f : FormW) : Prop :=
  ∀ i (h : i < f.size), TermWAt d (off a (termBytes * i)) f[i]

/-- **A form** at `a` (`FormBuf`, 5928 bytes): at most `formCap` terms, the count, then the terms
from byte `8`. -/
structure FormBufAt (d : Mem 64) (a : BitVec 64) (f : FormW) : Prop where
  len_le : f.size ≤ formCap
  len : WordAt d a f.size.toUInt64
  terms : TermsAt d (off a 8) f

/-! ## The layout -/

/-- **A placement** at `a` (`PlacementAt`, 24 bytes): `present` `0` for `none`; `1`, then the
variable count and the index, for `some`. -/
def PlacementWAt (d : Mem 64) (a : BitVec 64) : Option Placement → Prop
  | none => WordAt d a 0
  | some p => WordAt d a 1 ∧ p.variableCount < 2 ^ 64 ∧ p.index < 2 ^ 64 ∧
      WordAt d (off a 8) p.variableCount.toUInt64 ∧ WordAt d (off a 16) p.index.toUInt64

/-- **The layout** at `a` (`LayoutW`, 3912 bytes) represents `L` (but its bytecode): the log-sizes
(at most `30`, as `buildLayout` checks), the stack's log-size, the six tables' log-heights (at most
`30`) and the row counts (at most `2 ^ 30`) the bus blocks are built from, and the `158` global
columns' placements. -/
structure LayoutWAt (d : Mem 64) (a : BitVec 64) (L : LayoutW) : Prop where
  log_memory_le : L.logMemory ≤ 30
  log_memory : WordAt d a L.logMemory.toUInt64
  log_bytecode_le : L.logBytecode ≤ 30
  log_bytecode : WordAt d (off a 8) L.logBytecode.toUInt64
  stack_log_lt : L.stackLog < 2 ^ 64
  stack_log : WordAt d (off a 16) L.stackLog.toUInt64
  heights_size : L.tableLogHeights.size = nTables
  heights_le : ∀ h ∈ L.tableLogHeights, h ≤ 30
  heights : WordsAt d (off a 24) (L.tableLogHeights.toList.map Nat.toUInt64)
  rows : ∃ rows : Array Nat, rows.size = nTables ∧ (∀ r ∈ rows, r ≤ 2 ^ 30) ∧
    WordsAt d (off a 72) (rows.toList.map Nat.toUInt64) ∧
    busBlocks L.tableLogHeights rows = (L.push, L.pull, L.count)
  placements_size : L.placements.size = columnCountW
  placements : ∀ c (h : c < L.placements.size),
    PlacementWAt d (off a (120 + placementBytes * c)) L.placements[c]

/-! ## The claims -/

/-- **A column claim** at `a` (`ColumnClaimW`, 608 bytes): the column, the point (a
`Buf<EW, 36>`), the value. -/
structure ColumnClaimAt (d : Mem 64) (a : BitVec 64) (c : ColumnClaimW) : Prop where
  column_lt : c.column < 2 ^ 64
  column : WordAt d a c.column.toUInt64
  point : BufEWAt d (off a 8) pointCap c.point.toList
  value : EWAt d (off a 592) c.value

/-- **The column claims** at `a` (`ClaimsW`, a `Buf<ColumnClaimW, 160>`, 97288 bytes): at most
`claimCap`, the count, then claim `i` at byte `8 + 608 i`. -/
structure ClaimsWAt (d : Mem 64) (a : BitVec 64) (cs : Array ColumnClaimW) : Prop where
  len_le : cs.size ≤ claimCap
  len : WordAt d a cs.size.toUInt64
  claims : ∀ i (h : i < cs.size), ColumnClaimAt d (off a (8 + columnClaimBytes * i)) cs[i]

/-- **An equality claim** at `a` (`EqClaimW`, 504 bytes): the stack claim `⟨.eq z, value⟩`, `z`
a `Buf<EW, 30>`, the value at byte `488`. -/
def EqClaimAt (d : Mem 64) (a : BitVec 64) (z : Array EW) (value : EW) : Prop :=
  BufEWAt d a stackCap z.toList ∧ EWAt d (off a 488) value

end

end NativeRustcVm.Layout
