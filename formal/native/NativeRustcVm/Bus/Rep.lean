module

public import NativeRustcVm.Layout.Rep
public import NativeVm.Model.Bus

/-!
# The bus's structs in memory

The crate's `#[repr(C)]` structs of `bus.rs` and `gkr.rs` represent the model's values
(`NativeVm/Model/Bus.lean`, `Gkr.lean`):

| struct | bytes | fields | represents |
|---|---|---|---|
| `Placement` | `16` | `variable_count` `0`, `index` `8` | `Placement` (`PlacementAt`) |
| `Buf<Placement, N>` | `8 + 16 N` | `len` `0`, `items` `8` | `Array Placement` (`PlacementsAt`) |
| `BusLayoutW` | `888` | `depth` `0`, `framework: Buf<Placement, 3>` `8`, `tables: Buf<Placement, 51>` `64` | `BusLayoutW` (`BusLayoutWAt`) |
| `GkrStateW` | `1064` | `values[3]` `0`, `point: Buf<EW, 63>` `48` | `GkrStateW` (`GkrStateWAt`) |
| `BusW` | `107768` | `forms[6][3]` `0`, `point: Buf<EW, 63>` `106704`, `totals[3]` `107720` | `BusResultW` but its claims and bytecode point (`BusWAt`) |

`BusW` holds what phase 4 reads of the bus's result: each table's form per side (`forms[t][side]`
at byte `5928 (3 t + side)`, a `FormBuf`), the GKR point and the three sides' totals. The four
column claims go to the claims (`ClaimsWAt`), the bytecode point nowhere (no later phase reads it).
-/

namespace NativeRustcVm.Bus

open NativeVm.Model NativeRustcVm.Layout LeanVM.Protocol.Verifier
open NativeRustcVm.Transcript (off)

@[expose] public section

/-! ## Sizes -/

/-- `BUS_POINT_CAP`: the GKR point's capacity. -/
def busPointCap : Nat := 63
/-- `MAX_BLOCKS`: the most table blocks of a side (the push side's). -/
def maxBlocks : Nat := 51
/-- `Placement`'s bytes. -/
def placementBytes : Nat := 16
/-- `Buf<EW, 63>`'s bytes. -/
def pointBufBytes : Nat := 8 + 16 * busPointCap
/-- `GkrStateW`'s bytes. -/
def gkrStateBytes : Nat := 48 + pointBufBytes
/-- `BusLayoutW`'s bytes. -/
def busLayoutBytes : Nat := 64 + 8 + placementBytes * maxBlocks
/-- The tables' forms' bytes (`[[FormBuf; 3]; N_TABLES]`). -/
def formsBytes : Nat := formBufBytes * (3 * nTables)
/-- `BusW.point`'s offset. -/
def busPointOff : Nat := formsBytes
/-- `BusW.totals`'s offset. -/
def busTotalsOff : Nat := busPointOff + pointBufBytes
/-- `BusW`'s bytes. -/
def busBytes : Nat := busTotalsOff + 48

theorem gkrStateBytes_eq : gkrStateBytes = 1064 := rfl
theorem busLayoutBytes_eq : busLayoutBytes = 888 := rfl
theorem busPointOff_eq : busPointOff = 106704 := rfl
theorem busTotalsOff_eq : busTotalsOff = 107720 := rfl
theorem busBytes_eq : busBytes = 107768 := rfl

/-! ## Placements and a side's layout -/

/-- **A placement** at `a` (`Placement`, 16 bytes): its variable count, its index. -/
def PlacementAt (d : Mem 64) (a : BitVec 64) (p : Placement) : Prop :=
  p.variableCount < 2 ^ 64 ∧ p.index < 2 ^ 64 ∧ WordAt d a p.variableCount.toUInt64 ∧
    WordAt d (off a 8) p.index.toUInt64

/-- **Placements** at `a` (`Buf<Placement, N>`): at most `N`, the count, then placement `i` at
byte `8 + 16 i`. -/
def PlacementsAt (d : Mem 64) (a : BitVec 64) (N : Nat) (ps : Array Placement) : Prop :=
  ps.size ≤ N ∧ WordAt d a ps.size.toUInt64 ∧
    ∀ i (h : i < ps.size), PlacementAt d (off a (8 + placementBytes * i)) ps[i]

/-- **A side's layout** at `a` (`BusLayoutW`, 888 bytes): its depth, the framework blocks'
placements (at most `3`), the table blocks' (at most `51`). -/
structure BusLayoutWAt (d : Mem 64) (a : BitVec 64) (L : BusLayoutW) : Prop where
  depth_lt : L.depth < 2 ^ 64
  depth : WordAt d a L.depth.toUInt64
  framework : PlacementsAt d (off a 8) 3 L.framework
  tables : PlacementsAt d (off a 64) maxBlocks L.tables

/-- An `Option<BusLayoutW>` at `a` (896 bytes): tag word `0`, or tag word `1` and the layout. -/
def OptBusLayoutWAt (d : Mem 64) (a : BitVec 64) : Option BusLayoutW → Prop
  | none => WordAt d a 0
  | some L => WordAt d a 1 ∧ BusLayoutWAt d (off a 8) L

/-! ## The GKR walk's state -/

/-- **The GKR walk's state** at `a` (`GkrStateW`, 1064 bytes): the three trees' values, the point
(a `Buf<EW, 63>`). -/
structure GkrStateWAt (d : Mem 64) (a : BitVec 64) (g : GkrStateW) : Prop where
  values_size : g.values.size = 3
  values : EWsAt d a g.values.toList
  point : BufEWAt d (off a 48) busPointCap g.point.toList

/-! ## The bus's result -/

/-- **The tables' forms** at `a` (`[[FormBuf; 3]; N_TABLES]`, `busPointOff` bytes): table `t`'s
form of side `s` at byte `5928 (3 t + s)`. -/
structure FormsAt (d : Mem 64) (a : BitVec 64) (F : Array (Array FormW)) : Prop where
  size : F.size = nTables
  row_size : ∀ t (h : t < F.size), F[t].size = 3
  forms : ∀ t (ht : t < F.size) s (hs : s < F[t].size),
    FormBufAt d (off a (formBufBytes * (3 * t + s))) F[t][s]

/-- **The bus's result** at `a` (`BusW`, 107768 bytes) represents `r` but its claims and bytecode
point: table `t`'s form of side `s` at byte `5928 (3 t + s)`, the GKR point (a `Buf<EW, 63>`) at
byte `106704`, the three totals at byte `107720`. -/
structure BusWAt (d : Mem 64) (a : BitVec 64) (r : BusResultW) : Prop where
  forms_size : r.forms.size = nTables
  row_size : ∀ t (h : t < r.forms.size), r.forms[t].size = 3
  forms : ∀ t (ht : t < r.forms.size) s (hs : s < r.forms[t].size),
    FormBufAt d (off a (formBufBytes * (3 * t + s))) r.forms[t][s]
  point : BufEWAt d (off a busPointOff) busPointCap r.point.toList
  totals_size : r.totals.size = 3
  totals : EWsAt d (off a busTotalsOff) r.totals.toList

/-- A bus result's forms are the tables' forms at its address. -/
theorem BusWAt.formsAt {d : Mem 64} {a : BitVec 64} {r : BusResultW} (h : BusWAt d a r) :
    FormsAt d a r.forms := ⟨h.forms_size, h.row_size, h.forms⟩

/-- The bus result from its forms, point and totals. -/
theorem BusWAt.of_formsAt {d : Mem 64} {a : BitVec 64} {r : BusResultW} (hf : FormsAt d a r.forms)
    (hp : BufEWAt d (off a busPointOff) busPointCap r.point.toList) (ht : r.totals.size = 3)
    (htot : EWsAt d (off a busTotalsOff) r.totals.toList) : BusWAt d a r :=
  ⟨hf.size, hf.row_size, hf.forms, hp, ht, htot⟩

end

end NativeRustcVm.Bus
