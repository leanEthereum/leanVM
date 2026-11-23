module

public import NativeRustcVmArm.Bus.AccumulateSide.Env

/-!
# `accumulate_side`: the descriptions of the table loop

At the loop head (`b27`, turn `j`): `DL`, the registers `DLr` and the frame words `DLf`. In the
turn, before each block `k`: `L<k>`. A turn ends with `DL` shifted (`shiftD`: the indices from
`90` on `100` up), the next turn's values (`T_shift`).
-/

namespace NativeRustcVmArm.Bus.AccumulateSide

open NativeRustcArm NativeRustcArm.Sym
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Bus NativeRustcVm.Layout

@[expose] public section

/-- The frame words the body keeps from the loop's setup on, but the ones and the padding rows. -/
def DLf0 : List (Sym × Nat) :=
  [(.load 0 16 8, 0), (.load 0 24 8, 81), (.load 0 32 8, 80), (.load 0 40 8, 21),
    (.load 0 48 8, 20), (.load 0 56 8, 22), (.load 0 64 8, 10), (.load 0 72 8, 11),
    (.load 0 80 8, 23), (.load 0 88 8, 8), (.load 0 96 8, 9), (.load 0 104 8, 12),
    (.load 0 112 8, 13)]

/-- The frame words at the loop head. -/
def DLf : List (Sym × Nat) := DLf0 ++ [(.load 0 136 8, 90), (.load 0 144 8, 91)]

/-- The registers at the loop head but X12. -/
def DLr : List (Sym × Nat) :=
  [(.reg .X20, 12), (.reg .X21, 93), (.reg .X22, 92), (.reg .X26, 13),
    (.reg .X27, 98), (.reg .X28, 99), (.reg .X29, 100)]

/-- **The loop head.** -/
def DL : List (Sym × Nat) := (.reg .X12, 97) :: (DLr ++ DLf)

/-- An index of the next turn. -/
def shiftI (i : Nat) : Nat := if 90 ≤ i then i + 100 else i

/-- A description of the next turn. -/
def shiftD (D : List (Sym × Nat)) : List (Sym × Nat) := D.map fun p ↦ (p.1, shiftI p.2)

/-- After `b27`'s call: the selector in X0, X1. -/
def L28 : List (Sym × Nat) := (.reg .X0, 94) :: (.reg .X1, 95) :: (DLr ++ DLf)

/-- The selector in X23, X24 and the registers kept from `b29` on. -/
def L29r : List (Sym × Nat) :=
  [(.reg .X21, 93), (.reg .X22, 92), (.reg .X23, 94), (.reg .X24, 95),
    (.reg .X27, 98), (.reg .X28, 99), (.reg .X29, 100)]

/-- After `block_form`. -/
def L29 : List (Sym × Nat) := (.reg .X20, 12) :: (.reg .X26, 13) :: (L29r ++ DLf)

/-- After `b29`. -/
def L30 : List (Sym × Nat) := (.reg .X20, 12) :: (L29r ++ DLf)

/-- After `b30`: the owner in X20. -/
def L31 : List (Sym × Nat) := (.reg .X20, 96) :: (L29r ++ DLf)

/-- After `add_scaled`. -/
def L32 : List (Sym × Nat) :=
  [(.reg .X19, 101), (.reg .X20, 96), (.reg .X21, 102), (.reg .X22, 103), (.reg .X23, 94),
    (.reg .X24, 95), (.reg .X25, 23), (.reg .X27, 98), (.reg .X28, 99), (.reg .X29, 100),
    (.load 0 120 8, 92), (.load 0 128 8, 93)] ++ DLf

/-- The registers and frame words from `padding_weight` on. -/
def L34c : List (Sym × Nat) :=
  [(.reg .X19, 101), (.reg .X20, 12), (.reg .X21, 102), (.reg .X22, 104), (.reg .X25, 23),
    (.reg .X26, 13), (.reg .X27, 198), (.reg .X28, 199), (.reg .X29, 100),
    (.load 0 120 8, 92), (.load 0 128 8, 93), (.load 0 136 8, 190), (.load 0 144 8, 191)] ++ DLf0

/-- After `padding_weight`: its value in X0, X1. -/
def L34 : List (Sym × Nat) :=
  (.reg .X0, 106) :: (.reg .X1, 107) :: (.reg .X23, 94) :: (.reg .X24, 95) :: L34c

/-- After the selector times the padding weight. -/
def L35 : List (Sym × Nat) := (.reg .X0, 108) :: (.reg .X1, 109) :: L34c

/-- After `evaluate`. -/
def L36 : List (Sym × Nat) :=
  (.reg .X0, 110) :: (.reg .X1, 111) :: (.reg .X23, 108) :: (.reg .X24, 109) :: L34c

/-- After the padding row's term. -/
def L37 : List (Sym × Nat) := (.reg .X0, 112) :: (.reg .X1, 113) :: L34c

end

end NativeRustcVmArm.Bus.AccumulateSide
