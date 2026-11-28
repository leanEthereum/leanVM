module

public import NativeRustcVmArm.Arrays.Common
public import NativeRustcVmArm.Code.Vm.BuildLayout
public meta import NativeRustcVmArm.Code.Vm.BuildLayout
public meta import NativeRustcVmArm.Arrays.Common

/-!
# `build_layout`'s blocks, run by the symbolic executor

- `entryS`, at the entry: region 0 the 1360-byte frame below SP (96 bytes of saved registers on
  top of the 1264-byte `kappas`). `b0` tests the bytecode's length a power of two (`b19` returns
  `0`); `b1` saves X19-X30 and calls `bit_length`.
- `rowsS`, after the call: region 0 the frame (SP its base), region 1 the six row counts (X21).
  `b2` to `b8` check the sizes; a failed check goes to `b20`, `b21` (`exitS`), returning `0`.
- `layS o`: region 0 the layout's first 120 bytes (X22, X21 at `o`): `b9` to `b14` store the
  sizes, the heights (`bit_length` of each row count less one) and the rows; `b15` the last and
  calls `column_kappas`; `b18` stores the stack's log-size.
- `regsS`: `b16` (the call of `placements_of`), `b17` (its result).
-/

namespace NativeRustcVmArm.Layout.BuildLayout

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.BuildLayout NativeRustcVmArm.Arrays

@[expose] public section

/-- At the entry: the frame. -/
def entryS : SState := init [(1360, true)] (.ptr 0 1360)
/-- After the first call: the frame, the row counts (X21). -/
def rowsS : SState := init [(1360, true), (48, false)] (.ptr 0 0) [(.X21, .ptr 1 0)]
/-- The layout's first 120 bytes (X22), X21 at `o`. -/
def layS (o : Int) : SState := init [(120, false)] .sp [(.X22, .ptr 0 0), (.X21, .ptr 0 o)]
/-- The layout's first 120 bytes (X22). -/
def lay9S : SState := init [(120, false)] .sp [(.X22, .ptr 0 0)]
/-- Registers only. -/
def regsS : SState := init [] .sp
/-- At the epilogue: the frame. -/
def exitS : SState := init [(1360, true)] (.ptr 0 0)

/-- The prologue's slots. -/
def slots : List (Nat × XReg) :=
  [(1264, .X29), (1272, .X30), (1280, .X28), (1288, .X27), (1296, .X26), (1304, .X25),
    (1312, .X24), (1320, .X23), (1328, .X22), (1336, .X21), (1344, .X20), (1352, .X19)]

/-- The callee-saved registers no slot holds. -/
def keptRegs : List XReg := calleeRegs.filter fun r ↦ !inSlots slots r

/-- `S` keeps `S₀`'s registers `rs`. -/
def keepR (S₀ S : SState) (rs : List XReg) : Bool :=
  rs.all fun r ↦ (S₀.reg r).isSome && S.reg r == S₀.reg r

/-- The registers kept from the checks to the end: the sizes, the layout, the row counts. -/
def cs : List XReg := [.X19, .X20, .X22, .X23, .X24, .X25, .X26, .X27, .X28]

/-- Every write of `S` is in region 0, inside its first `n` bytes. -/
def InR0 (S : SState) (n : Nat) : Bool := S.mem.all fun w ↦ w.r == 0 && decide (w.off + w.n ≤ n)

/-- Every write of `S` is in region 0, and misses the words at offsets `os`. -/
def Misses (S : SState) (os : List Nat) : Bool :=
  S.mem.all fun w ↦ w.r == 0 && os.all fun o ↦ decide (w.off + w.n ≤ o ∨ o + 8 ≤ w.off)

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b19 := exec b19 (after b0 entryS)
sym_block run_b1 := exec b1 (after b0 entryS)
sym_block run_b2 := exec b2 rowsS
sym_block run_b3 := exec b3 (after b2 rowsS)
sym_block run_b4 := exec b4 (after b3 (after b2 rowsS))
sym_block run_b5 := exec b5 (after b4 (after b3 (after b2 rowsS)))
sym_block run_b6 := exec b6 (after b5 (after b4 (after b3 (after b2 rowsS))))
sym_block run_b7 := exec b7 (after b6 (after b5 (after b4 (after b3 (after b2 rowsS)))))
sym_block run_b8 := exec b8 (after b7 (after b6 (after b5 (after b4 (after b3 (after b2 rowsS))))))
sym_block run_b20 := exec b20 regsS
sym_block run_b21 := exec b21 exitS
sym_block run_b9 := exec b9 lay9S
sym_block run_b10 := exec b10 (layS 0)
sym_block run_b11 := exec b11 (layS 24)
sym_block run_b12 := exec b12 (layS 24)
sym_block run_b13 := exec b13 (layS 24)
sym_block run_b14 := exec b14 (layS 24)
sym_block run_b15 := exec b15 (layS 24)
sym_block run_b16 := exec b16 regsS
sym_block run_b17 := exec b17 regsS
sym_block run_b18 := exec b18 (layS 24)

/-- The checks' last state. -/
public abbrev chkS : SState :=
  after b8 (after b7 (after b6 (after b5 (after b4 (after b3 (after b2 rowsS))))))

public theorem b1_frame : (∀ p ∈ slots, p.1 + 8 ≤ 1360 ∧
      ∀ i < 8, findWrite 0 (p.1 + i) (after b1 (after b0 entryS)).mem = some (.reg p.2, i)) ∧
    (∀ w ∈ (after b1 (after b0 entryS)).mem, w.r = 0 ∧ w.off + w.n ≤ 1360) ∧
    (∀ r ∈ calleeRegs, inSlots slots r = false →
      (after b1 (after b0 entryS)).reg r = some (.reg r)) := by
  decide +kernel

public theorem b19_keeps : keeps entryS (after b19 (after b0 entryS)) = true ∧
    (after b19 (after b0 entryS)).mem = [] := by decide +kernel
public theorem chk_keeps : keepsAll rowsS chkS keptRegs = true ∧ keepR rowsS chkS [.X19, .X22] = true := by
  decide +kernel
public theorem chk_all : ∀ S ∈ [after b2 rowsS, after b3 (after b2 rowsS),
    after b4 (after b3 (after b2 rowsS)), after b5 (after b4 (after b3 (after b2 rowsS))),
    after b6 (after b5 (after b4 (after b3 (after b2 rowsS)))),
    after b7 (after b6 (after b5 (after b4 (after b3 (after b2 rowsS)))))],
    keepsAll rowsS S keptRegs = true := by
  decide +kernel
public theorem b20_keeps : keepsAll regsS (after b20 regsS) keptRegs = true := by decide +kernel
public theorem b21_restores : restores slots 1360 (after b21 exitS) = true ∧
    (after b21 exitS).mem = [] := by decide +kernel
public theorem b16_keeps : keepsAll regsS (after b16 regsS) keptRegs = true ∧
    keepR regsS (after b16 regsS) (.X21 :: cs) = true := by decide +kernel
public theorem b17_keeps : keepsAll regsS (after b17 regsS) keptRegs = true ∧
    keepR regsS (after b17 regsS) (.X1 :: .X21 :: cs) = true := by decide +kernel

public theorem b9_facts : keepsAll lay9S { after b9 lay9S with mem := [] } keptRegs = true ∧
    InR0 (after b9 lay9S) 120 = true ∧ keepR lay9S (after b9 lay9S) cs = true ∧
    (∀ i < 8, findWrite 0 (0 + i) (after b9 lay9S).mem = some (.reg .X19, i)) ∧
    (∀ i < 8, findWrite 0 (8 + i) (after b9 lay9S).mem = some (.reg .X20, i)) ∧
    Misses (after b9 lay9S) [] = true := by
  decide +kernel
public theorem b10_facts : keepsAll (layS 0) { after b10 (layS 0) with mem := [] } keptRegs = true ∧
    InR0 (after b10 (layS 0)) 120 = true ∧ keepR (layS 0) (after b10 (layS 0)) cs = true ∧
    (∀ i < 8, findWrite 0 (24 + i) (after b10 (layS 0)).mem = some (.reg .X0, i)) ∧
    (∀ i < 8, findWrite 0 (72 + i) (after b10 (layS 0)).mem = some (.reg .X28, i)) ∧
    Misses (after b10 (layS 0)) [0, 8] = true := by
  decide +kernel
public theorem b11_facts : keepsAll (layS 24) { after b11 (layS 24) with mem := [] } keptRegs = true ∧
    InR0 (after b11 (layS 24)) 120 = true ∧ keepR (layS 24) (after b11 (layS 24)) (.X21 :: cs) = true ∧
    (∀ i < 8, findWrite 0 (32 + i) (after b11 (layS 24)).mem = some (.reg .X0, i)) ∧
    (∀ i < 8, findWrite 0 (80 + i) (after b11 (layS 24)).mem = some (.reg .X27, i)) ∧
    Misses (after b11 (layS 24)) [24, 72, 0, 8] = true := by
  decide +kernel
public theorem b12_facts : keepsAll (layS 24) { after b12 (layS 24) with mem := [] } keptRegs = true ∧
    InR0 (after b12 (layS 24)) 120 = true ∧ keepR (layS 24) (after b12 (layS 24)) (.X21 :: cs) = true ∧
    (∀ i < 8, findWrite 0 (40 + i) (after b12 (layS 24)).mem = some (.reg .X0, i)) ∧
    (∀ i < 8, findWrite 0 (88 + i) (after b12 (layS 24)).mem = some (.reg .X26, i)) ∧
    Misses (after b12 (layS 24)) [32, 80, 24, 72, 0, 8] = true := by
  decide +kernel
public theorem b13_facts : keepsAll (layS 24) { after b13 (layS 24) with mem := [] } keptRegs = true ∧
    InR0 (after b13 (layS 24)) 120 = true ∧ keepR (layS 24) (after b13 (layS 24)) (.X21 :: cs) = true ∧
    (∀ i < 8, findWrite 0 (48 + i) (after b13 (layS 24)).mem = some (.reg .X0, i)) ∧
    (∀ i < 8, findWrite 0 (96 + i) (after b13 (layS 24)).mem = some (.reg .X25, i)) ∧
    Misses (after b13 (layS 24)) [40, 88, 32, 80, 24, 72, 0, 8] = true := by
  decide +kernel
public theorem b14_facts : keepsAll (layS 24) { after b14 (layS 24) with mem := [] } keptRegs = true ∧
    InR0 (after b14 (layS 24)) 120 = true ∧ keepR (layS 24) (after b14 (layS 24)) (.X21 :: cs) = true ∧
    (∀ i < 8, findWrite 0 (56 + i) (after b14 (layS 24)).mem = some (.reg .X0, i)) ∧
    (∀ i < 8, findWrite 0 (104 + i) (after b14 (layS 24)).mem = some (.reg .X24, i)) ∧
    Misses (after b14 (layS 24)) [48, 96, 40, 88, 32, 80, 24, 72, 0, 8] = true := by
  decide +kernel
public theorem b15_facts : keepsAll (layS 24) { after b15 (layS 24) with mem := [] } keptRegs = true ∧
    InR0 (after b15 (layS 24)) 120 = true ∧ keepR (layS 24) (after b15 (layS 24)) (.X21 :: cs) = true ∧
    (∀ i < 8, findWrite 0 (64 + i) (after b15 (layS 24)).mem = some (Sym.ite
      ((SBool.cmp CmpOp.ult RegWidth.W64 (.reg .X0) (.lit 9)).not.and
        (SBool.cmp CmpOp.eq RegWidth.W64 (.reg .X0) (.lit 9)).not) (.reg .X0) (.lit 9), i)) ∧
    (∀ i < 8, findWrite 0 (112 + i) (after b15 (layS 24)).mem = some (.reg .X23, i)) ∧
    Misses (after b15 (layS 24)) [56, 104, 48, 96, 40, 88, 32, 80, 24, 72, 0, 8] = true := by
  decide +kernel
public theorem b18_facts : keepsAll (layS 24) { after b18 (layS 24) with mem := [] } keptRegs = true ∧
    InR0 (after b18 (layS 24)) 120 = true ∧
    (∀ i < 8, findWrite 0 (16 + i) (after b18 (layS 24)).mem = some (.reg .X1, i)) ∧
    Misses (after b18 (layS 24)) [64, 112, 56, 104, 48, 96, 40, 88, 32, 80, 24, 72, 0, 8] = true := by
  decide +kernel

end NativeRustcVmArm.Layout.BuildLayout
