module

public import NativeRustcVmArm.Bus.AccumulateSide.Step

/-!
# `accumulate_side`: the values the body keeps

The model's values the body computes, as functions of the entry: the framework's fingerprints
(`fpv`), selectors (`sel`), the known part's terms and partial sums (`term`, `kn`), the ones over
the framework (`onF`), the tree's value plus the known part (`tk`); in turn `j` of the table
loop: its block (`blk`), selector (`tsl`), form (`gf`), padding (`pad`), padding weight (`pw`),
the ones and padding rows so far (`onesT`, `prw`). The table `T` of a description: the entry's
arguments (`sv`) below `24`, these values' limbs above.
-/

namespace NativeRustcVmArm.Bus.AccumulateSide

open NativeRustcArm NativeRustcArm.Sym
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Bus NativeRustcVm.Layout

@[expose] public section

section
variable (SL : BusLayoutW) (m0 : MachineData)

/-- Fingerprint `i`. -/
abbrev fpv (i : Nat) : EW := (fpsA m0).getD i 0
/-- Framework selector `i`. -/
abbrev sel (i : Nat) : EW := fsel SL (ptA m0) i
/-- The known part's term `i`. -/
abbrev term (i : Nat) : EW := sel SL m0 i * (betaA m0 + fpv m0 i)
/-- The known part over the first `i` framework blocks. -/
abbrev kn (i : Nat) : EW := knownN SL (ptA m0) (fpsA m0) (betaA m0) i
/-- The known part's count. -/
abbrev cK : Nat := min SL.framework.size (nA m0)
/-- The tree's value plus the known part. -/
abbrev tk : EW := treeA m0 + kn SL m0 (cK SL m0)
/-- The ones over the first `k` framework blocks. -/
abbrev onF (k : Nat) : EW := onesF SL (ptA m0) k

variable (B : Array BusBlockW) (Fm : Array (Array FormW)) (j : Nat)

/-- Table block `j`. -/
abbrev blk : BusBlockW := B.getD j default
/-- Its selector. -/
abbrev tsl : EW := tsel SL (ptA m0) j
/-- The first `j` turns. -/
abbrev sta : Array (Array FormW) × EW :=
  stAt Fm m0.regs.X2.toNat B SL (wA m0) (betaA m0) (ptA m0) j
/-- Its form. -/
abbrev gf : FormW := blockForm (blk B j) (wA m0) (betaA m0)
/-- Its owner's padding row. -/
abbrev pad : Array EW := (tablesW.getD (blk B j).owner default).padding
/-- Its padding weight. -/
abbrev pw : EW := paddingWeight ((ptA m0).extract 0 (blk B j).logRows) (blk B j).rows
/-- Its selector times its padding weight. -/
abbrev sp1 : EW := tsl SL m0 j * pw m0 B j
/-- Its form's value at the padding row. -/
abbrev ev : EW := (gf m0 B j).evaluate (pad B j)
/-- Its padding row's term. -/
abbrev pterm : EW := sp1 SL m0 B j * (ev m0 B j + 1)

/-- The computed values a description's indices from `30` name, in turn `j`. -/
def Tx [Labels] : Nat → UInt64
  | 30 => (fpv m0 0).c0 | 31 => (fpv m0 0).c1 | 32 => (fpv m0 1).c0 | 33 => (fpv m0 1).c1
  | 34 => (fpv m0 2).c0 | 35 => (fpv m0 2).c1
  | 40 => (sel SL m0 0).c0 | 41 => (sel SL m0 0).c1 | 42 => (sel SL m0 1).c0
  | 43 => (sel SL m0 1).c1 | 44 => (sel SL m0 2).c0 | 45 => (sel SL m0 2).c1
  | 50 => (term SL m0 0).c0 | 51 => (term SL m0 0).c1 | 52 => (term SL m0 1).c0
  | 53 => (term SL m0 1).c1 | 54 => (term SL m0 2).c0 | 55 => (term SL m0 2).c1
  | 60 => (kn SL m0 1).c0 | 61 => (kn SL m0 1).c1 | 62 => (kn SL m0 2).c0
  | 63 => (kn SL m0 2).c1 | 64 => (kn SL m0 3).c0 | 65 => (kn SL m0 3).c1
  | 66 => (kn SL m0 (cK SL m0)).c0 | 67 => (kn SL m0 (cK SL m0)).c1
  | 72 => (onF SL m0 1).c0 | 73 => (onF SL m0 1).c1 | 74 => (onF SL m0 2).c0
  | 75 => (onF SL m0 2).c1 | 76 => (onF SL m0 3).c0 | 77 => (onF SL m0 3).c1
  | 78 => (onF SL m0 SL.framework.size).c0 | 79 => (onF SL m0 SL.framework.size).c1
  | 80 => (tk SL m0).c0 | 81 => (tk SL m0).c1
  | 90 => (onesT SL (ptA m0) j).c0 | 91 => (onesT SL (ptA m0) j).c1
  | 92 => (sta SL m0 B Fm j).2.c0 | 93 => (sta SL m0 B Fm j).2.c1
  | 94 => (tsl SL m0 j).c0 | 95 => (tsl SL m0 j).c1
  | 96 => (blk B j).owner.toUInt64
  | 97 => 8
  | 98 => UInt64.ofBitVec (m0.regs.X6.toBitVec + BitVec.ofNat 64 (80 + 16 * j))
  | 99 => UInt64.ofBitVec (m0.regs.X3.toBitVec + BitVec.ofNat 64 (8 + 16 * j))
  | 100 => (B.size - j).toUInt64
  | 101 => (gf m0 B j).size.toUInt64
  | 102 => NativeRustcVmArm.Tables.TableTerms.tablesWords.getD (5 * (blk B j).owner + 4) 0
  | 103 => NativeRustcVmArm.Tables.TableTerms.tablesWords.getD (5 * (blk B j).owner + 3) 0
  | 104 => UInt64.ofBitVec (NativeRustcVmArm.rodataAddr .padding + BitVec.ofNat 64 (16 *
      (NativeRustcVmArm.Tables.TableTerms.tablesWords.getD (5 * (blk B j).owner + 3) 0).toNat))
  | 106 => (pw m0 B j).c0 | 107 => (pw m0 B j).c1
  | 108 => (sp1 SL m0 B j).c0 | 109 => (sp1 SL m0 B j).c1
  | 110 => (ev m0 B j).c0 | 111 => (ev m0 B j).c1
  | 112 => (pterm SL m0 B j).c0 | 113 => (pterm SL m0 B j).c1
  | _ => 0

/-- **The values** a description's indices name, in turn `j` of the table loop: the entry's
arguments below `30`. -/
def T0 [Labels] (i : Nat) : UInt64 := if i < 30 then sv m0 i else Tx SL m0 B Fm j i

/-- The values of turn `j`, and from `190` on turn `j + 1`'s (index less `100`). -/
def T [Labels] (i : Nat) : UInt64 :=
  if 190 ≤ i then T0 SL m0 B Fm (j + 1) (i - 100) else T0 SL m0 B Fm j i

end

end

end NativeRustcVmArm.Bus.AccumulateSide
