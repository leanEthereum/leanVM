module

public import NativeRustcVmX64.Ring.Seq
public meta import NativeRustcVmX64.Ring.Seq
public import NativeRustcVmX64.Code.Vm.RingCoefficients
public meta import NativeRustcVmX64.Code.Vm.RingCoefficients

/-!
# `ring_coefficients`' blocks, run by the symbolic executor (x86-64)

Region `0` the 176-byte frame (the call slot, the spills at offsets `8` to `127`, the six pushes
from `128`) and the return address. The entry block `b0` from `t0` (region `1` `g`, RSI); the
loop's blocks `b1` to `b17`: every register the loop keeps and every spill a variable
(`regVar`, `spillVar`), region `1` the row of `out` turn `p` writes (RBX + 8 RBP, an alias),
region `2` `f_p` (the spilled `f` + RBP, an alias): from the head's `tH`, then `tR j` after the
row's first `j` products are stored (`tRn` after the last, RBP moved on); the epilogue `b18` from
`tX`.
-/

namespace NativeRustcVmX64.Ring.Coeff

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeRustcVmX64.Vm.RingCoefficients

@[expose] public section

/-- A register's variable. -/
def regVar : Reg64 → Nat
  | .rax => 6 | .rdx => 7 | .rbp => 8 | .r12 => 9 | .r13 => 10 | .r14 => 11 | .r15 => 12
  | .rbx => 13 | _ => 0

/-- A spill's variable: frame offsets `8` to `120`. -/
def spillVar (o : Nat) : Nat := 13 + o / 8

/-- The pushes: RBP, R15, R14, R13, R12, RBX from offset `168` down, the variables `0` to `5`. -/
def pushW : List Write :=
  [⟨0, 168, 8, .var 0⟩, ⟨0, 160, 8, .var 1⟩, ⟨0, 152, 8, .var 2⟩, ⟨0, 144, 8, .var 3⟩,
    ⟨0, 136, 8, .var 4⟩, ⟨0, 128, 8, .var 5⟩]

/-- The spills' offsets. -/
def spills : List Nat := (List.range 15).map fun i ↦ 8 + 8 * i

/-- The row's address: `out + 8 · (16 p)`. -/
def rowKey : Sym := mkAdd64 (.var 13) (mkBin .mul .W64 (.var 8) (.lit 8))

/-- `f_p`'s address: `f + 16 p`. -/
def fKey : Sym := mkAdd64 (.var 28) (mkBin .mul .W64 (.var 8) (.lit 1))

/-- The aliases: the row (region 1), `f_p` (region 2). -/
def keys : List (Sym × Nat × Int) := [(rowKey, 1, 0), (fKey, 2, 0)]

/-- The spills of a template: the given offsets, then the pushes. -/
def spillW (os : List Nat) : List Write := os.map (fun o ↦ ⟨0, o, 8, .var (spillVar o)⟩) ++ pushW

/-- At the entry: `g` region 1. -/
def t0 : SState := tpl [184, 128] [(.rsp, .ptr 0 176), (.rsi, .ptr 1 0)] []

/-- At the loop's head: the spills but those at `104`, `112`, R12 and R13 their atoms. -/
def tH : SState :=
  tpl [184, 128, 16]
    ((.rsp, .ptr 0 8) :: [Reg64.rax, .rdx, .rbx, .rbp, .r14, .r15].map
      fun r ↦ (r, .var (regVar r)))
    (spillW (spills.filter fun o ↦ o != 104 && o != 112)) [] keys

/-- In the loop, after the row's first `j` products are stored (variables `29 + 2k`, `30 + 2k`). -/
def tR (j : Nat) : SState :=
  tpl [184, 128, 16]
    ((.rsp, .ptr 0 8) :: [Reg64.rax, .rdx, .rbx, .rbp, .r12, .r13, .r14, .r15].map
      fun r ↦ (r, .var (regVar r)))
    ((List.range j).flatMap (fun k ↦ [⟨1, 16 * k, 8, .var (29 + 2 * k)⟩,
      ⟨1, 16 * k + 8, 8, .var (30 + 2 * k)⟩]) ++ spillW spills) [] keys

/-- After the turn's last block: `tR 8` without the aliases (RBP has moved on). -/
def tRn : SState := { tR 8 with aliases := [] }

/-- At the epilogue: `tH` without the aliases. -/
def tX : SState := { tH with aliases := [] }

end

set_option Elab.async false

sym_block run_b0 := exec b0 t0
sym_block run_b1 := exec b1 tH
sym_block run_b2 := exec b2 (tR 0)
sym_block run_b3 := exec b3 (tR 1)
sym_block run_b4 := exec b4 (tR 2)
sym_block run_b5 := exec b5 (tR 3)
sym_block run_b6 := exec b6 (tR 4)
sym_block run_b7 := exec b7 (tR 5)
sym_block run_b8 := exec b8 (tR 6)
sym_block run_b9 := exec b9 (tR 7)
sym_block run_b10 := exec b10 (tR 8)
sym_block run_b11 := exec b11 (tR 8)
sym_block run_b12 := exec b12 (tR 8)
sym_block run_b13 := exec b13 (tR 8)
sym_block run_b14 := exec b14 (tR 8)
sym_block run_b15 := exec b15 (tR 8)
sym_block run_b16 := exec b16 (tR 8)
sym_block run_b17 := exec b17 (tR 8)
sym_block run_b18 := exec b18 tX

/-- The row's words in `tRn`: product `k`'s limbs, the variables `29 + 2k`, `30 + 2k`. -/
public theorem tRn_row : ∀ k < 8, ∀ i < 8,
    findWrite 1 (16 * k + i) tRn.mem = some (.var (29 + 2 * k), i) ∧
    findWrite 1 (16 * k + 8 + i) tRn.mem = some (.var (30 + 2 * k), i) := by
  decide +kernel

end NativeRustcVmX64.Ring.Coeff
