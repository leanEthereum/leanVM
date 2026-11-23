module

public import NativeRustcVmX64.Ring.Seq
public meta import NativeRustcVmX64.Ring.Seq
public import NativeRustcVmX64.Code.Vm.RingPsi
public meta import NativeRustcVmX64.Code.Vm.RingPsi

/-!
# `ring_psi`'s blocks, run by the symbolic executor (x86-64)

Region `0` the 80-byte frame (the call slot, the spills at offsets `8`, `16`, `24`, the six pushes
from `32`) and the return address, region `1` `g` (128 bytes). The entry template `t0` (RSP at the
frame's offset `80`, `g` in RDX); after each call the template `tB rr ss`: RSP at offset `8`, `g` in
RBX, the registers `rr` and the spills `ss` the variables `regVar`, `spillVar`, the pushed
registers the variables `0` to `5`.
-/

namespace NativeRustcVmX64.Ring.Psi

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeRustcVmX64.Vm.RingPsi

@[expose] public section

/-- A register's variable. -/
def regVar : Reg64 → Nat
  | .rax => 6 | .rdx => 7 | .rbp => 8 | .r12 => 9 | .r13 => 10 | .r14 => 11 | .r15 => 12
  | _ => 0

/-- A spill's variable: offsets `8`, `16`, `24`. -/
def spillVar (o : Nat) : Nat := 12 + o / 8

/-- The pushes: RBP, R15, R14, R13, R12, RBX from offset `72` down, the variables `0` to `5`. -/
def pushW : List Write :=
  [⟨0, 72, 8, .var 0⟩, ⟨0, 64, 8, .var 1⟩, ⟨0, 56, 8, .var 2⟩, ⟨0, 48, 8, .var 3⟩,
    ⟨0, 40, 8, .var 4⟩, ⟨0, 32, 8, .var 5⟩]

/-- At the entry. -/
def t0 : SState := tpl [88, 128] [(.rsp, .ptr 0 80), (.rdx, .ptr 1 0)] []

/-- After a call: the registers `rr`, the spills `ss`. -/
def tB (rr : List Reg64) (ss : List Nat) : SState :=
  tpl [88, 128] ((.rsp, .ptr 0 8) :: (.rbx, .ptr 1 0) :: rr.map fun r ↦ (r, .var (regVar r)))
    (ss.map (fun o ↦ ⟨0, o, 8, .var (spillVar o)⟩) ++ pushW)

def t1 : SState := tB [.rax, .rdx, .r14, .r15] []
def t2 : SState := tB [.rax, .rdx, .rbp, .r12] []
def t3 : SState := tB [.rax, .rdx, .rbp, .r12, .r14, .r15] []
def t4 : SState := tB [.rax, .rdx, .r13] [24]
def t5 : SState := tB [.rax, .rdx, .r13, .r14, .r15] [24]
def t6 : SState := tB [.rax, .rdx, .r13] [8, 16, 24]
def t7 : SState := tB [.rax, .rdx, .rbp, .r12, .r13] [8, 16, 24]
def t8 : SState := tB [.rax, .rdx] [8, 16, 24]
def t9 : SState := tB [.rax, .rdx, .r12, .r13] [8, 16, 24]
def t10 : SState := tB [.rax, .rdx, .r14, .r15] [8, 16, 24]
def t11 : SState := tB [.rax, .rdx, .r12, .r13, .r14, .r15] [8, 16, 24]
def t12 : SState := tB [.rax, .rdx, .rbp] [8, 16, 24]
def t13 : SState := tB [.rax, .rdx, .rbp, .r14, .r15] [8, 16, 24]
def t14 : SState := tB [.rax, .rdx, .r12, .r13] [8, 16, 24]
def t15 : SState := tB [.rax, .rdx, .r12, .r13] [8, 16, 24]

end

set_option Elab.async false

sym_block run_b0 := exec b0 t0
sym_block run_b1 := exec b1 t1
sym_block run_b2 := exec b2 t2
sym_block run_b3 := exec b3 t3
sym_block run_b4 := exec b4 t4
sym_block run_b5 := exec b5 t5
sym_block run_b6 := exec b6 t6
sym_block run_b7 := exec b7 t7
sym_block run_b8 := exec b8 t8
sym_block run_b9 := exec b9 t9
sym_block run_b10 := exec b10 t10
sym_block run_b11 := exec b11 t11
sym_block run_b12 := exec b12 t12
sym_block run_b13 := exec b13 t13
sym_block run_b14 := exec b14 t14
sym_block run_b15 := exec b15 t15

end NativeRustcVmX64.Ring.Psi
