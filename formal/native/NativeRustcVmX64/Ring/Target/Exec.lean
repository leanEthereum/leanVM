module

public import NativeRustcVmX64.Ring.Seq
public meta import NativeRustcVmX64.Ring.Seq
public import NativeRustcVmX64.Code.Vm.RingTarget
public meta import NativeRustcVmX64.Code.Vm.RingTarget

/-!
# `ring_target`'s blocks, run by the symbolic executor (x86-64)

Region `0` the 2352-byte frame (the six pushes from `2304`, the products' and powers' spills from
`16`, the images from `256`, their copy from `1280`, a callee's return address at `0`) and the
return address. The images loop (`b0` to `b3`) has `s` as region `1` (`sizesL`): `t0L` at the
entry, `H i` at turn `i`'s head (R15 the literal `8 + 16 i`), `A i` after `ring_psi`, `t4L` after
`memcpy`. The turns (`b4` to `b36`) have `f` as region `1` (`sizesC`), reached through R12, the
variable `10` (`fKey`): `t<j>` before block `j` (`tC`: registers and spills the variables
`regVar`, `spillVar`).
-/

namespace NativeRustcVmX64.Ring.Target

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeRustcVmX64.Vm.RingTarget

@[expose] public section

/-- The pushes: RBP, R15, R14, R13, R12, RBX from offset `2344` down, the variables `0` to `5`. -/
def pushW : List Write :=
  [⟨0, 2344, 8, .var 0⟩, ⟨0, 2336, 8, .var 1⟩, ⟨0, 2328, 8, .var 2⟩, ⟨0, 2320, 8, .var 3⟩,
    ⟨0, 2312, 8, .var 4⟩, ⟨0, 2304, 8, .var 5⟩]

/-- The pushes' links. -/
def pushL : List (Nat × Sym) :=
  [(0, .var 0), (1, .var 1), (2, .var 2), (3, .var 3), (4, .var 4), (5, .var 5)]

def sizesL : List Nat := [2360, 1024]
def sizesC : List Nat := [2360, 128]

/-- At the entry. -/
def t0L : SState := tpl sizesL [(.rsp, .ptr 0 2352), (.rdi, .ptr 1 0)] []

/-- Turn `i`'s head: `g` in RBX, `f` in R12, `s` region `1` in R14, R15 `8 + 16 i`. -/
def H (i : Nat) : SState :=
  tpl sizesL [(.rsp, .ptr 0 8), (.rbx, .var 8), (.r12, .var 10), (.r14, .ptr 1 0),
    (.r15, .lit (8 + 16 * i))] pushW

/-- After `ring_psi`: its result in RAX, RDX. -/
def A (i : Nat) : SState :=
  tpl sizesL [(.rsp, .ptr 0 8), (.rbx, .var 8), (.r12, .var 10), (.r14, .ptr 1 0),
    (.r15, .lit (8 + 16 * i)), (.rax, .var 6), (.rdx, .var 7)] pushW

/-- After `memcpy`. -/
def t4L : SState := tpl sizesL [(.rsp, .ptr 0 8), (.r12, .var 10), (.r15, .ptr 0 1280)] pushW

/-- The copy alone reads the `memcpy` slot, as a third ordinary-memory region. -/
def copyBase : SState :=
  tpl [2360, 1024, 8] [(.rsp, .ptr 0 8), (.r12, .var 10)] pushW []
    [(.gotSlot "memcpy", 2, 0)]
def copyS : SState := copyBase.withKnownBytes 2 0 8 (.label "memcpy")
def copiedS : SState :=
  tpl [2360, 1024, 8] [(.rsp, .ptr 0 8), (.r12, .var 10), (.r15, .ptr 0 1280)] pushW

/-- A register's variable. -/
def regVar : Reg64 → Nat
  | .rax => 6 | .rdx => 7 | .rbx => 8 | .rbp => 9 | .r12 => 10 | .r13 => 11 | .r14 => 12
  | .r15 => 13 | _ => 0

/-- A spill's variable (its offset from RSP). -/
def spillVar (o : Nat) : Nat := 13 + o / 8

/-- `f` through R12. -/
def fKey : List (Sym × Nat × Int) := [(.var 10, 1, 0)]

/-- A turns' template: RSP at the frame's offset `8`, the registers `ptrs`, the registers `rr`
and the spills `ss` (offsets from RSP) their variables. -/
def tC (ptrs : List (Reg64 × Sym)) (rr : List Reg64) (ss : List Nat)
    (keys : List (Sym × Nat × Int)) : SState :=
  tpl sizesC ((.rsp, .ptr 0 8) :: ptrs ++ rr.map fun r ↦ (r, .var (regVar r)))
    (ss.map (fun o ↦ ⟨0, 8 + o, 8, .var (spillVar o)⟩) ++ pushW) [] keys

def t4 : SState := tC [(.r15, .ptr 0 1280)] [.r12] [] fKey
def t5 : SState := tC [(.r15, .ptr 0 1280)] [.rax, .rdx, .r12] [] fKey
def t6 : SState := tC [(.r15, .ptr 0 1280)] [.rax, .rdx, .rbx, .r12, .r14] [232, 240] fKey
def t7 : SState := tC [(.r15, .ptr 0 1280)] [.rax, .rdx, .rbx, .r12, .r14] [232, 240] fKey
def t8 : SState := tC [(.r15, .ptr 0 1280)] [.rax, .rdx, .rbx, .r12, .r14] [216, 224, 232, 240] fKey
def t9 : SState := tC [(.r15, .ptr 0 1280)] [.rax, .rdx, .rbx, .r12, .r14] [200, 208, 216, 224, 232, 240] fKey
def t10 : SState := tC [(.r15, .ptr 0 1280)] [.rax, .rdx, .rbx, .r12, .r14] [200, 208, 216, 224, 232, 240] fKey
def t11 : SState := tC [(.r15, .ptr 0 1280)] [.rax, .rdx, .rbx, .r12, .r14] [184, 192, 200, 208, 216, 224, 232, 240] fKey
def t12 : SState := tC [(.r15, .ptr 0 1280)] [.rax, .rdx, .rbx, .r12, .r14] [56, 176, 184, 192, 200, 208, 216, 224, 232, 240] fKey
def t13 : SState := tC [(.r15, .ptr 0 1280)] [.rax, .rdx, .rbx, .r12, .r14] [56, 176, 184, 192, 200, 208, 216, 224, 232, 240] fKey
def t14 : SState := tC [(.r15, .ptr 0 1280)] [.rax, .rdx, .rbx, .r12, .r14] [56, 160, 168, 176, 184, 192, 200, 208, 216, 224, 232, 240] fKey
def t15 : SState := tC [(.r15, .ptr 0 1280)] [.rax, .rdx, .rbx, .r12, .r14] [48, 56, 152, 160, 168, 176, 184, 192, 200, 208, 216, 224, 232, 240] fKey
def t16 : SState := tC [(.r15, .ptr 0 1280)] [.rax, .rdx, .rbx, .r12, .r14] [48, 56, 152, 160, 168, 176, 184, 192, 200, 208, 216, 224, 232, 240] fKey
def t17 : SState := tC [(.r15, .ptr 0 1280)] [.rax, .rdx, .rbx, .r12, .r14] [48, 56, 136, 144, 152, 160, 168, 176, 184, 192, 200, 208, 216, 224, 232, 240] fKey
def t18 : SState := tC [(.r15, .ptr 0 1280)] [.rax, .rdx, .rbx, .r12, .r14] [32, 40, 48, 56, 136, 144, 152, 160, 168, 176, 184, 192, 200, 208, 216, 224, 232, 240] fKey
def t19 : SState := tC [(.r15, .ptr 0 1280)] [.rax, .rdx, .rbx, .r12, .r14] [32, 40, 48, 56, 136, 144, 152, 160, 168, 176, 184, 192, 200, 208, 216, 224, 232, 240] fKey
def t20 : SState := tC [(.r15, .ptr 0 1280)] [.rax, .rdx, .rbx, .r12, .r14] [32, 40, 48, 56, 88, 96, 136, 144, 152, 160, 168, 176, 184, 192, 200, 208, 216, 224, 232, 240] fKey
def t21 : SState := tC [(.r15, .ptr 0 1280)] [.rax, .rdx, .rbx, .rbp, .r12, .r14] [8, 16, 32, 40, 48, 56, 88, 96, 136, 144, 152, 160, 168, 176, 184, 192, 200, 208, 216, 224, 232, 240] fKey
def t22 : SState := tC [(.r15, .ptr 0 1280)] [.rax, .rdx, .rbx, .rbp, .r12, .r14] [8, 16, 32, 40, 48, 56, 88, 96, 136, 144, 152, 160, 168, 176, 184, 192, 200, 208, 216, 224, 232, 240] fKey
def t23 : SState := tC [(.r15, .ptr 0 1280)] [.rax, .rdx, .rbx, .rbp, .r12, .r14] [8, 16, 32, 40, 48, 56, 64, 72, 88, 96, 136, 144, 152, 160, 168, 176, 184, 192, 200, 208, 216, 224, 232, 240] fKey
def t24 : SState := tC [(.r15, .ptr 0 1280)] [.rax, .rdx, .rbx, .rbp, .r12, .r13, .r14] [8, 16, 24, 32, 40, 48, 56, 64, 72, 88, 96, 136, 144, 152, 160, 168, 176, 184, 192, 200, 208, 216, 224, 232, 240] fKey
def t25 : SState := tC [(.r15, .ptr 0 1280)] [.rax, .rdx, .rbx, .rbp, .r12, .r13, .r14] [8, 16, 24, 32, 40, 48, 56, 64, 72, 88, 96, 136, 144, 152, 160, 168, 176, 184, 192, 200, 208, 216, 224, 232, 240] fKey
def t26 : SState := tC [] [.rax, .rdx, .rbx, .rbp, .r12, .r13, .r14, .r15] [8, 16, 24, 32, 40, 48, 56, 64, 72, 88, 96, 136, 144, 152, 160, 168, 176, 184, 192, 200, 208, 216, 224, 232, 240] fKey
def t27 : SState := tC [] [.rax, .rdx, .rbx, .rbp, .r12, .r13, .r14, .r15] [8, 16, 24, 32, 40, 48, 56, 64, 72, 88, 96, 104, 112, 120, 128, 136, 144, 152, 160, 168, 176, 184, 192, 200, 208, 216, 224, 232, 240] fKey
def t28 : SState := tC [] [.rax, .rdx, .rbx, .rbp, .r12, .r13, .r14, .r15] [8, 16, 24, 32, 40, 48, 56, 64, 72, 80, 88, 96, 104, 112, 120, 128, 136, 144, 152, 160, 168, 176, 184, 192, 200, 208, 216, 224, 232, 240] fKey
def t29 : SState := tC [] [.rax, .rdx, .rbx, .rbp, .r12, .r13, .r14, .r15] [8, 16, 24, 32, 40, 48, 56, 64, 72, 80, 88, 96, 104, 112, 120, 128, 136, 144, 152, 160, 168, 176, 184, 192, 200, 208, 216, 224, 232, 240] fKey
def t30 : SState := tC [] [.rax, .rdx, .rbx, .rbp, .r12, .r13, .r14, .r15] [8, 16, 24, 32, 40, 48, 56, 64, 72, 80, 88, 96, 104, 112, 120, 128, 136, 144, 152, 160, 168, 176, 184, 192, 200, 208, 216, 224, 232, 240] fKey
def t31 : SState := tC [] [.rax, .rdx, .rbx, .rbp, .r12, .r13, .r14, .r15] [8, 16, 24, 32, 40, 48, 56, 64, 72, 80, 88, 96, 104, 112, 120, 128, 136, 144, 152, 160, 168, 176, 184, 192, 200, 208, 216, 224, 232, 240] fKey
def t32 : SState := tC [] [.rax, .rdx, .rbx, .rbp, .r12, .r13, .r14, .r15] [8, 16, 24, 32, 40, 48, 56, 64, 72, 80, 88, 96, 104, 112, 120, 128, 136, 144, 152, 160, 168, 176, 184, 192, 200, 208, 216, 224, 232, 240] fKey
def t33 : SState := tC [] [.rax, .rdx, .rbx, .rbp, .r12, .r13, .r14, .r15] [8, 16, 24, 32, 40, 48, 56, 64, 72, 80, 88, 96, 104, 112, 120, 128, 136, 144, 152, 160, 168, 176, 184, 192, 200, 208, 216, 224, 232, 240] fKey
def t34 : SState := tC [] [.rax, .rdx, .rbx, .rbp, .r12, .r13, .r14, .r15] [8, 16, 24, 32, 40, 48, 56, 64, 72, 80, 88, 96, 104, 112, 120, 128, 136, 144, 152, 160, 168, 176, 184, 192, 200, 208, 216, 224, 232, 240] []
def t35 : SState := tC [] [.rax, .rdx, .rbx, .rbp, .r12, .r13, .r14, .r15] [8, 16, 24, 32, 40, 48, 56, 64, 72, 80, 88, 96, 104, 112, 120, 128, 136, 144, 152, 160, 168, 176, 184, 192, 200, 208, 216, 224, 232, 240] []
def t36 : SState := tC [] [.rax, .rdx, .rbx, .rbp, .r12, .r13, .r14, .r15] [8, 16, 24, 32, 40, 48, 56, 64, 72, 80, 88, 96, 104, 112, 120, 128, 136, 144, 152, 160, 168, 176, 184, 192, 200, 208, 216, 224, 232, 240] []

end

set_option Elab.async false

sym_block run_b0 := exec b0 t0L
sym_block run_b3 := exec b3 copyS
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
sym_block run_b16 := exec b16 t16
sym_block run_b17 := exec b17 t17
sym_block run_b18 := exec b18 t18
sym_block run_b19 := exec b19 t19
sym_block run_b20 := exec b20 t20
sym_block run_b21 := exec b21 t21
sym_block run_b22 := exec b22 t22
sym_block run_b23 := exec b23 t23
sym_block run_b24 := exec b24 t24
sym_block run_b25 := exec b25 t25
sym_block run_b26 := exec b26 t26
sym_block run_b27 := exec b27 t27
sym_block run_b28 := exec b28 t28
sym_block run_b29 := exec b29 t29
sym_block run_b30 := exec b30 t30
sym_block run_b31 := exec b31 t31
sym_block run_b32 := exec b32 t32
sym_block run_b33 := exec b33 t33
sym_block run_b34 := exec b34 t34
sym_block run_b35 := exec b35 t35
sym_block run_b36 := exec b36 t36

end NativeRustcVmX64.Ring.Target
