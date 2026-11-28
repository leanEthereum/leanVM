module

public import NativeRustcVmX64.Ring.Weight.Exec
public import NativeRustcVmX64.Code.Vm.RingWeight.Names

/-!
# `ring_weight`'s blocks outside the loops, checked by the kernel (x86-64)

Each block from its template: its exit, its writes, its links to the next template (`JOk`), the
frame bytes it leaves alone (`missR`), its stores (`storeOk`); the epilogue's registers.
-/

namespace NativeRustcVmX64.Ring.Weight

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeRustcVmX64.Vm.RingWeight
open NativeRustcVmX64.Transcript (after)

set_option Elab.async false

public theorem f_b0 : JOk b0 t0 (tA sz0 [])
    (.cond (.cmp .eq .W64 (.bin .and .W64 (.reg .rdx) (.reg .rdx)) (.lit 0)) NativeRustcVmX64.Vm.RingWeight.label_1)
    sz0 (fun _ ↦ false)
    [(12, .reg .rcx), (11, .reg .rdx), (10, .reg .rsi), (13, .reg .r8), (9, .reg .r9)]
    [(8, .reg .rdi), (0, .reg .rbp), (1, .reg .r15), (2, .reg .r14), (3, .reg .r13),
      (4, .reg .r12), (5, .reg .rbx)] = true := by
  decide +kernel

public theorem f_b1 : JOk b1 (tA sz0 []) (tB sz0 [])
    (.cond (.not (.cmp .eq .W64 (.var 11) (.lit 1))) NativeRustcVmX64.Vm.RingWeight.label_14) sz0 (fun _ ↦ false)
    [(14, .bin .shl .W64 (.var 11) (.lit 4)), (10, .var 10), (13, .var 13), (9, .var 9),
      (11, .var 11), (12, .var 12)] oL = true ∧ missR 48 624 (after b1 (tA sz0 [])) = true := by
  decide +kernel

public theorem f_b2 : JOk b2 (tB sz0 []) (tL sz0 [] 0) (.jump NativeRustcVmX64.Vm.RingWeight.label_6) sz0 (fun _ ↦ false)
    [(14, .var 14), (10, .var 10), (13, .var 13), (9, .var 9), (11, .var 11), (12, .var 12)]
    oL = true ∧ missR 48 624 (after b2 (tB sz0 [])) = true := by
  decide +kernel

public theorem f_b3 : JOk b3 (tA sz0 []) (tZ sz0 [] 0) .fall sz0 (fun _ ↦ false)
    [(20, .lit 0), (9, .var 9), (21, .lit 0)] oL = true := by
  decide +kernel

public theorem f_b5 : JOk b5 (tZ (sz1 1024) cAl 16) (tE (sz1 1024) []) (.jump NativeRustcVmX64.Vm.RingWeight.label_13)
    (sz1 1024) (fun _ ↦ false) [(20, .var 20), (21, .var 21)] oL = true := by
  decide +kernel

public theorem f_b6 : JOk b6 (tB sz0 []) (tC sz0 [] 0) .fall sz0 (fun _ ↦ false)
    [(14, .var 14), (25, and25), (10, .var 10), (13, .var 13), (9, .var 9), (11, .var 11),
      (12, .var 12)] oL = true ∧ missR 48 624 (after b6 (tB sz0 [])) = true := by
  decide +kernel

public theorem f_b10 : JOk b10 (tD sz0 []) (tF sz0 [])
    (.cond (.cmp .eq .W64 (.bin .and .W64 (.var 13) (.var 13)) (.lit 0)) NativeRustcVmX64.Vm.RingWeight.label_9)
    sz0 (fun _ ↦ false) [(15, end15), (9, .var 9), (16, min16), (12, .var 12)] ocL = true ∧
    missR 48 624 (after b10 (tD sz0 [])) = true := by
  decide +kernel

public theorem f_b11 : JOk b11 (tF sz0 []) (tO sz0 []) .fall sz0 (fun _ ↦ false)
    [(15, .var 15), (19, .lit 0), (20, .lit 0), (9, .var 9), (17, .bin .shl .W64 (.var 16) (.lit 4)),
      (21, .lit 0), (12, .var 12)] ocL = true ∧ missR 48 624 (after b11 (tF sz0 [])) = true := by
  decide +kernel

public theorem f_b12 : JOk b12 (tO (sz1 16) kAl) (tP (sz1 16) [] 0) .fall (sz1 16) (fun _ ↦ false)
    [(6, .load 1 0 8), (15, .var 15), (7, .load 1 8 8), (20, .var 20), (17, .var 17),
      (21, .var 21), (12, .var 12)] ockL = true ∧
    missR 48 624 (after b12 (tO (sz1 16) kAl)) = true := by
  decide +kernel

public theorem f_b19 : JOk b19 (tO sz0 []) (tE sz0 []) (.jump NativeRustcVmX64.Vm.RingWeight.label_13) sz0
    (fun _ ↦ false) [(20, .var 20), (21, .var 21)] oL = true := by
  decide +kernel

public theorem f_b20 : JOk b20 (tF sz0 []) (tO2 sz0 []) .fall sz0 (fun _ ↦ false)
    [(15, .var 15), (20, .lit 0), (9, .var 9), (21, .lit 0), (19, .lit 0)] ocL = true ∧
    missR 48 624 (after b20 (tF sz0 [])) = true := by
  decide +kernel

public theorem f_b21 : JOk b21 (tO2 (sz1 16) kAl) (tS2 (sz1 16) 0) .fall (sz1 16) (fun _ ↦ false)
    [(15, .var 15), (20, .var 20), (21, .var 21), (24, .load 1 0 8), (19, .var 19)]
    ((23, .load 1 8 8) :: ocL) = true ∧ missR 48 624 (after b21 (tO2 (sz1 16) kAl)) = true := by
  decide +kernel

/-- The epilogue: the output's tag, the total, the registers restored, RSP above the return
address. -/
public theorem f_b25 :
    exec b25 (tE (sz1 24) oAl) = some (after b25 (tE (sz1 24) oAl), .ret (.load 0 672 8)) ∧
    (after b25 (tE (sz1 24) oAl)).mem.all (writeOk 672 (sz1 24) fun r ↦ r == 1) = true ∧
    (after b25 (tE (sz1 24) oAl)).reg .rsp = some (.ptr 0 680) ∧
    (after b25 (tE (sz1 24) oAl)).reg .rbx = some (.var 5) ∧
    (after b25 (tE (sz1 24) oAl)).reg .rbp = some (.var 0) ∧
    (after b25 (tE (sz1 24) oAl)).reg .r12 = some (.var 4) ∧
    (after b25 (tE (sz1 24) oAl)).reg .r13 = some (.var 3) ∧
    (after b25 (tE (sz1 24) oAl)).reg .r14 = some (.var 2) ∧
    (after b25 (tE (sz1 24) oAl)).reg .r15 = some (.var 1) ∧
    (∀ u < 8, findWrite 1 u (after b25 (tE (sz1 24) oAl)).mem = some (.lit 1, u) ∧
      findWrite 1 (8 + u) (after b25 (tE (sz1 24) oAl)).mem = some (.var 20, u) ∧
      findWrite 1 (16 + u) (after b25 (tE (sz1 24) oAl)).mem = some (.var 21, u)) := by
  decide +kernel

end NativeRustcVmX64.Ring.Weight
