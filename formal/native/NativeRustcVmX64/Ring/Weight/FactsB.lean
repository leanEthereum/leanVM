module

public import NativeRustcVmX64.Ring.Weight.Exec
public import NativeRustcVmX64.Code.Vm.RingWeight.Names

/-!
# `ring_weight`'s product loop, checked by the kernel at each factor (x86-64)

`b13` (factor `i < 36`: `EW::mul` of the product so far and `1 + P_i + r'_i`), `b14` (the next
factor), `b15` (the product spilled, the powers' loop set up).
-/

namespace NativeRustcVmX64.Ring.Weight

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeRustcVmX64.Vm.RingWeight
open NativeRustcVmX64.Transcript (after)

set_option Elab.async false

public theorem f_b13 : ∀ i < 36,
    COk b13 (tP (sz1 (16 * i + 16)) qAl i) (tP (sz1 (16 * i + 16)) qAl i) (sz1 (16 * i + 16))
      qkL ockL = true ∧
    (after b13 (tP (sz1 (16 * i + 16)) qAl i)).reg .rdi = some (.var 6) ∧
    (after b13 (tP (sz1 (16 * i + 16)) qAl i)).reg .rsi = some (.var 7) ∧
    (after b13 (tP (sz1 (16 * i + 16)) qAl i)).reg .rdx = some (fA i) ∧
    (after b13 (tP (sz1 (16 * i + 16)) qAl i)).reg .rcx = some (fB i) ∧
    missR 48 624 (after b13 (tP (sz1 (16 * i + 16)) qAl i)) = true := by
  decide +kernel

public theorem f_b14 : ∀ i < 36,
    JOk b14 (tP (sz1 (16 * i + 16)) qAl i) (tP (sz1 (16 * i + 16)) qAl (i + 1))
      (.cond (.not (.cmp .eq .W64 (.var 17) (.lit (16 * i + 16)))) NativeRustcVmX64.Vm.RingWeight.label_18)
      (sz1 (16 * i + 16)) (fun _ ↦ false) ((6, .var 6) :: (15, .var 15) :: (7, .var 7) ::
        [(20, .var 20), (17, .var 17), (21, .var 21), (12, .var 12)]) ockL = true ∧
    missR 48 624 (after b14 (tP (sz1 (16 * i + 16)) qAl i)) = true := by
  decide +kernel

public theorem f_b15 : ∀ i < 37,
    JOk b15 (tP sz0 [] i) (tS sz0 0) .fall sz0 (fun _ ↦ false) qkL
      ((23, .var 7) :: (8, .var 8) :: (9, .var 9) :: (19, .var 19) :: (24, .var 6) :: pL) = true ∧
    missR 48 624 (after b15 (tP sz0 [] i)) = true := by
  decide +kernel

end NativeRustcVmX64.Ring.Weight
