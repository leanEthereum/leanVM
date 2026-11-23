module

public import NativeRustcVmX64.Ring.Weight.Exec
public import NativeRustcVmX64.Code.Vm.RingWeight.Names

/-!
# `ring_weight`'s sum and copy loops, checked by the kernel at each turn (x86-64)

`b4` (the coefficients' sum, `r` empty) at turn `t < 16`; `b7` (a pair of `r` copied into powers
`2 t`, `2 t + 1`) at turn `t < 18`; `b8` (`|r|` odd?) after `t` turns; `b9` (the last element
`c` copied).
-/

namespace NativeRustcVmX64.Ring.Weight

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeRustcVmX64.Vm.RingWeight
open NativeRustcVmX64.Transcript (after)

set_option Elab.async false

public theorem f_b4 : ∀ t < 16, JOk b4 (tZ (sz1 1024) cAl t) (tZ (sz1 1024) cAl (t + 1))
    (.cond (.lit (decide (t < 15))) NativeRustcVmX64.Vm.RingWeight.label_2) (sz1 1024) (fun _ ↦ false)
    [(20, sumX 20 (64 * t)), (9, .var 9), (21, sumX 21 (64 * t + 8))] oL = true := by
  decide +kernel

public theorem f_b7 : ∀ t < 18,
    JOk b7 (tC (sz1 (32 * t + 32)) rAl t) (tC (sz1 (32 * t + 32)) rAl (t + 1))
      (.cond (.not (.cmp .eq .W64 (.var 25) (.lit (2 * t + 2)))) NativeRustcVmX64.Vm.RingWeight.label_15)
      (sz1 (32 * t + 32)) (fun _ ↦ false)
      [(14, .var 14), (25, .var 25), (10, .var 10), (13, .var 13), (9, .var 9), (11, .var 11),
        (12, .var 12)] oL = true ∧
    storeOk (after b7 (tC (sz1 (32 * t + 32)) rAl t)) (48 + 32 * t) (.load 1 (32 * t) 8)
      (.load 1 (32 * t + 8) 8) = true ∧
    storeOk (after b7 (tC (sz1 (32 * t + 32)) rAl t)) (64 + 32 * t) (.load 1 (32 * t + 16) 8)
      (.load 1 (32 * t + 24) 8) = true ∧
    missR 48 (48 + 32 * t) (after b7 (tC (sz1 (32 * t + 32)) rAl t)) = true ∧
    missR (80 + 32 * t) 624 (after b7 (tC (sz1 (32 * t + 32)) rAl t)) = true := by
  decide +kernel

public theorem f_b8 : ∀ t < 19,
    JOk b8 (tC (sz1 (32 * t)) rAl t) (tL (sz1 (32 * t)) rAl (2 * t))
      (.cond (.cmp .eq .W8 (.bin .and .W8 (.var 11) (.lit 1)) (.lit 0)) NativeRustcVmX64.Vm.RingWeight.label_7)
      (sz1 (32 * t)) (fun _ ↦ false) cpL oL = true ∧
    missR 48 624 (after b8 (tC (sz1 (32 * t)) rAl t)) = true := by
  decide +kernel

public theorem f_b9 : ∀ c < 36,
    JOk b9 (tL (sz1 (16 * c + 16)) rAl c) (tD (sz1 (16 * c + 16)) []) .fall (sz1 (16 * c + 16))
      (fun _ ↦ false) [(14, .var 14), (13, .var 13), (9, .var 9), (11, .var 11), (12, .var 12)]
      oL = true ∧
    storeOk (after b9 (tL (sz1 (16 * c + 16)) rAl c)) (48 + 16 * c) (.load 1 (16 * c) 8)
      (.load 1 (16 * c + 8) 8) = true ∧
    missR 48 (48 + 16 * c) (after b9 (tL (sz1 (16 * c + 16)) rAl c)) = true ∧
    missR (64 + 16 * c) 624 (after b9 (tL (sz1 (16 * c + 16)) rAl c)) = true := by
  decide +kernel

end NativeRustcVmX64.Ring.Weight
