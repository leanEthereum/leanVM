module

public import NativeRustcVmX64.Ring.Weight.Exec
public import NativeRustcVmX64.Code.Vm.RingWeight.Names

/-!
# `ring_weight`'s squaring loops, checked by the kernel at each power (x86-64)

With `r'` not empty: `b16` (power `j < 36` squared by `EW::mul`), `b17` (stored), `b18` (the
next coefficient). With `r'` empty: `b22`, `b23`, `b24`.
-/

namespace NativeRustcVmX64.Ring.Weight

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeRustcVmX64.Vm.RingWeight
open NativeRustcVmX64.Transcript (after)

set_option Elab.async false

public theorem f_b16 : ∀ j < 36,
    COk b16 (tS sz0 j) (tSA sz0 j) sz0 qkL sL = true ∧
    (after b16 (tS sz0 j)).reg .rdi = some (.load 0 (48 + 16 * j) 8) ∧
    (after b16 (tS sz0 j)).reg .rsi = some (.load 0 (56 + 16 * j) 8) ∧
    (after b16 (tS sz0 j)).reg .rdx = some (.load 0 (48 + 16 * j) 8) ∧
    (after b16 (tS sz0 j)).reg .rcx = some (.load 0 (56 + 16 * j) 8) ∧
    missR 48 624 (after b16 (tS sz0 j)) = true := by
  decide +kernel

public theorem f_b17 : ∀ j < 36,
    JOk b17 (tSA sz0 j) (tS sz0 (j + 1))
      (.cond (.not (.cmp .eq .W64 (.ptr 0 ((64 + 16 * j : Nat) : Int)) (.var 15))) NativeRustcVmX64.Vm.RingWeight.label_20)
      sz0 (fun _ ↦ false) qkL sL = true ∧
    storeOk (after b17 (tSA sz0 j)) (48 + 16 * j) (.var 6) (.var 7) = true ∧
    missR 48 (48 + 16 * j) (after b17 (tSA sz0 j)) = true ∧
    missR (64 + 16 * j) 624 (after b17 (tSA sz0 j)) = true := by
  decide +kernel

public theorem f_b18 : ∀ j < 37,
    JOk b18 (tS sz0 j) (tO sz0 [])
      (.cond (.not (.cmp .eq .W64 k16 (.lit 1024))) NativeRustcVmX64.Vm.RingWeight.label_17) sz0 (fun _ ↦ false)
      [(15, .var 15), (19, k16), (20, t20), (9, .var 9), (17, .var 17), (21, t21), (12, .var 12)]
      ocL = true ∧
    missR 48 624 (after b18 (tS sz0 j)) = true := by
  decide +kernel

public theorem f_b22 : ∀ j < 36,
    COk b22 (tS2 sz0 j) (tSA2 sz0 j) sz0 q2L s2L = true ∧
    (after b22 (tS2 sz0 j)).reg .rdi = some (.load 0 (48 + 16 * j) 8) ∧
    (after b22 (tS2 sz0 j)).reg .rsi = some (.load 0 (56 + 16 * j) 8) ∧
    (after b22 (tS2 sz0 j)).reg .rdx = some (.load 0 (48 + 16 * j) 8) ∧
    (after b22 (tS2 sz0 j)).reg .rcx = some (.load 0 (56 + 16 * j) 8) ∧
    missR 48 624 (after b22 (tS2 sz0 j)) = true := by
  decide +kernel

public theorem f_b23 : ∀ j < 36,
    JOk b23 (tSA2 sz0 j) (tS2 sz0 (j + 1))
      (.cond (.not (.cmp .eq .W64 (.ptr 0 ((64 + 16 * j : Nat) : Int)) (.var 15))) NativeRustcVmX64.Vm.RingWeight.label_11)
      sz0 (fun _ ↦ false) q2L s2L = true ∧
    storeOk (after b23 (tSA2 sz0 j)) (48 + 16 * j) (.var 6) (.var 7) = true ∧
    missR 48 (48 + 16 * j) (after b23 (tSA2 sz0 j)) = true ∧
    missR (64 + 16 * j) 624 (after b23 (tSA2 sz0 j)) = true := by
  decide +kernel

public theorem f_b24 : ∀ j < 37,
    JOk b24 (tS2 sz0 j) (tO2 sz0 [])
      (.cond (.not (.cmp .eq .W64 k16 (.lit 1024))) NativeRustcVmX64.Vm.RingWeight.label_10) sz0 (fun _ ↦ false)
      [(15, .var 15), (20, t20), (9, .var 9), (21, t21), (19, k16)] ocL = true ∧
    missR 48 624 (after b24 (tS2 sz0 j)) = true := by
  decide +kernel

end NativeRustcVmX64.Ring.Weight
