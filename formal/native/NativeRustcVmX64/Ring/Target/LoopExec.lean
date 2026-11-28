module

public import NativeRustcVmX64.Ring.Target.Exec
public import NativeRustcVmX64.Transcript.Glue
public import NativeRustcVmX64.Spec.Ring
public import NativeRustcVmX64.Code.Vm.RingPsi.Names
public import NativeRustcVmX64.Code.Vm.RingTarget.Names

/-!
# `ring_target`'s images loop, run by the symbolic executor at each turn (x86-64)

Turn `i` (`i < 64`) from `H i`: `b1` loads `s_i` (region `1`'s offsets `16 i`, `16 i + 8`) and calls
`ring_psi` (`loop_b1`), `b2` stores its result at the frame's offsets `256 + 16 i`, `264 + 16 i`,
steps R15 and branches back while `i < 63` (`loop_b2`). Checked by the kernel for every turn.
-/

namespace NativeRustcVmX64.Ring.Target

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeRustcVmX64.Vm.RingTarget
open NativeRustcVmX64.Transcript (after)

set_option Elab.async false

public theorem loop_b1 : ∀ i < 64,
    exec b1 (H i) = some (after b1 (H i), .call NativeRustcVmX64.Vm.RingPsi.entryLabel) ∧
    (after b1 (H i)).reg .rdi = some (.load 1 (16 * i) 8) ∧
    (after b1 (H i)).reg .rsi = some (.load 1 (16 * i + 8) 8) ∧
    (after b1 (H i)).reg .rdx = some (.var 8) ∧ (after b1 (H i)).reg .rsp = some (.ptr 0 0) ∧
    rlinks true (after b1 (H i)) (A i) = some [(8, .var 8), (10, .var 10)] ∧
    wlinks (after b1 (H i)) (A i).mem = some pushL ∧
    (after b1 (H i)).mem.all (writeOk 2352 sizesL (fun _ ↦ false)) = true ∧
    (after b1 (H i)).mem.all (fun w ↦ w.r == 0 && (decide (w.off + w.n ≤ 8) ||
      decide (2304 ≤ w.off))) = true := by
  decide +kernel

public theorem loop_b2 : ∀ i < 64,
    exec b2 (A i) = some (after b2 (A i), .cond (.lit (decide (i < 63))) NativeRustcVmX64.Vm.RingTarget.label_1) ∧
    rlinks false (after b2 (A i)) (H (i + 1)) = some [(8, .var 8), (10, .var 10)] ∧
    wlinks (after b2 (A i)) (H (i + 1)).mem = some pushL ∧
    (after b2 (A i)).mem.all (writeOk 2352 sizesL (fun _ ↦ false)) = true ∧
    (after b2 (A i)).mem.all (fun w ↦ w.r == 0 && (decide (w.off + w.n ≤ 256) ||
      decide (256 + 16 * i ≤ w.off))) = true := by
  decide +kernel

public theorem loop_b2w : ∀ i < 64, ∀ t < 8,
    findWrite 0 (256 + 16 * i + t) (after b2 (A i)).mem = some (.var 6, t) ∧
    findWrite 0 (264 + 16 * i + t) (after b2 (A i)).mem = some (.var 7, t) := by
  decide +kernel

end NativeRustcVmX64.Ring.Target
