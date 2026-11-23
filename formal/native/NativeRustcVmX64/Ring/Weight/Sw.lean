module

public import NativeRustcVmX64.Ring.Weight.Exec

/-!
# `ring_weight`'s template switches, checked by the kernel (x86-64)

Where a block's next template reads another window (or none), the same registers and writes
under the new template (`SwOk`).
-/

namespace NativeRustcVmX64.Ring.Weight

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring

set_option Elab.async false

public theorem sw_sum : SwOk (tZ sz0 [] 0) (tZ (sz1 1024) cAl 0) = true ∧
    SwOk (tE (sz1 1024) []) (tE (sz1 24) oAl) = true := by
  decide +kernel

public theorem sw_one : SwOk (tL sz0 [] 0) (tL (sz1 (16 * 0 + 16)) rAl 0) = true := by
  decide +kernel

public theorem sw_b6 : SwOk (tC sz0 [] 0) (tC (sz1 (32 * 0 + 32)) rAl 0) = true := by
  decide +kernel

public theorem sw_b7 : ∀ t < 17,
    SwOk (tC (sz1 (32 * t + 32)) rAl (t + 1)) (tC (sz1 (32 * (t + 1) + 32)) rAl (t + 1)) = true := by
  decide +kernel

public theorem sw_b8 : ∀ h < 19, SwOk (tL (sz1 (32 * h)) rAl (2 * h)) (tD sz0 []) = true ∧
    SwOk (tL (sz1 (32 * h)) rAl (2 * h)) (tL (sz1 (16 * (2 * h) + 16)) rAl (2 * h)) = true := by
  decide +kernel

public theorem sw_b9 : ∀ c < 36, SwOk (tD (sz1 (16 * c + 16)) []) (tD sz0 []) = true := by
  decide +kernel

public theorem sw_out : SwOk (tO sz0 []) (tO (sz1 16) kAl) = true ∧
    SwOk (tP (sz1 16) [] 0) (tP (sz1 (16 * 0 + 16)) qAl 0) = true ∧
    SwOk (tE sz0 []) (tE (sz1 24) oAl) = true ∧
    SwOk (tO2 sz0 []) (tO2 (sz1 16) kAl) = true ∧
    SwOk (tS2 (sz1 16) 0) (tS2 sz0 0) = true ∧
    SwOk (tO2 sz0 []) (tE (sz1 24) oAl) = true := by
  decide +kernel

public theorem sw_prod : ∀ i < 36,
    SwOk (tP (sz1 (16 * i + 16)) qAl (i + 1)) (tP (sz1 (16 * (i + 1) + 16)) qAl (i + 1)) = true ∧
    SwOk (tP (sz1 (16 * i + 16)) qAl (i + 1)) (tP sz0 [] (i + 1)) = true := by
  decide +kernel

end NativeRustcVmX64.Ring.Weight
