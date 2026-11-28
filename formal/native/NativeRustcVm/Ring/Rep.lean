module

public import NativeRustcVm.Mem
public import NativeVm.Model.RingSwitch

/-!
# Ring switching's output in memory

The crate's `RingW` (`rustc/vm/src/ring_switch.rs`, `#[repr(C)]`, 1040 bytes) holds what phase 7a
hands on (`RingWAt`): the target `T` at byte `0`, the 64 Frobenius coefficients `c_k` from byte
`16`, sixteen bytes each. The point of the ring-switched claim's weight is `KeccakOutW`'s.
-/

namespace NativeRustcVm.Ring

open NativeVm.Model

@[expose] public section

/-- `RING_COEFF_COUNT`: the coefficients' count, `ringMapWidth²`. -/
def coeffCount : Nat := 64

/-- `RingW`'s bytes: the target, then the coefficients. -/
def ringWBytes : Nat := 16 + 16 * coeffCount

/-- The `RingW` at `p` holds the target and the `64` coefficients. -/
def RingWAt (d : Mem 64) (p : BitVec 64) (target : EW) (coefficients : Array EW) : Prop :=
  EWAt d p target ∧ coefficients.size = coeffCount ∧ EWsAt d (p + 16#64) coefficients.toList

end

end NativeRustcVm.Ring
