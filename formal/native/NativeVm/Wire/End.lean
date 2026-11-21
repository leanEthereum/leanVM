module

public import NativeVm.Code.Contracts
import NativeVm.Wire.RunDecode

/-!
# The decoder's contract

`decode` meets `DecodeOk`, the contract `NativeVm.Code.Main` assumes of it (`decode_ok`). The
build fails if its axiom footprint grows beyond Lean's three standard axioms.
-/

public section

namespace NativeVm.Wire

/-- **The wire decoder meets its contract.** -/
theorem decode_ok' : Code.DecodeOk Wire.decode := fun _ _ P hr hm ↦ decode_ok P hr hm

end NativeVm.Wire

/-- info: 'NativeVm.Wire.decode_ok'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeVm.Wire.decode_ok'
