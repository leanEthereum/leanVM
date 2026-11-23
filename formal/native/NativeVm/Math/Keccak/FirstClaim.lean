module

public import NativeVm.Math.Keccak.Facts

/-!
# The first Keccak claim's weights and value
-/

@[expose] public section

namespace NativeVm.Math.Keccak

open NativeVm.Model LeanVM.Parameters LeanVM.Protocol.Verifier

/-- The first claim's weight of bit position `j`. -/
def bitW (lanes : Array EW) (j : Nat) : EW :=
  lanes.getD (j / 64) 0 * EW.ofK ((1 : UInt64) <<< (j % 64).toUInt64)

theorem kfc_weights (inst segment lanePoint output : Array EW) (committed : EW) :
    (keccakFirstClaim inst segment lanePoint output committed).weights =
      (Array.range keccakBits).map (bitW (eqKernel lanePoint)) := (rfl)

theorem kfc_value (inst segment lanePoint output : Array EW) (committed : EW) :
    (keccakFirstClaim inst segment lanePoint output committed).value = committed +
      (eqKernel segment).getD (keccakSegments - 1) 0 *
        dot ((eqKernel lanePoint).extract 0 25) output := (rfl)

end NativeVm.Math.Keccak
