import Rv64Verifier.Proofs.Pcs.VsoRowsD5
import Rv64Verifier.Proofs.Runtime.All
import Rv64Verifier.Proofs.Multilinear.All

/-!
# A deeper level's rows, closed

`RowsDeep` (`VsoRowed.lean`) from the proved contracts of `try_allocate_in`, `reserve` and `dot`.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso

/-- **A deeper level's rows**: from `0x8000b158` to `0x8000b42c` (`Rowed`), or a failure. -/
theorem rowsDeep : RowsDeep :=
  RowsD.rowsDeepOf Rv64Verifier.Runtime.tryAllocZeroed Rv64Verifier.Runtime.reserveFast_80008a10
    Rv64Verifier.Proofs.Multilinear.dot

end Rv64Verifier.Proofs.Pcs.Vso

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.rowsDeep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.rowsDeep
