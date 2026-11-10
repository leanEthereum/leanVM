import Rv64Verifier.Proofs.Pcs.VsoRows0
import Rv64Verifier.Proofs.Runtime.All
import Rv64Verifier.Proofs.Field.All

/-!
# Level 0's rows, closed

`rowsZero` with its callees' proved contracts: `try_allocate_in` (`Runtime.tryAllocZeroed`),
`Vec<E>::reserve` (`Runtime.reserveFast_80008a10`), `<E as Mul<K>>::mul` (`Field.mulK`).
-/

namespace Rv64Verifier.Proofs.Pcs

/-- **Level `0`'s rows**, closed. -/
theorem rowsZeroProved : Vso.RowsZero :=
  Vso.rowsZero Runtime.tryAllocZeroed Runtime.reserveFast_80008a10 Field.mulK

end Rv64Verifier.Proofs.Pcs

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.rowsZero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.rowsZero

/-- info: 'Rv64Verifier.Proofs.Pcs.rowsZeroProved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.rowsZeroProved
