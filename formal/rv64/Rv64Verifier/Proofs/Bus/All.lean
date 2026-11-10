import Rv64Verifier.Proofs.Bus.Fingerprints
import Rv64Verifier.Proofs.Bus.TableSumcheck
import Rv64Verifier.Proofs.Multilinear.All

/-!
# The bus's contracts, their callees' discharged

`verify_bus_balance::{closure#2}` closed, down to the allocator's and `dot`'s proofs.
`table_sumcheck` and `verify_bus_balance` are stated in `Contracts.lean`; of `table_sumcheck`,
only the loop taking the heights' maximum is proved (`TableSumcheck.lean`).
-/

namespace Rv64Verifier.Proofs.Bus
open Rv64Verifier.Bus Rv64Verifier.Runtime

theorem fingerprints : FingerprintsSpec :=
  Fingerprints.fingerprints_spec alloc_spec Multilinear.dot

end Rv64Verifier.Proofs.Bus

/-! Lean's three axioms, nothing native. -/

/-- info: 'Rv64Verifier.Proofs.Bus.fingerprints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Bus.fingerprints

/-- info: 'Rv64Verifier.Proofs.Bus.TableSumcheck.maxLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Bus.TableSumcheck.maxLoop
