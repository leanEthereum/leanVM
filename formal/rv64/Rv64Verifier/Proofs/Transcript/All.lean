import Rv64Verifier.Proofs.Transcript.Duplex
import Rv64Verifier.Proofs.Transcript.Absorb
import Rv64Verifier.Proofs.Transcript.NextScalar
import Rv64Verifier.Proofs.Transcript.ShuntNext
import Rv64Verifier.Proofs.Transcript.Samples
import Rv64Verifier.Proofs.Transcript.NextScalars
import Rv64Verifier.Proofs.Runtime.All
import Rv64Verifier.Proofs.Hash.All

/-!
# The transcript's functions, composed

`duplex`, `absorb`, `next_scalar`, `GenericShunt::next` `samples` and `next_scalars` from the runtime's contracts
(`Runtime/All.lean`) and `keccak_f`'s (`Hash/All.lean`), with no hypothesis.
-/

namespace Rv64Verifier.Transcript

theorem duplex : DuplexSpec := Duplex.duplex_spec Runtime.memcpy Runtime.memset Hash.keccakF

theorem absorb : AbsorbSpec := Absorb.absorb_spec duplex

theorem nextScalar : NextScalarSpec := NextScalar.next_scalar_spec absorb

theorem shuntNext : ShuntNextSpec := ShuntNext.shunt_next_spec nextScalar

theorem samples : SamplesSpec :=
  Samples.samples_spec duplex Runtime.tryAllocZeroed Runtime.reserveFresh_80008a10

theorem nextScalars : NextScalarsSpec :=
  NextScalars.next_scalars_spec shuntNext Runtime.alloc_spec Runtime.reserveFresh_80008a10

end Rv64Verifier.Transcript

/-- info: 'Rv64Verifier.Transcript.shuntNext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Transcript.shuntNext

/-- info: 'Rv64Verifier.Transcript.samples' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Transcript.samples

/-- info: 'Rv64Verifier.Transcript.nextScalars' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Transcript.nextScalars
