import Rv64Verifier.Proofs.Transcript.Duplex
import Rv64Verifier.Proofs.Transcript.Absorb
import Rv64Verifier.Proofs.Transcript.NextScalar
import Rv64Verifier.Proofs.Transcript.ShuntNext
import Rv64Verifier.Proofs.Runtime.All

/-!
# The transcript's functions, composed

`duplex`, `absorb`, `next_scalar` and `GenericShunt::next` from the contracts of `memcpy` (the
runtime proves it only for co-aligned ranges, which `duplex`'s are) and `keccak_f`
(`Proofs/Hash/`); `memset`'s is the runtime's.
-/

namespace Rv64Verifier.Transcript

theorem duplex (hMC : Runtime.MemcpySpec 0x800126e4) (hK : Contracts.KeccakFSpec) : DuplexSpec :=
  Duplex.duplex_spec hMC Runtime.memset hK

theorem absorb (hMC : Runtime.MemcpySpec 0x800126e4) (hK : Contracts.KeccakFSpec) : AbsorbSpec :=
  Absorb.absorb_spec (duplex hMC hK)

theorem nextScalar (hMC : Runtime.MemcpySpec 0x800126e4) (hK : Contracts.KeccakFSpec) :
    NextScalarSpec :=
  NextScalar.next_scalar_spec (absorb hMC hK)

theorem shuntNext (hMC : Runtime.MemcpySpec 0x800126e4) (hK : Contracts.KeccakFSpec) :
    ShuntNextSpec :=
  ShuntNext.shunt_next_spec (nextScalar hMC hK)

end Rv64Verifier.Transcript

/-- info: 'Rv64Verifier.Transcript.shuntNext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Transcript.shuntNext
