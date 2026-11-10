import Rv64Verifier.Proofs.Transcript.Duplex
import Rv64Verifier.Proofs.Transcript.Absorb
import Rv64Verifier.Proofs.Transcript.NextScalar
import Rv64Verifier.Proofs.Transcript.ShuntNext
import Rv64Verifier.Proofs.Transcript.Samples
import Rv64Verifier.Proofs.Transcript.NextScalars
import Rv64Verifier.Proofs.Transcript.RoundPolySpec
import Rv64Verifier.Proofs.Transcript.Openings
import Rv64Verifier.Proofs.Multilinear.All
import Rv64Verifier.Proofs.Runtime.All
import Rv64Verifier.Proofs.Hash.All

/-!
# The transcript's functions, composed

`duplex`, `absorb`, `next_scalar`, `GenericShunt::next`, `samples`, `next_scalars` and
`sumcheck_round_poly` from the runtime's contracts (`Runtime/All.lean`), `keccak_f`'s
(`Hash/All.lean`), `E`'s product's (`Field/All.lean`) and `concat`'s (`Multilinear/All.lean`), with
no hypothesis.
-/

namespace Rv64Verifier.Transcript
open RiscvZkvm.Rv64 Rv64Verifier.Runtime

theorem duplex : DuplexSpec := Duplex.duplex_spec Runtime.memcpy Runtime.memset Hash.keccakF

theorem absorb : AbsorbSpec := Absorb.absorb_spec duplex

theorem nextScalar : NextScalarSpec := NextScalar.next_scalar_spec absorb

theorem shuntNext : ShuntNextSpec := ShuntNext.shunt_next_spec nextScalar

theorem samples : SamplesSpec :=
  Samples.samples_spec duplex Runtime.tryAllocZeroed Runtime.reserveFresh_80008a10

theorem nextScalars : NextScalarsSpec :=
  NextScalars.next_scalars_spec shuntNext Runtime.alloc_spec Runtime.reserveFresh_80008a10

theorem roundPoly : RoundPolySpec :=
  RoundPoly.round_poly_spec nextScalars nextScalar Runtime.alloc_spec Proofs.Field.mul
    Proofs.Multilinear.concat

/-- `sumcheck_round_poly`'s contract with its `Err`'s discriminant not `-1`
(`PcsContracts.RoundPolyErrSpec`, whose `okTag` is `errNiche`). -/
theorem roundPolyErr : FunSpec Image.code 0x8000c334 RoundPolyPre fun s t ↦
    RoundPolyPost s t ∧
      (vecCap t (s.getReg .x10) = errNiche → t.getMem (s.getReg .x10 + 8) ≠ errNiche) :=
  fun s hpc hpre ↦ by
    obtain ⟨t, hr, h | h⟩ := roundPoly s hpc hpre
    · exact ⟨t, hr, Or.inl ⟨h.1, h.2.1, h.2.2, h.2.2.err⟩⟩
    · exact ⟨t, hr, Or.inr h⟩

end Rv64Verifier.Transcript

/-- info: 'Rv64Verifier.Transcript.shuntNext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Transcript.shuntNext

/-- info: 'Rv64Verifier.Transcript.samples' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Transcript.samples

/-- info: 'Rv64Verifier.Transcript.nextScalars' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Transcript.nextScalars

/-- info: 'Rv64Verifier.Transcript.roundPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Transcript.roundPoly
