import Rv64Verifier.Proofs.Pcs.Contracts

/-!
# What `verify_stacked_opening`'s proof assumes of callees beyond their contracts

`sumcheck_round_poly`'s `Err` is returned as is: `verify_stacked_opening` returns the word after
the niche (`0x8000b84c`), so its `Ok` (`a0 = -1`) needs that word not to be `-1`. A
`VerifierError`'s tag never is; `RoundPolyPost` does not say so yet.
-/

namespace Rv64Verifier.PcsContracts
open RiscvZkvm.Rv64 Rv64Verifier.Runtime Rv64Verifier.Transcript

/-- `sumcheck_round_poly`'s contract, its `Err`'s tag not `-1`. -/
abbrev RoundPolyErrSpec : Prop := FunSpec Image.code 0x8000c334 RoundPolyPre fun s t ↦
  RoundPolyPost s t ∧ (vecCap t (s.getReg .x10) = errNiche → t.getMem (s.getReg .x10 + 8) ≠ okTag)

end Rv64Verifier.PcsContracts
