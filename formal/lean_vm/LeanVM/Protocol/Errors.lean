/-
  LeanVM.Protocol.Errors

  The cost of building Keccak-256 and Keccak-f[1600] from one random permutation.
-/

module

public import Mathlib.Basic.ENNReal.Inv

/-!
# The random-permutation transfer's error

With Keccak-256 and Keccak-f[1600] two independent random functions, a proof bounds an event of a
verifier; building both functions from one random permutation costs `rpmError q` more, `q` the
experiment's permutation calls (`Common.keccak256_transfer2`, `LeanVM.Rpm.detRun_le_rom`). The
bus era's errors of leanVM's knowledge soundness and completeness (`verifierQueries`,
`completenessError`, …) are archived at tag `formal-bus-archive`.
-/

namespace LeanVM

open scoped ENNReal

@[expose] public section

/-- The cost of building Keccak-256 and Keccak-f[1600] from one random permutation rather than
taking them independent random functions, for an experiment of `q` permutation calls:
`q² / 2^508` (`Common.keccak256_transfer2`). -/
noncomputable def rpmError (q : ℕ) : ℝ≥0∞ := (q ^ 2 : ℝ≥0∞) / 2 ^ 508

end
end LeanVM
