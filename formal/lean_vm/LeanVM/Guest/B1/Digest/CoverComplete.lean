/-
  LeanVM.Guest.B1.Digest.CoverComplete

  A coverage slot's bound: `g^n · g⁻¹ = g^(n-1)`.
-/

module

public import LeanVM.Guest.B1.Digest.CompleteSmall

/-!
# A coverage slot's bound

A slot `i` is range-checked against `g^n` by reads at `g^i` and `g^(n-1-i)`; `gen_pow_mul_ginv`
gives the second's exponent.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem gen_pow_mul_ginv {n : ℕ} (hn : 1 ≤ n) : gen ^ n * ginvW = gen ^ (n - 1) := by
  conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ, mul_assoc, mul_comm gen, ginvW_mul_gen,
    mul_one]

end
end LeanVM.Guest.B1.Digest
