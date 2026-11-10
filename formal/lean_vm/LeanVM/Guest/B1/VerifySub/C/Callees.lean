/-
  LeanVM.Guest.B1.VerifySub.C.Callees

  `verify_sub`'s callees, placed: the pure ones from their meanings, the shapes of the others.
-/

module

public import LeanVM.Guest.B1.VerifySub.C.Flat
public import LeanVM.Guest.B1.Fwd.PureIn
public import LeanVM.Guest.Memory.Uniform
public import LeanVM.Guest.B1.Bits.GPower
public import LeanVM.Guest.B1.Tables.Base
public import LeanVM.Guest.B1.KeccakGkr.Interface
public import LeanVM.Guest.B1.Bits.Tables

/-!
# The callees, placed

`verify_sub` calls its sixteen callees (Template.lean). Here: `g_power_of_word`, loadless and
allocation-free, placed anywhere from its meaning (`gpw_completeAt`, by
`completeAt_of_rel_pureD`), and the shape of `log2_ceil_in_the_exponent`'s placement
(`Log2CompleteAt`). The others are placed by their own families (`verify_keccak`'s by KeccakGkr,
`ring_switch_target`'s by Ring, the bus's and the tables' by Tables and Gkr, `open_stacked`'s by
Whir, the Fs and Bits leaves by theirs).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-! ## Loadless callees -/

theorem gpw_pure : coreProgram.PureIn ["g_power_of_word"] :=
  Tables.pureIn_of_pureInB (by decide +kernel)

/-- **`g_power_of_word`, placed** anywhere, on any words: `g^n` for the word of `n < 64`. -/
theorem gpw_completeAt (κ : ℕ) (Lin : Main.Layout) {n : ℕ} (hn : n < 2 ^ 6) :
    CompleteAtD fs cert κ "g_power_of_word" Lin [eOfNat n] (Returns [gen ^ n]) :=
  completeAt_of_rel_pureD gpw_pure (List.mem_singleton_self _)
    (fun rd _ ↦ (g_power_of_word_holds rd [eOfNat n] [gen ^ n]).2
      (show ∃ m < 2 ^ 6, eOfNat n = eOfNat m ∧ [gen ^ n] = [gen ^ m] from ⟨n, hn, rfl, rfl⟩)) κ

/-! ## The shapes the assembly takes -/

/-- The exponent table's words (`exponent_tables`' one table, `B1.expTableWords`: the squares,
the nibble shares, the rank keys, the groups' sides). -/
noncomputable def expTablesL (sqE : ℕ) : Main.Layout := [(sqE, B1.expTableWords)]

/-- **`log2_ceil_in_the_exponent` (floor `fl`), placed** (`name` its specialization): on `g^N`,
`N < 2^34`, with the exponent table, it returns `g^max fl (log2Ceil N)`. -/
def Log2CompleteAt (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (name : String) (fl : ℕ) :
    Prop :=
  ∀ (N sqE : ℕ), N < 2 ^ 34 → max fl (log2Ceil N) < 34 →
    CompleteAtD fs cert κ name (expTablesL sqE)
      [gen ^ N, ofK (addressOfIndex sqE)] (Returns [gen ^ max fl (log2Ceil N)])

end
end LeanVM.Guest.B1.VerifySub
