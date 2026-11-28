/-
  LeanVM.Guest.B1.KeccakGkr.Section

  `verify_sub`'s section `KECCAK validity, by GKR over the rounds`: the statement of its soundness.
-/

module

public import LeanVM.Guest.B1.Common.Run
public import LeanVM.Guest.ExpTables
public import LeanVM.Guest.CoreData

/-!
# The Keccak reduction in the circuit: the interface

`verify_sub` calls, at the section `KECCAK validity, by GKR over the rounds`,

    verify_keccak(fs0, fs1, fs2, fs3, fs4, cursor, h5, chi, sent * GEN ** SENT_OUT_LANES, z_vals, kslices, tabs)

with `h5 = g^τ` the `KECCAK` table's height (`9 ≤ τ ≤ 24`: the table's floor `keccakMinStepsLog`,
and `τ < N_ROW_LOGS`, which the shape section asserts), `chi` the link's row point, the output lanes
the `25` values the link sent from `SENT_OUT_LANES`, `z_vals` and `kslices` the buffers the stacked
opening reads, `tabs` the window table.

`MeaningVerifyKeccak rd args rets` is what such a call means: from the carried capacity, the stream
words `xs` at the cursor run `verifyKeccak τ (chis.take τ) outs` (`RunsTo`, `Common/Run.lean`), the
Statement's reduction (`Statement/Verifier/Keccak.lean`, which `keccakValidity` calls), to the
committed outputs' claim `⟨qkeccak, op, word⟩` and the input opening's point and slices, leaving a
sponge `s'` whose queue is full (the last four slices); `op` is at `z_vals`, the point at
`z_vals·g^QKECCAK_VARS_CAP`, the slices at `kslices`; the call returns the capacity after that
queue's permutation (the next grind's `absorb` makes it), the cursor past `xs`, and `word`.

`KeccakSectionSound rd`: every run of `verify_keccak`'s core relation on the reader `rd` has that
meaning. Its proof (`keccak_section_sound`, on a memory image) is the section's B1; `verify_sub`'s
soundness chains it with the phases before and after, as the archive's `VerifySub/Accept.lean` did
(`RunsTo.bind`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- `QKECCAK_VARS_CAP`: the two opening points of `verify_keccak` are `39` words apart. -/
abbrev qkeccakVarsCap : ℕ := 39

/-- The least `KECCAK` table log-height: its floor (`FLOORS[TABLE_KECCAK] = keccakMinStepsLog`). -/
abbrev keccakTauMin : ℕ := 9

/-- The largest `KECCAK` table log-height: `τ < N_ROW_LOGS = 25`. -/
abbrev keccakTauMax : ℕ := 24

/-- **`verify_keccak(fs0..fs4, cursor, tau_g, chi, output_lanes, z_vals, slices, tabs)`**: on the
window table `tabs` (`WinTabs`, which the layers' grinds read), for the `KECCAK` table's log-height
`τ` (`tau_g = g^τ`, `9 ≤ τ ≤ 24`), the link's point `chis` at `chi` (at least `τ` coordinates) and
the twenty-five output lane values `outs` at `output_lanes`: from the carried capacity, the stream
words `xs` at the cursor run `verifyKeccak τ (chis.take τ) outs` to the committed outputs' claim
`⟨qkeccak, op, word⟩` and the input opening's point and slices, leaving the sponge `s'` with a
full queue; `op` is at `z_vals`, the point at `z_vals·g^39`, the slices at `slices`; the function
returns the capacity after that queue's permutation, the cursor past `xs`, and `word`. -/
def MeaningVerifyKeccak (rd : Reader) : List E → List E → Prop
  | [f0, f1, f2, f3, f4, cur, tg, chi, ol, zv, sl, tabs], rets =>
      WinTabs rd tabs → ∀ (τ : ℕ) (chis outs : List E), keccakTauMin ≤ τ → τ ≤ keccakTauMax →
        tg = gen ^ τ → τ ≤ chis.length → ReadsAt rd chi chis → outs.length = 25 →
        ReadsAt rd ol outs →
        ∃ (xs op point slices : List E) (word : E) (s' : Fs), ReadsAt rd cur xs ∧
          RunsTo (verifyKeccak τ (chis.take τ) outs) ⟨[f0, f1, f2, f3, f4], []⟩ xs
            ([⟨qkeccak, op, word⟩], point, slices) s' ∧ s'.pend.length = rateScalars ∧
          ReadsAt rd zv op ∧ ReadsAt rd (zv * gen ^ qkeccakVarsCap) point ∧ ReadsAt rd sl slices ∧
          op.length = τ + qkeccakSlotBits ∧ point.length = τ + qkeccakSlotBits ∧
          slices.length = 64 ∧ rets = capOf s'.perm ++ [cur * gen ^ xs.length, word]
  | _, _ => False

/-- **The section's soundness on the reader `rd`**: every run of `verify_keccak`'s core relation
has its meaning. Proved on a memory image (`keccak_section_sound`), where `grind_check` has its
meaning. -/
def KeccakSectionSound (rd : Reader) : Prop :=
  ∀ (args rets : List E), coreProgram.Rel rd "verify_keccak" args rets → MeaningVerifyKeccak rd args rets

end
end LeanVM.Guest.B1.VerifySub
