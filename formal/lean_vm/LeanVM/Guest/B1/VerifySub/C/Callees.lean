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

`verify_sub` calls (in order, `vs_calls`): `g_power_of_word` twice, `log2_ceil_in_the_exponent`
(floors `0` and `15`), `assert_canonical` twice, `verify_bus_gkr`, `verify_tables`,
`verify_keccak`, `ring_switch_target`, `certify_placement`, `open_stacked` (dispatched on the
candidate) and `check_opening_terminal`.

* Loadless and allocation-free (`assert_canonical`, `g_power_of_word`): placed anywhere from their
  meanings (`gpw_completeAt`, `ac_completeAt`, by `completeAt_of_rel_pureD`).
* Proved elsewhere, placed: `verify_bus_gkr_completeAt`, `verify_tables_completeAt`,
  `certify_placement_completeAt` (B1-c), `open_stacked_completeAtD` (B1-b),
  `rst_completeAt` (`ring_switch_target`, fork B1-d-c3).
* Shapes the assembly takes as hypotheses until they are proved:
  `Log2CompleteAt` (`log2_ceil_in_the_exponent`, which allocates its bit and prefix runs: owned by
  B1-a), `VkCompleteAt` (`verify_keccak`, fork B1-d-c1), `RstCompleteAt` (as `rst_completeAt`
  states it). The terminal's is fork B1-d-c3's to state.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-! ## Loadless callees -/

theorem gpw_pure : coreProgram.PureIn ["g_power_of_word"] :=
  Tables.pureIn_of_pureInB (by decide +kernel)

theorem ac_pure : coreProgram.PureIn ["assert_canonical"] :=
  Tables.pureIn_of_pureInB (by decide +kernel)

/-- **`g_power_of_word`, placed** anywhere, on any words: `g^n` for the word of `n < 64`. -/
theorem gpw_completeAt (κ : ℕ) (Lin : Main.Layout) {n : ℕ} (hn : n < 2 ^ 6) :
    CompleteAtD fs cert κ "g_power_of_word" Lin [eOfNat n] (Returns [gen ^ n]) :=
  completeAt_of_rel_pureD gpw_pure (List.mem_singleton_self _)
    (fun rd _ ↦ (g_power_of_word_holds rd [eOfNat n] [gen ^ n]).2
      (show ∃ m < 2 ^ 6, eOfNat n = eOfNat m ∧ [gen ^ n] = [gen ^ m] from ⟨n, hn, rfl, rfl⟩)) κ

/-- **`assert_canonical`, placed** anywhere, on a canonical cell. -/
theorem ac_completeAt (κ : ℕ) (Lin : Main.Layout) {w : E} (hw : IsCanonical128 w) :
    CompleteAtD fs cert κ "assert_canonical" Lin [w] (Returns [0]) :=
  completeAt_of_rel_pureD ac_pure (List.mem_singleton_self _)
    (fun rd _ ↦ (assert_canonical_holds rd [w] [0]).2
      (show IsCanonical128 w ∧ [(0 : E)] = [0] from ⟨hw, rfl⟩)) κ

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

/-- **`verify_keccak`, placed**: from a carried canonical capacity `f`, on the transcript words `xs`
at the cursor, the table sumcheck's point `chis` (at least `τ` of them) at `chi`, the output lanes'
values `outs` at `ol`, the honest run of `keccakSeg τ (chis.take τ) outs` returning the committed
outputs' opening `op`, the inputs' point `point`, the slices and the ring map's first challenge, it
writes `op` at `zv`, `point` at `zv·g^39`, the slices at `sl`, and returns the capacity after, the
cursor past `xs`, the word and the challenge. -/
def VkCompleteAt (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) : Prop :=
  ∀ (τ : ℕ) (f chis outs xs op point slices cap' : List E) (word m0 : E)
    (curE chiE olE zvE slE : ℕ), 9 ≤ τ → τ ≤ 28 → τ ≤ chis.length → outs.length = 25 →
    f.length = 5 → AllCanonical f → (∃ sp, (⟨f, []⟩ : Fs).Carries sp) →
    RunsTo (keccakSeg τ (chis.take τ) outs) ⟨f, []⟩ xs
      (([⟨qkeccak, op, word⟩], point, slices), m0) ⟨cap', []⟩ →
    CompleteAtD fs cert κ "verify_keccak"
      [(curE, xs), (chiE, chis), (olE, outs), (zvE, op), (zvE + qkeccakVarsCap, point),
        (slE, slices)]
      (f ++ [ofK (addressOfIndex curE), gen ^ τ, ofK (addressOfIndex chiE), ofK (addressOfIndex
          olE), ofK (addressOfIndex zvE),
        ofK (addressOfIndex slE)])
      (Returns (cap' ++ [ofK (addressOfIndex curE) * gen ^ xs.length, word, m0]))

/-- **`ring_switch_target`, placed** (as fork B1-d-c3's `rst_completeAt` states it). -/
def RstCompleteAt (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) : Prop :=
  ∀ (bs bm : ℕ) (s chs : List E), s.length = 64 → chs.length = 6 →
    CompleteAtD fs cert κ "ring_switch_target" [(bs, s), (bm, chs)]
      [ofK (addressOfIndex bs), ofK (addressOfIndex bm)] (Returns [polyEval (s.map
          (phiMap · chs)) gen])

end
end LeanVM.Guest.B1.VerifySub
