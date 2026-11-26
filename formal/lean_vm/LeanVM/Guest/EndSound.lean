/-
  LeanVM.Guest.EndSound

  B2 for the deployed bytecode, from the certificates (`Sound.lean`), B1's statements about the
  core IR and the walks' cut obligations.
-/

module

public import LeanVM.Guest.EndKnow
public import LeanVM.Guest.Sound
public import LeanVM.Guest.B1.Bits.Tables
public import LeanVM.Guest.B1.VerifySub.Sound
public import LeanVM.Guest.B1.VerifySub.KnownAll
public import LeanVM.Guest.VsTabs
public import LeanVM.Guest.WalkKnownAll

/-!
# B2, proved, and the end theorems from B1's statements

* `expTablesSound`: `exponent_tables`' returns are the exponent tables (B1-a's
  `exponent_tables_holds`).
* `vsDimsKnown_proved`: `verify_sub`'s `dims_g[g^0]` below `g^34`, an arm `verify_tables`
  dispatches on (B1-d's `VerifySub.vsDimsKnown0_holds`).
* `vsKnown_proved`: `verify_sub`'s `kappa_base` entries below `vsKbBound`, the arms
  `check_opening_terminal` dispatches on (B1-d's `VerifySub.vsKnown_holds`), and the window table
  it hands `open_stacked` (`vsTabsKnown_proved`, `VsTabs.lean`).
* `EndPending`, `endPending_proved`: the walks' cut obligations (`WalkKnown`; `walkKnown_proved`,
  `WalkKnownAll.lean`: whir's `QueriesWalk` and ostack's `oqMainWins_of_queryWinsOk` through the
  certificates' cells, and the GKR layers' parities); `verify_sub`'s statement is
  `VerifySub.verify_sub_sound_w`.
* `b2SoundL_of`, `b2SoundL`: checker K's B2 (`b2_step`, `b2_mainL`), `b2SoundL` from
  `EndPending`.
-/

namespace LeanVM.Guest.End

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Node LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash

@[expose] public section

/-- **`exponent_tables`' relation is the exponent tables** (B1-a's `exponent_tables_holds`). -/
theorem expTablesSound : ExpTablesSound := fun rd q h ↦
  (exponent_tables_holds rd [] [q]).mp h

/-- **`verify_sub`'s `kappa_base`** below `vsKbBound` (B1-d's `VerifySub.vsKnown_holds`;
`coreOf (fn_idx% «verify_sub»)` is `fn% «verify_sub»`), and its window table at `tabs`. -/
theorem vsKnown_proved : VsKnown :=
  ⟨fun L h16 h32 σ hexp h ↦ VerifySub.vsKnown_holds L h16 h32 σ hexp h, vsTabsKnown_proved⟩

/-- **`verify_sub`'s `dims_g[g^0]`** below `g^34`, an arm `verify_tables` dispatches on (B1-d's
`VerifySub.vsDimsKnown0_holds`). -/
theorem vsDimsKnown_proved : VsDimsKnown := fun L h16 h32 σ h ↦
  VerifySub.vsDimsKnown0_holds L h16 h32 σ h

/-- **The walks' cut obligations**, what B2 takes beyond `verify_sub`'s. -/
structure EndPending : Prop where
  /-- The walks' cut obligations. -/
  walk : WalkKnown

/-- **The walks' cut obligations hold** (`walkKnown_proved`). -/
theorem endPending_proved : EndPending := ⟨walkKnown_proved⟩

/-- **B2, proved**, given `verify_sub`'s `dims_g` and `kappa_base` bounds and the walks'
obligations. -/
theorem b2SoundL_of (hvd : VsDimsKnown) (hvs : VsKnown) (hwalk : WalkKnown) : B2SoundL :=
  ⟨b2_step fun _ h2 hj ↦ cutsKnown_of hvd hvs hwalk h2 hj, b2_mainL expTablesSound⟩

/-- **B2, proved**, given `verify_sub`'s obligations. -/
theorem b2SoundL (h : EndPending) : B2SoundL := b2SoundL_of vsDimsKnown_proved vsKnown_proved h.walk

variable {piOf : Reader → Val → FrameMap → Protocol.Compile.Proof}

end
end LeanVM.Guest.End
