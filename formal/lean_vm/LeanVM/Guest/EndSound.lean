/-
  LeanVM.Guest.EndSound

  B2 for the deployed bytecode, from the certificates (`Sound.lean`) and B1's statements about the
  core IR.
-/

module

public import LeanVM.Guest.EndLoc
public import LeanVM.Guest.Sound
public import LeanVM.Guest.VsTabs
public import LeanVM.Guest.B1.Bits.Tables

/-!
# B2, from B1's statements

`b2SoundL_of`: checker K's B2 (`b2_step`, `b2_mainL`) for Hotwire's guest, from

* `VsKapsKnown`: `verify_sub`'s kappas, the `52` entries of the `kaps` it hands
  `check_stack_terminal`, below `g^31` (`certify_stack` and `verify_sub`'s range check of the
  stack's log);
* `VsGmvKnown`: the stack's log `gmv` it hands `check_stack_terminal` is `g^(16 + e)`, `e < 15`
  (`verify_sub`'s range check of `gmv·g^-16`), which `check_stack_terminal` dispatches on, shifted;
* `WalkKnown`: the windowed Merkle walks' cut obligations (`opening_queries`, its loops,
  `level_queries`, `open_stacked`).

`verify_sub`'s window table at `tabs` is proved (`vsTabsKnown_proved`), and `exponent_tables`' return is
the exponent table, with its window section (`expTablesSound`, B1's `exponent_tables_holds`).
-/

namespace LeanVM.Guest.End

@[expose] public section

/-- **`exponent_tables`' relation is the exponent tables** (B1's `exponent_tables_holds`). -/
theorem expTablesSound : ExpTablesSound := fun rd q h ↦
  (B1.exponent_tables_holds rd [] [q]).mp h

/-- **B2, proved**, given `verify_sub`'s kappas and stack log and the walks' obligations. -/
theorem b2SoundL_of (hkaps : VsKapsKnown) (hgmv : VsGmvKnown) (hwalk : WalkKnown) : B2SoundL :=
  ⟨b2_step fun _ h2 hj ↦ cutsKnown_of hkaps hgmv vsTabsKnown_proved hwalk h2 hj, b2_mainL expTablesSound⟩

end
end LeanVM.Guest.End
