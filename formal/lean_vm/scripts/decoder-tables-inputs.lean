/-
  The inputs of `scripts/decoder-tables` and `scripts/decoder-table-chunks`, from the built modules:
  one line each, `entries: …` (`--entries`) and `rows: …` (`--row-lengths`). Run from lean_vm
  after `lake build`: `lake env lean scripts/decoder-tables-inputs.lean` (`regen-guest.sh` splits
  the lines and runs both scripts, with `--check` in the gate).
-/
import LeanVM.Cost.Decoder.GuestTables
import LeanVM.Guest.Glob

open LeanVM.Guest LeanVM.Cost.Decoder

#eval IO.println s!"entries: {(List.range nFns).map fun j ↦ (fnOf j).entryPc}"
#eval IO.println s!"rows: {guestLocsList.map List.length}"
