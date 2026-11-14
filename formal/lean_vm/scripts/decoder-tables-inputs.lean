/-
  The inputs of `scripts/decoder-tables` and `scripts/decoder-table-chunks`, from the built modules:
  one line each, `entries: …` (`--entries`), `rows: …` (`--row-lengths`) and `split: …`
  (`--split-lengths`). Run from lean_vm after `lake build`: `lake env lean
  scripts/decoder-tables-inputs.lean` (`check-all.sh` and the CI split the lines and run both
  scripts' `--check`).
-/
import LeanVM.Cost.Decoder.GuestTables
import LeanVM.Guest.Glob

open LeanVM.Guest LeanVM.Cost.Decoder

#eval IO.println s!"entries: {(List.range nFns).map fun j ↦ (fnOf j).entryPc}"
#eval IO.println s!"rows: {guestLocsList.map List.length}"
#eval IO.println s!"split: {guestLocsSplit.map List.length}"
