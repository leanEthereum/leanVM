/-
  The input of `scripts/decoder-tables`, from the built guest alone: the line `entries: …`
  (`--entries`). `scripts/regen-guest.sh` runs it before `decoder-tables` writes
  `Cost/Decoder/GuestTables.lean`, which `decoder-tables-inputs.lean` imports.
-/
import LeanVM.Guest.Glob

open LeanVM.Guest

#eval IO.println s!"entries: {(List.range nFns).map fun j ↦ (fnOf j).entryPc}"
