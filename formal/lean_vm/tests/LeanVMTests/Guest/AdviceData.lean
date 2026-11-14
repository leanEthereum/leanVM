import LeanVM.Prover.Advice
import LeanVM.Guest.Data.Advice
import LeanVM.Guest.Data.AdviceHints
import LeanVM.Guest.Mode.Hints

/-!
# The guest's advice text against its data

`scripts/guest-export` writes the guest's advice twice: as the text the executor parses
(`Data.adviceText`, `parseAdvice`) and as data (`Data.AdviceHints`), which the mode walk's
certificates' hints are proved to be (`Mode.HintsOk`). The text parses to the data.
-/

open LeanVM.Guest.Data

#guard match LeanVM.Prover.parseAdvice adviceText with
  | .ok a => a.mainFrame = adviceMainFrame && decide (a.hints = adviceHints) && a.streams.isEmpty
  | .error _ => false
