/-!
# Tests: the runs, compiled

A check too slow for the interpreter is a run: `test_runs X := [(name, fun _ ↦ check), …]` in its
test module defines `X`, which `cli/TestRuns.lean` lists, and `lake exe test-runs` evaluates it
compiled (check-all runs it after the build). Each run is evaluated when called, not when the
executable starts (`compiler.extract_closed`), so the executable times it and can run one alone.
A module importing `LeanVM.Facts.Guest` (as `LeanVM.Cost.Decoder.*` do) keeps its checks as
`#guard`s: the executable's start would evaluate the guest's bytecode words.
-/

namespace LeanVMTests

/-- A test module's runs: each a name and its check. -/
abbrev Runs := List (String × (Unit → Bool))

/-- `test_runs X := [(name, fun _ ↦ check), …]` defines the runs `X : Runs`. -/
macro doc?:(docComment)? "test_runs " n:ident " := " v:term : command =>
  `(set_option compiler.extract_closed false in $[$doc?]? def $n : LeanVMTests.Runs := $v)

end LeanVMTests
