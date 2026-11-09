module

public import LeanVM.Guest.Check

/-!
# A function's precondition, as its test reads it

`Located.preTest rd j fp` (`Located/Replay.lean`) decides function `j`'s precondition at the frame
`fp` from what a caller knows of `j` (`glob.sig j`): its entry environment (`env`, through the trie
`envOf env`), its bounds on frame cells (`pre`) and on memory (`mem`); its semantic tuples it does
not test (they carry over from the frame B2 locates, `Located.semHolds_of_args`). `FnPre` holds the
three, the environment as the pairs the trie keeps (`envChecks`: each key of `env` with the value
`envOf env` gives it, the keys it drops left out); `fnPreOf s` is `none` when all three are empty
(the test holds), else `some` of them. The decoder's precondition test
(`Fast/PreTest.lean`) reads them from a table built once (`Fast/PreTable.lean`).
-/

namespace LeanVM.Guest.Fast

open LeanVM.Guest.Exec LeanVM.Guest.Check

@[expose] public section

/-- What function's precondition test reads of it: the entry environment's checked pairs, the
bounds on frame cells and on memory (`Check.Sig`). -/
structure FnPre where
  env : List (ℕ × Sym)
  pre : List (ℕ × ℕ)
  mem : List (ℕ × ℕ × ℕ)
  deriving DecidableEq

/-- The pairs of the entry environment `env` the test checks: each key with the value the trie
`envOf env` gives it (the last one listed), the keys the trie drops left out. -/
noncomputable def envChecks (env : List (ℕ × Sym)) : List (ℕ × Sym) :=
  env.filterMap fun p ↦ ((envOf env).get p.1).map (p.1, ·)

/-- **Function `s`'s precondition, as its test reads it**: `none` when there is nothing to check. -/
noncomputable def fnPreOf (s : Sig) : Option FnPre :=
  bif (envChecks s.env).isEmpty && s.pre.isEmpty && s.mem.isEmpty then none
  else some ⟨envChecks s.env, s.pre, s.mem⟩

end

end LeanVM.Guest.Fast
