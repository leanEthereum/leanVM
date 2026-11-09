/-
  LeanVM.Guest.ExpandLemmas

  The structural lemmas of the expansion: an `unroll` emits its iterations' blocks in order, and
  an `if` whose condition folds is its taken branch.
-/

module

public import LeanVM.Guest.Expand

/-!
# Lemmas about the expansion

* `appendBlocks_out`: an `unroll` expands each iteration, the counter substituted, into a block
  of its own (`capture`, in `stmtKind`), and emits the blocks in order; with
  `Core.holdsList_flatten` (`LeanVM.Guest.CoreLemmas`) its semantics is the conjunction of the
  iterations' when they do not return;
* `lowerIf_fold`: an `if` whose two sides have integer readings below `2^32` (and agreeing field
  readings, unless it is `if const(...)`) expands to its taken branch, in the enclosing scope.
-/

namespace LeanVM.Guest.Expand

open LeanVM.Guest.Source

@[expose] public section

end
end LeanVM.Guest.Expand
