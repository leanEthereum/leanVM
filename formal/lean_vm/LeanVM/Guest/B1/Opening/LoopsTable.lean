/-
  LeanVM.Guest.B1.Opening.LoopsTable

  Every deployed shape of `opening_queries` has its loop helper in `openingQueriesLoops`.
-/

module

public import LeanVM.Guest.B1.Opening.Witness

/-!
# The loop helpers' table

`openingQueriesLoops` (`Witness.lean`) holds `(name, loop, shape)` for every deployed
specialization, and `openingQueriesLoops_shapes` (by `rfl`) says its names and shapes are
`openingQueriesShapes`'.
-/
