/-
  LeanVM.Guest.B1.Whir.CPtrs

  The pointers of open_stacked's own buffers, in allocation order.
-/

module

public import LeanVM.Guest.B1.Whir.Template

/-!
# The body's buffers' pointers

`OsAt`: a pointer for each `HeapBuf` the body allocates: the head's thirteen fixed buffers, each
level's message `sent` (non-final) and squeeze run, the final level's normalized lane,
`tail_challenges`, `point`, `point1`, `basis_d`, `level_scale`, `level_after`, `inner_chain`, and
each non-final level's residual chain. `osPtrL c A`: them in allocation order, entry for entry
with Place/OsBos's `osSizesF c`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

/-- The pointers of the body's own buffers. -/
structure OsAt where
  /-- The head's thirteen fixed buffers, in allocation order (`osCaps`, `osFlags`, … `osQbp`). -/
  P : List E
  /-- A non-final level's message. -/
  sent : ℕ → E
  /-- A level's squeeze run. -/
  sqz : ℕ → E
  /-- The final level's normalized lane. -/
  hsF : E
  tch : E
  pt : E
  pt1 : E
  bd : E
  ls : E
  la : E
  ich : E
  /-- A non-final level's residual chain. -/
  rc : ℕ → E

/-- **The pointers in allocation order.** -/
def osPtrL (c : OsCfg) (A : OsAt) : List E :=
  A.P ++
  (List.range c.levels.length).flatMap (fun i ↦
    (if i = c.yrLevel then [] else [A.sent i]) ++ [A.sqz i] ++ (if i = c.yrLevel then [A.hsF] else [])) ++
  [A.tch, A.pt, A.pt1, A.bd, A.ls, A.la, A.ich] ++
  (List.range c.yrLevel).map A.rc

end
end LeanVM.Guest.B1.Whir
