/-
  LeanVM.Guest.WalkWindows

  The windows `opening_queries`' Merkle walk dispatches on, for the checker's semantic relations
  (`Glob.sem`, `WalkTags.lean`): definitions only, apart from B1's proofs.
-/

module

public import LeanVM.Guest.Core
public import Statement.Field

/-!
# The walk's windows (lean_ethereum.py:798-909, 1308-1344, 1393-1417 at 40f877dc)

A position of shape `(d, cd)` is hinted in `qwN d cd` windows (`qwWin`: offset and width; the
path's six bits at a time, the last the remainder, the cap child bit, the cap parent index).
`WinsAt`, `WinWalk`, `WinWalk2`, `OqMainWins` are the walk's obligations, defined here so that the
check context (`Glob`), and with it the kernel-checked certificates and the decoder's table checks,
do not import B1 (`B1/Bits/QueryWindowsT.lean`, `B1/Opening/WalkDefs.lean` re-export them; their
facts are `B1/Opening/QueriesWalk.lean`'s).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- The path windows of a position: `⌈(d - cd) / 6⌉`. -/
def qwNp (d cd : ℕ) : ℕ := (d - cd + 5) / 6

/-- The windows of a position: the path's, the cap child bit, the cap parent index. -/
def qwN (d cd : ℕ) : ℕ := qwNp d cd + 2

/-- Window `i` of a position: its offset and width. -/
def qwWin (d cd i : ℕ) : ℕ × ℕ :=
  if i = qwNp d cd then (d - cd, 1)
  else if i = qwNp d cd + 1 then (d - cd + 1, cd - 1)
  else if i + 1 = qwNp d cd then (6 * i, d - cd - 6 * i)
  else (6 * i, 6)

/-- The windows at `w` of a position of shape `(d, cd)`: window `i`, if read, is `g^e` with `e`
below `2^width`. -/
def WinsAt (rd : Reader) (d cd : ℕ) (w : E) : Prop :=
  ∀ i < qwN d cd, ∀ v, LoadHolds rd w i v → ∃ e < 2 ^ (qwWin d cd i).2, v = ofK (addressOfIndex e)

/-- **The walk of a deeper loop** from `x` to `N`: the window pointer `t[x·g^c]` of every
iteration still to run names windows. -/
def WinWalk (rd : Reader) (d cd : ℕ) (t x N : E) : Prop :=
  ∀ c : ℕ, (∀ c' ≤ c, x * gen ^ c' ≠ N) →
    ∀ w, LoadHolds rd (t * (x * gen ^ c)) 0 w → WinsAt rd d cd w

/-- **The walk of a level-0 loop** from `x` to `N`: the window pointers `(t·(x·g^c)²)[g^o]`,
`o = odd, odd + 1`, of every iteration still to run name windows. -/
def WinWalk2 (rd : Reader) (d cd odd : ℕ) (t x N : E) : Prop :=
  ∀ c : ℕ, (∀ c' ≤ c, x * gen ^ c' ≠ N) → ∀ o, odd ≤ o → o ≤ odd + 1 →
    ∀ w, LoadHolds rd (t * (x * gen ^ c) * (x * gen ^ c)) o w → WinsAt rd d cd w

/-- **`opening_queries`' obligation** on its window pointers `t` and `N = n_iters_g`: an odd
count's first query's windows, and the loop's walk from `1`. -/
def OqMainWins (rd : Reader) (d cd odd base : ℕ) (t N : E) : Prop :=
  (odd = 1 → ∀ w, LoadHolds rd t 0 w → WinsAt rd d cd w) ∧
    (if base = 1 then WinWalk2 rd d cd odd t 1 N else WinWalk rd d cd t 1 N)

end
end LeanVM.Guest.B1
