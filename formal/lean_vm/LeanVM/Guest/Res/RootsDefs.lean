/-
  LeanVM.Guest.Res.RootsDefs

  The roots' tree's reads (`rootsB`): `da_roots_tree__L{k}`'s leaves inside the blob roots and the
  padding roots.
-/

module

public import LeanVM.Guest.Res.SelDefs
public import LeanVM.Guest.B1.Da.VerifyDefs

/-!
# The roots' tree's reads

`rtRes R N G lo hi S d`: the run `[R]·g^(S·c + d)`, `lo ≤ c < hi`, inside the four runs of stride
`2` (`rtSubs`): the blob roots' two cells, from `[R]` up to `[N]`'s exponent, and the padding
roots', past `[R]·[N]^2` up to `[G]`'s exponent. `rootsB j`: `j` is arm `k` of the roots' tree,
`S·hi ≤ 2^(k+1)`, `d < S`, and `R`, `N`, `G` its parameters' cells, `N` and `G` inside the frame.
-/

namespace LeanVM.Guest.Res

open LeanVM.Guest LeanVM.Guest.Core
open LeanVM.Guest.B2C (cellJ)

@[expose] public section

/-- The blob roots' and the padding roots' two cells, runs of stride `2`. -/
def rtSubs (R N G : ℕ) : List Mode.Rng :=
  [⟨⟨0, 0, [(.fr R, 1)]⟩, .num 0, .ex (.fr N) 0, 2, 0⟩,
    ⟨⟨0, 0, [(.fr R, 1), (.fr N, 2)]⟩, .num 0, .ex (.fr G) 0, 2, 0⟩,
    ⟨⟨0, 0, [(.fr R, 1)]⟩, .num 0, .ex (.fr N) 0, 2, 1⟩,
    ⟨⟨0, 0, [(.fr R, 1), (.fr N, 2)]⟩, .num 0, .ex (.fr G) 0, 2, 1⟩]

/-- The run `[R]·g^(S·c + d)`, `lo ≤ c < hi`, inside `rtSubs`. -/
def rtRes (R N G lo hi S d : ℕ) : Mode.Res :=
  .sub ⟨⟨0, 0, [(.fr R, 1)]⟩, .num lo, .num hi, S, d⟩ (rtSubs R N G)

/-- **A read of the roots' tree's leaves** at function `j`, arm `k` of the tree. -/
noncomputable def rootsB (j : ℕ) : Mode.Res → Bool
  | .sub a bs => match a.lo, a.hi with
    | .num lo, .num hi => inFr j (cellJ j (.n 1)) && inFr j (cellJ j (.n 2)) && decide (a.d < a.S) &&
        (List.range 11).any (fun k ↦ (coreOf j).name == B1.Da.rtName k && decide (a.S * hi ≤ 2 ^ (k + 1))) &&
        decide (Mode.Res.sub a bs = rtRes (cellJ j (.n 0)) (cellJ j (.n 1)) (cellJ j (.n 2)) lo hi a.S a.d)
    | _, _ => false
  | _ => false

end

end LeanVM.Guest.Res
