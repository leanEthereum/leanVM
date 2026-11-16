/-
  LeanVM.Guest.Res.GkrDefs

  `verify_bus_gkr`'s residual families: its pair loop's reads of the proof stream, the final point
  row's copy, and its layer loop's residuals by offset.
-/

module

public import LeanVM.Guest.Res.FamDefs

/-!
# `verify_bus_gkr`'s residuals

`gkrStB j x`: at the pair loop `verify_bus_gkr_loop0_loop0`, a read `c < 8` words past its record's
cursor (cell `17`) inside the layer loop's stream, read through its header (`[[1]·g^11]`).
`vbgRowB j x`: at `verify_bus_gkr`, the final point row `F = gkr_pts·(n_pairs·g)^40` read up to
`g_bus_mu`'s exponent inside its pairs of cells, `n_pairs`' exponent many, and the two past them.
`lyResB i x`: the layer loop's residuals at offset `i`: reads past the record the pairs end at (cell
`81`, below eight words) and past the last record (cell `100`, below twelve) inside its stream (cell
`11`); at the call of `gkr_rounds__L2` (offset `70`) the reads past its callee's cursor `[[86]·g^4]`,
below eight, and at the call of `gkr_rounds__L1` (offset `83`) past `[[91]·g^4]`, below four; and the
next point row `R = gkr_pts·x^40·g^80` by pairs, its first cell then the rest one index on
(`lyExtRes`). `callInG f as bs ss`: the block `ss` reaches the call `f as bs` past atoms.
-/

namespace LeanVM.Guest.Res

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- The read `c` words past the cursor base `cur`, inside the stream `st·[0, 8192)`. -/
def gkrStRes (cur st : Mode.Base) (c : ℕ) : Mode.Res :=
  .sub ⟨⟨0, c, [(cur, 1)]⟩, .num 0, .num 1, 1, 0⟩ [⟨⟨0, 0, [(st, 1)]⟩, .num 0, .num 8192, 1, 0⟩]

/-- **The pair loop's reads** past its record's cursor inside the layer loop's stream. -/
noncomputable def gkrStB (j : ℕ) : Mode.Res → Bool
  | .sub a bs => (coreOf j).name == name% «verify_bus_gkr_loop0_loop0» && decide (a.q.k < 8) &&
      decide (Mode.Res.sub a bs = gkrStRes (.fr 17) (.hp 1 11) a.q.k)
  | _ => false

/-- The final point row `[27]·[398]^40·g^40`, times `[398]^e` and `g^k`. -/
def vbgRow (e k : ℕ) : Mode.Mono := ⟨0, 40 + k, [(.fr 27, 1), (.fr 398, 40 + e)]⟩

/-- The final point row up to `[8]`'s exponent inside its pairs up to `[398]`'s and the two cells
past them. -/
def vbgRowRes : Mode.Res :=
  .sub ⟨vbgRow 0 0, .num 0, .ex (.fr 8) 0, 1, 0⟩
    [⟨vbgRow 0 0, .num 0, .ex (.fr 398) 0, 2, 0⟩, ⟨vbgRow 0 0, .num 0, .ex (.fr 398) 0, 2, 1⟩,
      ⟨vbgRow 2 0, .num 0, .num 1, 1, 0⟩, ⟨vbgRow 2 1, .num 0, .num 1, 1, 0⟩]

/-- **The final point row's copy to `zeta`**, at `verify_bus_gkr`. -/
noncomputable def vbgRowB (j : ℕ) (x : Mode.Res) : Bool :=
  (coreOf j).name == name% «verify_bus_gkr» && decide (x = vbgRowRes)

/-- The next point row `[7]·[2]^40·g^(80 + k)`. -/
def lyRow (k : ℕ) : Mode.Mono := ⟨0, k, [(.fr 2, 40), (.fr 7, 1)]⟩

/-- The next point row by pairs from cell `d`, up to `[2]`'s exponent and one, inside the same pairs
one index on and its first pair's cell. -/
def lyExtRes (d : ℕ) : Mode.Res :=
  .sub ⟨lyRow 80, .num 0, .ex (.fr 2) 1, 2, d⟩
    [⟨lyRow 40, .num 0, .ex (.fr 2) 0, 2, 42 + d⟩, ⟨lyRow 80, .num 0, .num 1, 2, d⟩]

/-- **The layer loop's residuals at offset `i`.** -/
def lyResB (i : ℕ) (x : Mode.Res) : Bool :=
  match x with
  | .sub a _ =>
    (decide (a.q.k < 8) && decide (x = gkrStRes (.fr 81) (.fr 11) a.q.k)) ||
      (decide (a.q.k < 12) && decide (x = gkrStRes (.fr 100) (.fr 11) a.q.k)) ||
      (i == 70 && decide (a.q.k < 8) && decide (x = gkrStRes (.hp 86 4) (.fr 11) a.q.k)) ||
      (i == 83 && decide (a.q.k < 4) && decide (x = gkrStRes (.hp 91 4) (.fr 11) a.q.k)) ||
      decide (x = lyExtRes 0) || decide (x = lyExtRes 1)
  | _ => false

/-- A block reaching the call `f as bs` past atoms. -/
def callInG (f : String) (as bs : List V) : List Stmt → Bool
  | .atom _ :: ss => callInG f as bs ss
  | .call f' as' bs' :: ss => (f' == f && as' == as && bs' == bs) || callInG f as bs ss
  | _ => false

end

end LeanVM.Guest.Res
