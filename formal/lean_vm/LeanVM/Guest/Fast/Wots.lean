module

public import LeanVM.Guest.Fast.LogG
public import LeanVM.Guest.Fast.Numbers
public import LeanVM.Guest.Fast.Common
public import LeanVM.Guest.Fast.SpWotsTables

/-!
# `sp_wots`' codeword's chain starts, as numbers

`sp_wots`' codeword (`B1/Sig/SpWotsT.lean`) has `G` groups of three digits and a last chain, its
dispatches back to back: group `p`'s digit word at the cell `dg + p`, its arm `k < 64` the word's
exponent, and chain `3p + r`'s start in arm `k` at the group's base plus an offset, the same for
every group but the first (whose arms fold the encoding) and the last (one digit). So the starts
are the bases `base` plus two small tables (`first`, `rest`: row `r`, arm `k`) and the last
chain's offset (`spLastOff`, arithmetic):

* `cwCell`: the start's cell off the bases, the tables and the exponent search `logGT`;
* `cwCellA`: the same off arrays and the lanes of `g^k`, built once by the caller (`cwCellA_eq`).
-/

namespace LeanVM.Guest.Fast

open LeanVM.Parameters LeanVM.Core LeanVM.Guest.B1.Sig

@[expose] public section

/-- **Chain `i`'s start cell**, off the bases `base` of the `G + 1` groups, the first digit word's
cell `dg` and the tables. -/
def cwCell (G dg : ℕ) (base : List ℕ) (first rest : List (List ℕ)) (σ : Val) (i : ℕ) : ℕ :=
  let p := i / 3
  let k := logGT (σ (.n (dg + p))) 64
  base.getD p 0 + if p < G then offAt (if p = 0 then first else rest) (i % 3) k else spLastOff k

/-- **Chain `i`'s start cell, off arrays** (`cwCell`): the bases `base`, the tables `first`,
`rest` (`tabA`) and the lanes of `g^k` (`gLanes`), built once by the caller. -/
def cwCellA (lanes : List ℕ) (G dg : ℕ) (base : Array ℕ) (first rest : Array (Array ℕ)) (σ : Val)
    (i : ℕ) : ℕ :=
  let p := i / 3
  let k := logGTWith lanes (σ (.n (dg + p))) 64
  base.getD p 0 + if p < G then offAtA (if p = 0 then first else rest) (i % 3) k else spLastOff k

theorem cwCellA_eq (G dg : ℕ) (base : List ℕ) (first rest : List (List ℕ)) (σ : Val) (i : ℕ) :
    cwCellA gLanes G dg base.toArray (tabA first) (tabA rest) σ i = cwCell G dg base first rest σ i := by
  unfold cwCellA cwCell
  simp only [getD_toArray, logGTWith_gLanes]
  split_ifs <;> simp only [offAtA_tabA]

end
end LeanVM.Guest.Fast
