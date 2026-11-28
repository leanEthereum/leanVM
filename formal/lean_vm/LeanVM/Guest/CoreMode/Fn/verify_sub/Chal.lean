/-
  LeanVM.Guest.CoreMode.Fn.verify_sub.Chal

  `verify_sub`'s own residuals over the link's challenges (`fn/verify_sub.py`'s `chal_fam`): the packed count's bound,
  which bounds `squeeze_packed`'s promised runs at its call, and the challenges read inside them: `chal·g^c` and
  `chal·g_n·g^c` (`zeta`'s), `1 ≤ c ≤ 113`, and `nu = chal·g_n·g_w·g^89` under `link_terminal`'s arm, in the `8`
  residue runs merged, `⟨chal·g, 1, 0, g_p^8⟩`.
-/

module

public import LeanVM.Guest.CoreMode.CoreRes
public meta import LeanVM.Guest.CoreRef
public import LeanVM.Guest.Data.NameStrings

namespace LeanVM.Guest.CoreMode.Own.verify_sub

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **The packed count's bound** `(v, n)`, `e(v) < n`: `g_p` (value `645`, `link_shape[3]`, `g^p`, `p < 64`, its
`squeeze_packed`'s meaning). -/
def chalBounds : List (ℕ × ℕ) := [(645, 64)]

/-- **The challenges written**: `squeeze_packed`'s `8` residue runs at `chal·g` (`chal` value `10`), merged:
`⟨[10]·g, 1, 0, [645]^8⟩`. -/
def chalRun : CRun := ⟨⟨[(10, 1)], 1⟩, 1, .num 0, .mono ⟨[(645, 8)], 0⟩⟩

/-- **A run of challenges read**: `⟨[10]·M·g^c, 1, lo, m⟩`, `M` one or `g_n = [115]·[412]`, `1 ≤ c`, `c + m ≤ 114`
(`8p ≥ 88 + n + w + d ≥ 113 + n`). -/
def chalRead (q : CRun) : Bool :=
  match q.lo, q.hi with
  | .num _, .num m => (q.base.bases == [(10, 1)] || q.base.bases == [(10, 1), (115, 1), (412, 1)]) &&
      Nat.beq q.stride 1 && Nat.ble 1 q.base.off && Nat.ble (q.base.off + m) 114
  | _, _ => false

/-- `CHUNK_D[19 + j]`, `j < 6`: the chunk count `d` at the pointer width `19 + j`. -/
def nuLens : List ℕ := [6, 6, 7, 7, 8, 9]

/-- `nu = zeta·g_w = chal·g_n·g_w·g^89` as bases: `[10]·[108]·[115]·[412]·[460]`, `g_w = [108]·[460]·g`. -/
def nuBases : List (ℕ × ℕ) := [(10, 1), (108, 1), (115, 1), (412, 1), (460, 1)]

/-- **A run of `nu` read under `link_terminal`'s dispatch** (selector value `2893`, `g_w·g^-19`): `⟨nu, 1, lo, m⟩`,
`nu` the cell `nuBases·g^90`, the arm `j` among the conditions, `m ≤ nuLens[j]` (`88 + n + w + d ≤ 8p`). -/
def nuRead (g : List CCond) (q : CRun) : Bool :=
  match q.lo, q.hi with
  | .num _, .num m => q.base.bases == nuBases && Nat.beq q.base.off 90 && Nat.beq q.stride 1 &&
      g.any fun c => match c with
        | .arm x j => Nat.beq x 2893 && Nat.blt j 6 && Nat.ble m (nuLens.getD j 0)
        | _ => false
  | _, _ => false

/-- **Its residuals over the link's challenges**: the packed count's bound (`chalBounds`), `e(g_p) > k`, `k ≤ 14`, and
a run of challenges read inside the written one, each possibly under branch conditions, `nu`'s under
`link_terminal`'s arm (`nuRead`). -/
def chalFam : CRes → Bool
  | .lt (.val x) (.num n) => chalBounds.contains (x, n)
  | .lt (.num k) (.val v) => Nat.beq v 645 && Nat.ble k 14
  | .subR q r => chalRead q && decide (r = chalRun)
  | .under g (.subR q r) => (chalRead q || nuRead g q) && decide (r = chalRun)
  | .under _ r => chalFam r
  | _ => false

end

end LeanVM.Guest.CoreMode.Own.verify_sub
