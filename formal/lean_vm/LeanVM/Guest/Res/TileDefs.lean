/-
  LeanVM.Guest.Res.TileDefs

  The tile families of the `sub` residuals: a run cut into parts whose exponents add up to its
  bound, a run one point past another, offsets modulo `g`'s order, and a run past a lift's shift.
-/

module

public import LeanVM.Guest.Res.FamDefs
public import LeanVM.Guest.Res.ExpDefs

/-!
# Tiles

`tileRes Q n S d ps`: the run `⟨Q, 0, [n], S, d⟩` inside its parts, `ps = [(x_0, m_0), …]`: part `k`
is `m_k` runs of stride `S·m_k` up to `[x_k]`'s exponent over `Q·x_0^(S·m_0)···x_{k-1}^(S·m_{k-1})`,
the `t`-th from `d + S·t`. It holds where `[n]`'s exponent is `Σ m_k·e(x_k)`, or `0`.
`mulTileB`: two parts of one run each, `[p] = [x]·[y]` a top-level `MUL`, `[x]` and `[y]` powers of
`g` (`cellPow`: bounded, or touched). `tileListB`: a tile of `tiles`, its sum proved at the honest
frames (`EndExec.TileAt`).
`extB`: `⟨Q, 0, [n] + 1, S, d⟩` inside `⟨Q, 0, [n], S, d⟩` and the point `Q·[n]^S·g^d`.
`ordB`: runs between constants over one product, offsets compared modulo `g`'s order `2^64 - 1`.
`ordShiftB`: a run named one index up, its offset `S` down modulo the order.
`liftBack u v k`: `⟨P, k, [v], 1, 0⟩` inside `⟨P·g^k, 0, [u], 1, 0⟩`, `[v] = g^k·[u]` a lift's.
-/

namespace LeanVM.Guest.Res

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B2C (cellJ fsN)

@[expose] public section

/-- The order of `g`. -/
abbrev ordG : ℕ := 2 ^ 64 - 1

/-! ## Tiles -/

/-- A tile's parts over `Q`: part `(x, m)`'s runs, then the parts past `x^(S·m)`. -/
def tileParts (S d : ℕ) : Mode.Mono → List (Mode.Base × ℕ) → List Mode.Rng
  | _, [] => []
  | Q, (x, m) :: ps => (List.range m).map (fun t ↦ ⟨Q, .num 0, .ex x 0, S * m, d + S * t⟩) ++
      tileParts S d ⟨Q.fp, Q.k, Mode.insertBs (x, S * m) Q.bs⟩ ps

/-- The run up to `[n]`'s exponent inside its parts. -/
def tileRes (Q : Mode.Mono) (n : Mode.Base) (S d : ℕ) (ps : List (Mode.Base × ℕ)) : Mode.Res :=
  .sub ⟨Q, .num 0, .ex n 0, S, d⟩ (tileParts S d Q ps)

/-- A residual is the tile of `[n]` into the parts `ps`. -/
def tileShape (n : Mode.Base) (ps : List (Mode.Base × ℕ)) : Mode.Res → Bool
  | .sub a bs => decide (Mode.Res.sub a bs = tileRes a.q n a.S a.d ps)
  | _ => false

/-- **Cell `o` of function `j` holds a power of `g`**: bounded (`cellLt`), or touched by a top-level
atom. -/
noncomputable def cellPow (j : ℕ) (w : Wit) (o : ℕ) : Bool :=
  cellLt j w o (2 ^ 33) || (inFr j o && w.as.any fun
    | .touch _ p => cellJ j p == o
    | _ => false)

/-- A top-level `MUL` of the witness: `[p] = [x]·[y]`, the product inside the frame. -/
noncomputable def mulCells (j : ℕ) (w : Wit) (p x y : ℕ) : Bool :=
  w.as.any fun
    | .mul P X Y => inFr j (cellJ j P) && cellJ j P == p &&
        ((cellJ j X == x && cellJ j Y == y) || (cellJ j X == y && cellJ j Y == x))
    | _ => false

/-- **A run up to a product's exponent cut at a factor's**: the tile of `[p]` into `[x]` and `[y]`,
the code's `[p] = [x]·[y]`, both powers of `g`. -/
noncomputable def mulTileB (j : ℕ) (w : Wit) : Mode.Res → Bool
  | .sub a [b, c] => match frEx a.hi, frEx b.hi, frEx c.hi with
    | some p, some x, some y => tileShape (.fr p) [(.fr x, 1), (.fr y, 1)] (.sub a [b, c]) &&
        mulCells j w p x y && cellPow j w x && cellPow j w y
    | _, _, _ => false
  | _ => false

/-- **The frames' tiles**: function, the bound's base, the parts. `claim_list_digest`'s list
`n_g = bigs^136·groups^17·rest`, the three `list_split` returns read through its frame (cell `23`). -/
noncomputable def tiles : List (ℕ × Mode.Base × List (Mode.Base × ℕ)) :=
  [(fn_idx% «claim_list_digest», .fr 3, [(.hp 23 3, 136), (.hp 23 4, 17), (.hp 23 5, 1)])]

/-- A tile of function `j`'s (`tiles`). -/
noncomputable def tileListB (j : ℕ) (x : Mode.Res) : Bool :=
  tiles.any fun p ↦ p.1 == j && tileShape p.2.1 p.2.2 x

/-! ## A run one point past another -/

/-- **A run one point past another** (the last point read on its own): `⟨Q, 0, [o] + 1, S, d⟩`
inside `⟨Q, 0, [o], S, d⟩` and the point `Q·[o]^S·g^d`, `[o]` a power of `g`. -/
noncomputable def extB (j : ℕ) (w : Wit) : Mode.Res → Bool
  | .sub a [b, c] => match a.hi with
    | .ex (.fr o) 1 => cellPow j w o && decide (a.lo = .num 0 ∧ b = ⟨a.q, .num 0, .ex (.fr o) 0, a.S, a.d⟩ ∧
        c = ⟨⟨a.q.fp, a.q.k + a.d, Mode.insertBs (.fr o, a.S) a.q.bs⟩, .num 0, .num 1, 1, 0⟩)
    | _ => false
  | _ => false

/-! ## Offsets modulo the order -/

/-- **A run inside another modulo `g`'s order**: both over one product, stride `1`, between constants,
`a`'s offsets `lo + d .. hi - 1 + d` reduced modulo `2^64 - 1` without wrapping inside `b`'s. -/
def ordB : Mode.Res → Bool
  | .sub a [b] => match a.lo, a.hi, b.lo, b.hi with
    | .num lo, .num hi, .num blo, .num bhi =>
      decide (a.q = b.q ∧ a.S = 1 ∧ b.S = 1 ∧ blo + b.d ≤ (lo + a.d) % ordG ∧
        (lo + a.d) % ordG + (hi - lo) ≤ bhi + b.d ∧ (lo + a.d) % ordG + (hi - lo) ≤ ordG)
    | _, _, _, _ => false
  | _ => false

/-- An index one up: a constant's successor, an exponent's offset one up. -/
def idxSucc : Mode.Idx → Mode.Idx
  | .num n => .num (n + 1)
  | .ex B c => .ex B (c + 1)

/-- An index whose exponent's base is a selector's of function `j` (`ltSelB`) or a cell `pw` bounds,
so a power of `g`. -/
noncomputable def idxPow (j : ℕ) (w : Wit) : Mode.Idx → Bool
  | .num _ => true
  | .ex B _ => ltSelB j (.lt (.ex B 0) (.num (2 ^ 62))) || match B with
    | .fr o => pw j w o
    | _ => false

/-- **The same cells named one index up** (`g^ordG = 1`): `⟨Q, lo + 1, hi + 1, S, d'⟩` inside
`⟨Q, lo, hi, S, d⟩`, `d' + S = d + ordG`, or the other way round, each exponent's base a selector's of
function `j` or a cell `pw` bounds. -/
noncomputable def ordShiftB (j : ℕ) (w : Wit) : Mode.Res → Bool
  | .sub a [b] => (decide (a.q = b.q ∧ a.S = b.S ∧ a.lo = idxSucc b.lo ∧ a.hi = idxSucc b.hi ∧
      a.d + a.S = b.d + ordG) && idxPow j w b.lo && idxPow j w b.hi) ||
    (decide (a.q = b.q ∧ a.S = b.S ∧ b.lo = idxSucc a.lo ∧ b.hi = idxSucc a.hi ∧
      b.d + b.S = a.d + ordG) && idxPow j w a.lo && idxPow j w a.hi)
  | _ => false

/-! ## A lift read back -/

/-- **A run past a lift's shift**: `⟨P, k, [v], 1, 0⟩` inside `⟨P·g^k, 0, [u], 1, 0⟩`. -/
def liftBack (u v k : ℕ) : Mode.Res → Bool
  | .sub a [b] => decide (a.q.fp = b.q.fp ∧ b.q.k = a.q.k + k ∧ a.q.bs = b.q.bs ∧ a.lo = .num k ∧
      a.hi = .ex (.fr v) 0 ∧ a.S = 1 ∧ a.d = 0 ∧ b.lo = .num 0 ∧ b.hi = .ex (.fr u) 0 ∧ b.S = 1 ∧ b.d = 0)
  | _ => false

/-- **The tile families** at function `j` with the witness `w`. -/
noncomputable def tileFamB (j : ℕ) (w : Wit) (x : Mode.Res) : Bool :=
  mulTileB j w x || tileListB j x || extB j w x || ordB x

end

end LeanVM.Guest.Res
