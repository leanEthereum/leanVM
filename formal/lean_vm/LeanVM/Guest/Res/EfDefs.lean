/-
  LeanVM.Guest.Res.EfDefs

  The exponent facts' families of the `sub` and order residuals: runs, points and tiles whose bounds
  a function's facts on its bases' exponents order, and reads past a cursor its facts place in a
  stream.
-/

module

public import LeanVM.Guest.Mode.Step
public import LeanVM.Guest.B2C.Cells
public meta import LeanVM.Guest.CoreRef

/-!
# Exponent facts

`EFacts`: facts on a frame's bases, each proved at the honest frames of the function that lists
them: `pows`, a base's word is `g^x`, `lo ≤ x ≤ hi`; `les`, two bases' words are `g^x`, `g^y`,
`x ≤ y + c`; `curs`, a cursor base's word is the stream base's times `g^p`, room for `n` words past it.

`efLeB F a b`: exponent `a` at most `b` by the bounds (`efHi`, `efLo`) or a listed order.
`efFamB F x`: `x` is an order residual the bounds decide (`efLtB`), a run inside a run over one
product up to a larger bound (`efRunB`), a point `Q·X·g^k` inside `Q`'s run past `X`'s exponent
plus `k` (`efPtB`), a run up to `e(X) + c` tiled by `[0, c0)`, `[c0, e(X))` and `Q·X·[0, c)`
(`efTileB`), or a read `c` words past a listed cursor inside its stream (`efCurB`).
`vsFacts`: `verify_sub`'s facts (`EndExecRVs`); `vsB j x`: residual `x` of `verify_sub` in the
families on them.
-/

namespace LeanVM.Guest.Res

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **Exponent facts** on a frame's bases. -/
structure EFacts where
  pows : List (Mode.Base × ℕ × ℕ)
  les : List (Mode.Base × Mode.Base × ℕ)
  curs : List (Mode.Base × Mode.Base × ℕ)

/-- A base's listed exponent bounds. -/
def efPow (F : EFacts) (B : Mode.Base) : Option (ℕ × ℕ) :=
  (F.pows.find? fun p ↦ decide (p.1 = B)).map (·.2)

/-- An exponent's largest value by the bounds. -/
def efHi (F : EFacts) : Mode.Idx → Option ℕ
  | .num n => some n
  | .ex B c => (efPow F B).map (·.2 + c)

/-- An exponent's least value by the bounds, its base a listed power. -/
def efLo (F : EFacts) : Mode.Idx → Option ℕ
  | .num n => some n
  | .ex B c => (efPow F B).map (·.1 + c)

/-- Exponent `a` at most exponent `b`: by the bounds, or a listed order of their bases. -/
def efLeB (F : EFacts) (a b : Mode.Idx) : Bool :=
  (match efHi F a, efLo F b with
    | some x, some y => decide (x ≤ y)
    | _, _ => false) ||
  (match a, b with
    | .ex X c1, .ex Y c2 => F.les.any fun l ↦ decide (l.1 = X ∧ l.2.1 = Y ∧ c1 + l.2.2 ≤ c2)
    | _, _ => false)

/-- An order residual the bounds decide. -/
def efLtB (F : EFacts) : Mode.Res → Bool
  | .lt a b => match efHi F a, efLo F b with
    | some x, some y => decide (x < y)
    | _, _ => false
  | _ => false

/-- A run inside a run over the same product, up to a larger bound. -/
def efRunB (F : EFacts) : Mode.Res → Bool
  | .sub a [b] => decide (a.q = b.q ∧ a.lo = .num 0 ∧ b.lo = .num 0 ∧ a.S = 1 ∧ b.S = 1 ∧ a.d = b.d) &&
      efLeB F a.hi b.hi
  | _ => false

/-- The point `Q·X·g^k` (offset `d`) inside `Q`'s run from offset `d' ≤ k + d`, past `X`'s exponent plus
`k + d - d'`. -/
def efPtB (F : EFacts) : Mode.Res → Bool
  | .sub a [b] => match a.q.bs.head?, a.q.bs.getLast? with
    | some (X, ex), some (Y, ey) =>
      decide (a.q.fp = b.q.fp ∧ b.q.k = 0 ∧ a.lo = .num 0 ∧ a.hi = .num 1 ∧ b.lo = .num 0 ∧ a.S = 1 ∧
        b.S = 1 ∧ b.d ≤ a.q.k + a.d) &&
      ((decide (ex = 1 ∧ a.q.bs = (X, 1) :: b.q.bs) && efLeB F (.ex X (a.q.k + a.d - b.d + 1)) b.hi) ||
        (decide (ey = 1 ∧ a.q.bs = b.q.bs ++ [(Y, 1)]) && efLeB F (.ex Y (a.q.k + a.d - b.d + 1)) b.hi))
    | _, _ => false
  | _ => false

/-- A run up to `e(X) + c` tiled by `[0, c0)`, `[c0, e(X))` and `Q·X` up to `c`. -/
def efTileB (F : EFacts) : Mode.Res → Bool
  | .sub a [b1, b2, b3] => match a.hi, b1.hi with
    | .ex X c, .num c0 => (efPow F X).isSome &&
        decide (a.lo = .num 0 ∧ a.S = 1 ∧ b1 = ⟨a.q, .num 0, .num c0, 1, a.d⟩ ∧
          b2 = ⟨a.q, .num c0, .ex X 0, 1, a.d⟩ ∧
          b3 = ⟨⟨a.q.fp, a.q.k, a.q.bs ++ [(X, 1)]⟩, .num 0, .num c, 1, a.d⟩)
    | _, _ => false
  | _ => false

/-- The read `c` words past cursor `B` inside the stream `St·[0, 8192)`. -/
def efCurRes (B St : Mode.Base) (c : ℕ) : Mode.Res :=
  .sub ⟨⟨0, c, [(B, 1)]⟩, .num 0, .num 1, 1, 0⟩ [⟨⟨0, 0, [(St, 1)]⟩, .num 0, .num 8192, 1, 0⟩]

/-- A read past a listed cursor, below its room. -/
def efCurB (F : EFacts) : Mode.Res → Bool
  | .sub a bs => F.curs.any fun l ↦ decide (a.q.k < l.2.2 ∧ Mode.Res.sub a bs = efCurRes l.1 l.2.1 a.q.k)
  | _ => false

/-- **The exponent facts' families.** -/
def efFamB (F : EFacts) (x : Mode.Res) : Bool :=
  efLtB F x || efRunB F x || efPtB F x || efTileB F x || efCurB F x

/-! ## `verify_sub` -/

/-- **`verify_sub`'s exponent facts**: the tables' log-heights `dims[1..6]` (`[[92]·g^t]`), the
keccak table's (`t = 6`) at least `9` and at most `24`; the stack's log less `20` (`[224]`); the bus
depth (`log2_ceil`'s return, `[[185]·g^4]`); the table sumcheck's depth (`verify_tables`' return,
`[[591]·g^29]`), at least the keccak table's; the stack's log (`[[221]·g^4]`); the cursors
`verify_bus_gkr`, `verify_tables` and `verify_keccak` return, in the stream `[27]`. -/
def vsFacts : EFacts where
  pows := ((List.range 5).map fun t ↦ (.hp 92 (t + 1), 0, 30)) ++
    [(.hp 92 6, 9, 24), (.fr 224, 0, 10), (.hp 185 4, 20, 33), (.hp 591 29, 9, 33), (.hp 221 4, 20, 30)]
  les := [(.hp 92 6, .hp 591 29, 0), (.hp 221 4, .fr 224, 20)]
  curs := [(.hp 577 17, .fr 27, 14), (.hp 591 28, .fr 27, 49), (.hp 604 20, .fr 27, 207)]

/-- **A residual of `verify_sub` its exponent facts take.** -/
noncomputable def vsB (j : ℕ) (x : Mode.Res) : Bool :=
  (coreOf j).name == name% «verify_sub» && efFamB vsFacts x

end

end LeanVM.Guest.Res
