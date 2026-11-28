/-
  LeanVM.Guest.CoreMode.CoreResS

  A run of symbolic bounds inside a run of constant bounds (`subRS`): its bounds from the exponent facts the same
  heap certificate states, each of a family.
-/

module

public import LeanVM.Guest.CoreMode.CoreRes

/-!
# Symbolic runs inside a constant run

`subR Q R`, `R = [b]·g^o'·[l, N)` of stride `1`, `Q = [b·Π vᵢ^aᵢ]·g^o·g^(S·[lo, hi))`: every cell of `Q` is the cell
`o - o' + Σ aᵢ·e(vᵢ) + S·j` of `R`, inside it when `o - o' + Σ aᵢ·(nᵢ - 1) + S·(H - 1) < N`, `e(vᵢ) < nᵢ` and
`e(hi) ≤ H` from facts `e(v) < n` among the certificate's residuals `L` (`factB`: unconditional, or under conditions
the residual's own include). Those facts are residuals of a family themselves (`resOk`), so the family holds where
they do (`subRS_sound`, `CoreResSSound.lean`), at any valuation.
-/

namespace LeanVM.Guest.CoreMode

@[expose] public section

/-- **A fact's bound** `n`, `e(v) < n < 2^62`: a residual `e(v) < n`, or one under conditions among `g`. -/
def factOf (g : List CCond) (v : ℕ) : CRes → Option ℕ
  | .lt (.val x) (.num n) => bif Nat.beq x v && Nat.blt n capE then some n else none
  | .under g' (.lt (.val x) (.num n)) =>
      bif Nat.beq x v && Nat.blt n capE && g'.all (fun c ↦ g.contains c) then some n else none
  | _ => none

/-- **The least fact's bound** on `v` among the residuals `L` (`factOf`). -/
def factB (L : List CRes) (g : List CCond) (v : ℕ) : Option ℕ := (L.filterMap (factOf g v)).min?

/-- **A product's exponent at most** `Σ aᵢ·(nᵢ - 1)`, `e(vᵢ) < nᵢ` (`factB`). -/
def prodMax (L : List CRes) (g : List CCond) : List (ℕ × ℕ) → Option ℕ
  | [] => some 0
  | (v, a) :: bs => (factB L g v).bind fun n ↦ (prodMax L g bs).map (a * (n - 1) + ·)

/-- **An index's exponent at most**: a constant's, `n - 1` for a value of a fact `e(v) < n`, a monomial's
`prodMax` plus its offset. -/
def idxMax (L : List CRes) (g : List CCond) : CIdx → Option ℕ
  | .num h => some h
  | .val v => (factB L g v).map (· - 1)
  | .mono c => (prodMax L g c.bases).map (· + c.off)

/-- **A symbolic run inside a constant run** (under conditions `g`): `R = ⟨⟨rb, o'⟩, 1, l, N⟩`, `Q`'s bases `rb`
then `rest`, `o' ≤ o`, `l ≤ o - o'`, `o - o' + prodMax rest + S·(idxMax hi - 1) < N < 2^62`. -/
def subRSg (L : List CRes) (g : List CCond) (q r : CRun) : Bool :=
  match r.lo, r.hi with
  | .num l, .num N =>
      basesBeq (q.base.bases.take r.base.bases.length) r.base.bases && Nat.beq r.stride 1 &&
        Nat.ble r.base.off q.base.off && Nat.ble l (q.base.off - r.base.off) && Nat.blt N capE &&
        (idxMax L g q.hi).any fun H ↦ (prodMax L g (q.base.bases.drop r.base.bases.length)).any fun M ↦
          Nat.blt (q.base.off - r.base.off + M + q.stride * (H - 1)) N
  | _, _ => false

/-- **The `subRS` family** over the certificate's residuals `L`: `subRSg`, unconditional or under conditions. -/
def subRS (L : List CRes) : CRes → Bool
  | .subR q r => subRSg L [] q r
  | .under g (.subR q r) => subRSg L g q r
  | _ => false

end

end LeanVM.Guest.CoreMode
