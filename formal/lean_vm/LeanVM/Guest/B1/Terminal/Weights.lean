/-
  LeanVM.Guest.B1.Terminal.Weights

  The weights `check_opening_terminal` batches, factored as the guest computes them: a committed
  column's claim, a `q_keccak` lane's claim and the ring switch's claim.
-/

module

public import LeanVM.Protocol.Verifier.Claims
public import LeanVM.Guest.B1.Terminal.EqMath
public import LeanVM.Guest.B1.Terminal.Sum

/-!
# The claims' weights, factored

On a stack of `L` coordinates at `x`:

* `wOf_committed`: a claim on a column placed at `(κ, o)` weighs its point's weight against `x`'s
  first `κ` coordinates times the offset bits' weight `selProd o κ (L - κ) x`;
* `wOf_lane`: a `q_keccak` lane's claim at `(τ, oq + s·2^τ)` weighs its point's weight, its slot's
  six bits' and `oq`'s bits' above `τ + 6`;
* `ringClaim_eq`: the ring switch's claim weighs `oq`'s bits above `κ` times the ring weight at
  `x`'s first `κ` coordinates.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier Finset

@[expose] public section

theorem stack_eqEval {p : List E} {κ o L : ℕ} {x : List E} (hp : p.length = κ) (hx : x.length = L)
    (hκ : κ ≤ L) :
    eqEval (p ++ (selectorPoint o L).drop κ) x = eqEval p (x.take κ) * selProd o κ (L - κ) x := by
  rw [← List.take_append_drop κ x,
    eqEval_append (by rw [hp, List.length_take]; omega), List.take_append_drop,
    eqEval_sel o hx hκ]

/-- **A committed column's claim.** -/
theorem wOf_committed {layout : Layout} {x : List E} {c : ColumnClaim} {κ o : ℕ}
    (hpl : layout.placement c.column = Placement.mk κ o) (hp : c.point.length = κ)
    (hx : x.length = layout.stackLog) (hκ : κ ≤ layout.stackLog) :
    wOf layout x c = eqEval c.point (x.take κ) * selProd o κ (layout.stackLog - κ) x := by
  simp only [wOf, ColumnClaim.stackClaim, Placement.stackPoint_eq_drop, hpl]
  exact stack_eqEval hp hx hκ

/-- **A `q_keccak` lane's claim.** -/
theorem wOf_lane {layout : Layout} {x : List E} {c : ColumnClaim} {τ oq s : ℕ}
    (hpl : layout.placement c.column = Placement.mk τ (oq + s * 2 ^ τ)) (hp : c.point.length = τ)
    (hx : x.length = layout.stackLog) (hκ : τ + 6 ≤ layout.stackLog) (hq : 2 ^ (τ + 6) ∣ oq)
    (hs : s < 64) :
    wOf layout x c = eqEval c.point (x.take τ) *
      ((∏ i ∈ range 6, bitF (s.testBit i) (x.getD (τ + i) 0)) *
        selProd oq (τ + 6) (layout.stackLog - (τ + 6)) x) := by
  rw [wOf_committed hpl hp hx (by omega), selProd_lane hq hs (by omega),
    show layout.stackLog - τ - 6 = layout.stackLog - (τ + 6) by omega]

theorem selProd_shift (o κ n : ℕ) (x : List E) :
    selProd (o >>> κ) 0 n (x.drop κ) = selProd o κ n x := by
  unfold selProd
  refine prod_congr rfl fun i _ ↦ ?_
  rw [Nat.testBit_shiftRight, zero_add, getD_drop']

/-- **The ring switch's claim.** -/
theorem ringClaim_eq {layout : Layout} {x : List E} {κ o : ℕ} {ringPoint coeffs : List E}
    (hpl : layout.placement qkeccak = Placement.mk κ o) (hx : x.length = layout.stackLog) :
    (ringSwitchClaim layout 0 (fun rP ↦ ringWeight ringPoint rP coeffs)).1 x =
      selProd o κ (layout.stackLog - κ) x * ringWeight ringPoint (x.take κ) coeffs := by
  simp only [ringSwitchClaim, Placement.eqAbove, hpl]
  have h := eqEval_sel (o >>> κ) (x := x.drop κ) (L := layout.stackLog - κ) (κ := 0)
    (by rw [List.length_drop, hx]) (Nat.zero_le _)
  simp only [List.drop_zero, Nat.sub_zero] at h
  rw [hx, h, selProd_shift]

end
end LeanVM.Guest.B1.VerifySub
