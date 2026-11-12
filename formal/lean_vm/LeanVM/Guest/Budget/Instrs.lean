/-
  LeanVM.Guest.Budget.Instrs

  `main`'s instruction bound (`mainCount`) at the honest counts within a budget linear in the
  node's work (`mainInstrs`).
-/

module

public import LeanVM.Guest.Budget.MainCount
public import LeanVM.Guest.B1.Main.MainWords
public import LeanVM.Guest.AcceptableChild

/-!
# The instruction budget

`mainInstrs H c5 s5 v5 jt`: per unit of work, `mainCount`'s terms: a constant, `main`'s static
callees and the claim lists' constants, the claim lists' slope per declared claim, the loops per
coverage slot and raw signature, `da_verify`'s constant per direct blob and slopes per row and
padded row, and the
children's loop (`l5Lin`): `c5` and `aggregate_claims`' per child, `s5` per child's claim and
`v5 μ r` per child of announced stack log `μ` and rate `r`. `mainCount_le`: on the honest run
within the limits, `mainCount` at the claim lists' and `da_verify`'s affine bounds and the
children's loop's `l5Lin`, plus `jt`, is at most it.
-/
namespace LeanVM.Guest.Budget

open LeanVM.Guest.Completeness

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Guest.End (Linear work)
open LeanVM.Guest.B1.Main (hm hData hData_bounds coverage_eq xPlan sPlan)

@[expose] public section

/-- **The children's loop's instructions** at the work `u`: `c5` per child, `s5` per child's
claim, `v5 μ r` per child of announced stack log `μ` and rate `r`. -/
def l5Lin (c5 s5 : ℕ) (v5 : ℕ → ℕ → ℕ) (u : End.Work) : ℕ :=
  c5 * u.children + s5 * u.childClaims + (u.childShapes.map fun p => v5 p.1 p.2).sum

variable {ω fs : String → ℕ}

/-- **The instruction budget** at `ω`: `mainCount`'s terms, linearly in the work, the children's
loop's at `l5Lin c5 s5 v5`. -/
def mainInstrs (H : MainCounts ω fs) (c5 s5 : ℕ) (v5 : ℕ → ℕ → ℕ) (jt : ℕ) : Linear where
  base := ω "main" + H.kExp + H.kSd + jt + 2 * H.clA
  declared := H.clS
  coverage := H.kL1 + H.kL2
  rawXmss := H.kL3
  rawSphincs := H.kL4
  rawDa := H.dvA
  rawDaRows := H.dvR
  rawDaPad := H.dvP
  children := c5 + H.aggC + H.aggD
  childClaims := s5
  childShape := v5

/-- **`main`'s instruction bound within the budget** on the honest run within the limits, the
claim lists within their affine bounds on their claims, `da_verify` on its rows, the children's
loop within `l5Lin c5 s5 v5`. -/
theorem mainCount_le (H : MainCounts ω fs) (c5 s5 : ℕ) (v5 : ℕ → ℕ → ℕ) (jt : ℕ)
    {seed : Digest} {s : NodeStatement} {w : NodeWitness} (hl : GuestLimits s w) :
    mainCount H (hm fs 0 seed s w) (H.clA + H.clS * s.claims.xmss.length)
      (H.clA + H.clS * s.claims.sphincs.length)
      (H.dvA + H.dvR * (work s w).rawDaRows + H.dvP * (work s w).rawDaPad)
      (l5Lin c5 s5 v5 (work s w)) + jt ≤ (mainInstrs H c5 s5 v5 jt).eval (work s w) := by
  have hcov := coverage_eq (s := s) (w := w)
  simp only [List.length_append] at hcov
  have hd : (hm fs 0 seed s w).nd ≤ 1 := (hData_bounds hl fs 0).nd
  have hdecl : s.claims.xmss.length + s.claims.sphincs.length ≤ (work s w).declared := by
    simp only [work]; omega
  have hcov' : Coverage.planSlots s w = (work s w).coverage := rfl
  have e1 : (hm fs 0 seed s w).nxd = (xPlan s w).duplicates.length := rfl
  have e2 : (hm fs 0 seed s w).nsd = (sPlan s w).duplicates.length := rfl
  have e3 : (hm fs 0 seed s w).nrx = (work s w).rawXmss := rfl
  have e4 : (hm fs 0 seed s w).nrs = (work s w).rawSphincs := rfl
  have e5 : (hm fs 0 seed s w).nc = (work s w).children := rfl
  have e6 : (hm fs 0 seed s w).nd = (work s w).rawDa := rfl
  have c1 : (hm fs 0 seed s w).nxd * H.kL1 ≤ H.kL1 * (work s w).coverage := by
    rw [e1, Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
  have c2 : (hm fs 0 seed s w).nsd * H.kL2 ≤ H.kL2 * (work s w).coverage := by
    rw [e2, Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
  have cX : H.clS * s.claims.xmss.length + H.clS * s.claims.sphincs.length ≤
      H.clS * (work s w).declared := by
    rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ hdecl
  unfold mainCount
  simp only [Linear.eval, mainInstrs]
  rw [e3, e4]
  have r3 : (work s w).rawXmss * H.kL3 = H.kL3 * (work s w).rawXmss := Nat.mul_comm _ _
  have r4 : (work s w).rawSphincs * H.kL4 = H.kL4 * (work s w).rawSphincs := Nat.mul_comm _ _
  -- the direct blob
  have hDa : (if (hm fs 0 seed s w).nd = 1 then
      H.dvA + H.dvR * (work s w).rawDaRows + H.dvP * (work s w).rawDaPad else 0) ≤
      H.dvA * (work s w).rawDa + H.dvR * (work s w).rawDaRows +
        H.dvP * (work s w).rawDaPad := by
    split_ifs with h1
    · have hra : (work s w).rawDa = 1 := by rw [← e6, h1]
      rw [hra]; omega
    · omega
  -- the children
  have hCh : (if (hm fs 0 seed s w).nc = 0 then 0 else
      l5Lin c5 s5 v5 (work s w) + (H.aggC + H.aggD * (hm fs 0 seed s w).nc)) ≤
      (c5 + H.aggC + H.aggD) * (work s w).children + s5 * (work s w).childClaims +
        ((work s w).childShapes.map fun p => v5 p.1 p.2).sum := by
    split_ifs with h0
    · omega
    · have hn1 : 1 ≤ (work s w).children := Nat.pos_of_ne_zero (by rw [← e5]; exact h0)
      have : H.aggC ≤ H.aggC * (work s w).children := Nat.le_mul_of_pos_right _ hn1
      have e7 : (c5 + H.aggC + H.aggD) * (work s w).children = c5 * (work s w).children +
          H.aggC * (work s w).children + H.aggD * (work s w).children := by ring
      rw [e5]
      unfold l5Lin
      omega
  have ecov : (H.kL1 + H.kL2) * (work s w).coverage =
      H.kL1 * (work s w).coverage + H.kL2 * (work s w).coverage := by ring
  omega

end
end LeanVM.Guest.Budget
