/-
  LeanVM.Guest.EndCompleteCounts

  The instruction budget: per opcode a `Linear` in the node's work dominating `main`'s weight bound
  `mainWeight` at the honest words.
-/

module

public import LeanVM.Guest.EndCompleteWords

/-!
# `main`'s instruction counts within a linear budget

For a frame weight `ω : String → ℕ` (an opcode's instructions on one path through a frame) and
`main`'s weight hypotheses `Wt : MainWeightHyps fs ω`, `eaWLin ω Bd A Wt`: a constant, plus per unit
of work the weight a declared claim, a coverage slot, a raw signature or matrix, a child and a
child's claim add, the claim lists' and the child claim lists' bounds `Bd` affine (`EaAffOk Bd A`)
and taken at the ratios `α / 1000`. `ea_weight`: at the honest words of a node within the limits,
`mainWeight ω Bd Wt` is at most it. `eaInstrs`: per opcode, at `ω op` and the words' callee bounds,
plus the jump table's `jt op`; `ea_hinstrs`: `mainComplete_of`'s instruction hypothesis.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.End (Limits CapsAgree Linear work coverage bytecode)

@[expose] public section

/-- A ratio of an affine bound, affinely. -/
theorem ea_ratio (α a b n : ℕ) : α * (a * n + b) / 1000 ≤ (α * a / 1000 + 1) * n + (α * b / 1000 + 1) := by
  have h1 := Nat.lt_div_mul_add (a := α * a) (b := 1000) (by norm_num)
  have h2 := Nat.lt_div_mul_add (a := α * b) (b := 1000) (by norm_num)
  rw [Nat.div_le_iff_le_mul_add_pred (by norm_num)]
  have e : α * (a * n + b) = α * a * n + α * b := by ring
  rw [e]
  have h3 : α * a * n ≤ (α * a / 1000 * 1000 + 1000) * n := Nat.mul_le_mul_right _ (by omega)
  nlinarith

variable {fs : String → ℕ} (ω : String → ℕ) (Bd : CalleeBounds) (A : EaAffC) (Wt : MainWeightHyps fs ω)

/-- A claim list's weight: slope and constant. -/
def ewClA : ℕ := Wt.αcl * A.aCl / 1000 + 1
def ewClB : ℕ := Wt.αcl * A.bCl / 1000 + 1
/-- A child's weight, affinely in its claims: constant and slope. -/
def ewChK : ℕ := 2 * (Wt.αccl * A.bCcl / 1000 + 1) + Wt.Bdl + Wt.Bsd + Bd.vsW ω Wt.vsc
def ewChA : ℕ := Wt.αccl * A.aCcl / 1000 + 1 + Wt.Kl100

/-- **`main`'s weight bound, linearly in the work.** -/
def eaWLin : Linear where
  base := ω "main" + Wt.Bexp + Wt.Bdl + 2 * ewClB ω A Wt + ω "__loop5" + Wt.cAgg + Wt.Bsd
  declared := ewClA ω A Wt
  coverage := Wt.Kl0 + Wt.Kl1 + Wt.Kl2
  rawXmss := Wt.Kl3
  rawSphincs := Wt.Kl4
  rawDa := Digest.dvWA ω + Wt.Bcov
  rawDaRows := Digest.dvWB ω
  children := ω "__loop5" + ewChK ω Bd A Wt + Wt.dAgg
  childClaims := ewChA ω A Wt

theorem ea_childW {Bd : CalleeBounds} {A : EaAffC} (hA : EaAffOk Bd A) (r : ChildWords) :
    childW ω Bd Wt r ≤ ewChK ω Bd A Wt + ewChA ω A Wt * (r.nx + r.ns + r.da.length) := by
  have c1 : Wt.αccl * Bd.ccl r.nx / 1000 ≤ (Wt.αccl * A.aCcl / 1000 + 1) * r.nx + (Wt.αccl * A.bCcl / 1000 + 1) :=
    le_trans (Nat.div_le_div_right (Nat.mul_le_mul_left _ (hA.ccl r.nx))) (ea_ratio _ _ _ _)
  have c2 : Wt.αccl * Bd.ccl r.ns / 1000 ≤ (Wt.αccl * A.aCcl / 1000 + 1) * r.ns + (Wt.αccl * A.bCcl / 1000 + 1) :=
    le_trans (Nat.div_le_div_right (Nat.mul_le_mul_left _ (hA.ccl r.ns))) (ea_ratio _ _ _ _)
  have e : ewChA ω A Wt * (r.nx + r.ns + r.da.length) = (Wt.αccl * A.aCcl / 1000 + 1) * r.nx +
      (Wt.αccl * A.aCcl / 1000 + 1) * r.ns + (Wt.αccl * A.aCcl / 1000 + 1) * r.da.length +
      Wt.Kl100 * (r.nx + r.ns) + Wt.Kl100 * r.da.length := by
    simp only [ewChA]; ring
  have e2 : r.da.length * Wt.Kl100 = Wt.Kl100 * r.da.length := Nat.mul_comm _ _
  simp only [childW, ewChK]
  omega

set_option maxHeartbeats 1000000 in
/-- **`main`'s weight bound at the honest words is within `eaWLin`**, for a node within the limits. -/
theorem ea_weight {Bd : CalleeBounds} {A : EaAffC} (hA : EaAffOk Bd A) {seed : Digest}
    {s : NodeStatement} {w : NodeWitness} (hlim : Limits s w) :
    mainWeight ω Bd Wt (honestWords seed s w) ≤ (eaWLin ω Bd A Wt).eval (work s w) := by
  set W := honestWords seed s w with hW
  have hcov : (work s w).coverage = W.total := by
    show coverage s w = _
    rw [coverage_eq]; rfl
  have hdecl : (work s w).declared = W.dx + W.ds + W.da := rfl
  have hrx : (work s w).rawXmss = W.rx := rfl
  have hrs : (work s w).rawSphincs = W.rs := rfl
  have hrd : (work s w).rawDa = W.rd := rfl
  have hrr : (work s w).rawDaRows = W.drows := rfl
  have hnc : (work s w).children = W.nc := rfl
  have hcc : (work s w).childClaims = (w.children.map cnw).sum := rfl
  have hrd1 : W.rd ≤ 1 := hlim.directDa
  have htot : W.total = W.dx + W.ux + (W.ds + W.us) + (W.da + W.ud) := rfl
  have c1 : Wt.αcl * Bd.cl W.dx / 1000 ≤ ewClA ω A Wt * W.dx + ewClB ω A Wt :=
    le_trans (Nat.div_le_div_right (Nat.mul_le_mul_left _ (hA.cl W.dx))) (ea_ratio _ _ _ _)
  have c2 : Wt.αcl * Bd.cl W.ds / 1000 ≤ ewClA ω A Wt * W.ds + ewClB ω A Wt :=
    le_trans (Nat.div_le_div_right (Nat.mul_le_mul_left _ (hA.cl W.ds))) (ea_ratio _ _ _ _)
  have m0 : (W.da + W.ud) * Wt.Kl0 ≤ Wt.Kl0 * W.total := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
  have m1 : W.ux * Wt.Kl1 ≤ Wt.Kl1 * W.total := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
  have m2 : W.us * Wt.Kl2 ≤ Wt.Kl2 * W.total := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
  have m3 : (Wt.Kl0 + Wt.Kl1 + Wt.Kl2) * W.total = Wt.Kl0 * W.total + Wt.Kl1 * W.total + Wt.Kl2 * W.total := by
    ring
  have m4 : ewClA ω A Wt * (W.dx + W.ds + W.da) ≥ ewClA ω A Wt * W.dx + ewClA ω A Wt * W.ds := by
    rw [Nat.mul_add, Nat.mul_add]; omega
  have m5 : W.rx * Wt.Kl3 = Wt.Kl3 * W.rx := Nat.mul_comm _ _
  have m6 : W.rs * Wt.Kl4 = Wt.Kl4 * W.rs := Nat.mul_comm _ _
  have hda : (if W.rd = 1 then Bd.daVerifyW ω W.drows + Wt.Bcov else 0) ≤
      (Digest.dvWA ω + Wt.Bcov) * W.rd + Digest.dvWB ω * W.drows := by
    split_ifs with h
    · rw [h, Nat.mul_one]; have := hA.dvW ω W.drows; omega
    · exact Nat.zero_le _
  have hch : loopSum (ω "__loop5") (fun c => childW ω Bd Wt (W.child c)) 0 W.nc ≤
      W.nc * (ω "__loop5" + ewChK ω Bd A Wt) + ω "__loop5" + ewChA ω A Wt * (w.children.map cnw).sum := by
    refine ea_loopSum (ω "__loop5") (ewChK ω Bd A Wt) (ewChA ω A Wt) _ w.children 0 fun i hi => ?_
    have hc : W.child (0 + i) = childWordsOf seed w.children[i] (hbase s w i) := by
      simp only [hW, honestWords, Nat.zero_add, hi, ↓reduceDIte]
    show childW ω Bd Wt (W.child (0 + i)) ≤ _
    rw [hc]
    exact ea_childW ω Wt hA _
  have hagg : (if W.nc = 0 then 0 else Wt.cAgg + Wt.dAgg * W.nc) ≤ Wt.cAgg + Wt.dAgg * W.nc := by
    split_ifs <;> omega
  have hn5 : W.nc * (ω "__loop5" + ewChK ω Bd A Wt) = ω "__loop5" * W.nc + ewChK ω Bd A Wt * W.nc := by ring
  have hn6 : (ω "__loop5" + ewChK ω Bd A Wt + Wt.dAgg) * W.nc =
      ω "__loop5" * W.nc + ewChK ω Bd A Wt * W.nc + Wt.dAgg * W.nc := by ring
  simp only [mainWeight, eaWLin, Linear.eval, hcov, hdecl, hrx, hrs, hrd, hrr, hnc, hcc]
  omega

/-! ## Per opcode -/

variable {cert : String → V → ℕ} (H : CalleesHyps fs cert bytecode)

/-- **The instruction budget**: per opcode `eaWLin` at its weight and the words' callee bounds, plus
the jump table's `jt op`. -/
def eaInstrs (a86 b86 : ℕ) {ωs : Opcode → String → ℕ} (Wts : ∀ op, MainWeightHyps fs (ωs op))
    (jt : Opcode → ℕ) (op : Opcode) : Linear :=
  let l := eaWLin (ωs op) (calleeBd fs H) (eaWordsC fs H a86 b86) (Wts op)
  { l with base := l.base + jt op }

/-- **`mainComplete_of`'s instruction hypothesis**: `mainWeight` at each opcode's weight, plus the
jump table's, is within `eaInstrs`. -/
theorem ea_hinstrs {a86 b86 : ℕ} (h86 : ∀ q, H.B86 (gen ^ q) ≤ a86 * q + b86) {ωs : Opcode → String → ℕ}
    (Wts : ∀ op, MainWeightHyps fs (ωs op)) (jt : Opcode → ℕ) :
    ∀ seed s w, NodeRel bytecode seed s w → Limits s w → CapsAgree seed w → ∀ op,
      mainWeight (ωs op) (calleeBd fs H) (Wts op) (honestWords seed s w) + jt op ≤
        (eaInstrs H a86 b86 Wts jt op).eval (work s w) := by
  intro seed s w _ hlim _ op
  have := ea_weight (ωs op) (Wts op) (ea_wordsOk fs H h86) (seed := seed) hlim
  simp only [eaInstrs, Linear.eval] at this ⊢
  omega

end
end LeanVM.Guest.B1.Main
