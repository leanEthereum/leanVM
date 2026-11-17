module

public import Quantum.StdModel.Qrom.Cpre
public import Quantum.StdModel.Qrom.XmssTcr

@[expose] public section

/-!
# The leanXMSS CPRE instance of the QROM bound (B3)

The obligations of `Quantum.StdModel.Qrom.CpreQ.probAvg_cpre_slRed_le` at leanXMSS's CPRE game
`cpre romWorld xmssChains noEval` played by B3 (`cpreRed`):

* `cellAt_xmss`, `xmss_cellInj`: a step cell is the cell of its chain slot, and distinct steps
  or values have distinct cells (`cell_injective`);
* `stepW_le_slotCost`: a step cell is a cell of a chain slot, so B3's step-cell reads are among
  its calls at the chain slots (`cpreRed_onChallenge`: `0`, `0`, `870`);
* `lenMax_xmssChains`: the chains have `chainLength - 1 = 3` steps;
* the truncation's fibers have `2^128` digests (`card_truncateHash_fiber_le`).

`probAvg_cpreRed_le`: for an adversary of `n` hash calls,
`probAvg ≤ ((n + 873) √(gradeEta 2^128) + √(4 n · n κ) + √(873 κ))²`, `κ = kappaC Digest 2^128`.
-/

open IPFunctor OracleComp OracleSpec HashSig HashSig.OverPermutation LeanXmss
open scoped ENNReal

set_option synthInstance.maxSize 2000

namespace Quantum.StdModel.Xmss

open Quantum.StdModel Props Common
open Quantum.Qrom (HashDomain)
open Quantum.StdModel.Qrom (gradeEta)
open Quantum.StdModel.Qrom.CpreQ (cellAt CellInj stepW stepCells redW lenMax kappaC
  probAvg_cpre_slRed_le)

-- A bound on a reduction is otherwise unfolded by `whnf`.
attribute [local irreducible] QueryCostAtMost

/-- **A step cell is the cell of its chain slot.** -/
theorem cellAt_xmss (P : PublicParameter) (l : Layer) (e : KeyIndex) (i : ChainIndex) {ν : ℕ}
    (hν : ν < chainLength - 1) (x : Digest) :
    cellAt xmssChains P (l, e, i) ν x = Qrom.Xmss.cell P (.chain l e ⟨ν, hν⟩ i) x := by
  unfold cellAt
  rw [xmssChains_tweak l e i hν]
  rfl

/-- **Distinct steps or values have distinct cells.** -/
theorem xmss_cellInj (P : PublicParameter) : CellInj xmssChains P := by
  rintro ⟨l, e, i⟩ ν x ⟨l', e', i'⟩ ν' x' hν hν' h
  rw [cellAt_xmss P l e i hν, cellAt_xmss P l' e' i' hν'] at h
  obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp (Qrom.Xmss.cell_injective P
    (s := .chain l e ⟨ν, hν⟩ i) (s' := .chain l' e' ⟨ν', hν'⟩ i') trivial trivial h)
  injection h1 with hl he hs hi
  subst hl he hi
  obtain rfl : ν = ν' := congrArg Fin.val hs
  exact ⟨rfl, rfl, eq_of_heq h2⟩

/-- **B3's step-cell reads are among its calls at the chain slots.** -/
theorem stepW_le_slotCost (P : PublicParameter) (t : Qrom.RomOracles.Domain) :
    stepW (ch := xmssChains) P t ≤ slotCost chainSlots t := by
  rcases t with _ | z
  · exact le_rfl
  · by_cases hz : z ∈ stepCells xmssChains P
    · refine (show stepW (ch := xmssChains) P (.inr z) ≤ 1 by simp [stepW, hz]).trans ?_
      obtain ⟨⟨l, e, i⟩, ν, x, hν, rfl⟩ := hz
      change 1 ≤ slotCost chainSlots (.inr (cellAt xmssChains P (l, e, i) ν x))
      have hν' : ν < chainLength - 1 := hν
      have hs : (Qrom.Xmss.slotOf (Qrom.Xmss.cell P (.chain l e ⟨ν, hν'⟩ i) x)).any chainSlots =
          true := by
        rw [Qrom.Xmss.slotOf_cell P (s := .chain l e ⟨ν, hν'⟩ i) trivial x]
        rfl
      rw [cellAt_xmss P l e i hν', slotCost]
      exact le_of_eq (ite_eq_left_of_eq_true _ _ (eq_true hs)).symm
    · simp [stepW, hz]

theorem redW_le_sumCost (P : PublicParameter) :
    ∀ t : Qrom.RomOracles.Domain ⊕ CpreQuery CpreRed.CJ XTw Empty (fun _ ↦ Unit),
      redW (ch := xmssChains) P (fun _ ↦ 0) t ≤ sumCost (slotCost chainSlots) t
  | .inl t => stepW_le_slotCost P t
  | .inr _ => le_rfl

theorem lenMax_xmssChains : lenMax xmssChains = 3 :=
  Finset.sup_const ⟨(⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩), Finset.mem_univ _⟩ _

/-- **The leanXMSS CPRE game in the QROM (B3)**: for an adversary of `n` hash calls (and any
number `k` of signing requests), B3 wins with probability at most
`((n + 873) √(gradeEta 2^128) + √(4 n · n κ) + √(873 κ))²`, `κ = kappaC Digest 2^128`: B3 reads
`870` step cells in its output and the decision walks at most `3` steps. -/
theorem probAvg_cpreRed_le
    (A : SufAdversary romWorld PublicKey SigningRequest (Option Signature) Forgery) {n k : ℕ}
    (hn : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge hashCharge) n)
    (hk : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge callCharge) k) :
    romWorld.probAvg ((cpre romWorld xmssChains noEval).game (cpreRed romWorld A)) ≤
      (((n + 873 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (gradeEta HashOutput (2 ^ 128)) ^ (2⁻¹ : ℝ) +
        (4 * (n * (n * kappaC Digest (2 ^ 128)))) ^ (2⁻¹ : ℝ) +
        (((873 : ℕ) : ℝ≥0∞) * kappaC Digest (2 ^ 128)) ^ (2⁻¹ : ℝ)) ^ 2 := by
  have h := probAvg_cpre_slRed_le (ch := xmssChains) noEval
    (fun P _ _ x _ ↦ xmssStep_lengthLe () P _ x) xmss_cellInj card_truncateHash_fiber_le
    (fun _ ↦ CpreRed.pre romWorld) (fun _ s0 ↦ A s0.2.2.1) (fun _ ↦ CpreRed.st0)
    (fun _ ↦ CpreRed.handler romWorld) (fun _ ↦ CpreRed.post romWorld) (fun _ _ ↦ 0)
    (c₀ := 0) (m := 0) (c₁ := 870) (fun _ l ↦ l.elim)
    (fun P ↦ cpreRed_onChallenge.1.mono_weight (redW_le_sumCost P))
    (fun P st q ↦ (cpreRed_onChallenge.2.1 st q).mono_weight (redW_le_sumCost P))
    (fun P s0 f st ↦ (cpreRed_onChallenge.2.2 s0 f st).mono_weight (redW_le_sumCost P))
    (fun s0 ↦ hn s0.2.2.1) (fun s0 ↦ hk s0.2.2.1)
  simp only [lenMax_xmssChains, zero_mul, zero_add] at h
  exact h

end Quantum.StdModel.Xmss

end
