module

public import FORS.SmallBudget.Contact.PotentialH
public import FORS.LargeBudget.HonestCoupling
public import FORS.CoverPotential.OneCoinH

@[expose] public section

/-! **The honest signing call pays the contact potential and keeps its invariants.** The honest
signer is the honest form of the charged one (`signCostSourceH_eq`), so its result, reveals and
final state are distributed as the charged signer's at a budget the charged signer cannot exhaust,
and its trace is empty (no budget spent). The charged payment at that budget, with the potential's
budget left whole (`psiF_sign_at`), is then the honest payment (`psiF_sign`), and the charged
invariants through the call give the honest ones (`signInvH`), the count kept for the messages
still live. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.ForsPotential

variable [Params]

open FORS.Base
open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner HiddenBridge
open PotentialA

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false
attribute [local instance] Classical.propDecidable

section SignPaysH

variable (K : Ctx) (data : PublicData) (wbar κ : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight))) (Qtot : ℕ)
  (model : HiddenRows.Model HashInput HashOutput Address Coordinate)
  (hMp : model.parse = HiddenGraph.parse K.p (candidateActive K.p))
  (hMi : model.incoming = Address.inputCoordinate) (hMo : model.outgoing = Address.outputCoordinate)

include hMp hMi hMo in
/-- **An honest signing call on a fresh message pays the contact potential.** -/
theorem psiF_sign (hparse : ∀ p call, model.parse (pblk K.p data p call) = none)
    (hmsg : ∀ x, IsMsgInput x → K.tg.kind x = .none)
    (hfail : ∀ m ρ digest budget (s1 : State), Prepared K.initial s1 →
      ∀ out ∈ support (interp K.tg K.initial model (finishRest K.p data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    (hw : wbar ≤ 1) (Lmax : ℕ) :
    SignPaysF K data Qtot model (psiF K data wbar κ Fail Lmax) := by
  intro budget s P Ms L d R hB m hm
  set G : (Option (Option Signature) × List Coordinate) × State → ℝ≥0∞ := fun p =>
    p.1.1.elim 0 (fun r => psiF K data wbar κ Fail Lmax p.2 (newPairs K.p data m s p.2 ++ P) (addMsg Ms m)
      (L ++ [⟨m, r⟩]) (discAfter K.p data m s d ((p.1.1, p.1.2, [], []), p.2)) (R ++ p.1.2) budget) with hG
  have hGproj : ∀ o1 : Run HashInput Coordinate (Option Signature) × State,
      G (runProj o1) = o1.1.1.elim 0 (fun r => psiF K data wbar κ Fail Lmax o1.2 (newPairs K.p data m s o1.2 ++ P)
        (addMsg Ms m) (L ++ [⟨m, r⟩]) (discAfter K.p data m s d o1) (R ++ o1.1.2.1) budget) := fun o1 => by
    simp only [hG, runProj, discAfter_congr (o := ((o1.1.1, o1.1.2.1, [], []), o1.2)) (o' := o1) rfl rfl]
  rw [signCostSourceH_eq]
  obtain ⟨B, -, hsum⟩ := tsum_interp_toHonest K.tg K.initial model (signCostSource K.p data m) G budget s
  calc _ = ∑' o1, Pr{let x ← (interp K.tg K.initial model (simulateQ toHonest (signCostSource K.p data m))
          budget s)}[x = o1] * G (runProj o1) := by
        refine tsum_congr fun o1 => ?_
        by_cases ho1 : o1 ∈ support (interp K.tg K.initial model (simulateQ toHonest (signCostSource K.p data m))
          budget s)
        · obtain ⟨htr, -⟩ := interp_toHonest_quiet K.tg K.initial model _ budget s o1 ho1
          rw [hGproj, htr]
          simp [traceCost]
        · rw [(prEvent_eq_zero_of_not_mem_support _) ho1, zero_mul, zero_mul]
    _ = ∑' o1, Pr{let x ← interp K.tg K.initial model (signCostSource K.p data m) B s}[x = o1] *
          G (runProj o1) := hsum
    _ ≤ _ := by
        simp only [hGproj]
        have hBc : BInvF K data (Fintype.card Randomness + B) model s P Ms d R B :=
          ⟨hB.inv, hB.pinv, hB.minv, hB.dinv, countInv_card K.p data s B, hB.gc, hB.rinv⟩
        exact psiF_sign_at K data wbar κ Fail _ model hMp hMi hMo hparse hmsg hfail hw Lmax B budget
          (fun _ => budget) (fun _ => le_rfl) hBc m hm

end SignPaysH

/-! ### The invariants through an honest signing call -/

section SignInvH

variable {K : Ctx} {data : PublicData} {Qtot : ℕ} {model : HiddenRows.Model HashInput HashOutput Address Coordinate}

/-- **An honest signing call on a fresh message keeps the invariants**, at the same budget: the
charged call's at a budget it cannot exhaust, the count kept for the messages still live (the
others' cached digest entries do not move). -/
theorem signInvH (hMp : model.parse = HiddenGraph.parse K.p (candidateActive K.p))
    (hMi : model.incoming = Address.inputCoordinate)
    (hparse : ∀ p call, model.parse (pblk K.p data p call) = none) : SignInvH K data Qtot model := by
  intro budget s P Ms L d R hB m hm o1 ho1 r hres
  rw [signCostSourceH_eq] at ho1
  obtain ⟨htr, -⟩ := interp_toHonest_quiet K.tg K.initial model _ budget s o1 ho1
  have hbud : budget - traceCost o1.1.2.2.1 = budget := by rw [htr]; simp [traceCost]
  obtain ⟨B, hBc⟩ := exists_costAtMost (signCostSource K.p data m)
  obtain ⟨o1', ho1', hpr⟩ := mem_support_interp_toHonest K.tg K.initial model _ B hBc budget s o1 ho1
  have h11 : o1'.1.1 = o1.1.1 := congrArg (fun p => p.1.1) hpr
  have h121 : o1'.1.2.1 = o1.1.2.1 := congrArg (fun p => p.1.2) hpr
  have h2 : o1'.2 = o1.2 := congrArg (fun p => p.2) hpr
  have hB' : BInvF K data (Fintype.card Randomness + B) model s P Ms d R B :=
    ⟨hB.inv, hB.pinv, hB.minv, hB.dinv, countInv_card K.p data s B, hB.gc, hB.rinv⟩
  have hF := binvF_sign hMp hMi hparse m B hB' o1' ho1' r (h11.trans hres)
  rw [h2, h121, discAfter_congr h11 h2] at hF
  rw [hbud]
  refine ⟨hF.inv, hF.pinv, hF.minv, hF.dinv, fun m' hm' => ?_, hF.gc, hF.rinv⟩
  have hne : m' ≠ m := fun he => hm' ⟨m, r⟩ (List.mem_append_right _ (List.mem_singleton_self _)) he.symm
  have hlive : MsgLive L m' := fun e he => hm' e (List.mem_append_left _ he)
  have hkeep : cachedCount K.p data m' o1.2 = cachedCount K.p data m' s := by
    unfold cachedCount
    refine congrArg Finset.card (Finset.filter_congr fun ρ _ => ?_)
    have hk := other_message_keptS K.tg K.initial model B s o1' ho1' (m', ρ) hne firstCall
    rw [h2] at hk
    exact Iff.of_eq (congrArg (· ≠ none) hk)
  have := hB.count m' hlive
  omega

end SignInvH

end FORS.Security.ForsPotential
