import Sphincs.BridgeForsGame
import Sphincs.BridgeNoRepeatDef
import Sphincs.BridgeForsPotentialOnce

/-! The one-coin FORS potential through an adversary that never requests a signature on the same
message twice. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.ForsPotential

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForestPrice ForestSigner SphincsFors.Security.Domination

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable [Params]

section Induction

variable (parameter : PublicParameter) (data : PublicData) (wbar b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))
  (Qtot Lmax : ℕ) {A : Type} (tg : Targeting HashInput HashOutput Coordinate)
  (initial : HiddenOutside.Cache HashInput HashOutput) (model : HiddenRows.Model HashInput HashOutput A Coordinate)

theorem goodO_finish (hparse : ∀ p, model.parse (pblk parameter data p) = none)
    (hdigest : ∀ p, tg.digest (pblk parameter data p))
    {Cmax : ℕ} (hfair : FairS wbar Cmax Lmax) (hQ : Qtot ≤ Cmax) (L : QueryLog SigningSpec) (forgery : Forgery) :
    GoodO parameter data wbar b0 Fail Qtot Lmax tg initial model L (finishGame parameter data L forgery) := by
  unfold finishGame
  exact goodO_liftHash parameter data wbar b0 Fail Qtot Lmax tg initial model hparse hdigest hfair hQ L _ _
    fun v => goodO_pure parameter data wbar b0 Fail Qtot Lmax tg initial model hfair.le_one L forgery v

/-- **The one-coin potential of the scan signer through any adversary that never repeats a
message.** -/
theorem goodO_advProg (hparse : ∀ p, model.parse (pblk parameter data p) = none)
    (hdigest : ∀ p, tg.digest (pblk parameter data p))
    (hfail : ∀ m ρ digest budget (s1 : State), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    {Cmax : ℕ} (hfair : FairS wbar Cmax Lmax) (hQ : Qtot ≤ Cmax) :
    ∀ (M : OracleComp (OracleWorld + SigningSpec) Forgery) (L : QueryLog SigningSpec),
      NoRepeat M (L.map Sigma.fst) →
        GoodO parameter data wbar b0 Fail Qtot Lmax tg initial model L (advProg parameter data M L) := by
  intro M
  induction M using OracleComp.inductionOn with
  | pure forgery =>
      intro L _
      rw [advProg_pure]
      exact goodO_finish parameter data wbar b0 Fail Qtot Lmax tg initial model hparse hdigest hfair hQ L forgery
  | query_bind input next ih =>
      intro L hnr
      rcases input with (draw | bytes) | message
      · rw [advProg_draw]
        exact goodO_draw parameter data wbar b0 Fail Qtot Lmax tg initial model L draw _ fun v => ih v L (hnr v)
      · rw [advProg_hash]
        exact goodO_ordinary parameter data wbar b0 Fail Qtot Lmax tg initial model hparse hdigest hfair hQ L
          bytes _ fun v => ih v L (hnr v)
      · rw [advProg_sign]
        obtain ⟨hnot, hrest⟩ := (noRepeat_sign message next _).1 hnr
        have hm : MsgLive L message := by
          intro entry he heq
          exact hnot (heq ▸ List.mem_map_of_mem he)
        refine goodO_sign tg initial model parameter data wbar b0 Fail Qtot message Lmax hparse hfail hfair.le_one L hm _
          fun r => ih r _ ?_
        rw [List.map_append]
        exact hrest r

end Induction

end Sphincs.Security.ForsPotential
