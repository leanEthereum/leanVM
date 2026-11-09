/-
  LeanVM.Guest.B1.Place.OsCandB

  open_stacked is complete placed at every candidate, within its frame-size bound.
-/

module

public import LeanVM.Guest.B1.Place.OsCandAll
public import LeanVM.Guest.B1.Place.OsFinalB

/-!
# `open_stacked`, placed within its bound, at every candidate

**`open_stacked_completeAtB`** proves `open_stacked_completeAtB_Spec`: `open_stacked_completeAtD_Spec`
within `osBos fs (osBk fs Bnd Kr c) (openName μ r) c` words, `c` the candidate's configuration,
given the named callees' words bounds `Bnd` (`OsLeafBounds`, constants by name) and the residual
loops' words an iteration `Kr` (`OsLoopBounds`, G7-cnt's `LoopRunLe.totalLeOn`: and the run's one
phantom frame). The bound is the frame, the buffers, and for each call statement of the body the
larger of its callee's frame and bound (`osBk`: `Bnd`, each squeeze loop's `sqTot`, each
`opening_queries`' `oqBound`, each residual loop's `queries / 8 * Kr` and its frame).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- `open_stacked`'s frame-size bound at the candidate of `μ`, `r`. -/
def osBosAt (fs Bnd Kr : String → ℕ) (μ r : ℕ) : ℕ :=
  osBos fs (osBk fs Bnd Kr (osCfg (candidate μ r))) (openName μ r) (osCfg (candidate μ r))

/-- **`open_stacked` is complete placed at every candidate, within `osBosAt` words.** -/
def open_stacked_completeAtB_Spec : Prop :=
  ∀ (μ r : ℕ), 22 ≤ μ → μ ≤ 28 → 1 ≤ r → r ≤ 4 →
    ∀ (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (Bnd Kr : String → ℕ),
      Lift.RunsFit fs cert → RunsConsec cert → 7 ≤ κ → OsFitsAt fs cert (osCfg (candidate μ r)) →
      OsLeafBounds fs Bnd → OsLoopBounds fs Kr (osCfg (candidate μ r)) →
      ∀ (S : KeccakState) (root : Digest) (target cur : E) (xs : List E) (os : List (List Opening))
        (w : WhirEnd) (s' : Fs) (roots' : List (Digest × ℕ × ℕ)),
        RunsWith (whirOpen μ r target) ⟨capOf S, []⟩ xs os [(root, stackShape μ r)] w s' roots' →
        Whir.NoZeroChallenge μ r target S xs os root → Whir.CapsAgree μ r target S xs os root →
        ∀ Lin : Layout, (∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd cur xs) →
          CompleteAtB fs cert κ (openName μ r) Lin
            (capOf S ++ [target, (digestHalves root).1, (digestHalves root).2, cur]) (OsOut μ w)
            (osBosAt fs Bnd Kr μ r)

/-- **`open_stacked` is complete placed at every candidate, within `osBosAt` words.** -/
theorem open_stacked_completeAtB : open_stacked_completeAtB_Spec := by
  intro μ r h1 h2 h3 h4 fs cert κ Bnd Kr hk hcons hκ hfits hT hL S root target cur xs os w s'
    roots' hrun hnz hcaps Lin hLin
  have hm : candidate μ r < 28 := by unfold candidate; omega
  obtain ⟨cfg, hF, hnames, -⟩ := candB_sound (candB_all μ r h1 h2 h3 h4)
  have hdata := osData_all _ hm
  unfold osBosAt
  rw [openName_eq μ r hm]
  obtain ⟨fn, hf, hps, hb⟩ := hdata.1
  have hP : OsCfgPlaced fs cert (osCfg (candidate μ r)) := by
    refine cfgPlaced_of (placedP_all _ hm) (fun l hl ↦ hnames l hl) (fun l hl ↦ ?_) (fun l hl ↦ ?_) hfits
    · rw [osCfg_lvAt _ _ hl]; exact (hdata.2 l hl).1
    · rw [osCfg_lvAt _ _ hl]; exact (hdata.2 l hl).2
  exact os_completeAtB_cfg hk hcons hκ hF hP (osCalleeBounds_of hT hL) hf hps hb
    (osBody_notLoop hf hb) hrun hnz hcaps hLin

end
end LeanVM.Guest.B1
