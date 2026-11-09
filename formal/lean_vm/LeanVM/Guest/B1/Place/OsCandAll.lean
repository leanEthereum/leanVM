/-
  LeanVM.Guest.B1.Place.OsCandAll

  open_stacked is complete placed at every candidate.
-/

module

public import LeanVM.Guest.B1.Place.OsCandP0
public import LeanVM.Guest.B1.Place.OsCandP1
public import LeanVM.Guest.B1.Place.OsCandP2
public import LeanVM.Guest.B1.Place.OsCandP3
public import LeanVM.Guest.B1.Whir.Sound

/-!
# `open_stacked`, placed, at every candidate

`placedP_all`: every candidate's decided placed facts. **`open_stacked_completeAtD`** proves
`open_stacked_completeAtD_Spec`: for every stack log `μ ∈ [22, 28]` and rate `r ∈ [1, 4]`, with the
frame runs fitting their frames, their cells consecutive (`Lift.RunsFit`, `RunsConsec`), on
memories defined below `2^κ`, `7 ≤ κ` (`decode_query_windows`' range checks), and the frame
certificates of the candidate's `opening_queries` frames (`OsFitsAt`, now `True`), on every
accepting run of `whirOpen μ r target` from `⟨capOf S, []⟩` with no zero challenge and openings
that agree in the caps, the words at the cursor among the caller's words, the candidate's
specialization is complete placed (`CompleteAtD`), returning the run's claim, its two point
buffers' pointers, its glued weight and its residual's value, the buffers the run's point
zero-padded and one plus each coordinate one-padded (`OsOut`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- **Every candidate's decided placed facts.** -/
theorem placedP_all (m : ℕ) (h : m < 28) : PlacedP (osCfg m) := by
  interval_cases m
  · exact placedP_0
  · exact placedP_1
  · exact placedP_2
  · exact placedP_3
  · exact placedP_4
  · exact placedP_5
  · exact placedP_6
  · exact placedP_7
  · exact placedP_8
  · exact placedP_9
  · exact placedP_10
  · exact placedP_11
  · exact placedP_12
  · exact placedP_13
  · exact placedP_14
  · exact placedP_15
  · exact placedP_16
  · exact placedP_17
  · exact placedP_18
  · exact placedP_19
  · exact placedP_20
  · exact placedP_21
  · exact placedP_22
  · exact placedP_23
  · exact placedP_24
  · exact placedP_25
  · exact placedP_26
  · exact placedP_27

/-- **`open_stacked` is complete placed at every candidate.** -/
def open_stacked_completeAtD_Spec : Prop :=
  ∀ (μ r : ℕ), 22 ≤ μ → μ ≤ 28 → 1 ≤ r → r ≤ 4 →
    ∀ (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ), Lift.RunsFit fs cert →
      RunsConsec cert → 7 ≤ κ → OsFitsAt fs cert (osCfg (candidate μ r)) →
      ∀ (S : KeccakState) (root : Digest) (target cur : E) (xs : List E) (os : List (List Opening))
        (w : WhirEnd) (s' : Fs) (roots' : List (Digest × ℕ × ℕ)),
        RunsWith (whirOpen μ r target) ⟨capOf S, []⟩ xs os [(root, stackShape μ r)] w s' roots' →
        Whir.NoZeroChallenge μ r target S xs os root → Whir.CapsAgree μ r target S xs os root →
        ∀ Lin : Layout, (∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd cur xs) →
          CompleteAtD fs cert κ (openName μ r) Lin
            (capOf S ++ [target, (digestHalves root).1, (digestHalves root).2, cur]) (OsOut μ w)

theorem osCfg_lvAt (m i : ℕ) (h : i < (osCfg m).levels.length) : lvAt (osCfg m) i = osLv m i := by
  rw [lvAt, lv_getD h, osCfg_levels_getElem _ _ h]

/-- **`open_stacked` is complete placed at every candidate.** -/
theorem open_stacked_completeAtD : open_stacked_completeAtD_Spec := by
  intro μ r h1 h2 h3 h4 fs cert κ hk hcons hκ hfits S root target cur xs os w s' roots' hrun hnz
    hcaps Lin hLin
  have hm : candidate μ r < 28 := by unfold candidate; omega
  obtain ⟨cfg, hF, hnames, -⟩ := candB_sound (candB_all μ r h1 h2 h3 h4)
  have hdata := osData_all _ hm
  rw [openName_eq μ r hm]
  obtain ⟨fn, hf, hps, hb⟩ := hdata.1
  have hP : OsCfgPlaced fs cert (osCfg (candidate μ r)) := by
    refine cfgPlaced_of (placedP_all _ hm) (fun l hl ↦ hnames l hl) (fun l hl ↦ ?_) (fun l hl ↦ ?_) hfits
    · rw [osCfg_lvAt _ _ hl]; exact (hdata.2 l hl).1
    · rw [osCfg_lvAt _ _ hl]; exact (hdata.2 l hl).2
  exact os_completeAtD_cfg hk hcons hκ hF hP hf hps hb (osBody_notLoop hf hb) hrun hnz hcaps hLin

end
end LeanVM.Guest.B1
