/-
  LeanVM.Guest.B1.VerifySub.Dispatch

  `verify_sub`'s dispatch to `open_stacked` (G:3493-3499), with the opening's witness.
-/

module

public import LeanVM.Guest.B1.VerifySub.Template
public import LeanVM.Guest.B1.Whir.Sound
public import LeanVM.Guest.B1.Main.Frames

/-!
# The dispatch to `open_stacked`

* `OsSoundW C rd osW`: every `C`-call of a specialization `openName μ r` is `OpenOutW` at the
  words and openings `osW (candidate μ r) args rets`.
* `osSoundW_of`: on a memory below `2^32` words, under a call relation `C ≤ Rel` unfolding at `V`,
  the witness
  `open_stacked_osW rd m (V (openNames.getD m "") args rets) V` (B1-b's `open_stacked_sound_w`).
* `vs_dispatch`: the template's fused `match` on `g^candidate` calls the candidate's
  specialization, so its returns are `OpenOutW`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **`open_stacked`'s calls are sound with the witness `osW`.** -/
def OsSoundW (C : CallRel) (rd : Reader) (osW : ℕ → List E → List E → List E × List (List Opening)) :
    Prop :=
  ∀ μ r, 22 ≤ μ → μ ≤ 28 → 1 ≤ r → r ≤ 4 → ∀ (root : Digest) (fs : List E)
    (target root0 root1 cur : E) (rets : List E), fs.length = 5 →
    (root0, root1) = digestHalves root →
    C (B1.Whir.openName μ r) (fs ++ [target, root0, root1, cur]) rets →
    B1.Whir.OpenOutW rd μ r root fs target cur rets
      (osW (B1.Whir.candidate μ r) (fs ++ [target, root0, root1, cur]) rets).1
      (osW (B1.Whir.candidate μ r) (fs ++ [target, root0, root1, cur]) rets).2

/-- **The witness of `open_stacked`'s calls**, from the frame map (B1-b's `open_stacked_sound_w`). -/
theorem osSoundW_of {κ : ℕ} (hκ : κ ≤ 32) {L : MemoryImage κ} {C : CallRel} {V : FrameMap}
    (hU : UnfoldsV L.read C V) (hLe : CallRel.Le C (coreProgram.Rel L.read)) :
    OsSoundW C L.read (fun m args rets ↦
      B1.Whir.open_stacked_osW L.read m (V (B1.Whir.openNames.getD m "") args rets) V) := by
  intro μ r hμ1 hμ2 hr1 hr2 root fs target root0 root1 cur rets hfs hroot hc
  obtain ⟨fn, hfind, hpar, hbody⟩ := hU _ _ _ hc
  exact B1.Whir.open_stacked_sound_w hκ L C V hU hLe μ r hμ1 hμ2 hr1 hr2 root fs target root0
    root1 cur rets fn _ hfs hroot hfind hpar hbody

theorem candidate_lt {μ r : ℕ} (hμ2 : μ ≤ 28) (hr1 : 1 ≤ r) (hr2 : r ≤ 4) :
    B1.Whir.candidate μ r < 28 := by
  unfold B1.Whir.candidate; omega

/-- **The dispatch** (G:3493-3499): the fused `match` on `g^candidate` calls the candidate's
specialization of `open_stacked`, whose returns are `OpenOutW` at the witness. -/
theorem vs_dispatch {C : CallRel} {rd : Reader} {σ : Val}
    {osW : ℕ → List E → List E → List E × List (List Opening)} (hos : OsSoundW C rd osW) {μ r : ℕ}
    (hμ1 : 22 ≤ μ) (hμ2 : μ ≤ 28) (hr1 : 1 ≤ r) (hr2 : r ≤ 4)
    (h1901 : σ (.n 1695) = gen ^ B1.Whir.candidate μ r)
    (hd : ∃ (j : ℕ) (hj : j < vsOpenNames.length), σ (.n 1695) = ofK (addressOfIndex j) ∧
      C vsOpenNames[j] [σ (.n 1100), σ (.n 1101), σ (.n 1102), σ (.n 1103), σ (.n 1104),
        σ (.n 1681), σ (.n 324), σ (.n 334), σ (.n 656)]
        [σ (.n 1700), σ (.n 1701), σ (.n 1702), σ (.n 1703), σ (.n 1704)])
    {root : Digest} (hroot : (σ (.n 324), σ (.n 334)) = digestHalves root) :
    B1.Whir.OpenOutW rd μ r root [σ (.n 1100), σ (.n 1101), σ (.n 1102), σ (.n 1103), σ (.n 1104)]
      (σ (.n 1681)) (σ (.n 656)) [σ (.n 1700), σ (.n 1701), σ (.n 1702), σ (.n 1703), σ (.n 1704)]
      (osW (B1.Whir.candidate μ r) [σ (.n 1100), σ (.n 1101), σ (.n 1102), σ (.n 1103),
        σ (.n 1104), σ (.n 1681), σ (.n 324), σ (.n 334), σ (.n 656)]
        [σ (.n 1700), σ (.n 1701), σ (.n 1702), σ (.n 1703), σ (.n 1704)]).1
      (osW (B1.Whir.candidate μ r) [σ (.n 1100), σ (.n 1101), σ (.n 1102), σ (.n 1103),
        σ (.n 1104), σ (.n 1681), σ (.n 324), σ (.n 334), σ (.n 656)]
        [σ (.n 1700), σ (.n 1701), σ (.n 1702), σ (.n 1703), σ (.n 1704)]).2 := by
  obtain ⟨j, hj, hj1901, hc⟩ := hd
  have hlen : vsOpenNames.length = 28 := by simp [vsOpenNames]
  have hcand := candidate_lt hμ2 hr1 hr2
  have hjc : j = B1.Whir.candidate μ r := by
    rw [h1901, gen_pow_eq_ofK] at hj1901
    exact (gen_pow_inj (by omega) (by omega)
      (by rw [gen_pow_eq_ofK, gen_pow_eq_ofK]; exact hj1901.symm))
  subst hjc
  have hname : vsOpenNames[B1.Whir.candidate μ r] = B1.Whir.openName μ r := by
    rw [B1.Whir.openName, List.getD_eq_getElem _ _ (by rw [← vsOpenNames_eq]; omega)]
    simp only [vsOpenNames_eq]
  rw [hname] at hc
  exact hos μ r hμ1 hμ2 hr1 hr2 root [σ (.n 1100), σ (.n 1101), σ (.n 1102), σ (.n 1103),
    σ (.n 1104)] (σ (.n 1681)) (σ (.n 324)) (σ (.n 334)) (σ (.n 656)) _ rfl hroot hc

/-! ## The stack's configuration -/

theorem cfg_cons {μ r : ℕ} (h1 : 22 ≤ μ) (h2 : μ ≤ 28) (h3 : 1 ≤ r) (h4 : r ≤ 4) :
    ∃ level rest, Whir.ladder μ r = some (level :: rest) := by
  obtain ⟨cfg, hF, -, -⟩ := B1.Whir.candB_sound (B1.Whir.candB_all μ r h1 h2 h3 h4)
  rcases cfg with _ | ⟨level, rest⟩
  · exfalso
    have hl := hF.lok
    have hn := hF.n2
    generalize (B1.Whir.osCfg (B1.Whir.candidate μ r)).levels = lvs at hl hn
    match lvs, hn with
    | _ :: _ :: _, _ => simp [B1.Whir.LevelsOk] at hl
  · exact ⟨level, rest, hF.dc⟩

end
end LeanVM.Guest.B1.VerifySub
