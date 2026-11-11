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

* `OsSoundW C rd osW`: every `C`-call of a specialization `openName μ` on the rate's selector
  `rateSel r` is `OpenOutW` at the words and openings `osW (μ - 20) r args rets`.
* `osSoundW_of`: on a memory below `2^32` words, under a call relation `C ≤ Rel` unfolding at `V`,
  the witness `open_stacked_osW rd m r (V (openNames.getD m "") args rets) V` (B1-b's
  `open_stacked_sound_w`).
* `vs_dispatch`: the template's `match` on `g^(μ - 20)` calls the size's specialization with
  the rate's selector, so its returns are `OpenOutW`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- `open_stacked`'s witness functions: the size's index, the rate, the arguments and the returns
give the stream words and the openings. -/
abbrev OsWit : Type := ℕ → ℕ → List E → List E → List E × List (List Opening)

/-- **`open_stacked`'s calls are sound with the witness `osW`.** -/
def OsSoundW (C : CallRel) (rd : Reader) (osW : OsWit) : Prop :=
  ∀ μ r, B1.Whir.minOpenLog ≤ μ → μ ≤ 30 → 1 ≤ r → r ≤ 4 → ∀ (root : Digest) (fs : List E)
    (target root0 root1 cur : E) (rets : List E), fs.length = 5 →
    (root0, root1) = digestHalves root →
    C (B1.Whir.openName μ) (B1.Whir.rateSel r :: fs ++ [target, root0, root1, cur]) rets →
    B1.Whir.OpenOutW rd μ r root fs target cur rets
      (osW (μ - B1.Whir.minOpenLog) r (B1.Whir.rateSel r :: fs ++ [target, root0, root1, cur])
        rets).1
      (osW (μ - B1.Whir.minOpenLog) r (B1.Whir.rateSel r :: fs ++ [target, root0, root1, cur])
        rets).2

/-- **The witness of `open_stacked`'s calls**, from the frame map (B1-b's `open_stacked_sound_w`). -/
theorem osSoundW_of {κ : ℕ} (hκ : κ ≤ 32) {L : MemoryImage κ} {C : CallRel} {V : FrameMap}
    (hU : UnfoldsV L.read C V) (hLe : CallRel.Le C (coreProgram.Rel L.read)) :
    OsSoundW C L.read (fun m r args rets ↦
      B1.Whir.open_stacked_osW L.read m r (V (B1.Whir.openNames.getD m "") args rets) V) := by
  intro μ r hμ1 hμ2 hr1 hr2 root fs target root0 root1 cur rets hfs hroot hc
  obtain ⟨fn, hfind, hpar, hbody⟩ := hU _ _ _ hc
  exact B1.Whir.open_stacked_sound_w hκ L C V hU hLe μ r hμ1 hμ2 hr1 hr2 root fs target root0
    root1 cur rets fn _ hfs hroot hfind hpar hbody

theorem vsOpenNames_length : vsOpenNames.length = 11 := by simp [vsOpenNames]

/-- **The dispatch** (G:3542-3544): the `match` on `g^(μ - 20)` calls the size's specialization
of `open_stacked` on the rate's selector, whose returns are `OpenOutW` at the witness. -/
theorem vs_dispatch {C : CallRel} {rd : Reader} {σ : Val} {osW : OsWit} (hos : OsSoundW C rd osW)
    {μ r : ℕ} (hμ1 : B1.Whir.minOpenLog ≤ μ) (hμ2 : μ ≤ 30) (hr1 : 1 ≤ r) (hr2 : r ≤ 4)
    (h1686 : σ (.n 1686) = gen ^ (μ - B1.Whir.minOpenLog)) (h122 : σ (.n 122) = B1.Whir.rateSel r)
    (hd : ∃ (j : ℕ) (hj : j < vsOpenNames.length), σ (.n 1686) = ofK (addressOfIndex j) ∧
      C vsOpenNames[j] [σ (.n 122), σ (.n 1100), σ (.n 1101), σ (.n 1102), σ (.n 1103),
        σ (.n 1104), σ (.n 1681), σ (.n 324), σ (.n 334), σ (.n 656)]
        [σ (.n 1691), σ (.n 1692), σ (.n 1693), σ (.n 1694), σ (.n 1695)])
    {root : Digest} (hroot : (σ (.n 324), σ (.n 334)) = digestHalves root) :
    B1.Whir.OpenOutW rd μ r root [σ (.n 1100), σ (.n 1101), σ (.n 1102), σ (.n 1103), σ (.n 1104)]
      (σ (.n 1681)) (σ (.n 656)) [σ (.n 1691), σ (.n 1692), σ (.n 1693), σ (.n 1694), σ (.n 1695)]
      (osW (μ - B1.Whir.minOpenLog) r [σ (.n 122), σ (.n 1100), σ (.n 1101), σ (.n 1102),
        σ (.n 1103), σ (.n 1104), σ (.n 1681), σ (.n 324), σ (.n 334), σ (.n 656)]
        [σ (.n 1691), σ (.n 1692), σ (.n 1693), σ (.n 1694), σ (.n 1695)]).1
      (osW (μ - B1.Whir.minOpenLog) r [σ (.n 122), σ (.n 1100), σ (.n 1101), σ (.n 1102),
        σ (.n 1103), σ (.n 1104), σ (.n 1681), σ (.n 324), σ (.n 334), σ (.n 656)]
        [σ (.n 1691), σ (.n 1692), σ (.n 1693), σ (.n 1694), σ (.n 1695)]).2 := by
  obtain ⟨j, hj, hj1686, hc⟩ := hd
  have hj11 : j < 11 := vsOpenNames_length ▸ hj
  have hjc : j = μ - B1.Whir.minOpenLog := by
    rw [h1686, gen_pow_eq_ofK] at hj1686
    exact (gen_pow_inj (by omega) (by omega)
      (by rw [gen_pow_eq_ofK, gen_pow_eq_ofK]; exact hj1686.symm))
  have hname : vsOpenNames[j] = B1.Whir.openName μ := by
    rw [B1.Whir.openName, List.getD_eq_getElem _ _ (by rw [← vsOpenNames_eq, vsOpenNames_length]; omega)]
    simp only [vsOpenNames_eq, hjc]
  replace hc := (congrArg (fun n ↦ C n _ _) hname).mp hc
  subst hjc
  rw [h122] at hc ⊢
  exact hos μ r hμ1 hμ2 hr1 hr2 root [σ (.n 1100), σ (.n 1101), σ (.n 1102), σ (.n 1103),
    σ (.n 1104)] (σ (.n 1681)) (σ (.n 324)) (σ (.n 334)) (σ (.n 656)) _ rfl hroot hc

/-! ## The stack's configuration -/

theorem cfg_cons {μ r : ℕ} (h1 : B1.Whir.minOpenLog ≤ μ) (h2 : μ ≤ 30) (h3 : 1 ≤ r) (h4 : r ≤ 4) :
    ∃ level rest, Whir.ladder μ r = some (level :: rest) := by
  have hadm : Whir.Admissible μ r := ⟨by unfold Whir.minLogStack B1.Whir.minOpenLog at *; omega,
    h2, h3, h4⟩
  obtain ⟨cfg, hcfg⟩ := Option.isSome_iff_exists.1 (Whir.ladder_isSome hadm)
  have hl := Whir.ladder_length hadm cfg hcfg
  match cfg, hl with
  | level :: rest, _ => exact ⟨level, rest, hcfg⟩

end
end LeanVM.Guest.B1.VerifySub
