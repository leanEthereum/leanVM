/-
  LeanVM.Guest.B1.Whir.Sound

  `open_stacked` is sound at every size and rate.
-/

module

public import LeanVM.Guest.B1.Whir.FactsSound
public import LeanVM.Guest.B1.Whir.FactsAll
public import LeanVM.Guest.B1.Whir.DataAll
public import LeanVM.Guest.B1.Whir.Names
public import LeanVM.Guest.B1.Whir.HsScale
public import LeanVM.Guest.B1.Bits.Grind
public import LeanVM.Guest.B1.Bits.QueryWindowsAll
public import LeanVM.Guest.B1.Merkle.CapAll
public import LeanVM.Guest.B1.Fs.MessageComplete
public import LeanVM.Guest.B1.Fs.SqueezePoint
public import LeanVM.Guest.B1.Fs.TailRound
public import LeanVM.Guest.B1.Eq.FoldFinal

/-!
# `open_stacked`, soundly (TRIAGE G #42)

`open_stacked_sound_w : open_stacked_sound_w_Spec open_stacked_osW` and
`open_stacked_sound : open_stacked_sound_Spec`: for every stack log `20 ≤ μ ≤ 30` and rate
`1 ≤ r ≤ 4`, a call of `open_stacked__L{μ - 20}` on the rate's selector establishes `OpenOut`
(at the witness's words and openings): the words it reads and the openings run the Spec's
`whirOpen μ r target` (the stacked WHIR opening up to its terminal check, `verifyWhir_split`), and
it returns the terminal's claim, point, glued weight and residual. From the size's core IR
(`osData_all`), its body at the rate's levels (`osBody_rate`), its checked facts at the rate
(`candB_all`), its semantic facts (`vanish_allR`, `hsScale_mid`, `hsScale_final`), B1-a's
callees, the helpers' tables and `open_generic`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier

@[expose] public section

theorem openName_eq {μ : ℕ} (h : μ - minOpenLog < ligNSizes) :
    openName μ = "open_stacked__L" ++ natStr (μ - minOpenLog) := by
  rw [openName, openNames, natStr_eq, List.getD_eq_getElem _ _ (by simpa using h)]
  simp

theorem osCfgR_levels_length (m ri : ℕ) : (osCfgR m ri).levels.length = osNLevels m := by
  simp [osCfgR, osLevelsR]

theorem osCfgR_levels_getD {m ri l : ℕ} (h : l < osNLevels m) :
    (osCfgR m ri).levels.getD l default = osLvR m ri l := by
  simp [osCfgR, osLevelsR, List.getD_eq_getElem?_getD, h]

/-- The deployed callees' meanings under a call relation below `coreProgram.Rel`, on a memory
image whose window tables are at `σ tabs`. -/
theorem callees_of {κ : ℕ} (hκ : κ ≤ 32) (hw : winTabBits ≤ κ) (L : MemoryImage κ) {C : CallRel}
    (hle : CallRel.Le C (coreProgram.Rel L.read)) {σ : Val} (hwt : WinTabs L.read (σ (.n osTabs))) :
    Callees L.read C σ := by
  refine ⟨fun a r ha hc ↦ opening_round_sound (grind_check_holds 7 (by decide)) hκ hw L a r ha
      (hle _ _ _ hc),
    fun p hp a r hc ↦ (opening_message_holds p hp L.read a r).mp (hle _ _ _ hc),
    fun n hn a r hc ↦ (squeeze_point_from_holds n hn L.read a r).mp (hle _ _ _ hc),
    fun w hc ↦ ?_, fun w hc ↦ ?_,
    fun p hp a r ha hc ↦ decode_query_windows_all_holds p hp hκ L a r ha hc,
    fun p hp a r hc ↦ (verify_merkle_cap_holds p hp L.read a r).mp (hle _ _ _ hc),
    fun a r hc ↦ (opening_tail_round_holds L.read a r).mp (hle _ _ _ hc),
    fun p hp a r hc ↦ (fold_final_msg_holds p hp L.read a r).mp (hle _ _ _ hc)⟩
  · have hn : "grind_check__L" ++ natStr queryGrind = grindCheckName 17 := by decide
    rw [hn] at hc
    exact ((grind_check_holds 17 (by decide) hκ hw L w _ hwt []).mp (hle _ _ _ hc)).2
  · have hn : "grind_check__L" ++ natStr levelOodGrind = grindCheckName 15 := by decide
    rw [hn] at hc
    exact ((grind_check_holds 15 (by decide) hκ hw L w _ hwt []).mp (hle _ _ _ hc)).2

/-- Size `m`'s semantic facts at rate `ri`: the rate changes none of the columns they read. -/
theorem semOk_of {m ri μ r : ℕ} (hm : m < ligNSizes) {cfg : List Whir.Level}
    (hC : CandOk m ri μ r cfg) : SemOk (osCfgR m ri) := by
  obtain ⟨-, -, -, -, hn2, hyr, -⟩ := hC
  have hlen := osCfgR_levels_length m ri
  refine ⟨fun l hl ↦ ?_, fun l hl c' hc ↦ ?_, fun i hi ↦ ?_⟩
  · rw [osCfgR_levels_getD (by omega)]; exact vanish_allR hm (by omega)
  · rw [osCfgR_levels_getD (by omega)] at hc ⊢; exact hsScale_mid hm (by omega) hc
  · have hy : (osCfgR m ri).yrLevel < osNLevels m := by
      have := (osCfgR m ri).levels.length; omega
    rw [osCfgR_levels_getD hy] at hi ⊢
    exact hsScale_final hm hi

/-- **`open_stacked` is sound with its witness named**, at every size and rate. -/
theorem open_stacked_sound_w : open_stacked_sound_w_Spec open_stacked_osW := by
  intro κ hκ hwb L C V hU hle μ r h1 h2 h3 h4 root fs target root0 root1 cur tabs rets fn σ hfs
    hroot hwt hfind hp hh
  set m := μ - minOpenLog with hmdef
  set ri := r - 1 with hridef
  have hm : m < ligNSizes := by simp only [m, minOpenLog, ligNSizes]; omega
  have hri : ri < 4 := by omega
  have hμ : μ = m + minOpenLog := by simp only [m, minOpenLog] at h1 ⊢; omega
  have hr : r = ri + 1 := by omega
  obtain ⟨cfg, hdc, hC⟩ := candB_sound (candB_all m ri hm hri)
  rw [← hμ, ← hr] at hdc hC
  have hd : FnIs ("open_stacked__L" ++ natStr m) (osParams 11) (osBody (osCfgR m ri)) := by
    have := osData_all m hm
    unfold OsData at this
    rwa [osBody_rate m ri] at this
  obtain ⟨fn', hf', hps, hbody⟩ := hd
  rw [openName_eq hm, hf'] at hfind
  cases hfind
  have hp' := hp
  rw [hps] at hp'
  obtain ⟨f0, f1, f2, f3, f4, rfl⟩ : ∃ f0 f1 f2 f3 f4, fs = [f0, f1, f2, f3, f4] := by
    match fs, hfs with
    | [f0, f1, f2, f3, f4], _ => exact ⟨f0, f1, f2, f3, f4, rfl⟩
  have h10 : σ (.n osTabs) = tabs := by
    have := congrArg (·.getD 10 0) hp'
    simpa [osParams] using this
  have h0 : σ (.n osRate) = ofK (addressOfIndex ri) := by
    have := congrArg (·.getD 0 0) hp'
    simpa [osParams, rateSel] using this
  have hcal := callees_of hκ hwb L hle (σ := σ) (by rw [h10]; exact hwt)
  have hsem := semOk_of hm hC
  have hFS := finStatic_of hcal hsem hle hC
  have hrate : ∀ i < (osCfgR m ri).levels.length,
      LvRate σ (osCfgR m ri) i ((osCfgR m ri).levels.getD i default) := fun i _ ↦
    ⟨ri, hri, h0, osCfgR_lvAt_length m ri i, osCfgR_lvAt_getD i hri⟩
  obtain ⟨hmu, hshape, hoff0, hlane, -, -, -, -, -, -, -, -, -, hlv⟩ := hC
  have hLOk := levelsOk_of (logN := μ) hcal hsem hle hrate 0 _ cfg List.drop_zero hlv
  exact open_generic hU hle hdc hmu hshape hoff0 hlane hLOk hFS hrate hps hbody (by rfl) hroot hwt
    hp hh

/-- **`open_stacked` is sound** at every size and rate. -/
theorem open_stacked_sound : open_stacked_sound_Spec := by
  intro κ hκ hwb L μ r h1 h2 h3 h4 root fs target root0 root1 cur tabs rets hfs hroot hwt hrel
  obtain ⟨fn, hf, σ, hp, hb⟩ := (rel_iff coreProgram _ _ _).mp hrel
  have h := open_stacked_sound_w hκ hwb L (coreProgram.Rel L.read) (relV L.read)
    (unfoldsV_rel L.read) (fun _ _ _ h ↦ h) μ r h1 h2 h3 h4 root fs target root0 root1 cur tabs rets
    fn σ hfs hroot hwt hf hp hb
  exact OpenOutW.openOut h

end
end LeanVM.Guest.B1.Whir
