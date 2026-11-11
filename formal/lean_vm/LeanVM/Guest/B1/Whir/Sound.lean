/-
  LeanVM.Guest.B1.Whir.Sound

  `open_stacked` is sound at every candidate.
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
`open_stacked_sound : open_stacked_sound_Spec`: for every stack log `22 ≤ μ ≤ 28` and rate
`1 ≤ r ≤ 4`, a call of `open_stacked__L{candidate μ r}` establishes `OpenOut` (at the witness's
words and openings): the words it reads and the openings run the Spec's `whirOpen μ r target`
(the stacked WHIR opening up to its terminal check, `verifyWhir_split`), and it returns the
terminal's claim, point, glued weight and residual. From the candidate's core IR (`osData_all`),
its checked facts (`candB_all`, `qcallsB_all`), its semantic facts (`vanish_all`, `hsScale_mid`,
`hsScale_final`), B1-a's callees and `open_generic`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier

@[expose] public section

theorem openName_eq (μ r : ℕ) (h : candidate μ r < 28) :
    openName μ r = "open_stacked__L" ++ natStr (candidate μ r) := by
  rw [openName, openNames, natStr_eq, List.getD_eq_getElem _ _ (by simpa using h)]
  simp

theorem osCfg_levels_length (m : ℕ) : (osCfg m).levels.length = osNLevels m := by
  simp [osCfg]

theorem osCfg_levels_getD {m l : ℕ} (h : l < osNLevels m) :
    (osCfg m).levels.getD l default = osLv m l := by
  simp [osCfg, List.getD_eq_getElem?_getD, h]

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

/-- Candidate `m`'s semantic facts. -/
theorem semOk_of {m : ℕ} (hm : m < 28) (hd : OsData m) {μ r : ℕ} {cfg : List Whir.Level}
    (hC : CandOk m μ r cfg) : SemOk (osCfg m) := by
  obtain ⟨-, -, -, -, hn2, hyr, -, -, -, -, -, -, -⟩ := hC
  have hlen := osCfg_levels_length m
  refine ⟨fun l hl ↦ ?_, fun l hl c' hc ↦ ?_, fun i hi ↦ ?_, fun l hl ↦ ?_, fun l hl ↦ ?_⟩
  · rw [osCfg_levels_getD (by omega)]; exact vanish_all m hm l (by omega)
  · rw [osCfg_levels_getD (by omega)] at hc ⊢; exact hsScale_mid hm (by omega) hc
  · have hy : (osCfg m).yrLevel < osNLevels m := by
      have := (osCfg m).levels.length; omega
    rw [osCfg_levels_getD hy] at hi ⊢
    exact hsScale_final hm hi
  · rw [osCfg_levels_getD (by omega)]; exact hd.2.1 l (by omega)
  · rw [osCfg_levels_getD (by omega)]; exact hd.2.2 l hl

/-- **`open_stacked` is sound with its witness named**, at every candidate. -/
theorem open_stacked_sound_w : open_stacked_sound_w_Spec open_stacked_osW := by
  intro κ hκ hwb L C V hU hle μ r h1 h2 h3 h4 root fs target root0 root1 cur tabs rets fn σ hfs
    hroot hwt hfind hp hh
  have hm : candidate μ r < 28 := by unfold candidate; omega
  obtain ⟨cfg, hdc, hC⟩ := candB_sound (candB_all μ r h1 h2 h3 h4)
  have hq : osQCalls (osCfg (candidate μ r)) =
      osQCallsL (osCfg (candidate μ r)) 0 (osCfg (candidate μ r)).levels
        (osHead (osCfg (candidate μ r))).2 := by
    have h := qcallsB_all _ hm
    unfold qcallsB at h
    exact of_decide_eq_true h
  have hd := osData_all _ hm
  obtain ⟨fn', hf', hps, hbody⟩ := hd.1
  rw [openName_eq μ r hm, hf'] at hfind
  cases hfind
  have hp' := hp
  rw [hps] at hp'
  obtain ⟨f0, f1, f2, f3, f4, rfl⟩ : ∃ f0 f1 f2 f3 f4, fs = [f0, f1, f2, f3, f4] := by
    match fs, hfs with
    | [f0, f1, f2, f3, f4], _ => exact ⟨f0, f1, f2, f3, f4, rfl⟩
  have h9 : σ (.n osTabs) = tabs := by
    have := congrArg (·.getD 9 0) hp'
    simpa [osParams] using this
  have hcal := callees_of hκ hwb L hle (σ := σ) (by rw [h9]; exact hwt)
  have hsem := semOk_of hm hd hC
  have hFS := finStatic_of hcal hsem hC
  obtain ⟨hmu, hshape, hoff0, hlane, -, -, -, -, -, -, -, -, hlv⟩ := hC
  have hLOk := levelsOk_of (logN := μ) hcal hsem hle 0 _ cfg List.drop_zero hlv
  have h := open_generic (V := V) hU hle hdc hmu hshape hoff0 hlane hLOk hFS hps hbody hfs hroot hwt hp hh
  have hops : (open_stacked_osW L.read (candidate μ r) σ V).2 =
      osLevelsW L.read V σ (osCfg (candidate μ r)) 0 (osCfg (candidate μ r)).levels
        (osHead (osCfg (candidate μ r))).2 := by
    rw [← osQCallsL_openings V (osCfg (candidate μ r)) (fun l ↦ (osCfg (candidate μ r)).levels.getD l default)
      _ 0 _ fun i _ ↦ by rw [Nat.zero_add], ← hq]
    simp only [open_stacked_osW]
  have hosW : open_stacked_osW L.read (candidate μ r) σ V =
      (osReadN L.read (σ (.n 8)) (osWordsLen (osCfg (candidate μ r))),
        osLevelsW L.read V σ (osCfg (candidate μ r)) 0 (osCfg (candidate μ r)).levels
          (osHead (osCfg (candidate μ r))).2) := Prod.ext rfl hops
  rw [hosW]
  exact h

/-- **`open_stacked` is sound** at every candidate. -/
theorem open_stacked_sound : open_stacked_sound_Spec := by
  intro κ hκ hwb L μ r h1 h2 h3 h4 root fs target root0 root1 cur tabs rets hfs hroot hwt hrel
  obtain ⟨fn, hf, σ, hp, hb⟩ := (rel_iff coreProgram _ _ _).mp hrel
  have h := open_stacked_sound_w hκ hwb L (coreProgram.Rel L.read) (relV L.read)
    (unfoldsV_rel L.read) (fun _ _ _ h ↦ h) μ r h1 h2 h3 h4 root fs target root0 root1 cur tabs rets
    fn σ hfs hroot hwt hf hp hb
  exact OpenOutW.openOut h

end
end LeanVM.Guest.B1.Whir
