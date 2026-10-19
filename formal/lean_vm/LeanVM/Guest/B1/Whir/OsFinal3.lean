/-
  LeanVM.Guest.B1.Whir.OsFinal3

  `open_stacked` at a configuration is complete, placed: `CompleteOpenAt`'s shape.
-/

module

public import LeanVM.Guest.B1.Whir.OsFinal2

/-!
# `open_stacked`, placed (TRIAGE #36)

`os_completeOpenAt`: a function whose body is `osBody cfg`, at a configuration whose facts match
the ladder of `(μ, r)` (`OsCfgOk`), whose compiled body has the decided facts `OsBodyFacts` and
whose callees are complete (`OsKidsAt`), is complete on every run of `whinOpen μ r target` whose
queries agree at the caps: it returns the run's claim, the pointer to its point buffer, its glued
weight and its residual's value, the buffer the run's point zero-padded.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ}

theorem os_holdsList_of_eq {C : CallRel} {rd : Reader} {σ : Val} {l l' : List Stmt} {next : Prop}
    {kret : List E → Prop} (he : l = l') (h : Stmt.HoldsList C rd σ l' next kret) : Stmt.HoldsList C rd σ l next kret :=
  he ▸ h

set_option maxHeartbeats 1000000 in
/-- **`open_stacked` at a configuration is complete, placed.** -/
theorem os_completeOpenAt {cfg : OsCfg} {μ r : ℕ} {Lall : List Whir.Level} (hok : OsCfgOk cfg μ r Lall)
    (hbf : OsBodyFacts cfg) (hk : OsKidsAt fs cert κ cfg) (hcal : ∀ rd, OsCallees rd cfg) {name : String} {fn : Fn}
    (hfind : coreProgram.find? name = some fn) (hp : fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5])
    (hb : fn.body = osBody cfg) (hloop : coreProgram.loop name = false) {root cv : Digest} {xs : List E}
    {os : List Opening} {w : WhirEnd} {cv' : Digest} {roots' : List (Digest × ℕ × ℕ)} {target : E} {c : ℕ}
    {Lin : Main.Layout} (hrun : RunsWith (whirOpen μ r target) cv xs os [(root, stackShape μ r)] w cv' roots')
    (hcap : CapAgrees μ r root cv xs os target)
    (hLin : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd (ofK (Parameters.gpow c)) xs) :
    CompleteAtD fs cert κ name Lin [(digestScalars cv).1, (digestScalars cv).2, target, (digestScalars root).1,
      (digestScalars root).2, ofK (Parameters.gpow c)] fun rets Lout =>
      ∃ b, rets = [w.target, ofK (Parameters.gpow b), w.inner, w.residual] ∧
        Lout = [(b, w.point ++ List.replicate (pointCap - w.point.length) 0)] := by
  obtain ⟨d, hx, hcv, htg, hrt, hkit⟩ := os_kit_of_run hok hrun hcap
  subst hx hcv htg hrt
  have hn := hok.len2
  obtain ⟨sp', Q', hQ, hch⟩ := hkit.chain
  have hrunOk := d.runOk_of hok hkit.len hch hkit.chst
  have hbody : fn.body = (osHead cfg).1 ++ (osLevels cfg 0 cfg.levels (osHead cfg).2).1 ++
      (osTail cfg.yrLog (OsRun.sL cfg)).1 ++ osFinPre cfg ++ [.ret (osRetVs cfg)] := by
    rw [hb, hbf.last, os_pre_eq]
  have hst := hbf.straight
  rw [os_pre_eq] at hst
  have had := hbf.addrs
  rw [os_pre_eq] at had
  have hal := hbf.allocs
  rw [os_pre_eq] at hal
  have htf : d.tf.length = cfg.yrLog := by
    simp only [OsData.tf, List.length_append, List.length_cons, List.length_nil, hkit.chst]; have := hok.yr2; omega
  have hjo : 11 + 2 * cfg.levels.length + 1 < (osSizes cfg).length := by rw [os_length_osSizes]; omega
  refine os_completeAt_place hfind hloop κ Lin _ _ hbody hst had (osSizes cfg) (11 + 2 * cfg.levels.length + 1) hjo
    (C := osTC) fun fp => ?_
  set b0 := fp + fs name
  set R := d.runOf cfg (ofK (Parameters.gpow c)) b0
  set σ := Val.ofArgs (osBodyVals cfg R)
  set rets : List E := [w.target, ofK (Parameters.gpow (b0 + ((osSizes cfg).take (11 + 2 * cfg.levels.length + 1)).sum)),
    w.inner, w.residual]
  have hpt : osPtrAt cfg b0 (11 + 2 * cfg.levels.length + 1) =
      ofK (Parameters.gpow (b0 + ((osSizes cfg).take (11 + 2 * cfg.levels.length + 1)).sum)) := by
    unfold osPtrAt; rw [os_bases_getD _ _ _ hjo]
  have hout : ∀ Q : List E, (fun rets Lout => ∃ b, rets = [w.target, ofK (Parameters.gpow b), w.inner, w.residual] ∧
      Lout = [(b, w.point ++ List.replicate (pointCap - w.point.length) 0)]) rets
      [(b0 + ((osSizes cfg).take (11 + 2 * cfg.levels.length + 1)).sum,
        (d.ownQ cfg Q).getD (11 + 2 * cfg.levels.length + 1) [])] := fun Q => by
    refine ⟨_, rfl, ?_⟩
    have hhd : (cfg.levels.headD default).folds = (cfg.lv 0).folds := by
      cases h' : cfg.levels with
      | nil => simp [h'] at hn
      | cons a b' => simp [OsCfg.lv, h']
    have hlane : (cfg.levels.headD default).folds ≤ cfg.nFolds := by rw [hhd]; exact hok.laneLe
    rw [OsData.ownQ_getD_pt, OsData.ptC_eq hrunOk.fchLen htf hlane hok.pt42 hbf.tch, hkit.w, hhd]
    have hfl' : ((d.endL cfg).2.2.folds ++ d.tf).length = cfg.nFolds + cfg.yrLog := by
      rw [List.length_append, htf]; exact congrArg (· + _) hrunOk.fchLen
    have hpl : (((d.endL cfg).2.2.folds ++ d.tf).drop (cfg.lv 0).folds ++
        ((d.endL cfg).2.2.folds ++ d.tf).take (cfg.lv 0).folds).length = cfg.nFolds + cfg.yrLog := by
      simp only [List.length_append, List.length_drop, List.length_take, hfl']
      have := hok.laneLe; omega
    rw [hpl]
    rfl
  have hparams : fn.params.map σ = [(digestScalars d.cv).1, (digestScalars d.cv).2, d.target,
      (digestScalars d.root).1, (digestScalars d.root).2, ofK (Parameters.gpow c)] := by
    rw [hp]; rfl
  have hfit : ∀ Q : List E, Q.length ≤ cfg.posLen →
      List.Forall₂ (fun c s => c.length ≤ s) (d.ownQ cfg Q) (osSizes cfg) := fun Q hQ =>
    os_own_fits hbf.layout hok.yr5 (by rw [hkit.chst]; have := hok.yr2; omega) hQ (le_of_eq hrunOk.fchLen)
  by_cases hex : ∃ rd0, LowDef κ rd0 ∧ MemL rd0 (osLk cfg d Lin b0)
  · obtain ⟨N, L, ps, hW, hD, hK⟩ := d.kids_at hok hbf hk hkit hLin hex (b0 + (osSizes cfg).sum)
    refine ⟨σ, d.ownQ cfg (OsData.qbpC cfg fs cert fun l => ps.getD l 0), rets, N, L, fun _ => False, _,
      os_calls_eq cfg σ, hfit _ (by rw [OsData.qbpC, os_length_segC]), hout _, hW, hD, hparams,
      fun rd hl hmB hmLin => ?_, fun rd hl hmB hmL hmLin => hK rd hl hmB hmL hmLin⟩
    obtain ⟨hH, hA⟩ := d.body_at hok hbf hkit (hcal rd) (os_bufReads hmB) (hLin rd hl hmLin)
    rw [hpt] at hH
    rw [hal]
    refine ⟨os_holdsList_of_eq hb hH, ?_, ?_⟩
    · have := congrArg (List.map Prod.snd) hA
      simp only [osAllocs, List.map_map] at this
      rw [osAllocVals_snd] at this
      exact this
    · have := congrArg (List.map Prod.fst) hA
      simp only [osAllocs, List.map_map] at this
      rw [osAllocVals_fst (d.runOf_ptrs cfg _ b0)] at this
      rw [List.map_map]; exact this
  · refine ⟨σ, d.ownQ cfg (OsData.qbpC cfg fs cert fun _ => 0), rets, 0, [], fun _ => False, _, os_calls_eq cfg σ,
      hfit _ (by rw [OsData.qbpC, os_length_segC]), hout _, fun _ h => by simp at h, disj_nil, hparams,
      fun rd hl hmB hmLin => absurd ⟨rd, hl, Main.memL_append.mpr ⟨hmLin, OsData.memL_ownQ_nil hmB⟩⟩ hex,
      fun rd hl hmB _ hmLin => absurd ⟨rd, hl, Main.memL_append.mpr ⟨hmLin, OsData.memL_ownQ_nil hmB⟩⟩ hex⟩

end
end LeanVM.Guest.B1
