/-
  LeanVM.Guest.B1.Whir.OsFinal1

  On a memory holding `open_stacked`'s buffers' honest words, its body holds, returning the run's
  end, and allocates its buffers at the allocator's pointers.
-/

module

public import LeanVM.Guest.B1.Whir.OsFinal0

/-!
# The body on a memory (TRIAGE #36)

`os_body_at`: on a memory holding the buffers' words (`OsBufReads`) and the run's words at the
cursor, the body holds at its honest valuation, returning the run's claim, the point buffer's
pointer, the glued weight and the residual's value (`osFinish_sound` at that memory gives the
glued weight), and its `HeapBuf`s are `osAllocVals`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

namespace OsData

variable {cfg : OsCfg} {d : OsData}

theorem fmsg_len {μ r lane : ℕ} {Lall : List Whir.Level} (hok : OsCfgOk cfg μ r Lall) {e : WhirEnd} {sp' : St}
    {Q : List (ℕ × List (ℕ × Opening))} (hlen : d.Hs.length = cfg.levels.length)
    (hch : OsChain cfg μ lane d.xs Lall e sp' Q 0 d.cv0 2 (osW0 d.target d.xs) d.os (d.roots0 cfg) d.Hs) :
    (d.fmsgC cfg).length = cfg.yrLen ∧ cfg.yrLen = 2 ^ cfg.yrLog := by
  have hn := hok.len2
  have hy := hok.yrLevel
  obtain ⟨hm, hlv⟩ := lv_mem (cfg := cfg) (d := d) (l := cfg.yrLevel) (by omega)
  have hokL := (os_chain_mem d.Hs 0 _ _ _ _ _ hch _ hm).ok
  rw [hlv] at hokL
  have hl := hokL.len
  unfold osHPEnd osHP2 at hl
  rw [ite_pos' rfl] at hl
  refine ⟨by simp only [fmsgC, osHMs, List.length_take, List.length_drop]; omega, ?_⟩
  have hlast := hok.spec (cfg.levels.length - 1) (by rw [hok.len]; omega)
  rw [show cfg.levels.length - 1 + 1 = Lall.length by rw [hok.len]; omega, List.drop_length] at hlast
  rw [hlast.yrLen, hok.nFolds, ← hok.total, Nat.add_sub_cancel_left]

theorem lvsCallH_triv {xs : List E} {cur : E} {P : OsPtrs} {sqz rew : ℕ → E} :
    ∀ (Hs : List OsLvH) lvl p w roots, OsLvsCallH (fun _ => osTC) (fun _ => osTC) (fun _ => osTC) cfg xs cur P sqz rew
      lvl p w roots Hs
  | [], _, _, _, _ => trivial
  | _ :: Hs, _, _, _, _ => ⟨⟨fun _ _ _ _ _ => trivial, fun _ => trivial, fun _ => ⟨trivial, trivial, trivial⟩, trivial,
      fun _ => trivial, trivial, trivial, trivial⟩, lvsCallH_triv Hs _ _ _ _⟩

/-- **The body on a memory holding its buffers.** -/
theorem body_at {μ r : ℕ} {Lall : List Whir.Level} (hok : OsCfgOk cfg μ r Lall) (hbf : OsBodyFacts cfg) {w : WhirEnd}
    (hkit : OsRunKit cfg μ Lall d w) {rd : Reader} (hcal : OsCallees rd cfg) {b : ℕ} {Q : List E} {cur : E}
    (hbr : OsBufReads rd cfg d b Q) (hxs : ReadsAt rd cur d.xs) :
    Stmt.HoldsList osTC rd (Val.ofArgs (osBodyVals cfg (d.runOf cfg cur b))) (osBody cfg) False
      (fun rs => rs = [w.target, osPtrAt cfg b (11 + 2 * cfg.levels.length + 1), w.inner, w.residual]) ∧
    osAllocs (Val.ofArgs (osBodyVals cfg (d.runOf cfg cur b))) (osAllocList cfg) = osAllocVals cfg (d.runOf cfg cur b) := by
  set R := d.runOf cfg cur b with hR
  set σ := Val.ofArgs (osBodyVals cfg R) with hσ
  obtain ⟨sp', Q', hQ, hch⟩ := hkit.chain
  obtain ⟨ospT, rootsT, hrunT⟩ := hkit.tail
  have hrun := d.runOk_of hok hkit.len hch hkit.chst
  have hm := d.bodyMem hok hbf.tch hbf.layout hrun hbr hxs σ
  have hlay := hbf.layout
  have hn := hok.len2
  have hlenH := hkit.len
  obtain ⟨hfl, hyl⟩ := d.fmsg_len hok hkit.len hch
  have htf : d.tf.length = cfg.yrLog := by
    simp only [tf, List.length_append, List.length_cons, List.length_nil, hkit.chst]; have := hok.yr2; omega
  have htch : ReadsAt rd (osPtrAt cfg b (11 + 2 * cfg.levels.length)) d.tf := fun k hk => by
    have := hbr.tch k (by simp only [tchC, List.length_append]; omega)
    simp only [tchC, List.getElem_append_left hk] at this
    exact this
  let Chon : CallRel := fun f a r' => (a.length = 7 → coreProgram.Rel rd f a r') ∧
    (a.length = 2 → MeaningFoldFinalMsg cfg.yrLog rd a r')
  have hcff : Chon cfg.foldFinal [R.P.fmsg, R.tchv] [R.D.yat] :=
    ⟨fun h => absurd h (by simp), fun _ => ⟨d.fmsgC cfg, d.tf, by rw [hfl, hyl], htf, hbr.fmsg, htch, rfl⟩⟩
  have hcres : ∀ l < cfg.levels.length, 1 + osGw (cfg.levels.getD l default).queries ≠ 0 →
      Chon (cfg.levels.getD l default).resLoop [1, osGw (cfg.levels.getD l default).queries, R.P.qpos, R.D.ba, R.D.bb,
        R.D.chv l, R.P.qw] [] := by
    intro l hl _
    refine ⟨fun _ => ?_, fun h => absurd h (by simp)⟩
    obtain ⟨fn, hfind, hp, hb⟩ := hcal.res l hl
    obtain ⟨-, -, -, hml0, hml1, hlc, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hq62, -⟩ :=
      hok.spec l (by rw [hok.len]; exact hl)
    have hq0 := hlay.queries l hl
    obtain ⟨lp, la, lb, lr, lw, lr1⟩ := resFacts hok hlay hbr hl
    have h := resLoop_rel hfind hp hb (by omega) (show (cfg.lv l).queries < ordG by simp only [ordG]; omega)
      lp la lb lr lw lr1 0 hq0
    rw [pow_zero, ← os_gw_eq (by omega)] at h
    exact h
  have hzD : ∀ i < 42, osPtSrc cfg.nFolds (cfg.levels.headD default).folds cfg.yrLog (OsRun.tch cfg) i = none →
      R.D.ent i = 0 := fun i _ h => by
    show d.ent cfg i = 0; unfold ent; rw [h]
  have hnq : ∀ lv ∈ cfg.levels, lv.queries < 2 ^ 128 := fun lv hlv => by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hlv
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hq62, -⟩ :=
      hok.spec i (by rw [hok.len]; exact hi)
    have : cfg.lv i = cfg.levels[i] := by simp [OsCfg.lv, List.getD_eq_getElem?_getD, hi]
    rw [← this]; omega
  obtain ⟨hHold, hcs, -, hF, hts, hfs⟩ := osBody_complete (R := R) (σ := σ) (rd := rd) hok hkit.x2 hkit.len hch
    hrunT rfl hzD hnq (fun _ _ => rfl) hm (CA := fun _ => osTC) (CB := fun _ => osTC) (Csq := fun _ => osTC)
    (lvsCallH_triv _ _ _ _ _) (CT := osTC) (fun _ _ _ _ _ => trivial) (CF := Chon) hcff hcres
  -- the head's pointers
  have hhv : ∀ j < 61, σ (.n j) = (osHeadVals cfg (digestScalars R.cv).1 (digestScalars R.cv).2 R.target
      (digestScalars R.root).1 (digestScalars R.root).2 R.cur R.cv (R.xs.getD 0 0) (R.xs.getD 1 0) R.P).getD j 0 :=
    fun j hj => by
      rw [hσ, ofArgs_n, osBodyVals, List.append_assoc, List.append_assoc,
        oq_getD_app_lt (by rw [os_length_headVals]; exact hj)]
  obtain ⟨hP, hhead⟩ := os_head_sig hhv
  -- the finish's returns
  obtain ⟨pt, hrets, -⟩ := osFinish_sound (σ := σ) (rd := rd) hok hcal (wL := (d.endL cfg).2.2)
    (residual := d.fmsgC cfg) (tf := d.tf) hrun.fchLen
    (fun j hj => by rw [hP.fch]; exact os_readsAt_getD hbr.fch hj)
    ⟨(d.lvs cfg).map (osRecOf cfg d.xs), by simp [lvs, os_lvsList_length, hkit.len],
      d.glued_eq hok hkit.len hch, fun i hi => by
        obtain ⟨hmi, hlvi⟩ := lv_mem (cfg := cfg) (d := d) (l := i) (by omega)
        rw [List.getD_eq_getElem _ _ (by simp [lvs, os_lvsList_length, hkit.len]; omega), List.getElem_map]
        have := recOk hok hlay hbr hP hi hlvi
        unfold lv at this
        rwa [List.getD_eq_getElem _ _ (by simp [lvs, os_lvsList_length, hkit.len]; omega)] at this⟩
    hfl (by rw [hP.fmsg]; exact hbr.fmsg) htf
    (by rw [show OsRun.tch cfg = (OsRun.sL cfg).k + 1 from rfl, hts.2]; exact hbr.tch)
    (fun _ _ _ _ h => h.1 (by assumption)) (fun _ _ ha h => h.2 ha) hF
  have hw := hkit.w
  rw [show R.Hs.length = cfg.levels.length from hkit.len] at hcs
  refine ⟨?_, osAllocs_eq hbf.sizes hhead hcs hts hfs⟩
  have e : [R.D.t, R.D.pt, osFinTot cfg R.D, R.D.yat] =
      [w.target, osPtrAt cfg b (11 + 2 * cfg.levels.length + 1), w.inner, w.residual] := by
    simp only [List.cons.injEq] at hrets
    rw [hw]
    refine List.cons_eq_cons.mpr ⟨rfl, List.cons_eq_cons.mpr ⟨rfl, List.cons_eq_cons.mpr ⟨hrets.2.2.1, ?_⟩⟩⟩
    rfl
  rw [← e]
  exact hHold

end OsData

end
end LeanVM.Guest.B1
