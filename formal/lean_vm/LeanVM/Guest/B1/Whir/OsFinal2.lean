/-
  LeanVM.Guest.B1.Whir.OsFinal2

  `open_stacked`'s callees composed from after its buffers.
-/

module

public import LeanVM.Guest.B1.Whir.OsFinal1

/-!
# The callees, composed (TRIAGE #36)

`OsData.kids_at`: when some defined-low memory holds the caller's words, the body's frames are
`KidsFromIn` from any `bk`: the levels' (their loops' positions `ps`), the tail's folds, the
finish's callees, on every memory holding the buffers with the decoders' pointers at `ps`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

/-- **The body's frames, in its parts.** -/
theorem os_calls_eq (cfg : OsCfg) (σ : Val) :
    (((osHead cfg).1 ++ (osLevels cfg 0 cfg.levels (osHead cfg).2).1 ++ (osTail cfg.yrLog (OsRun.sL cfg)).1 ++
      osFinPre cfg).filterMap Main.Stmt.callS).map (Main.mkCall σ) =
      (osLvsKOf cfg σ 0 (osHead cfg).2 cfg.levels.length).flatMap OsLvK.calls ++
        (((osTail cfg.yrLog (OsRun.sL cfg)).1.filterMap Main.Stmt.callS).map (Main.mkCall σ) ++
        ((osFinPre cfg).filterMap Main.Stmt.callS).map (Main.mkCall σ)) := by
  rw [List.filterMap_append, List.filterMap_append, List.filterMap_append, List.map_append, List.map_append,
    List.map_append, os_head_noCalls, List.map_nil, List.nil_append,
    show osLevels cfg 0 cfg.levels (osHead cfg).2 = osLevels cfg 0 (cfg.levels.drop 0) (osHead cfg).2 by rw [List.drop_zero],
    os_levels_calls cfg σ cfg.levels.length 0 _ (by omega), List.append_assoc]

namespace OsData

variable {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ} {cfg : OsCfg} {d : OsData}

private theorem os_regionL_app {L L' : Main.Layout} {i : ℕ} (h : RegionL (L ++ L') i) : RegionL L i ∨ RegionL L' i := by
  obtain ⟨q, hq, h1, h2⟩ := h
  rcases List.mem_append.mp hq with hq | hq
  · exact Or.inl ⟨q, hq, h1, h2⟩
  · exact Or.inr ⟨q, hq, h1, h2⟩

private theorem os_lvsKOf_length (cfg : OsCfg) (σ : Val) : ∀ n lvl s, (osLvsKOf cfg σ lvl s n).length = n
  | 0, _, _ => rfl
  | n + 1, lvl, s => by simp [osLvsKOf, os_lvsKOf_length cfg σ n]

/-- **The body's frames, composed.** -/
theorem kids_at {μ r : ℕ} {Lall : List Whir.Level} (hok : OsCfgOk cfg μ r Lall) (hbf : OsBodyFacts cfg)
    (hk : OsKidsAt fs cert κ cfg) {w : WhirEnd} (hkit : OsRunKit cfg μ Lall d w) {Lin : Main.Layout} {b0 : ℕ} {cur : E}
    (hLin : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd cur d.xs)
    (hex : ∃ rd0, LowDef κ rd0 ∧ MemL rd0 (osLk cfg d Lin b0)) (bk : ℕ) :
    ∃ (N : ℕ) (L : Main.Layout) (ps : List ℕ), Within L bk N ∧ DisjL L ∧
      ∀ rd, LowDef κ rd → MemL rd (bufL b0 (osSizes cfg) (d.ownQ cfg (qbpC cfg fs cert fun l => ps.getD l 0))) →
        MemL rd L → MemL rd Lin →
        KidsFromIn coreProgram fs cert rd (Val.ofArgs (osBodyVals cfg (d.runOf cfg cur b0)))
          (fun i => RegionL Lin i ∨
            RegionL (bufL b0 (osSizes cfg) (d.ownQ cfg (qbpC cfg fs cert fun l => ps.getD l 0))) i)
          (fun _ => False) ((osLvsKOf cfg (Val.ofArgs (osBodyVals cfg (d.runOf cfg cur b0))) 0 (osHead cfg).2
            cfg.levels.length).flatMap OsLvK.calls ++
            (((osTail cfg.yrLog (OsRun.sL cfg)).1.filterMap Main.Stmt.callS).map
              (Main.mkCall (Val.ofArgs (osBodyVals cfg (d.runOf cfg cur b0)))) ++
            ((osFinPre cfg).filterMap Main.Stmt.callS).map
              (Main.mkCall (Val.ofArgs (osBodyVals cfg (d.runOf cfg cur b0)))))) bk N (fun _ => False) := by
  set R := d.runOf cfg cur b0 with hR
  set σ := Val.ofArgs (osBodyVals cfg R) with hσ
  set Lk := osLk cfg d Lin b0 with hLk
  set W : ℕ → ℕ → Main.Layout := fun l p => osW fs cert cfg b0 l p
  set S : ℕ → ℕ → Main.Layout := fun l p => osS fs cert cfg d l p
  obtain ⟨rd0, hl0, hm0⟩ := hex
  obtain ⟨sp', Q', hQ, hch⟩ := hkit.chain
  obtain ⟨ospT, rootsT, hrunT⟩ := hkit.tail
  have hrun := d.runOk_of hok hkit.len hch hkit.chst
  have hlay := hbf.layout
  have hn := hok.len2
  have hlenH := hkit.len
  have hbuf : ∀ rd, MemL rd Lk → OsBufReads rd cfg d b0 [] := fun rd hm => os_bufReads (Main.memL_append.mp hm).2
  have hxs0 : ReadsAt rd0 cur d.xs := hLin rd0 hl0 (Main.memL_append.mp hm0).1
  have hm := d.bodyMem hok hbf.tch hlay hrun (hbuf rd0 hm0) hxs0 σ
  obtain ⟨hfl, hyl⟩ := d.fmsg_len hok hkit.len hch
  have htf : d.tf.length = cfg.yrLog := by
    simp only [tf, List.length_append, List.length_cons, List.length_nil, hkit.chst]; have := hok.yr2; omega
  have hzD : ∀ i < 42, osPtSrc cfg.nFolds (cfg.levels.headD default).folds cfg.yrLog (OsRun.tch cfg) i = none →
      R.D.ent i = 0 := fun i _ h => by
    show d.ent cfg i = 0; unfold ent; rw [h]
  have hnq : ∀ lv ∈ cfg.levels, lv.queries < 2 ^ 128 := fun lv hlv => by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hlv
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hq62, -⟩ :=
      hok.spec i (by rw [hok.len]; exact hi)
    have : cfg.lv i = cfg.levels[i] := by simp [OsCfg.lv, List.getD_eq_getElem?_getD, hi]
    rw [← this]; omega
  have hcff : osCA fs cert κ Lk cfg.foldFinal [R.P.fmsg, R.tchv] [R.D.yat] :=
    os_kid_ff hk.foldFinal (m := d.fmsgC cfg) (ps := d.tf) (by rw [hfl, hyl]) htf fun rd hmm =>
      ⟨(hbuf rd hmm).fmsg, fun k hk' => by
        have := (hbuf rd hmm).tch k (by simp only [tchC, List.length_append]; omega)
        simp only [tchC, List.getElem_append_left hk'] at this
        exact this⟩
  have hcres : ∀ l < cfg.levels.length, 1 + osGw (cfg.levels.getD l default).queries ≠ 0 →
      osCA fs cert κ Lk (cfg.levels.getD l default).resLoop [1, osGw (cfg.levels.getD l default).queries, R.P.qpos,
        R.D.ba, R.D.bb, R.D.chv l, R.P.qw] [] := by
    intro l hl _
    obtain ⟨fn, hfind, hp, hb⟩ := (hk.lv l hl).resFn
    obtain ⟨-, -, -, hml0, hml1, hlc, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hq62, -⟩ :=
      hok.spec l (by rw [hok.len]; exact hl)
    have hq62' : (cfg.levels.getD l default).queries < 2 ^ 62 := hq62
    rw [os_gw_eq (by omega)]
    exact os_kid_res (hk.lv l hl).resPure hfind hp hb (by omega) (by simp only [ordG]; omega) (hlay.queries l hl)
      fun rd hmm => resFacts hok hlay (hbuf rd hmm) hl
  obtain ⟨-, hcs, hT, hF, -, -⟩ := osBody_complete (R := R) (σ := σ) (rd := rd0) hok hkit.x2 hkit.len hch
    hrunT rfl hzD hnq (fun _ _ => rfl) hm
    (CA := fun _ => osCA fs cert κ Lk) (CB := fun l => osCB fs cert κ Lk (W l) (S l))
    (Csq := fun l => osCsq fs cert κ Lk (W l) (S l))
    (lvsCallH hok hlay hrun hk hLin hbuf hQ hch) (CT := osCA fs cert κ Lk)
    (fun cv' p' q' hq hp => os_kid_fold hk.fold (fun rd hl hmm => hLin rd hl (Main.memL_append.mp hmm).1) cv' p' q' hq hp)
    (CF := osCA fs cert κ Lk) hcff hcres
  -- the blocks' frames
  have hstr := hbf.straight
  rw [os_pre_eq, List.all_append, List.all_append, List.all_append] at hstr
  simp only [Bool.and_eq_true] at hstr
  obtain ⟨⟨⟨-, -⟩, hTl⟩, hFp⟩ := hstr
  have hTok := os_callsOk_of_holdsList _ hTl hT
  rw [os_finish_eq hbf, holdsList_append] at hF
  have hFok := os_callsOk_of_holdsList _ hFp hF
  have hne : ∀ l, l < cfg.levels.length → 1 + osGw (cfg.lv l).squeezes ≠ 0 := fun l hl => by
    obtain ⟨-, -, -, -, -, -, -, -, -, hqs, -, -, hsq62, -⟩ := hok.spec l (by rw [hok.len]; exact hl)
    have hq0 := hlay.queries l hl
    refine os_one_add_gw ?_ hsq62
    rcases Nat.eq_zero_or_pos (cfg.lv l).squeezes with h | h
    · rw [h, Nat.zero_mul] at hqs; omega
    · exact h
  rw [show R.Hs.length = cfg.levels.length from hkit.len] at hcs
  have hksl := os_lvsKOf_length cfg σ cfg.levels.length 0 (osHead cfg).2
  have hks := os_lvsK_ok (fs := fs) (cert := cert) (κ := κ) (Lk := Lk) (W := W) (S := S) hne cfg.levels.length 0 _
    (by omega) hcs
  obtain ⟨N1, L1, ps, hps, hW1, hD1, hK1⟩ := os_levels_kids κ σ Lk W S (osLvsKOf cfg σ 0 (osHead cfg).2
    cfg.levels.length) 0 hks bk
  obtain ⟨N2, L2, hW2, hD2, hK2⟩ := os_kids_block (fs := fs) (cert := cert) κ Lk σ _ (fun c hc ht => hTok c hc ht)
    (bk + N1)
  obtain ⟨N3, L3, hW3, hD3, hK3⟩ := os_kids_block (fs := fs) (cert := cert) κ Lk σ _ (fun c hc ht => hFok c hc ht)
    (bk + N1 + N2)
  have hW23 : Within (L2 ++ L3) (bk + N1) (N2 + N3) := by
    rw [within_append]; exact ⟨hW2.mono le_rfl (by omega), hW3.mono (by omega) (by omega)⟩
  refine ⟨N1 + (N2 + N3), L1 ++ (L2 ++ L3), ps, ?_⟩
  constructor
  · rw [within_append]; exact ⟨hW1.mono le_rfl (by omega), hW23.mono (by omega) (by omega)⟩
  constructor
  · exact disj_append hD1 (disj_append hD2 hD3 hW2 hW3 le_rfl) hW1 hW23 le_rfl
  intro rd hl hmB hmL hmLin
  obtain ⟨hm1, hm23⟩ := Main.memL_append.mp hmL
  obtain ⟨hm2, hm3⟩ := Main.memL_append.mp hm23
  have hmk : MemL rd (Lin ++ bufL b0 (osSizes cfg) (d.ownQ cfg [])) :=
    Main.memL_append.mpr ⟨hmLin, memL_ownQ_nil hmB⟩
  have hRk : ∀ i, RegionL (Lin ++ bufL b0 (osSizes cfg) (d.ownQ cfg [])) i → RegionL Lin i ∨
      RegionL (bufL b0 (osSizes cfg) (d.ownQ cfg (qbpC cfg fs cert fun l => ps.getD l 0))) i := fun i hi =>
    (os_regionL_app hi).imp id regionL_ownQ_nil
  refine kidsFromIn_append _ _ _ _ _ _ _ _ (hK1 rd _ _ hl hm1 hmk (fun i hi => ?_) hRk
    (fun l h1 h2 p i hi => Or.inr (regionL_osW hlay (by omega) hi))) fun D1 _ => ?_
  · have := memL_osW (fs := fs) (cert := cert) (d := d) hlay hmB (l := i) (by omega)
    simp only [Nat.zero_add]
    rw [List.getD_eq_getElem _ _ hi] at this
    exact this
  refine kidsFromIn_append _ _ _ _ _ _ _ _ (hK2 rd _ _ hl hm2 hmk fun i hi => Or.inl (hRk i hi)) fun D2 _ => ?_
  exact hK3 rd _ _ hl hm3 hmk fun i hi => Or.inl (hRk i hi)

end OsData

end
end LeanVM.Guest.B1
