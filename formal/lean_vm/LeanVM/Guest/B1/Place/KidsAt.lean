/-
  LeanVM.Guest.B1.Place.KidsAt

  open_stacked's callees placed in sequence after its buffers.
-/

module

public import LeanVM.Guest.B1.Place.KidShapes
public import LeanVM.Guest.B1.Place.KidLq
public import LeanVM.Guest.B1.Place.OsKidsO
public import LeanVM.Guest.B1.Place.OsInj
public import LeanVM.Guest.B1.Place.ValsSpec

/-!
# The callees, placed

`os_kids_at`: on a body proved at `osCR` on every memory holding the callees' words `Lk`, its
frames (`osBodyAc_calls`) are placed in sequence from any `bk`, at an optional bound: per level
the calls before its positions (named: `hnamed`), its `level_positions` (`hlpK`, entered at `ps l`,
reading its window pointers `osW … l (ps l)`), the calls after (`hlqK` on its decoders' runs), then
the tail's and the finish's (`hlrK`). The special calls are the levels' by the values
(`OsCallVals`: the positions pointer, the row weights) and the names' shapes (`OsKidShapes`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ}

theorem mem_lvAt_of_rate {c : OsCfg} {ri : ℕ} (hN : OsNames c ri) {l : ℕ}
    (hl : l < c.levels.length) : lvAt c l ∈ c.lvAt l := by
  rw [← (hN.rate l hl).2, List.getD_eq_getElem _ _ (by rw [(hN.rate l hl).1]; exact hN.ri4)]
  exact List.getElem_mem _

theorem rate_name {c : OsCfg} {ri : ℕ} (hN : OsNames c ri) {l : ℕ} (hl : l < c.levels.length)
    (f : OsLv → String) : ((c.lvAt l).map f).getD ri "" = f (lvAt c l) := by
  have h4 : ri < (c.lvAt l).length := by rw [(hN.rate l hl).1]; exact hN.ri4
  rw [List.getD_eq_getElem _ _ (by simpa using h4), List.getElem_map,
    ← List.getD_eq_getElem _ default h4, (hN.rate l hl).2]

/-- **The callees, placed.** -/
theorem os_kids_at {Bd : Option (String → ℕ)} {c : OsCfg} {tr : OsTr} {σ0 : Val} {c0 c2 : E}
    {b0 : ℕ} {Lin : Layout} {D : ℕ → ℕ → ℕ → ℕ} {ri : ℕ}
    (hN : OsNames c ri) (hS : OsKidShapes c)
    (hpos : ∀ x ∈ osSizesL c, 0 < x) (htot : (osSizesL c).sum < 2 ^ 64 - 1)
    (hposOff : ∀ l < c.levels.length, (lvAt c l).posOff = l * ligPosCap)
    (hpoN : c.levels.length * ligPosCap < 2 ^ 64 - 1)
    (hcap5 : ∀ l < c.levels.length, (tr.L l).F2.cap.length = 5)
    (hR : osSigma c tr σ0 c0 c2 b0 (.n osRate) = ofK (addressOfIndex ri))
    (hV : OsCallVals c tr σ0 c0 c2 b0)
    (hall : ∀ rd, LowDef κ rd → MemL rd (osLk c tr b0 Lin) →
      AllOk (osCR rd (osSp c tr (osAtOf c b0)) (OsXOk κ (osLk c tr b0 Lin))) rd
        (osSigma c tr σ0 c0 c2 b0) (osBodyAc c))
    (hdo : ∀ s ∈ osBodyAc c, DispOk (osSigma c tr σ0 c0 c2 b0) s) (hfl : DispShort (osBodyAc c))
    (hex : ∃ rd0, LowDef κ rd0 ∧ MemL rd0 (osLk c tr b0 Lin))
    (hnamed : ∀ f ∈ osCalleeNames c, ∀ K, osKindOf f = some K → ∀ (args rets : List E) (L' : Layout),
      RegPtrs K.spec args (RegionL L') → (∀ rd, LowDef κ rd → MemL rd L' → K.Pre rd args rets) →
      CompleteAtO fs cert κ f L' args (Returns rets) (Bd.map (· f)))
    (hofrR : ∀ c' ∈ ((osBodyAc c).filterMap (Stmt.callSF (osSigma c tr σ0 c0 c2 b0))).map
        (Main.mkCall (osSigma c tr σ0 c0 c2 b0)), c'.taken = true → ∀ b, osKindOf c'.f = some (.ofr b) →
      RegPtrs [(7, roundLen b)] (c'.args.map (osSigma c tr σ0 c0 c2 b0)) (RegionL (osLk c tr b0 Lin)))
    (hlpK : ∀ l < c.levels.length, osPositionsName (lvAt c l) ∈ osCalleeNames c →
      CompleteAtPO fs cert κ (osPositionsName (lvAt c l))
      (fun p ↦ osLk c tr b0 Lin ++ osW cert c D b0 l p) (osLpArgs c tr (osAtOf c b0) l)
      (sqLast (lvAt c l) (tr.L l).F2.cap) (osS cert c tr D l)
      (Bd.map (· (osPositionsName (lvAt c l)))))
    (hlqK : ∀ l < c.levels.length, osQueriesName l (lvAt c l) ∈ osCalleeNames c → ∀ p,
      CompleteAtO fs cert κ (osQueriesName l (lvAt c l))
      (osLk c tr b0 Lin ++ osW cert c D b0 l p ++ osS cert c tr D l p)
      (osLqArgs c tr (osAtOf c b0) l) (Returns (osLqRets c tr l))
      (Bd.map (· (osQueriesName l (lvAt c l)))))
    (hlrK : ∀ l < c.levels.length, osResidualName (lvAt c l) ∈ osCalleeNames c →
      CompleteAtO fs cert κ (osResidualName (lvAt c l))
      (osLk c tr b0 Lin) (osLrArgs c tr (osAtOf c b0) l) (Returns [finH c tr l])
      (Bd.map (· (osResidualName (lvAt c l)))))
    (bk : ℕ) :
    ∃ (N : ℕ) (L : Layout) (ps : List ℕ), ps.length = c.levels.length ∧ Within L bk N ∧ DisjL L ∧
      (∀ Bk ∈ Bd, N ≤ osKidsB fs Bk c) ∧
      ∀ (rd : Reader) (R Dacc : ℕ → Prop), LowDef κ rd → MemL rd L → MemL rd (osLk c tr b0 Lin) →
        (∀ i (h : i < ps.length), MemL rd (osW cert c D b0 i ps[i])) →
        (∀ i, RegionL (osLk c tr b0 Lin) i → R i) →
        (∀ l < c.levels.length, ∀ p i, RegionL (osW cert c D b0 l p) i → R i) →
        KidsFromIn coreProgram fs cert rd (osSigma c tr σ0 c0 c2 b0) R Dacc
          (((osBodyAc c).filterMap (Stmt.callSF (osSigma c tr σ0 c0 c2 b0))).map
            (Main.mkCall (osSigma c tr σ0 c0 c2 b0))) bk N (fun _ ↦ False) := by
  set σ := osSigma c tr σ0 c0 c2 b0 with hσ
  set A := osAtOf c b0 with hA
  set Lk := osLk c tr b0 Lin with hLk
  set Ks := osLvKOf σ c 0 c.levels (osHead c).2 with hKs
  set cs2 := ((osTlSt c).1.filterMap (Stmt.callSF σ)).map (Main.mkCall σ) ++
    ((osFinA c (osTlSt c).2.1 (osTlSt c).2.2).filterMap (Stmt.callSF σ)).map (Main.mkCall σ)
    with hcs2
  have hcs : ((osBodyAc c).filterMap (Stmt.callSF σ)).map (Main.mkCall σ) =
      Ks.flatMap OsLvK.calls ++ cs2 := osBodyAc_calls σ c
  have hksl : Ks.length = c.levels.length := osLvKOf_length σ c 0 c.levels _
  have hmem : ∀ c', c' ∈ Ks.flatMap OsLvK.calls ∨ c' ∈ cs2 →
      c' ∈ ((osBodyAc c).filterMap (Stmt.callSF σ)).map (Main.mkCall σ) := fun c' h ↦ by
    rw [hcs, List.mem_append]; exact h
  have h64 : ri < 2 ^ 64 - 1 := by have := hN.ri4; omega
  -- the named calls
  have hnk : ∀ c' ∈ ((osBodyAc c).filterMap (Stmt.callSF σ)).map (Main.mkCall σ),
      c'.taken = true → ∀ K, osKindOf c'.f = some K → ∀ L' : Layout,
      (∀ i, RegionL Lk i → RegionL L' i) → (∀ rd, MemL rd L' → MemL rd Lk) →
      CompleteAtO fs cert κ c'.f L' (c'.args.map σ) (Returns (c'.rets.map σ)) (Bd.map (· c'.f)) := by
    intro c' hc' ht K hK L' hreg hmono
    have hpre : ∀ rd, LowDef κ rd → MemL rd Lk → K.Pre rd (c'.args.map σ) (c'.rets.map σ) ∧
        OsXOk κ Lk K (c'.args.map σ) := fun rd hl hm ↦ by
      have h := os_calls_of_allOkF (hall rd hl hm) hdo hfl c' hc' ht
      unfold osCR at h; rw [hK] at h; exact h
    obtain ⟨rd0, hl0, hm0⟩ := hex
    have hr := kind_region (fun n hn ↦ osKindOf_ood_pos (hn ▸ hK)) ⟨rd0, hl0, hm0⟩
      (fun rd hl hm ↦ (hpre rd hl hm).1) (hpre rd0 hl0 hm0).2
      (fun b hb ↦ by subst hb; exact hofrR c' hc' ht b hK)
    refine hnamed c'.f (osKids_names hdo c' hc') K hK _ _ L' (fun q hq t ht' ↦ ?_)
      (fun rd hl hm ↦ (hpre rd hl (hmono rd hm)).1)
    obtain ⟨i, hi, hi'⟩ := hr q hq t ht'
    exact ⟨i, hi, hreg i hi'⟩
  have hsp : ∀ c' ∈ ((osBodyAc c).filterMap (Stmt.callSF σ)).map (Main.mkCall σ),
      c'.taken = true → osKindOf c'.f = none → osSp c tr A c'.f (c'.args.map σ) (c'.rets.map σ) :=
    fun c' hc' ht hK ↦ os_kid_specialF hall hdo hfl hex hc' ht hK
  have hpoff : ∀ l < c.levels.length, (lvAt c l).posOff < 2 ^ 64 - 1 := fun l hl ↦ by
    rw [hposOff l hl]
    have : l * ligPosCap ≤ c.levels.length * ligPosCap := Nat.mul_le_mul_right _ hl.le
    omega
  -- the levels
  have hok : ∀ i (h : i < Ks.length), OsLvKOkO fs cert κ σ Lk (osW cert c D b0 (0 + i))
      (osS cert c tr D (0 + i)) Bd Ks[i] := by
    intro i h
    have hi : i < c.levels.length := by rw [← hksl]; exact h
    have hinK : ∀ c' ∈ Ks[i].calls, c' ∈ ((osBodyAc c).filterMap (Stmt.callSF σ)).map
        (Main.mkCall σ) := fun c' hc' ↦ hmem c' (Or.inl (List.mem_flatMap.mpr ⟨Ks[i],
          List.getElem_mem h, hc'⟩))
    have hvlp := hV.lp i h
    have hvlq := hV.lq i h
    have e := osLvKOf_get σ c 0 c.levels (osHead c).2 i hi
    have hli : c.levels[i] = lvAt c i := by rw [lvAt, List.getD_eq_getElem _ _ hi]
    simp only [Nat.zero_add, hli] at e
    have hst : (osLevels c 0 (c.levels.take i) (osHead c).2).2 = osLvSt0 c i := rfl
    rw [hst] at e
    simp only [← hKs] at e hvlp hvlq
    rw [e] at hinK hvlp hvlq ⊢
    simp only [Nat.zero_add]
    have hdoL : ∀ s ∈ (osLevel c i (lvAt c i) (osLvSt0 c i)).1, DispOk σ s :=
      fun s hs ↦ hdo s (osLevel_mem_body c hi hs)
    rw [osLevel_callSplit] at hdoL
    simp only [OsLvK.calls, List.mem_append, List.mem_cons] at hinK
    have hf : (Main.mkCall σ (lpCallS σ c i (lvM c i (lvAt c i) (osLvSt0 c i)).2.1)).f =
        osPositionsName (lvAt c i) := by
      simp only [Main.mkCall, lpCallS]
      rw [hR, logG_spec h64, rate_name hN hi]
    refine ⟨fun c' hc' ht ↦ ?_, rfl, ?_, fun p c' hc' ht ↦ ?_⟩
    · -- before the positions: named
      have hn := hS.lvA i hi c'.f (kid_mem_callees (fun s hs ↦ hdoL s (List.mem_append_left _ hs))
        c' hc')
      obtain ⟨K, hK⟩ := Option.ne_none_iff_exists'.mp hn
      exact hnk c' (hinK c' (Or.inl hc')) ht K hK Lk (fun _ h ↦ h) (fun _ h ↦ h)
    · -- `level_positions`
      obtain ⟨l, hl, hsp'⟩ := hsp _ (hinK _ (Or.inr (Or.inl rfl))) rfl (by rw [hf]; exact hN.pos i hi)
      rw [hf] at hsp'
      rcases hsp' with ⟨hfl', ha, hr⟩ | ⟨hfl', -, -⟩ | ⟨hfl', -, -⟩
      · have h5 : (osLpArgs c tr A l).getD 5 0 = A.P.qpos * gen ^ (lvAt c l).posOff := by
          rw [List.getD_append_right _ _ _ _ (by rw [hcap5 l hl]), hcap5 l hl]; rfl
        rw [ha, h5] at hvlp
        have hq0 : A.P.qpos ≠ 0 := fun h ↦
          gpow_ne_zero (osBase c b0 5) (ofK_injective (h.trans ofK_zero.symm))
        have hg := mul_left_cancel₀ hq0 hvlp
        rw [gen_pow_eq_ofK, gen_pow_eq_ofK] at hg
        have hpo := gpow_injOn (show (lvAt c l).posOff ∈ Set.Iio (2 ^ 64 - 1) from hpoff l hl)
          (show (lvAt c i).posOff ∈ Set.Iio (2 ^ 64 - 1) from hpoff i hi) (ofK_injective hg)
        rw [hposOff l hl, hposOff i hi] at hpo
        have hli' : l = i := Nat.eq_of_mul_eq_mul_right (by decide) hpo
        subst hli'
        have hmn := osKids_names hdo _ (hinK _ (Or.inr (Or.inl rfl)))
        rw [hf] at hmn
        rw [hf, ha, hr]
        exact hlpK l hl hmn
      · exact absurd hfl'.symm ((hS.apart l hl i hi _ (mem_lvAt_of_rate hN hl) _
          (mem_lvAt_of_rate hN hi)).1)
      · exact absurd hfl'.symm ((hS.apart l hl i hi _ (mem_lvAt_of_rate hN hl) _
          (mem_lvAt_of_rate hN hi)).2.2)
    · -- after the positions
      have hin := hinK c' (Or.inr (Or.inr hc'))
      cases hK : osKindOf c'.f with
      | some K =>
        refine hnk c' hin ht K hK _ (fun i' h' ↦ ?_) (fun rd hm ↦ ?_)
        · obtain ⟨q, hq, h1, h2⟩ := h'
          exact ⟨q, List.mem_append_left _ (List.mem_append_left _ hq), h1, h2⟩
        · exact (Main.memL_append.mp (Main.memL_append.mp hm).1).1
      | none =>
        have hfq := hS.lvB i hi c'.f (kid_mem_callees (fun s hs ↦ hdoL s
          (List.mem_append_right _ (List.mem_append_right _ hs))) c' hc') hK
        obtain ⟨lv', hlv', hfe⟩ := List.mem_map.mp hfq
        obtain ⟨l, hl, hsp'⟩ := hsp _ hin ht hK
        rcases hsp' with ⟨hfl', -, -⟩ | ⟨hfl', ha, hr⟩ | ⟨hfl', -, -⟩
        · exact absurd (hfe.trans hfl') ((hS.apart i hi l hl _ hlv' _ (mem_lvAt_of_rate hN hl)).1)
        · have h2 := hvlq c' hc' hK
          rw [ha] at h2
          have hwl : osIxWp l = osIxWp i := osPtrAt_inj (c := c) (b := b0)
            (by rw [osSizesL_length]; unfold osIxWp; omega)
            (by rw [osSizesL_length]; unfold osIxWp; omega) hpos htot h2
          have hli' : l = i := by unfold osIxWp at hwl; omega
          subst hli'
          have hmn := osKids_names hdo _ hin
          rw [hfl'] at hmn
          rw [hfl', ha, hr]
          exact hlqK l hl hmn p
        · exact absurd (hfe.trans hfl') ((hS.apart i hi l hl _ hlv' _ (mem_lvAt_of_rate hN hl)).2.1)
  obtain ⟨N1, L1, ps, hps, hW1, hD1, hN1, hK1⟩ := os_levels_kidsO (fs := fs) (cert := cert) (κ := κ) σ Lk
    (osW cert c D b0) (osS cert c tr D) Bd Ks 0 hok bk
  -- the tail and the finish
  have hc2 : ∀ c' ∈ cs2, c'.taken = true →
      CompleteAtO fs cert κ c'.f Lk (c'.args.map σ) (Returns (c'.rets.map σ)) (Bd.map (· c'.f)) := by
    intro c' hc' ht
    have hin := hmem c' (Or.inr hc')
    rcases List.mem_append.mp hc' with hc' | hc'
    · have hdoT : ∀ s ∈ (osTlSt c).1, DispOk σ s := fun s hs ↦ hdo s (by
        unfold osBodyAc; exact List.mem_append_left _ (List.mem_append_right _ hs))
      obtain ⟨K, hK⟩ := Option.ne_none_iff_exists'.mp (hS.tail c'.f (kid_mem_callees hdoT c' hc'))
      exact hnk c' hin ht K hK Lk (fun _ h ↦ h) (fun _ h ↦ h)
    · cases hK : osKindOf c'.f with
      | some K => exact hnk c' hin ht K hK Lk (fun _ h ↦ h) (fun _ h ↦ h)
      | none =>
        have hdoF : ∀ s ∈ osFinA c (osTlSt c).2.1 (osTlSt c).2.2, DispOk σ s := fun s hs ↦ hdo s (by
          unfold osBodyAc; exact List.mem_append_right _ hs)
        obtain ⟨l0, hl0, hfr⟩ := hS.fin c'.f (kid_mem_callees hdoF c' hc') hK
        obtain ⟨lv', hlv', hfe⟩ := List.mem_map.mp hfr
        obtain ⟨l, hl, hsp'⟩ := hsp _ hin ht hK
        rcases hsp' with ⟨hfl', -, -⟩ | ⟨hfl', -, -⟩ | ⟨hfl', ha, hr⟩
        · exact absurd (hfe.trans hfl') ((hS.apart l0 hl0 l hl lv' hlv' _
            (mem_lvAt_of_rate hN hl)).2.2)
        · exact absurd (hfe.trans hfl').symm ((hS.apart l hl l0 hl0 _ (mem_lvAt_of_rate hN hl) lv'
            hlv').2.1)
        · have hmn := osKids_names hdo _ hin
          rw [hfl'] at hmn
          rw [hfl', ha, hr]; exact hlrK l hl hmn
  obtain ⟨N2, L2, hW2, hD2, hN2, hK2⟩ := os_kids_blockO (fs := fs) (cert := cert) (κ := κ) Lk σ cs2 Bd
    hc2 (bk + N1)
  refine ⟨N1 + N2, L1 ++ L2, ps, by rw [hps, hksl], ?_, disj_append hD1 hD2 hW1 hW2 le_rfl,
    fun Bk hB ↦ ?_, ?_⟩
  · rw [within_append]
    exact ⟨hW1.mono le_rfl (by omega), hW2.mono (by omega) (by omega)⟩
  · have hb := osKids_bound fs Bk hdo
    rw [hcs, List.map_append, List.sum_append] at hb
    have := hN1 Bk hB
    have := hN2 Bk hB
    omega
  · intro rd R Dacc hl hL hLk hWm hR' hRW
    have hL12 : MemL rd L1 ∧ MemL rd L2 := Main.memL_append.mp hL
    rw [hcs]
    refine kidsFromIn_append _ _ Dacc bk N1 N2 (fun _ ↦ False) (fun _ ↦ False) ?_ fun Dacc' _ ↦ ?_
    · exact hK1 rd R Dacc hl hL12.1 hLk (fun i h ↦ by simpa using hWm i (by rw [hps] at h ⊢; exact h))
        hR' (fun l h1 h2 p i hi ↦ hRW l (by rw [hksl] at h2; omega) p i hi)
    · exact hK2 rd R Dacc' hl hL12.2 hLk fun i hi ↦ Or.inl (hR' i hi)

end
end LeanVM.Guest.B1
