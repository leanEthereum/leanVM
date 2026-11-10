import Rv64Verifier.Proofs.Pcs.VsoTailFinalT
import Rv64Verifier.Proofs.Pcs.VsoTailRoot
import Rv64Verifier.Proofs.Pcs.VsoTailAt
import Rv64Verifier.Proofs.Pcs.VsoLoop

/-!
# `verify_stacked_opening`'s level tail, whole

From the rows' values (`Rowed`): the intro message and the push (`tailFront`), the glue
(`GlueSpec`), the branch (`b510`), and the next level's head (`backEdge`, `nextHead`) or the final
level's tail (`finalIn`). `levelTail` proves `LevelTail`.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts LeanVM.Protocol

/-- **A level's tail.** -/
theorem levelTail (hDt : MultilinearContracts.DotSpec) (hRP : RoundPolyErrSpec)
    (hG : GrowOneFreshSpec 0x8000c7d0 80 8) (hGl : GlueSpec) : LevelTail := by
  intro s x h t u v w m t' k r ℓ Wl lf q res pend d qs hpre hc hnf hm hsl hk hr
  have ha := atR hpre hm hsl hk hr
  have hb := bounds hpre
  have hF := ha.head.facts
  have hlt := ha.head.lvl
  have hsl0 := hpre.heap.lo
  have hst : heapNext s ≤ heapNext t := le_trans hF.hs (le_trans hF.hL ha.ht)
  obtain ⟨hpwv, hpwe, hpwl, hpwb⟩ := ha.pw
  have hpwraw := hpwv.raw
  simp only [RawVecOk, Buf] at hpwraw
  have hpwlc := hpwv.len
  have hP := ha.pnd
  have hpraw := hP.vec.raw
  simp only [RawVecOk, Buf] at hpraw
  -- the front
  obtain ⟨g, r1, hg⟩ := tailFront hDt hRP hG hpre ha.pc ha.sp ha.inv ha.heap ha.rows
    ⟨hpwraw.1, by
      rcases hpwb with h0 | h0
      · exact Or.inl (by omega)
      · exact Or.inr ⟨by have := ha.tu; omega, by have := ha.wr; omega⟩⟩
    ha.m816 hP.vec ⟨hpraw.1, by
      by_cases hc : (vecCap r (s.getReg .x2 - 616)).toNat * 80 = 0
      · exact Or.inl hc
      · rcases hpraw.2 with h0 | h0
        · exact absurd h0 hc
        · refine Or.inr ⟨?_, h0.2⟩
          have := (hP.fresh (vecPtr r (s.getReg .x2 - 616)) (Or.inl (by simp only [Within]; omega))).1
          omega⟩
  rcases hg with hfl | ⟨qi, hf⟩
  · exact ⟨g, r1, Or.inl hfl⟩
  -- the glue
  obtain ⟨z, r2, hz⟩ := hGl s g _ _ _ hpre (glueIn hpre ha hf)
  rcases hz with hd | hgo
  · exact ⟨z, r1.trans r2, Or.inl (Or.inl hd)⟩
  -- the branch
  have heZ : TailEnd s x h t u w r g z z z ℓ Wl _ lf q res qi pend d qs :=
    ⟨ha, hf, hgo, fun _ ↦ rfl, fun _ _ ↦ rfl, DFrame.refl _ _, rfl, by
      rw [glue_eq, gacc_folds]; rfl⟩
  have kZ := heZ.keepSlot hpre
  obtain ⟨z1, r3, zm, zr, zx1, hbr⟩ := b510 hpre hgo.pc hgo.sp
    ((kZ _ (Or.inr (Or.inl (by addr_omega [hb])))).trans ha.m184)
    ((kZ _ (Or.inr (Or.inl (by addr_omega [hb])))).trans ha.m152) hlt
  have r13 := r1.trans (r2.trans r3)
  -- the mirror to `z1`
  have hpw' : eListAt r (vecPtr r (s.getReg .x2 - 488)) (r.getReg .x27).toNat =
      Verifier.powers (eAt w (s.getReg .x2 - 384)) qs.length := by
    rw [hf.hlen, ← hpwe]; rfl
  have V1 := RunsK.intro ha.value hr.value hpw' hf
  have hrst := hpre.root.stack
  rw [stackLo_vso, vso_stack] at hrst
  have hrf := hpre.root.free
  simp only [Outside] at hrf
  have hgi := glueIn hpre ha hf
  have hgbuf := hgi.glued.2.2
  have hgv := hgi.glued.1.raw
  simp only [RawVecOk, Buf] at hgv
  have hq := hgi.quad.2.2
  have hhz := hgo.heap.hi
  have hsg : heapNext s ≤ heapNext g := le_trans hst (le_trans (le_trans ha.tu
    (le_trans ha.uw ha.wr)) hf.mono)
  have V2 : RunsK s z1 ℓ 1 _ _ := (V1.keep hpre hf.inv hgo.fr (fun a ha' ↦ by
      rcases ha' with ha' | ha' | ha' | ha' | ha' | ha' | ha' | ha'
      · rcases hq with h0 | h0
        · simp only [Within] at ha'; omega
        · exact Or.inr (Or.inr (Or.inl ⟨by simp only [Within] at ha'; omega,
            by simp only [Within] at ha'; have := hf.heap.hi; omega⟩))
      · rcases hgv.2 with h0 | h0
        · simp only [Within] at ha'; omega
        · rcases hgbuf with h1 | h1
          · have : (vecCap g (s.getReg .x2 - 664)).toNat = 0 := by rw [h1]; rfl
            simp only [Within] at ha'; omega
          · exact Or.inr (Or.inr (Or.inl ⟨by simp only [Within] at ha'; omega,
              by simp only [Within] at ha'; have := hf.heap.hi; omega⟩))
      · exact Or.inl (by addr_omega [ha', hb])
      · exact Or.inl (by addr_omega [ha', hb])
      · exact Or.inl (by addr_omega [ha', hb])
      · exact Or.inl (by addr_omega [ha', hb])
      · exact Or.inr (Or.inl ha')
      · simp only [Fresh] at ha'
        exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))
    fun y hy hw ↦ by
      rcases hw with hw | hw | hw | hw | hw | hw | hw | hw
      · rcases hq with h0 | h0
        · simp only [Within] at hw; omega
        · rcases hrf.1 with h1 | h1
          · addr_omega [hy, hw, h1, h0]
          · have := hf.heap.hi; addr_omega [hy, hw, h1, h0, this]
      · rcases hgv.2 with h0 | h0
        · simp only [Within] at hw; omega
        · rcases hgbuf with h1 | h1
          · have : (vecCap g (s.getReg .x2 - 664)).toNat = 0 := by rw [h1]; rfl
            simp only [Within] at hw; omega
          · rcases hrf.1 with h2 | h2
            · addr_omega [hy, hw, h1, h2]
            · have := hf.heap.hi; addr_omega [hy, hw, h0, h2, this]
      · addr_omega [hy, hw, hrst, hb]
      · addr_omega [hy, hw, hrst, hb]
      · addr_omega [hy, hw, hrst, hb]
      · addr_omega [hy, hw, hrst, hb]
      · addr_omega [hy, hw, hrf.2]
      · simp only [Fresh] at hw
        rcases hrf.1 with h1 | h1
        · addr_omega [hy, hw.1, h1, hsg]
        · addr_omega [hy, hw.2, h1, hhz]).same
      (by simp only [digestAt, zm]) fun T hT ↦ tr_congr hT zm
  have hWf : (Model.Pcs.glueRust (eAt w (s.getReg .x2 - 384)) (Model.Pcs.foldSt Wl lf q).1
      (pend ++ [(qi, Model.Pcs.GluedWeightRust.queries (mlOf s Wl lf) qs
        (Verifier.powers (eAt w (s.getReg .x2 - 384)) qs.length))])).folds = Wl.folds ++ lf := by
    rw [glue_eq, gacc_folds]; rfl
  have hlen : (Wl.folds ++ lf).length =
      ((Model.Pcs.ladderFolds (K0 s + 1)).take (ℓ + 1)).sum := by
    rw [List.length_append, hnf, ha.fo.lfl, take_succ_sum]; rfl
  have hzn1 : heapNext z1 = heapNext z := by simp only [heapNext, zm]
  rcases hbr with ⟨hl, hpc1⟩ | ⟨hl, hpc1⟩
  · -- the final level
    have he : TailEnd s x h t u w r g z z1 z1 ℓ Wl _ lf q res qi pend d qs :=
      ⟨ha, hf, hgo, zm, zr, DFrame.refl _ _, hzn1, hWf⟩
    have hnx : nextRoots s ℓ d = [] := by rw [nextRoots, ite_eq_left_of_eq_true _ _ (eq_true hl)]
    rw [hnx, Model.Pcs.afterIntro, afterGlue_last hl] at V2
    refine ⟨z1, r13, Or.inr (Or.inr ⟨_, res, finalIn hpre hc hnf hl he hpc1 ?_⟩)⟩
    have := V2.toRunsF hpre
    rw [hWf]
    exact this
  · -- the next level
    have kz (y : Word) (hy : (s.getReg .x2 - 1040).toNat ≤ y.toNat ∧
        y.toNat + 8 ≤ (s.getReg .x2 - 904).toNat ∨ (s.getReg .x2 - 896).toNat ≤ y.toNat ∧
        y.toNat + 8 ≤ (s.getReg .x2 - 832).toNat ∨ (s.getReg .x2 - 816).toNat ≤ y.toNat ∧
        y.toNat + 8 ≤ (s.getReg .x2 - 784).toNat ∨ (s.getReg .x2 - 776).toNat ≤ y.toNat ∧
        y.toNat + 8 ≤ (s.getReg .x2 - 664).toNat ∨ (s.getReg .x2 - 592).toNat ≤ y.toNat ∧
        y.toNat + 8 ≤ (s.getReg .x2 - 512).toNat) : z1.getMem y = r.getMem y :=
      (zm y).trans (kZ y hy)
    have hNR : NR z1 (s.getReg .x2) d := by
      obtain ⟨n0, n1, n2, n3, n4⟩ := ha.root
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [kz _ (Or.inr (Or.inr (Or.inr (Or.inr (by addr_omega [hb])))))]; exact n0
      · rw [kz _ (Or.inl (by addr_omega [hb]))]; exact n1
      · rw [kz _ (Or.inl (by addr_omega [hb]))]; exact n2
      · rw [kz _ (Or.inl (by addr_omega [hb]))]; exact n3
      · rw [kz _ (Or.inl (by addr_omega [hb]))]; exact n4
    obtain ⟨u', r4, hpc', hdig, hfr', hregs', h5, h8, h10, h17, h22, h23, h27⟩ :=
      backEdge hpre hpc1 (by rw [zr .x2 (by decide), hgo.sp])
        ((kz _ (Or.inr (Or.inl (by addr_omega [hb])))).trans ha.m200) hNR
    obtain ⟨hnx8, -⟩ := sfacts hpre
    have hvn : heapNext u' = heapNext z := by
      rw [← hzn1]; simp only [heapNext]
      refine congrArg BitVec.toNat (hfr' nextAddr fun i hi hw ↦ ?_)
      rcases hw with hw | hw | hw
      · addr_omega [hw, hi, hrf.2]
      · addr_omega [hw, hi, hb, hnx8]
      · addr_omega [hw, hi, hb, hnx8]
    have he : TailEnd s x h t u w r g z z1 u' ℓ Wl _ lf q res qi pend d qs :=
      ⟨ha, hf, hgo, zm, zr, hfr', hvn, hWf⟩
    have hnx : nextRoots s ℓ d = [(d, rootShape s (ℓ + 1))] := by rw [nextRoots, ite_eq_right_of_eq_false _ _ (eq_false hl)]
    rw [hnx, Model.Pcs.afterIntro, afterGlue_next hl] at V2
    have hz1inv : InvR s z1 (z1.getMem nextAddr) := by
      rw [zm]; exact Inv.same' hgo.inv zm (zr .x2 (by decide))
    have hV := V2.toRuns rfl hdig fun T hT ↦ tr_keep hpre hz1inv hT hfr' fun a ha' ↦ by
      rcases ha' with ha' | ha' | ha'
      · exact Or.inr (Or.inr (Or.inr ha'))
      · exact Or.inl (by addr_omega [ha', hb])
      · exact Or.inl (by addr_omega [ha', hb])
    refine ⟨u', r13.trans r4, Or.inr (Or.inl ⟨_, nextHead hpre hl he
      ⟨hpc', hdig, hfr', hregs', h5, h8, h10, h17, h22, h23, h27⟩ zx1 hV, by rw [hWf, hlen]⟩)⟩

end Rv64Verifier.Proofs.Pcs.Vso
