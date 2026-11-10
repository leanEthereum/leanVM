import Rv64Verifier.Proofs.Pcs.VsoTailHead

/-!
# `verify_stacked_opening`'s level tail: into the final level's tail

At the last level the branch at `0x8000b510` goes to `0x8000b8ec` with nothing written since the
glue: `VsoFinalIn` (`finalIn`), the residual where the grinding spilled it.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts LeanVM.Protocol

/-- **The final level's tail**, at `0x8000b8ec`. -/
theorem finalIn {s : MachineState} {x : LCtx} {h t u w r g z v : MachineState} {ℓ : ℕ}
    {Wl Wl' : Model.Pcs.WhirLocals} {lf qq res q : List E}
    {pend : List (List E × Model.Pcs.GluedWeightRust)} {d : Digest} {qs : List Word}
    (hpre : VsoPre s) (hc : Cfg s x.QP x.QL)
    (hnf : Wl.folds.length = ((Model.Pcs.ladderFolds (K0 s + 1)).take ℓ).sum)
    (hl : ℓ = K0 s + 1) (he : TailEnd s x h t u w r g z v v ℓ Wl Wl' lf qq res q pend d qs)
    (hpc : v.pc = 0x8000b8ec)
    (hV : RunsF Transcript.OpeningsAt s v (finalTailM (cfgOf s) (basisOf s x) res
      ((s.getReg .x12).toNat - Wl'.folds.length) Wl')) :
    VsoFinalIn Transcript.OpeningsAt s x v Wl' res := by
  have hb := bounds hpre
  have ha := he.ha
  have hhd := ha.head
  have hF := hhd.facts
  have hfo := ha.fo
  have hgo := he.hgo
  have hf := he.hf
  have hlt := hhd.lvl
  have kS := he.keepSlot hpre
  have hzn : heapNext v = heapNext z := he.vn
  obtain ⟨q896, q23, q808, -⟩ := ha.quad
  obtain ⟨Ff, Fg, Fq, -, Fz, Fal⟩ := endFacts hpre he
  have rg := hfo.regions
  have hlf := he.wf
  have hlen : (Wl.folds ++ lf).length = ((Model.Pcs.ladderFolds (K0 s + 1)).take (ℓ + 1)).sum := by
    rw [List.length_append, hnf, hfo.lfl, take_succ_sum]; rfl
  have hle := folds_le hc hlt
  have hx12 := hc.logN
  have hP := ha.pnd
  have hpraw := hP.vec.raw
  simp only [RawVecOk, Buf] at hpraw
  have hhr := ha.heap.hi
  simp only [heapEnd] at hhr
  obtain ⟨hgv, -, -⟩ := hhd.glued
  have hgraw := hgv.raw
  simp only [RawVecOk, Buf] at hgraw
  obtain ⟨gc, gp, -, -, -⟩ := gluedG hpre ha hf
  have g896 : g.getMem (s.getReg .x2 - 896) = t.getReg .x22 := by
    rw [← q896]
    exact hf.fr _ fun i hi hw ↦ by
      rcases hw with hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw
      all_goals first
        | addr_omega [hw, hi, hb]
        | (have hI := hpre.self; have hS := Region.bounds hI.ok.self; have hIs := hI.stack
           rw [stackLo_vso, vso_stack] at hIs; addr_omega [hw, hi, hb, hS, hIs])
        | (obtain ⟨hnx, -⟩ := sfacts hpre; addr_omega [hw, hi, hb, hnx])
        | (rcases hpraw.2 with h0 | h0
           · simp only [Within] at hw; omega
           · addr_omega [hw, hi, hb, h0, hhr])
        | (simp only [Fresh] at hw; have := hf.heap.hi; simp only [heapEnd] at this
           addr_omega [hw.2, hi, hb, this])
  have g23 : g.getReg .x23 = t.getReg .x23 := (hf.regs .x23 (by decide)).trans q23
  refine {
    cfg := hhd.cfg
    mark := hhd.mark
    fr := tailLM hpre ha hf hgo he.zm (DFrame.refl _ _) (by rw [hzn])
    heap := ⟨by rw [hzn]; exact hgo.heap.lo, by rw [hzn]; exact hgo.heap.hi⟩
    mono := by rw [hzn]; have := hhd.mono; have := ha.ht; have := ha.tu; have := ha.uw; have := ha.wr
               have := hf.mono; have := hgo.mono; omega
    pc := hpc
    sp := by rw [he.zr .x2 (by decide), hgo.sp]; rfl
    x9 := by
      rw [he.zr .x9 (by decide), hgo.regs .x9 (by decide), hf.regs .x9 (by decide), ha.x9]
    x26 := by rw [he.zr .x26 (by decide), hgo.regs .x26 (by decide), hf.x26, ha.m128]
    fle := by rw [hlf, hlen]; omega
    m112 := by rw [kS _ (Or.inl (by addr_omega [hb])), ha.m112, hlf]
    m168 := by rw [kS _ (Or.inr (Or.inl (by addr_omega [hb]))), ha.m872, hlf]
    m224 := by rw [kS _ (Or.inr (Or.inr (Or.inl (by addr_omega [hb])))), ha.m816]
    m248 := by rw [kS _ (Or.inr (Or.inr (Or.inl (by addr_omega [hb])))), ha.m248]
    folds := Ff
    glued := Fg
    frozen := fun i hi y hy ↦ ⟨(Fz i hi y hy).1, (Fz i hi y hy).2.1⟩
    aligned := Fal
    quad := by
      rw [kS _ (Or.inr (Or.inl (by addr_omega [hb]))), q896,
        kS _ (Or.inr (Or.inr (Or.inl (by addr_omega [hb])))), q808]
      exact Fq
    res := by
      rw [kS _ (Or.inl (by addr_omega [hb])), kS _ (Or.inl (by addr_omega [hb]))]
      obtain ⟨r1, r2, r3⟩ := ha.rsd
      refine ⟨?_, r2, ?_⟩
      · rw [← r1]
        unfold Rv64Verifier.eListAt
        apply List.map_congr_left
        intro k hk
        simp only [List.mem_range] at hk
        rcases r3 with h0 | h0
        · omega
        have hq := rg.qb
        have hgb := rg.gb
        have htu := ha.tu
        have kw (m : ℕ) (hm : m < 3) :
            v.getMem (r.getMem (s.getReg .x2 - 968) + BitVec.ofNat 64 (24 * k) +
              BitVec.ofNat 64 (8 * m)) =
            r.getMem (r.getMem (s.getReg .x2 - 968) + BitVec.ofNat 64 (24 * k) +
              BitVec.ofNat 64 (8 * m)) :=
          he.keepHeap hpre _ (by addr_omega [h0, hk, hm, hF.hL, ha.ht, ha.uw, ha.wr, hhr])
            (by addr_omega [h0, hk, hm, hhr, ha.uw, ha.wr])
            (fun i hi hw ↦ by
              rw [g896, g23] at hw
              rcases hq with h1 | h1
              · simp only [Within] at hw; omega
              · addr_omega [h0, hk, hm, hhr, hw, hi, h1, ha.tu, ha.uw, ha.wr])
            (fun i hi hw ↦ by
              rw [gp, gc] at hw
              rcases hgb with h1 | h1
              · simp only [Within] at hw; omega
              · addr_omega [h0, hk, hm, hhr, hw, hi, h1, ha.ht, ha.uw, ha.wr])
            (fun i hi hw ↦ by
              rcases ha.rsdp with h1 | h1
              · omega
              · have : (vecCap r (s.getReg .x2 - 616)).toNat = 0 := by rw [h1]; rfl
                simp only [Within] at hw; omega)
        refine eAt_congr ?_ ?_ ?_
        · simpa using kw 0 (by decide)
        · simpa [BitVec.add_assoc] using kw 1 (by decide)
        · simpa [BitVec.add_assoc] using kw 2 (by decide)
      · rcases r3 with h0 | h0
        · exact Or.inl h0
        · refine Or.inr ⟨by have := hF.hL; have := ha.ht; omega, ?_⟩
          have := ha.uw; have := ha.wr; have := hf.mono; have := hgo.mono; rw [hzn]; omega
    rlen := by
      have h1 := ha.rlen hl
      rw [hlf, h1, Nat.mod_eq_of_lt (by omega)]
    value := hV }

end Rv64Verifier.Proofs.Pcs.Vso
