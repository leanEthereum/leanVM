import Rv64Verifier.Proofs.Pcs.VsoTailFront

/-!
# `verify_stacked_opening`'s level tail: the push assembled

`RPOut` (the intro message read), `Roomy` (room made) and `Pushed` (the push) make `Fronted`
(`tailFront`).
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts LeanVM.Protocol

/-- What `RPOut` keeps: the frame but `S - 512`, `S - 464`, `S - 384`, and the heap below `r`'s
`NEXT`. -/
theorem RPOut.keep {s r t : MachineState} {q : List E} (hpre : VsoPre s) (ho : RPOut s r t q)
    (hheap : HeapOk r) (y : Word) (hy : (s.getReg .x2 - 1040).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 512).toNat ∨ (s.getReg .x2 - 488).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 464).toNat ∨ (s.getReg .x2 - 440).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 384).toNat ∨ (s.getReg .x2 - 376).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2).toNat ∨ heapNext s ≤ y.toNat ∧ y.toNat + 8 ≤ heapNext r) :
    t.getMem y = r.getMem y := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hI := hpre.self
  have hT := Region.bounds hI.ok.self
  have hIs := hI.stack
  rw [stackLo_vso, vso_stack] at hIs
  have hIf := hI.free
  simp only [Outside] at hIf
  have hhr := hheap.hi
  have hht := ho.heap.hi
  refine ho.fr y fun i hi hw ↦ ?_
  rcases hw with hw | hw | hw | hw | hw | hw | hw
  · rcases hy with hy | hy | hy | hy | hy <;> addr_omega [hw, hi, hy, hb, hhr]
  · rcases hy with hy | hy | hy | hy | hy <;> addr_omega [hw, hi, hy, hb, hhr]
  · rcases hy with hy | hy | hy | hy | hy <;> addr_omega [hw, hi, hy, hb, hhr]
  · rcases hy with hy | hy | hy | hy | hy <;> addr_omega [hw, hi, hy, hb, hhr]
  · rcases hy with hy | hy | hy | hy | hy
    · addr_omega [hw, hi, hy, hb, hT, hIs]
    · addr_omega [hw, hi, hy, hb, hT, hIs]
    · addr_omega [hw, hi, hy, hb, hT, hIs]
    · addr_omega [hw, hi, hy, hb, hT, hIs]
    · rcases hIf.1 with h1 | h1 <;> addr_omega [hw, hi, hy, hT, h1, hhr]
  · rcases hy with hy | hy | hy | hy | hy <;> addr_omega [hw, hi, hy, hb, hnx, hhr]
  · simp only [Fresh] at hw
    rcases hy with hy | hy | hy | hy | hy <;> addr_omega [hw.1, hi, hy, hb, hhr, hw.2, hht]

/-- The pushes' frames and the pending claims, from `r`. -/
theorem assembleA {s r t p g : MachineState} {q : List E} (hpre : VsoPre s) (ho : RPOut s r t q)
    (hp : Roomy s t p) (hg : Pushed s p g) (hheap : HeapOk r)
    (hpb : HS s r (vecPtr r (s.getReg .x2 - 616)) ((vecCap r (s.getReg .x2 - 616)).toNat * 80)) :
    heapNext g = heapNext p ∧ DFrame r g (FrW s r g) ∧
    DFrame t g (fun a ↦ Within a (s.getReg .x2 - 2464) 2464 ∨ Within a nextAddr 8 ∨
      (heapNext s ≤ a.toNat ∧ a.toNat < heapNext r) ∨
      (heapNext t ≤ a.toNat ∧ a.toNat < heapNext g)) := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  have kr := ho.keep hpre hheap
  have ec₅ : vecCap t (s.getReg .x2 - 616) = vecCap r (s.getReg .x2 - 616) :=
    kr _ (Or.inl (by addr_omega [hb]))
  have ep₅ : vecPtr t (s.getReg .x2 - 616) = vecPtr r (s.getReg .x2 - 616) :=
    kr _ (Or.inl (by addr_omega [hb]))
  have el₅ : vecLen t (s.getReg .x2 - 616) = vecLen r (s.getReg .x2 - 616) :=
    kr _ (Or.inl (by addr_omega [hb]))
  have hlenp : vecLen p (s.getReg .x2 - 616) = vecLen r (s.getReg .x2 - 616) := hp.len.trans el₅
  have hlt := hp.lt
  obtain ⟨hQ8, hQb⟩ := hp.buf
  obtain ⟨hP8, hPb⟩ := hpb
  have hhr := hheap.hi
  have hhip := hp.heap.hi
  have hmp := hp.mono
  have hn5r := ho.mono
  have hQb' : heapNext s ≤ (vecPtr p (s.getReg .x2 - 616)).toNat ∧
      (vecPtr p (s.getReg .x2 - 616)).toNat + (vecCap p (s.getReg .x2 - 616)).toNat * 80 ≤
        heapNext p := by
    rcases hQb with h0 | h0
    · omega
    · exact h0
  have nxg : g.getMem nextAddr = p.getMem nextAddr := hg.fr _ fun i hi hw ↦ by
    rcases hw with hw | hw | hw
    · addr_omega [hw, hi, hb, hnx]
    · addr_omega [hw, hi, hb, hnx]
    · addr_omega [hw, hi, hQb', hhip, hlt]
  have hng : heapNext g = heapNext p := by simp only [heapNext, nxg]
  refine ⟨hng, ?_, ?_⟩
  · refine ((ho.fr.mono fun a ha ↦ ?_).trans (hp.fr.mono fun a ha ↦ ?_) fun _ h ↦ h).trans
      (hg.fr.mono fun a ha ↦ ?_) fun _ h ↦ h
    · rcases ha with ha | ha | ha | ha | ha | ha | ha
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ha)))))))
      · exact Or.inr (Or.inr (Or.inl (ha)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (ha))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ha))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ha))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ha)))))))))
      · simp only [Fresh] at ha
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨ha.1, by have := hmp; rw [hng]; omega⟩))))))))))
    · rcases ha with ha | ha | ha | ha | ha
      · exact Or.inl (ha)
      · exact Or.inr (Or.inl (by addr_omega [ha, hb]))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ha)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ha)))))))))
      · simp only [Fresh] at ha
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by rw [hng]; exact ha.2⟩))))))))))
    · rcases ha with ha | ha | ha
      · exact Or.inr (Or.inl (by addr_omega [ha, hb]))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ha)))))
      · rw [hlenp] at ha
        rcases hp.same with ⟨e1, e2⟩ | hnew
        · rw [e1, ep₅] at ha
          rw [e2, ec₅, hlenp] at hlt
          rw [e1, ep₅, e2, ec₅] at hQb'
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hlt, hQb', hhip]))))))))))
        · simp only [NewBuf] at hnew
          rw [hlenp] at hlt
          rcases hnew.2 with h0 | h0
          · omega
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by addr_omega [ha, h0, hn5r, hhip, hlt, hQb'], by rw [hng]; addr_omega [ha, h0, hlt, hhip, hQb']⟩))))))))))
  · refine (hp.fr.mono fun a ha ↦ ?_).trans (hg.fr.mono fun a ha ↦ ?_) fun _ h ↦ h
    · rcases ha with ha | ha | ha | ha | ha
      · exact Or.inl (by addr_omega [ha, hb])
      · exact Or.inl (by addr_omega [ha, hb])
      · exact Or.inl (by addr_omega [ha, hb])
      · exact Or.inr (Or.inl ha)
      · simp only [Fresh] at ha
        exact Or.inr (Or.inr (Or.inr ⟨ha.1, by rw [hng]; exact ha.2⟩))
    · rcases ha with ha | ha | ha
      · exact Or.inl (by addr_omega [ha, hb])
      · exact Or.inl (by addr_omega [ha, hb])
      · rw [hlenp] at ha
        rcases hp.same with ⟨e1, e2⟩ | hnew
        · rw [e1, ep₅] at ha
          rw [e2, ec₅, hlenp] at hlt
          rw [e1, ep₅, e2, ec₅] at hQb'
          refine Or.inr (Or.inr (Or.inl ⟨by addr_omega [ha, hlt, hQb', hhip], ?_⟩))
          rcases hPb with h0 | h0
          · omega
          · addr_omega [ha, hlt, h0, hhr]
        · simp only [NewBuf] at hnew
          rw [hlenp] at hlt
          rcases hnew.2 with h0 | h0
          · omega
          · exact Or.inr (Or.inr (Or.inr ⟨by addr_omega [ha, h0, hlt, hQb', hhip],
              by rw [hng]; addr_omega [ha, h0, hlt, hhip, hQb']⟩))

/-- **`Fronted`**, from the intro message, the room and the push. -/
theorem assemble {s r t p g : MachineState} {q : List E} (hpre : VsoPre s) (ho : RPOut s r t q)
    (hp : Roomy s t p) (hg : Pushed s p g) (hheap : HeapOk r)
    (hinv : InvR s r (r.getMem nextAddr)) (hpv : VecOk r (s.getReg .x2 - 616) 80 8)
    (hpb : HS s r (vecPtr r (s.getReg .x2 - 616)) ((vecCap r (s.getReg .x2 - 616)).toNat * 80)) :
    Fronted s r g q := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hI := hpre.self
  have hS := Region.bounds hI.ok.self
  have hrst := hpre.root.stack
  rw [stackLo_vso, vso_stack] at hrst
  have hrf := hpre.root.free
  simp only [Outside] at hrf
  have hrs := hpre.rootSponge
  obtain ⟨hng, FR, Z⟩ := assembleA hpre ho hp hg hheap hpb
  have kr := ho.keep hpre hheap
  have ec₅ : vecCap t (s.getReg .x2 - 616) = vecCap r (s.getReg .x2 - 616) :=
    kr _ (Or.inl (by addr_omega [hb]))
  have ep₅ : vecPtr t (s.getReg .x2 - 616) = vecPtr r (s.getReg .x2 - 616) :=
    kr _ (Or.inl (by addr_omega [hb]))
  have el₅ : vecLen t (s.getReg .x2 - 616) = vecLen r (s.getReg .x2 - 616) :=
    kr _ (Or.inl (by addr_omega [hb]))
  have hlenp : vecLen p (s.getReg .x2 - 616) = vecLen r (s.getReg .x2 - 616) := hp.len.trans el₅
  have hlt := hp.lt
  obtain ⟨hQ8, hQb⟩ := hp.buf
  obtain ⟨hP8, hPb⟩ := hpb
  have hhr := hheap.hi
  have hhip := hp.heap.hi
  have hmp := hp.mono
  have hn5r := ho.mono
  have hsr : heapNext s ≤ heapNext r := hinv.mono
  have hsl := hpre.heap.lo
  have hqb2 : heapNext s ≤ (vecPtr p (s.getReg .x2 - 616)).toNat ∧
      (vecPtr p (s.getReg .x2 - 616)).toNat + (vecCap p (s.getReg .x2 - 616)).toNat * 80 ≤
        heapNext p := by
    rcases hQb with h0 | h0
    · omega
    · exact h0
  have nxg : g.getMem nextAddr = p.getMem nextAddr := BitVec.eq_of_toNat_eq hng
  have kgp (y : Word) (hy : (s.getReg .x2 - 1040).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 600).toNat ∨ (s.getReg .x2 - 592).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 408).toNat ∨ (s.getReg .x2 - 384).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2).toNat) : g.getMem y = p.getMem y :=
    hg.fr y fun i hi hw ↦ by
      rcases hw with hw | hw | hw
      · rcases hy with hy | hy | hy <;> addr_omega [hw, hi, hy, hb]
      · rcases hy with hy | hy | hy <;> addr_omega [hw, hi, hy, hb]
      · rcases hy with hy | hy | hy <;> addr_omega [hw, hi, hy, hb, hqb2, hhip, hlt]
  have kpt (y : Word) (hy : (s.getReg .x2 - 1040).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 904).toNat ∨ (s.getReg .x2 - 896).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 616).toNat ∨ (s.getReg .x2 - 600).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2).toNat) : p.getMem y = t.getMem y :=
    hp.fr y fun i hi hw ↦ by
      rcases hw with hw | hw | hw | hw | hw
      · rcases hy with hy | hy | hy <;> addr_omega [hw, hi, hy, hb]
      · rcases hy with hy | hy | hy <;> addr_omega [hw, hi, hy, hb]
      · rcases hy with hy | hy | hy <;> addr_omega [hw, hi, hy, hb]
      · rcases hy with hy | hy | hy <;> addr_omega [hw, hi, hy, hb, hnx]
      · simp only [Fresh] at hw; rcases hy with hy | hy | hy <;> addr_omega [hw.2, hi, hy, hb, hhip]
  have hpA : pAddr g s (vecLen r (s.getReg .x2 - 616)).toNat =
      pAddr p s (vecLen p (s.getReg .x2 - 616)).toNat := by
    simp only [pAddr, hg.ptr, hlenp]
  have i8 : vecPtr g (pAddr g s (vecLen r (s.getReg .x2 - 616)).toNat) = t.getReg .x8 := by
    simp only [vecPtr]; rw [hpA, hg.e8, hp.regs .x8 (by decide)]
  have i16 : vecLen g (pAddr g s (vecLen r (s.getReg .x2 - 616)).toNat) = t.getReg .x19 := by
    rw [show vecLen g (pAddr g s (vecLen r (s.getReg .x2 - 616)).toNat) =
      g.getMem (pAddr g s (vecLen r (s.getReg .x2 - 616)).toNat + 16) from rfl, hpA, hg.e16,
      hp.regs .x19 (by decide)]
  have i0 : vecCap g (pAddr g s (vecLen r (s.getReg .x2 - 616)).toNat) = t.getReg .x21 := by
    simp only [vecCap]; rw [hpA, hg.e0, hp.regs .x21 (by decide)]
  have hilen := ho.ilen
  obtain ⟨hI8, hIb⟩ := ho.ibuf
  have hhit := ho.heap.hi
  have htg : heapNext t ≤ heapNext g := by rw [hng]; exact hmp
  have hhig : heapNext g ≤ heapEnd := by rw [hng]; exact hhip
  refine {
    pc := hg.pc
    sp := hg.sp
    inv := by
      rw [nxg]
      exact Inv.step' hpre hp.inv hg.fr (fun a ha ↦ by
          rcases ha with ha | ha | ha
          · exact frame_wr hpre (by addr_omega [ha, hb])
          · exact frame_wr hpre (by addr_omega [ha, hb])
          · exact Or.inr (Or.inr (Or.inr ⟨by addr_omega [ha, hqb2, hhip, hlt],
              by addr_omega [ha, hqb2, hhip, hlt]⟩)))
        (fun a ha ↦ by
          rcases ha with ha | ha | ha
          · addr_omega [ha, hb]
          · addr_omega [ha, hb]
          · addr_omega [ha, hb, hqb2, hhip, hlt]) nxg (le_refl _) hp.inv.fits
        (hg.sp.trans hp.sp.symm)
    heap := ⟨hng ▸ hp.heap.lo, hhig⟩
    mono := by omega
    fr := FR
    regs := fun q hq ↦ by
      rw [hg.regs q ((by decide : ∀ q ∈ [Reg.x9, .x23], q ∈ [Reg.x8, .x9, .x19, .x20, .x21, .x23,
        .x24, .x27]) q hq), hp.regs q ((by decide : ∀ q ∈ [Reg.x9, .x23], q ∈ [Reg.x8, .x9, .x19,
        .x21, .x23, .x26]) q hq), ho.regs q ((by decide : ∀ q ∈ [Reg.x9, .x23],
        q ∈ [Reg.x9, .x23, .x26]) q hq)]
    x18 := hg.x18.trans hg.ptr.symm
    x22 := hg.x22.trans hg.len.symm
    x25 := by
      rw [hg.x25]
      exact (kpt _ (Or.inr (Or.inl (by addr_omega [hb])))).trans (kr _ (Or.inl (by addr_omega [hb])))
    x26 := by
      rw [hg.x26]
      exact (kpt _ (Or.inl (by addr_omega [hb]))).trans (kr _ (Or.inl (by addr_omega [hb])))
    len := by rw [hg.len, hlenp]
    pnew := by
      rcases hp.same with ⟨e1, e2⟩ | hnew
      · exact Or.inl ⟨hg.ptr.trans (e1.trans ep₅), hg.cap.trans (e2.trans ec₅)⟩
      · refine Or.inr ?_
        simp only [NewBuf] at hnew ⊢
        rw [hg.ptr, hg.cap]
        exact ⟨hnew.1, hnew.2.imp id fun h ↦ ⟨by omega, by rw [hng]; exact h.2⟩⟩
    vec := by
      have hcl := (vecCap p (s.getReg .x2 - 616)).isLt
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simp only [RawVecOk, Buf]
        rw [hg.ptr, hg.cap, hng]
        exact ⟨hQ8, Or.inr ⟨by omega, hqb2.2⟩⟩
      · rw [hg.len, hg.cap]
        simp only [BitVec.toNat_add, show (1 : Word).toNat = 1 from rfl]
        omega
      · rw [hg.ptr, hg.cap]
        exact ⟨hQ8, Or.inr ⟨hqb2.1, by rw [hng]; exact hqb2.2⟩⟩
    old := fun o ho1 hoN ↦ by
      have hlr := hpv.len
      have hlt' : (vecLen r (s.getReg .x2 - 616)).toNat < (vecCap p (s.getReg .x2 - 616)).toNat :=
        hlenp ▸ hlt
      have hPb' : heapNext s ≤ (vecPtr r (s.getReg .x2 - 616)).toNat ∧
          (vecPtr r (s.getReg .x2 - 616)).toNat + (vecCap r (s.getReg .x2 - 616)).toNat * 80 ≤
            heapNext r := by
        rcases hPb with h0 | h0
        · omega
        · exact h0
      rw [hg.ptr, hg.fr _ fun i hi hw ↦ by
          rcases hw with hw | hw | hw
          · addr_omega [hw, hi, hb, hqb2, hhip, hlt', hoN]
          · addr_omega [hw, hi, hb, hqb2, hhip, hlt', hoN]
          · rw [hlenp] at hw; addr_omega [hw, hi, hqb2, hhip, hlt', hoN],
        hp.old o ho1 (by rw [el₅]; exact hoN), ep₅]
      exact kr _ (Or.inr (Or.inr (Or.inr (Or.inr ⟨by addr_omega [hPb', hoN, hlr, hhr],
        by addr_omega [hPb', hoN, hlr, hhr]⟩))))
    intro := by
      refine ⟨⟨?_, by rw [i16, i0]; exact hilen⟩, ?_, ?_⟩
      · simp only [RawVecOk, Buf]
        rw [i8, i0]
        refine ⟨hI8, hIb.imp id fun h ↦ ⟨by omega, by omega⟩⟩
      · simp only [vecEs]
        rw [i8, i16, ← ho.intro]
        exact Z.eListAt fun i hi hw ↦ by
          rcases hIb with h0 | h0
          · omega
          · rcases hw with hw | hw | hw | hw
            · addr_omega [hw, hi, h0, hilen, hb, hhit]
            · addr_omega [hw, hi, h0, hilen, hnx, hhit]
            · addr_omega [hw.2, hi, h0, hilen]
            · addr_omega [hw.1, hi, h0, hilen]
      · simp only [NewBuf]
        rw [i8, i0]
        exact ⟨hI8, hIb.imp id fun h ↦ ⟨h.1, by omega⟩⟩
    w24 := by
      rw [hpA, hg.e24]
      exact (kpt _ (Or.inl (by addr_omega [hb]))).trans (kr _ (Or.inl (by addr_omega [hb])))
    w32 := by
      rw [hpA, hg.e32]
      exact (kpt _ (Or.inr (Or.inl (by addr_omega [hb])))).trans (kr _ (Or.inl (by addr_omega [hb])))
    w40 := by rw [hpA, hg.e40, hp.regs .x26 (by decide), ho.regs .x26 (by decide)]
    w48 := by
      rw [hpA, hg.e48]
      exact (kpt _ (Or.inr (Or.inr (by addr_omega [hb])))).trans
        (kr _ (Or.inr (Or.inl (by addr_omega [hb]))))
    w56 := by
      rw [hpA, hg.e56]
      exact (kpt _ (Or.inr (Or.inr (by addr_omega [hb])))).trans
        (kr _ (Or.inr (Or.inl (by addr_omega [hb]))))
    w64 := by
      rw [hpA, hg.e64]
      exact (kpt _ (Or.inr (Or.inr (by addr_omega [hb])))).trans
        (kr _ (Or.inr (Or.inl (by addr_omega [hb]))))
    w72 := by
      rw [hpA, hg.e72]
      exact (kpt _ (Or.inr (Or.inl (by addr_omega [hb])))).trans (kr _ (Or.inl (by addr_omega [hb])))
    one := hg.one
    hlen := ho.hlen
    dig := digest_keep FR (root_bound hpre) fun y hy hw ↦ by
      rcases hw with hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw
      · addr_omega [hy, hw, hrst, hb]
      · addr_omega [hy, hw, hrst, hb]
      · addr_omega [hy, hw, hrst, hb]
      · addr_omega [hy, hw, hrst, hb]
      · addr_omega [hy, hw, hrst, hb]
      · addr_omega [hy, hw, hrst, hb]
      · addr_omega [hy, hw, hrst, hb]
      · addr_omega [hy, hw, hrs]
      · addr_omega [hy, hw, hrf.2]
      · rcases hPb with h0 | h0
        · simp only [Within] at hw; omega
        · rcases hrf.1 with h1 | h1 <;> addr_omega [hy, hw, h1, h0, hhr]
      · simp only [Fresh] at hw
        rcases hrf.1 with h1 | h1 <;> addr_omega [hy, hw.1, hw.2, h1, hsr, hhig]
    value := fun T hT ↦ by
      obtain ⟨T', e, hT', h1, h2, h3⟩ := ho.value T hT
      refine ⟨T', e, tr_keep hpre ho.inv hT' Z fun a ha ↦ ?_, h1, h2, h3⟩
      rcases ha with ha | ha | ha | ha
      · exact Or.inl ha
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr (Or.inl ⟨ha.1, by omega⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)) }

/-- **From the rows to the glue**, or an `Err`, or a dead end. -/
theorem tailFront (hDt : MultilinearContracts.DotSpec) (hRP : RoundPolyErrSpec)
    (hG : GrowOneFreshSpec 0x8000c7d0 80 8) {s r : MachineState} (hpre : VsoPre s)
    (hpc : r.pc = 0x8000b42c) (hsp : r.getReg .x2 = s.getReg .x2 - 1040)
    (hinv : InvR s r (r.getMem nextAddr)) (hheap : HeapOk r)
    (hrows : HS s r (r.getReg .x25) (24 * (r.getReg .x27).toNat))
    (hpw : HS s r (vecPtr r (s.getReg .x2 - 488)) (24 * (vecLen r (s.getReg .x2 - 488)).toNat))
    (h816 : r.getMem (s.getReg .x2 - 816) = s.getReg .x10)
    (hpv : VecOk r (s.getReg .x2 - 616) 80 8)
    (hpb : HS s r (vecPtr r (s.getReg .x2 - 616)) ((vecCap r (s.getReg .x2 - 616)).toNat * 80)) :
    ∃ g, Reaches Image.code r g ∧ (FailR s g ∨ ∃ q, Fronted s r g q) := by
  have hb := bounds hpre
  obtain ⟨t, r1, ht⟩ := tailRP hDt hRP hpre hpc hsp hinv hheap hrows hpw h816
  rcases ht with hf | ⟨q, ho⟩
  · exact ⟨t, r1, Or.inl hf⟩
  have kr := ho.keep hpre hheap
  have ec : vecCap t (s.getReg .x2 - 616) = vecCap r (s.getReg .x2 - 616) :=
    kr _ (Or.inl (by addr_omega [hb]))
  have ep : vecPtr t (s.getReg .x2 - 616) = vecPtr r (s.getReg .x2 - 616) :=
    kr _ (Or.inl (by addr_omega [hb]))
  have el : vecLen t (s.getReg .x2 - 616) = vecLen r (s.getReg .x2 - 616) :=
    kr _ (Or.inl (by addr_omega [hb]))
  have hmo := ho.mono
  have hpv' : VecOk t (s.getReg .x2 - 616) 80 8 := by
    have hraw := hpv.raw
    simp only [RawVecOk, Buf] at hraw
    refine ⟨?_, by rw [ec, el]; exact hpv.len⟩
    simp only [RawVecOk, Buf]
    rw [ec, ep]
    exact ⟨hraw.1, hraw.2.imp id fun h ↦ ⟨h.1, by omega⟩⟩
  have hpb' : HS s t (vecPtr t (s.getReg .x2 - 616)) ((vecCap t (s.getReg .x2 - 616)).toNat * 80) := by
    rw [ec, ep]
    exact ⟨hpb.1, hpb.2.imp id fun h ↦ ⟨h.1, by omega⟩⟩
  obtain ⟨p, r2, hp⟩ := room hG hpre ho.pc ho.sp ho.inv ho.heap hpv' hpb'
  rcases hp with hd | hp
  · exact ⟨p, r1.trans r2, Or.inl (Or.inl hd)⟩
  obtain ⟨g, r3, hg⟩ := push498 hpre hp.pc hp.sp hp.heap hp.lt hp.buf hp.x22
  exact ⟨g, r1.trans (r2.trans r3), Or.inr ⟨q, assemble hpre ho hp hg hheap hinv hpv hpb⟩⟩

end Rv64Verifier.Proofs.Pcs.Vso
