import Rv64Verifier.Proofs.Pcs.VsoTailAt
import Rv64Verifier.Proofs.Pcs.VsoLoop

/-!
# `verify_stacked_opening`'s level loop: what the rows read

`leavesSpec`: at `eq_kernel`'s return the slices at `S - 832` point to the leaves the Merkle checks
read (`wordsAt`), their words kept since; `s7` holds the quadratic's length as `S - 808` does; the
division constant at `S - 880` is the head's.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts LeanVM.Protocol

/-- From `lam`'s end through the Merkle checks, the slices and `eq_kernel`. -/
theorem Merkled.frWk {s : MachineState} {x : LCtx} {h t u v w m t' k : MachineState} {ℓ : ℕ}
    {Wl : Model.Pcs.WhirLocals} {lf q res : List E}
    {pend : List (List E × Model.Pcs.GluedWeightRust)} {d : Digest} {qs : List Word}
    (hpre : VsoPre s) (hm : Merkled s x h t u v w m ℓ Wl lf q res pend d qs)
    (hsl : Slices s m t') (hk : Kerneled s t' k lf) :
    DFrame w k (X1 s w k) ∧ heapNext w ≤ heapNext k := by
  have hb := bounds hpre
  have m1 := hm.mo.mono
  have m2 := hsl.mono
  have m3 := hk.mono
  have hm' : heapNext t' ≤ heapNext k := m3
  refine ⟨((hm.mo.fr.mono fun a ha ↦ ?_).trans (hsl.fr.mono fun a ha ↦ ?_) fun _ h ↦ h).trans
    (hk.fr.mono fun a ha ↦ ?_) fun _ h ↦ h, by omega⟩
  · rcases ha with (ha | ha | ha) | ((ha | ha | ha | ha) | ha | ha | ha)
    · exact Or.inl ha
    · exact Or.inr (Or.inr (Or.inl ha))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))
    · exact Or.inr (Or.inl ha)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ha)))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ha))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr ⟨ha.1, by omega⟩))))))))))
  · rcases ha with ha | ha | ha | ha | ha
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (by addr_omega [ha, hb])))))))))
    · exact Or.inr (Or.inl (by addr_omega [ha, hb]))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ha))))))))))
    · simp only [Fresh] at ha
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr ⟨by omega, by omega⟩))))))))))
  · rcases ha with ha | ha | ha | ha
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))))
    · exact Or.inr (Or.inl (by addr_omega [ha, hb]))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ha))))))))))
    · simp only [Fresh] at ha
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr ⟨by omega, by omega⟩))))))))))


section
variable {s : MachineState} {x : LCtx} {h t u v w m t' k : MachineState} {ℓ : ℕ}
  {Wl : Model.Pcs.WhirLocals} {lf q res : List E}
  {pend : List (List E × Model.Pcs.GluedWeightRust)} {d : Digest} {qs : List Word}

/-- The leaves the Merkle checks read, path by path. -/
theorem wordsAt_eq (s w : MachineState) :
    wordsAt s w = (List.range (vecLen w (phaseH s w)).toNat).map fun j ↦
      (w.readWords (vecPtr w (vecPtr w (phaseH s w) + BitVec.ofNat 64 (56 * j)))
        (vecLen w (vecPtr w (phaseH s w) + BitVec.ofNat 64 (56 * j))).toNat).map BF64.ofBitVec := by
  have e : phaseHdr w (proofAt w (s.getReg .x10)) (w.getMem (s.getReg .x10 + 352)).toNat =
      phaseH s w := by
    simp only [phaseHdr, phaseH, vecPtr, proofAt]
    rw [show w.getMem (s.getReg .x10) + 24 + 8 = w.getMem (s.getReg .x10) + 32 by rv_eval []]
  simp only [wordsAt, phaseAt, pathAddr, e, List.map_map]
  rfl

/-- `s7` holds the quadratic's length as `S - 808` does. -/
theorem Merkled.k808 (hpre : VsoPre s) (hm : Merkled s x h t u v w m ℓ Wl lf q res pend d qs)
    (hsl : Slices s m t') (hk : Kerneled s t' k lf) :
    k.getMem (s.getReg .x2 - 808) = k.getReg .x23 := by
  obtain ⟨F1, -⟩ := hm.frWk hpre hsl hk
  rw [hk.regs .x23 (by decide), hsl.regs .x23 (by decide), hm.mo.x23]
  exact F1 _ (X1.slot hpre hk.heap (o := 808) (by unfold x1Free; decide))

/-- The division constant at `S - 880`, the head's. -/
theorem Merkled.k880 (hpre : VsoPre s) (hm : Merkled s x h t u v w m ℓ Wl lf q res pend d qs)
    (hsl : Slices s m t') (hk : Kerneled s t' k lf) :
    k.getMem (s.getReg .x2 - 880) = 0xffffffffaaaaaaab := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hS := Region.bounds hpre.self.ok.self
  have hIs := hpre.self.stack
  rw [stackLo_vso, vso_stack] at hIs
  obtain ⟨T0, hl⟩ := hm.lo
  obtain ⟨F1, -⟩ := hm.frWk hpre hsl hk
  obtain ⟨F0, -⟩ := hm.frU hpre
  have hf := hm.op.fo
  have hh := hf.head
  have hhu := (hm.op.inv.heap hpre.heap).hi
  have hht := hf.heap.hi
  have hraw := hh.folds.vec.raw
  simp only [RawVecOk, Buf] at hraw
  have mht : heapNext h ≤ heapNext t := hf.mono
  refine (F1 _ (X1.slot hpre hk.heap (o := 880) (by unfold x1Free; decide))).trans
    ((F0 _ (X0.slot hpre (hl.inv.heap hpre.heap) (o := 880) (by decide))).trans
    ((hm.op.fr _ fun i hi hw ↦ ?_).trans ((hf.fr _ fun i hi hw ↦ ?_).trans hh.m160)))
  · rcases hw with hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw
    all_goals first
      | addr_omega [hw, hi, hb]
      | addr_omega [hw, hi, hb, hnx]
      | (simp only [W] at hw; addr_omega [hw, hi, hb, hS, hIs])
      | addr_omega [hw.2, hi, hb, hhu]
  · rcases hw with hw | hw | hw | hw | hw | hw | hw | hw | hw | hw
    all_goals first
      | addr_omega [hw, hi, hb]
      | addr_omega [hw, hi, hb, hnx]
      | (simp only [W] at hw; addr_omega [hw, hi, hb, hS, hIs])
      | addr_omega [hw.2, hi, hb, hht]
      | (rcases hraw.2 with h0 | h0
         · simp only [Within] at hw; omega
         · addr_omega [hw, hi, hb, h0, hht, mht])

/-- Pair `i` of the slices, the path's leaf pointer and length. -/
theorem Merkled.slice (hpre : VsoPre s) (hm : Merkled s x h t u v w m ℓ Wl lf q res pend d qs)
    (hsl : Slices s m t') (hk : Kerneled s t' k lf) {i : ℕ}
    (hi : i < (vecLen w (phaseH s w)).toNat) :
    sliceP s k i = vecPtr w (vecPtr w (phaseH s w) + BitVec.ofNat 64 (56 * i)) ∧
      sliceL s k i = vecLen w (vecPtr w (phaseH s w) + BitVec.ofNat 64 (56 * i)) := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hP := hm.mi.phase hm.mo.hdr
  have hsw : heapNext s ≤ heapNext w := hm.mi.inv.mono
  have hwm := hm.mo.mono
  have hmt := hsl.mono
  have htk : heapNext t' ≤ heapNext k := hk.mono
  have hhk := hk.heap.hi
  have hhm := (hm.mo.inv.heap hpre.heap).hi
  simp only [heapEnd] at hhk hhm
  have P' : k.getMem (s.getReg .x2 - 832) = t'.getMem (s.getReg .x2 - 832) :=
    hk.fr _ fun j hj hw ↦ by
      rcases hw with hw | hw | hw | hw
      · addr_omega [hw, hj, hb]
      · addr_omega [hw, hj, hb]
      · addr_omega [hw, hj, hb, hnx]
      · addr_omega [hw.2, hj, hb, hhk]
  have hbuf := hsl.buf
  rw [hm.mo.x20] at hbuf
  simp only [NewBuf] at hbuf
  have hsli := hsl.sliced
  rw [hm.mo.x20, hm.mo.x22] at hsli
  obtain ⟨e1, e2⟩ := hsli i hi
  have hpath := hP.paths
  simp only [BufOk] at hpath
  rcases hpath with h0 | ⟨hR, hC⟩
  · omega
  have hRb := Region.bounds hR
  rcases hbuf.2 with h0 | h0
  · omega
  have kP (o : ℕ) (ho : o + 8 ≤ 16 * (vecLen w (phaseH s w)).toNat) :
      k.getMem (t'.getMem (s.getReg .x2 - 832) + BitVec.ofNat 64 o) =
        t'.getMem (t'.getMem (s.getReg .x2 - 832) + BitVec.ofNat 64 o) :=
    hk.fr _ fun j hj hw ↦ by
      rcases hw with hw | hw | hw | hw
      · addr_omega [hw, hj, hb, h0, ho, hhk, htk]
      · addr_omega [hw, hj, hb, h0, ho, hhk, htk]
      · addr_omega [hw, hj, hb, hnx, h0, ho, hhk, htk]
      · addr_omega [hw.1, hj, h0, ho, hhk, htk]
  have kW (o : ℕ) (ho : o + 8 ≤ 56 * (vecLen w (phaseH s w)).toNat) :
      m.getMem (vecPtr w (phaseH s w) + BitVec.ofNat 64 o) =
        w.getMem (vecPtr w (phaseH s w) + BitVec.ofNat 64 o) :=
    Clear.keep hpre hm.mo.fr hC (hm.mo.inv.heap hpre.heap).hi (by omega)
      (by addr_omega [hRb, ho]) (by addr_omega [hRb, ho])
  refine ⟨?_, ?_⟩
  · show k.getMem (k.getMem (s.getReg .x2 - 832) + BitVec.ofNat 64 (16 * i)) =
      w.getMem (vecPtr w (phaseH s w) + BitVec.ofNat 64 (56 * i) + BitVec.ofNat 64 8)
    rw [P', kP _ (by omega), e1, kW _ (by omega), addOf]
  · show k.getMem (k.getMem (s.getReg .x2 - 832) + BitVec.ofNat 64 (16 * i + 8)) =
      w.getMem (vecPtr w (phaseH s w) + BitVec.ofNat 64 (56 * i) + BitVec.ofNat 64 16)
    rw [P', kP _ (by omega), e2, kW _ (by omega), addOf]

/-- **What the rows read**: the leaves the Merkle checks read. -/
theorem Merkled.leavesAt (hpre : VsoPre s)
    (hm : Merkled s x h t u v w m ℓ Wl lf q res pend d qs) (hsl : Slices s m t')
    (hk : Kerneled s t' k lf) : LeavesAt s k (wordsAt s w) := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hS := Region.bounds hpre.self.ok.self
  have hIf := hpre.self.free
  simp only [Outside] at hIf
  have hP := hm.mi.phase hm.mo.hdr
  have hsw : heapNext s ≤ heapNext w := hm.mi.inv.mono
  have hwm := hm.mo.mono
  have hmt := hsl.mono
  have htk : heapNext t' ≤ heapNext k := hk.mono
  have hhk := hk.heap.hi
  simp only [heapEnd] at hhk
  have hsl0 := hpre.heap.lo
  simp only [heapStart] at hsl0
  obtain ⟨F1, hwk⟩ := hm.frWk hpre hsl hk
  have hlen : (wordsAt s w).length = (vecLen w (phaseH s w)).toNat := by rw [wordsAt_eq]; simp
  have x20 : k.getReg .x20 = vecLen w (phaseH s w) :=
    (hk.regs .x20 (by decide)).trans ((hsl.regs .x20 (by decide)).trans hm.mo.x20)
  refine ⟨by rw [x20, hlen], ?_, fun i hi ↦ ?_, fun i hi ↦ ?_⟩
  · rw [hlen]
    have P' : k.getMem (s.getReg .x2 - 832) = t'.getMem (s.getReg .x2 - 832) :=
      hk.fr _ fun j hj hw ↦ by
        rcases hw with hw | hw | hw | hw
        · addr_omega [hw, hj, hb]
        · addr_omega [hw, hj, hb]
        · addr_omega [hw, hj, hb, hnx]
        · addr_omega [hw.2, hj, hb, hhk]
    have hbuf := hsl.buf
    rw [hm.mo.x20] at hbuf
    simp only [NewBuf] at hbuf
    rw [P']
    rcases hbuf.2 with h0 | h0
    · exact Or.inl (by omega)
    refine Or.inr ⟨heap_region (by addr_omega [h0, hsl0, hsw, hwm]) (by addr_omega [h0, hhk, htk])
      hbuf.1, ⟨⟨Or.inl (by addr_omega [h0, htk]), ?_, ?_⟩, ?_⟩⟩
    · simp only [Apart]; addr_omega [h0, hb, hhk, htk]
    · simp only [Apart]; addr_omega [h0, hhk, htk]
    · simp only [Apart]
      rcases hIf.1 with h1 | h1
      · addr_omega [h0, hS, h1, hsw, hwm]
      · addr_omega [h0, hS, h1, hhk, htk]
  · rw [hlen] at hi
    obtain ⟨ep, el⟩ := hm.slice hpre hsl hk hi
    rw [ep, el]
    rcases hP.leaves i hi with h0 | ⟨hR, hC⟩
    · exact Or.inl h0
    · exact Or.inr ⟨hR, hC.mono (by omega)⟩
  · have hi' : i < (vecLen w (phaseH s w)).toNat := by rw [hlen] at hi; exact hi
    obtain ⟨ep, el⟩ := hm.slice hpre hsl hk hi'
    simp only [wordsAt_eq, List.getElem_map, List.getElem_range]
    rw [ep, el]
    congr 1
    rcases hP.leaves i hi' with h0 | ⟨hR, hC⟩
    · rw [h0]; rfl
    · have hRb := Region.bounds hR
      obtain ⟨⟨c1, c2, c3⟩, c4⟩ := hC
      refine DFrame.readWords' F1 (fun a ha hin ↦ ?_) (by omega)
      rcases ha with ha | ha | ha | ha | ha | ha | ha | ha | ha | ha | ha | ha
      all_goals first
        | (simp only [Apart] at c4; addr_omega [ha, hin, c4, hS])
        | (simp only [Apart] at c2; addr_omega [ha, hin, c2, hb])
        | (simp only [Apart] at c3; addr_omega [ha, hin, c3])
        | (rcases c1 with c1 | c1
           · addr_omega [ha.1, hin, c1]
           · addr_omega [ha.2, hin, c1, hhk])

/-- **`LeavesSpec`**. -/
theorem leavesSpec : LeavesSpec := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hpre hm hsl hk ↦
  ⟨hm.leavesAt hpre hsl hk, hm.k808 hpre hsl hk, hm.k880 hpre hsl hk⟩

end

end Rv64Verifier.Proofs.Pcs.Vso
