import Rv64Verifier.Proofs.Pcs.VsoFoldPush

/-!
# `verify_stacked_opening`'s level loop: room in `level_folds`

`0x8000a260` calls `grow_one` on the full `level_folds` (`S - 640`); it returns at `0x8000a26c`,
which reloads the buffer's pointer into `s3`.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem growLF (hG : GrowOneFreshSpec 0x80011c78 24 8) {s : MachineState} {x : LCtx}
    {h u : MachineState} {ℓ : ℕ} {Wl : Model.Pcs.WhirLocals} {j : ℕ} {lf q : List E} {c : E}
    (hpre : VsoPre s) (hs : PF s x h u ℓ Wl j lf q c) (hpc : u.pc = 0x8000a260)
    (hfull : j = (vecCap u (s.getReg .x2 - 640)).toNat) :
    ∃ v, Reaches Image.code u v ∧ (Dead Image.code v ∨ (PF s x h v ℓ Wl j lf q c ∧
      v.pc = 0x8000a270)) := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hsp := hs.sp
  have inv := FW.inv hpre hs.head hs.fr hs.heap hs.mono (hsp.trans hs.head.sp.symm)
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000a260_spec hpc trivial
  have k₁ := b8000a260_keeps h₁
  have hm₁ := b8000a260_mem_same h₁
  have inv₁ : InvR s t₁ (t₁.getMem nextAddr) := by
    rw [hm₁]; exact Inv.same' inv hm₁ (k₁ .x2 (by decide))
  have hn₁ : heapNext t₁ = heapNext u := by simp only [heapNext, hm₁]
  have hLv : VecOk t₁ (s.getReg .x2 - 640) 24 8 := by
    have hv := hs.LF.1
    have e0 : vecCap t₁ (s.getReg .x2 - 640) = vecCap u (s.getReg .x2 - 640) := hm₁ _
    have e1 : vecPtr t₁ (s.getReg .x2 - 640) = vecPtr u (s.getReg .x2 - 640) := hm₁ _
    have e2 : vecLen t₁ (s.getReg .x2 - 640) = vecLen u (s.getReg .x2 - 640) := hm₁ _
    exact ⟨by simp only [RawVecOk, Buf, e0, e1, hn₁]; exact hv.raw, by rw [e0, e2]; exact hv.len⟩
  obtain ⟨t₂, hr₂, hv₂⟩ := callGrow24 hG hpre inv₁
    ⟨by rw [hn₁]; exact hs.heap.lo, by rw [hn₁]; exact hs.heap.hi⟩ (b8000a260_pc h₁)
    (by rw [b8000a260_x10 h₁, hsp]; rv_eval []) (by addr_omega [hb]) hLv
  rcases hv₂ with hd | ⟨hpc₂, hpres₂, hheap₂, hmono₂, X₂, hvL, heL, hlL, hcL, hnL⟩
  · exact ⟨t₂, hr₁.trans hr₂, Or.inl hd⟩
  have X : DFrame u t₂ fun a ↦ Within a (s.getReg .x2 - 640) 16 ∨
      Within a (s.getReg .x2 - 1200) 160 ∨ Within a nextAddr 8 ∨ Fresh u t₂ a :=
    (DFrame.of_same hm₁ _).trans X₂ fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · exact Or.inl ha
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr (by simpa only [Fresh, hn₁] using ha)))
  have hmono : heapNext u ≤ heapNext t₂ := by rw [← hn₁]; exact hmono₂
  have hB := hs.bufs
  have hhi := hheap₂.hi
  have hf := hs.head.facts
  have hFk := vecE_keep X hs.F.1 (fun a ha ↦ by
      refine ⟨fun hw ↦ ?_, fun hw ↦ ?_⟩
      · rcases ha with ha | ha | ha | ha
        · addr_omega [ha, hw, hb]
        · addr_omega [ha, hw, hb]
        · addr_omega [ha, hw, hb, hnx]
        · simp only [Fresh] at ha; addr_omega [ha.2, hw, hb, hhi]
      · rcases hB.F with h0 | h0
        · simp only [Within] at hw; omega
        rcases ha with ha | ha | ha | ha
        · addr_omega [ha, hw, hb, h0.2, hs.heap.hi]
        · addr_omega [ha, hw, hb, h0.2, hs.heap.hi]
        · addr_omega [ha, hw, hnx, h0.2, hs.heap.hi]
        · simp only [Fresh] at ha; addr_omega [ha.1, hw, h0.2])
    (by addr_omega [hb]) hmono hs.heap
  have hreg (r : Reg) (hr : r ∈ calleeSaved) : t₂.getReg r = u.getReg r := by
    rw [hpres₂ r hr]
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact k₁ _ (by decide)
  have hnL' := NewBuf.widen (h := h) hnL (by rw [hn₁]; exact hs.mono)
  have hfresh (a : Word) (ha : Fresh u t₂ a) :
      heapNext h ≤ a.toNat ∧ a.toNat < (t₂.getMem nextAddr).toNat := by
    have := hs.mono; simp only [Fresh, heapNext] at ha this ⊢; omega
  have hap : Apart (vecPtr t₂ (s.getReg .x2 - 688)) ((vecCap t₂ (s.getReg .x2 - 688)).toNat * 24)
      (vecPtr t₂ (s.getReg .x2 - 640)) ((vecCap t₂ (s.getReg .x2 - 640)).toNat * 24) ∧
      Apart (vecPtr t₂ (s.getReg .x2 - 688)) ((vecCap t₂ (s.getReg .x2 - 688)).toNat * 24)
        (u.getReg .x22) (24 * (u.getReg .x23).toNat) ∧
      Apart (vecPtr t₂ (s.getReg .x2 - 640)) ((vecCap t₂ (s.getReg .x2 - 640)).toNat * 24)
        (u.getReg .x22) (24 * (u.getReg .x23).toNat) := by
    rw [hFk.2.2.1, hFk.2.2.2.1]
    refine ⟨?_, hs.ap.2.1, ?_⟩
    · rcases hnL.2 with h0 | h0
      · exact Or.inr (Or.inl h0)
      · rcases hB.F with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (Or.inr (Or.inl (by rw [hn₁] at h0; omega)))
    · rcases hnL.2 with h0 | h0
      · exact Or.inl h0
      · rcases hB.Q with h1 | h1
        · exact Or.inr (Or.inl h1)
        · exact Or.inr (Or.inr (Or.inr (by rw [hn₁] at h0; omega)))
  have hRB := RB.carry2 (fl' := Wl.folds ++ lf ++ [c]) (lfs' := lf) hpre hs.toRB X (fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb])))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb]))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hfresh a ha)))))))))
    (fun a ha ↦ by
      refine ⟨fun hw ↦ ?_, fun hw ↦ ?_⟩
      · rcases ha with ha | ha | ha | ha
        · rcases hw with hw | hw | hw <;> addr_omega [ha, hw, hb]
        · rcases hw with hw | hw | hw <;> addr_omega [ha, hw, hb]
        · rcases hw with hw | hw | hw <;> addr_omega [ha, hw, hb, hnx]
        · simp only [Fresh] at ha
          rcases hw with hw | hw | hw <;> addr_omega [ha.2, hw, hb, hhi]
      · rcases hB.Q with h0 | h0
        · simp only [Within] at hw; omega
        rcases ha with ha | ha | ha | ha
        · addr_omega [ha, hw, hb, h0.2, hs.heap.hi]
        · addr_omega [ha, hw, hb, h0.2, hs.heap.hi]
        · addr_omega [ha, hw, hnx, h0.2, hs.heap.hi]
        · simp only [Fresh] at ha; addr_omega [ha.1, hw, h0.2])
    hheap₂ hmono (fun r hr ↦ hreg r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide))
    ⟨hFk.1, by rw [hFk.2.1]; exact hs.F.2.1, by
      rw [hFk.2.2.1, hFk.2.2.2.1]
      rcases hs.F.2.2 with h0 | h0
      · exact Or.inl h0
      · exact Or.inr (NewBuf.grow h0 hmono)⟩
    ⟨hvL, by rw [heL]; simp only [vecEs, eListAt, eAt, vecPtr, vecLen, hm₁]; exact hs.LF.2.1, hnL'⟩
    hap
  have hcu : vecCap u (s.getReg .x2 - 640) = vecCap t₁ (s.getReg .x2 - 640) := by
    simp only [vecCap, hm₁]
  have hsp₂ : t₂.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := by
    rw [hreg .x2 (by decide), hsp]
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000a26c_spec
    (by rw [hpc₂, returnAddress_eq, b8000a260_x1 h₁]; decide) (by
      rv_eval [hsp₂]; valid_access hpre.stack.valid [hb])
  have k₃ := b8000a26c_keeps h₃
  have hm₃ := b8000a26c_mem_same h₃
  have hRB₃ := RB.carry hpre hRB (DFrame.of_same hm₃ (fun _ ↦ False)) (fun _ h ↦ h.elim)
    (fun _ h ↦ h.elim) ⟨by simp only [heapNext, hm₃]; exact hheap₂.lo,
      by simp only [heapNext, hm₃]; exact hhi⟩ (by simp only [heapNext, hm₃]; exact Nat.le_refl _)
    (fun r hr' ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact k₃ _ (by decide))
  have keep128 : eAt t₂ (s.getReg .x2 - 128) = eAt u (s.getReg .x2 - 128) :=
    X.eAt' (fun y hy hw ↦ by
      rcases hw with hw | hw | hw | hw
      · addr_omega [hy, hw, hb]
      · addr_omega [hy, hw, hb]
      · addr_omega [hy, hw, hb, hnx]
      · simp only [Fresh] at hw; addr_omega [hy, hw.2, hb, hhi]) (by addr_omega [hb])
  have hrst := hpre.root.stack
  rw [stackLo_vso, vso_stack] at hrst
  have hrf := hpre.root.free
  simp only [Outside] at hrf
  have hval := hs.value.keep hpre inv X (fun a ha ↦ by
        rcases ha with ha | ha | ha | ha
        · exact Or.inl (by addr_omega [ha, hb])
        · exact Or.inl (by addr_omega [ha, hb])
        · exact Or.inr (Or.inl ha)
        · simp only [Fresh] at ha
          exact Or.inr (Or.inr (Or.inl ⟨by have := hs.mono; have := hf.hs; have := hf.hL; omega,
            by omega⟩)))
      fun y hy hw ↦ by
        rcases hw with hw | hw | hw | hw
        · addr_omega [hy, hw, hrst, hb]
        · addr_omega [hy, hw, hrst, hb]
        · addr_omega [hy, hw, hrf.2]
        · simp only [Fresh] at hw
          rcases hrf.1 with h0 | h0
          · addr_omega [hy, hw.1, h0, hs.mono, hf.hs, hf.hL]
          · addr_omega [hy, hw.2, h0, hhi]
  have inv₂ : InvR s t₂ (t₂.getMem nextAddr) :=
    FW.inv hpre hs.head hRB.fr hheap₂ (Nat.le_trans hs.mono hmono) (hsp₂.trans hs.head.sp.symm)
  refine ⟨t₃, hr₁.trans (hr₂.trans hr₃), Or.inr ⟨{
    toRB := hRB₃
    pc := Or.inl ⟨b8000a26c_pc h₃, by
      have h1 := hcL
      rw [← hcu] at h1
      simp only [vecCap] at h1 hfull ⊢
      rw [hm₃]; omega⟩
    x19 := by
      rw [b8000a26c_x19 h₃, hsp₂]; simp only [vecPtr, hm₃]; rv_eval []
    x20 := by rw [k₃ .x20 (by decide), hreg .x20 (by decide), hs.x20]
    x21 := by rw [k₃ .x21 (by decide), hreg .x21 (by decide), hs.x21]
    x24 := by rw [k₃ .x24 (by decide), hreg .x24 (by decide), hs.x24]
    jlt := hs.jlt
    lfl := hs.lfl
    chal := by
      have e : eAt t₃ (s.getReg .x2 - 128) = eAt t₂ (s.getReg .x2 - 128) := by simp only [eAt, hm₃]
      rw [e, keep128]; exact hs.chal
    value := hval.keep hpre inv₂ (DFrame.of_same hm₃ (fun _ ↦ False)) (fun _ h ↦ h.elim)
      fun _ _ h ↦ h }, b8000a26c_pc h₃⟩⟩

end Rv64Verifier.Proofs.Pcs.Vso
