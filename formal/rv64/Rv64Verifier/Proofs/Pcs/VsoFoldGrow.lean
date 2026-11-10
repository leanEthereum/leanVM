import Rv64Verifier.Proofs.Pcs.VsoFoldSample

/-!
# `verify_stacked_opening`'s level loop: room in `folds`

`0x8000a21c` calls `grow_one` on the full `folds` (`S - 688`), which returns at `0x8000a228`.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem growF (hG : GrowOneFreshSpec 0x80011c78 24 8) {s : MachineState} {x : LCtx}
    {h u : MachineState} {ℓ : ℕ} {Wl : Model.Pcs.WhirLocals} {j : ℕ} {lf q : List E} {c : E}
    (hpre : VsoPre s) (hs : Smp s x h u ℓ Wl j lf q c) (hpc : u.pc = 0x8000a21c)
    (hfull : Wl.folds.length + j = (vecCap u (s.getReg .x2 - 688)).toNat) :
    ∃ v, Reaches Image.code u v ∧ (Dead Image.code v ∨ (Smp s x h v ℓ Wl j lf q c ∧
      v.pc = 0x8000a228)) := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hsp := hs.sp
  have inv := FW.inv hpre hs.head hs.fr hs.heap hs.mono (hsp.trans hs.head.sp.symm)
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000a21c_spec hpc trivial
  have k₁ := b8000a21c_keeps h₁
  have hm₁ := b8000a21c_mem_same h₁
  have inv₁ : InvR s t₁ (t₁.getMem nextAddr) := by
    rw [hm₁]; exact Inv.same' inv hm₁ (k₁ .x2 (by decide))
  have hn₁ : heapNext t₁ = heapNext u := by simp only [heapNext, hm₁]
  have hFv : VecOk t₁ (s.getReg .x2 - 688) 24 8 := by
    have hv := hs.F.1
    have e0 : vecCap t₁ (s.getReg .x2 - 688) = vecCap u (s.getReg .x2 - 688) := hm₁ _
    have e1 : vecPtr t₁ (s.getReg .x2 - 688) = vecPtr u (s.getReg .x2 - 688) := hm₁ _
    have e2 : vecLen t₁ (s.getReg .x2 - 688) = vecLen u (s.getReg .x2 - 688) := hm₁ _
    exact ⟨by simp only [RawVecOk, Buf, e0, e1, hn₁]; exact hv.raw, by rw [e0, e2]; exact hv.len⟩
  obtain ⟨t₂, hr₂, hv₂⟩ := callGrow24 hG hpre inv₁
    ⟨by rw [hn₁]; exact hs.heap.lo, by rw [hn₁]; exact hs.heap.hi⟩ (b8000a21c_pc h₁)
    (by rw [b8000a21c_x10 h₁, hsp]; rv_eval []) (by addr_omega [hb]) hFv
  rcases hv₂ with hd | ⟨hpc₂, hpres₂, hheap₂, hmono₂, X₂, hvF, heF, hlF, hcF, hnF⟩
  · exact ⟨t₂, hr₁.trans hr₂, Or.inl hd⟩
  have X : DFrame u t₂ fun a ↦ Within a (s.getReg .x2 - 688) 16 ∨
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
  have hLk := vecE_keep X hs.LF.1 (fun a ha ↦ by
      refine ⟨fun hw ↦ ?_, fun hw ↦ ?_⟩
      · rcases ha with ha | ha | ha | ha
        · addr_omega [ha, hw, hb]
        · addr_omega [ha, hw, hb]
        · addr_omega [ha, hw, hb, hnx]
        · simp only [Fresh] at ha; addr_omega [ha.2, hw, hb, hhi]
      · rcases hB.LF with h0 | h0
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
  have hnF' := NewBuf.widen (h := h) hnF (by rw [hn₁]; exact hs.mono)
  have hfresh (a : Word) (ha : Fresh u t₂ a) :
      heapNext h ≤ a.toNat ∧ a.toNat < (t₂.getMem nextAddr).toNat := by
    have := hs.mono; simp only [Fresh, heapNext] at ha this ⊢; omega
  have hap : Apart (vecPtr t₂ (s.getReg .x2 - 688)) ((vecCap t₂ (s.getReg .x2 - 688)).toNat * 24)
      (vecPtr t₂ (s.getReg .x2 - 640)) ((vecCap t₂ (s.getReg .x2 - 640)).toNat * 24) ∧
      Apart (vecPtr t₂ (s.getReg .x2 - 688)) ((vecCap t₂ (s.getReg .x2 - 688)).toNat * 24)
        (u.getReg .x22) (24 * (u.getReg .x23).toNat) ∧
      Apart (vecPtr t₂ (s.getReg .x2 - 640)) ((vecCap t₂ (s.getReg .x2 - 640)).toNat * 24)
        (u.getReg .x22) (24 * (u.getReg .x23).toNat) := by
    rw [hLk.2.2.1, hLk.2.2.2.1]
    refine ⟨?_, ?_, hs.ap.2.2⟩
    · rcases hnF.2 with h0 | h0
      · exact Or.inl h0
      · rcases hB.LF with h1 | h1
        · exact Or.inr (Or.inl h1)
        · exact Or.inr (Or.inr (Or.inr (by rw [hn₁] at h0; omega)))
    · rcases hnF.2 with h0 | h0
      · exact Or.inl h0
      · rcases hB.Q with h1 | h1
        · exact Or.inr (Or.inl h1)
        · exact Or.inr (Or.inr (Or.inr (by rw [hn₁] at h0; omega)))
  have hRB := RB.carry2 (fl' := Wl.folds ++ lf) (lfs' := lf) hpre hs.toRB X (fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb]))))
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
    ⟨hvF, by rw [heF]; simp only [vecEs, eListAt, eAt, vecPtr, vecLen, hm₁]; exact hs.F.2.1, Or.inr hnF'⟩
    ⟨hLk.1, by rw [hLk.2.1]; exact hs.LF.2.1, by
      rw [hLk.2.2.1, hLk.2.2.2.1]; exact NewBuf.grow hs.LF.2.2 hmono⟩
    hap
  have hcu : vecCap u (s.getReg .x2 - 688) = vecCap t₁ (s.getReg .x2 - 688) := by
    simp only [vecCap, hm₁]
  have hLp := hLk.2.2.1
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
  refine ⟨t₂, hr₁.trans hr₂, Or.inr ⟨{
    toRB := hRB
    pc := Or.inl ⟨by rw [hpc₂, returnAddress_eq, b8000a21c_x1 h₁]; decide, by
      rw [← hcu] at hcF; omega⟩
    x8 := by rw [hreg .x8 (by decide), hs.x8]
    x19 := by rw [hreg .x19 (by decide), hs.x19, hLp]
    x20 := by rw [hreg .x20 (by decide), hs.x20]
    x21 := by rw [hreg .x21 (by decide), hs.x21]
    x24 := by rw [hreg .x24 (by decide), hs.x24]
    jlt := hs.jlt
    lfl := hs.lfl
    chal := by rw [keep128]; exact hs.chal
    value := hs.value.keep hpre inv X (fun a ha ↦ by
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
          · addr_omega [hy, hw.2, h0, hhi] }, by
    rw [hpc₂, returnAddress_eq, b8000a21c_x1 h₁]; decide⟩⟩

end Rv64Verifier.Proofs.Pcs.Vso
