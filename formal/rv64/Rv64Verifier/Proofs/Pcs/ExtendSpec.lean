import Rv64Verifier.Proofs.Pcs.ExtendEntry

/-!
# `Vec<StackClaim>::extend_desugared` meets its contract

The epilogue at `0x80009d7c` restores the saved registers and returns; `extend_spec` runs the
prologue, the loop and the epilogue.
-/

namespace Rv64Verifier.Proofs.Pcs.Extend
open RiscvZkvm.Rv64 Rv64Verifier.Runtime Rv64Verifier.Transcript Rv64Verifier.Pcs
  Rv64Verifier.PcsContracts Rv64Verifier.Model.Pcs Rv64Verifier.Blocks.F37 LeanVM.Parameters
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem epilogue {s u : MachineState} (hpre : Walk.ExtendPreE s) (hd : Done s u) :
    ∃ t, Reaches Image.code u t ∧ t.pc = returnAddress s ∧ Preserves s t ∧ Walk.ExtendPostE s t := by
  have hb := sbounds hpre
  have hv := hpre.stack.valid
  rw [hK] at hv
  have hsp := hd.p.sp
  obtain ⟨t, hr, h⟩ := Sym.BlockSpec.reaches b80009d7c_spec hd.pc (by
    rv_eval [hsp]
    and_intros <;> valid_access hv [hb])
  have m := b80009d7c_mem_same h
  have sl := hd.p.slots
  simp only [slots, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
    and_true] at sl
  obtain ⟨s1, s8, s9, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27⟩ := sl
  have a (o p : Nat) (hop : o + p = 240) : s.getReg .x2 - BitVec.ofNat 64 240 + BitVec.ofNat 64 o =
      s.getReg .x2 - BitVec.ofNat 64 p := by addr_omega [hb, hop]
  have hheap := hd.p.heap hpre.heap
  have hnt : heapNext t = heapNext u := by simp only [heapNext, m]
  have hPt : vecPtr t (s.getReg .x10) = vecPtr u (s.getReg .x10) := m _
  have hLt : vecLen t (s.getReg .x10) = vecLen u (s.getReg .x10) := m _
  refine ⟨t, hr, ?_, ?_, ⟨⟨by rw [hnt]; exact hheap.lo, by rw [hnt]; exact hheap.hi⟩,
    by rw [hnt]; exact hd.p.mono, ?_, ?_, ?_⟩, fun i hi k hk ↦ ?_, fun i h1 h2 ↦ ?_⟩
  · rw [b80009d7c_pc h, hsp, show (232 : Word) = BitVec.ofNat 64 232 from rfl, a 232 8 rfl, s1,
      returnAddress_eq]
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [b80009d7c_x2 h, hsp]; addr_omega [hb]
    · rw [b80009d7c_x8 h, hsp, show (224 : Word) = BitVec.ofNat 64 224 from rfl, a 224 16 rfl, s8]
    · rw [b80009d7c_x9 h, hsp, show (216 : Word) = BitVec.ofNat 64 216 from rfl, a 216 24 rfl, s9]
    · rw [b80009d7c_x18 h, hsp, show (208 : Word) = BitVec.ofNat 64 208 from rfl, a 208 32 rfl, s18]
    · rw [b80009d7c_x19 h, hsp, show (200 : Word) = BitVec.ofNat 64 200 from rfl, a 200 40 rfl, s19]
    · rw [b80009d7c_x20 h, hsp, show (192 : Word) = BitVec.ofNat 64 192 from rfl, a 192 48 rfl, s20]
    · rw [b80009d7c_x21 h, hsp, show (184 : Word) = BitVec.ofNat 64 184 from rfl, a 184 56 rfl, s21]
    · rw [b80009d7c_x22 h, hsp, show (176 : Word) = BitVec.ofNat 64 176 from rfl, a 176 64 rfl, s22]
    · rw [b80009d7c_x23 h, hsp, show (168 : Word) = BitVec.ofNat 64 168 from rfl, a 168 72 rfl, s23]
    · rw [b80009d7c_x24 h, hsp, show (160 : Word) = BitVec.ofNat 64 160 from rfl, a 160 80 rfl, s24]
    · rw [b80009d7c_x25 h, hsp, show (152 : Word) = BitVec.ofNat 64 152 from rfl, a 152 88 rfl, s25]
    · rw [b80009d7c_x26 h, hsp, show (144 : Word) = BitVec.ofNat 64 144 from rfl, a 144 96 rfl, s26]
    · rw [b80009d7c_x27 h, hsp, show (136 : Word) = BitVec.ofNat 64 136 from rfl, a 136 104 rfl, s27]
  · exact ⟨by simp only [RawVecOk, Buf, vecPtr, vecCap, heapNext, m]; exact hd.vec.raw,
      by simp only [vecLen, vecCap, m]; exact hd.vec.len⟩
  · refine Eq.trans ?_ hd.value
    have hP : vecPtr t (s.getReg .x10) = vecPtr u (s.getReg .x10) := m _
    have hL : vecLen t (s.getReg .x10) = vecLen u (s.getReg .x10) := m _
    rw [stackClaimsAt, stackClaimsAt, hP, hL]
    exact claimsAt_congr fun i _ ↦ (claim_move (P := fun _ _ ↦ True) (Q := fun _ _ ↦ True)
      (fun _ _ ↦ m _) (by unfold ClaimRegions; split_ifs <;> simp)
      (fun _ _ _ ↦ (DFrame.of_same m fun _ ↦ False).eListAt fun _ _ h ↦ h) (fun _ _ h ↦ h) trivial).1
  · refine (hd.p.frame.mono fun a h ↦ ?_).trans (DFrame.of_same m _) fun _ h ↦ h
    rcases h with (h | h) | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (by simp only [Fresh, hnt] at h ⊢; exact h))))
  · rw [hPt, m]
    exact hd.words i hi k hk
  · rw [hLt] at h2
    exact heapBuf_move (m _) (m _) (le_of_eq hnt.symm) (by rw [hPt]; exact hd.added i h1 h2)

/-- **`Vec<StackClaim>::extend_desugared` meets its contract as `walk` calls it**, given its
callees'. -/
theorem extend_spec (hS : MultilinearContracts.SelectorSpec)
    (hC : MultilinearContracts.SliceConcatSpec) (hG : GrowSpec) : Walk.ExtendSpecE := by
  intro s hpc hpre
  obtain ⟨t, hr, hd | hh⟩ := prologue hpc hpre
  · obtain ⟨v, hrv, hpcv, hpres, hpost⟩ := epilogue hpre hd
    exact ⟨v, hr.trans hrv, Or.inl ⟨hpcv, hpres, hpost⟩⟩
  · obtain ⟨v, hrv, hdv | he⟩ := loop hS hC hG hpre _ 0 t (Nat.le_refl _) hh
    · exact ⟨v, hr.trans hrv, Or.inr hdv⟩
    · obtain ⟨x, hrx, hpcx, hpres, hpost⟩ := epilogue hpre he.done
      exact ⟨x, hr.trans (hrv.trans hrx), Or.inl ⟨hpcx, hpres, hpost⟩⟩

end Rv64Verifier.Proofs.Pcs.Extend
