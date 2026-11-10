import Rv64Verifier.Proofs.Bus.VbbLayouts

/-!
# `verify_bus_balance`: the epilogue and the `Err` exit

`0x80007114` restores the saved registers and returns. `0x80007104` writes `Err` (`errNiche` in
`claims`' capacity, the error at `+8`, `+16`) through `out`, kept in `s2`, and falls into it.
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem slot {s u : MachineState} (hpre : BusBalancePre s) (h : Inv s u) (k i : Nat)
    (hi : i < 13) (hk : k = 1336 - 8 * i) :
    u.getMem (u.getReg .x2 + BitVec.ofNat 64 k) = s.getReg (savedRegs.getD i .x0) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  rw [← h.saved i hi, h.sp]
  congr 1
  addr_omega [hb1, hk, hi]

/-- The epilogue returns to the caller with its saved registers. -/
theorem epilogue {s u : MachineState} (hpre : BusBalancePre s) (h : Inv s u)
    (hpc : u.pc = 0x80007114) :
    ∃ t, Reaches Image.code u t ∧ t.pc = returnAddress s ∧ Preserves s t ∧
      ∀ a, t.getMem a = u.getMem a := by
  obtain ⟨hb1, hb2, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  obtain ⟨t, hr, ht⟩ := Sym.BlockSpec.reaches b80007114_spec hpc (by
    rv_eval [h.sp]
    and_intros <;> valid_access hval [hb1])
  have x2 := b80007114_x2 ht
  rw [h.sp] at x2
  rv_eval [] at x2
  refine ⟨t, hr, ?_, preserves_of x2 ?_ ?_ ?_ ?_ fun r hr' ↦ ?_, b80007114_mem_same ht⟩
  · rw [b80007114_pc ht, returnAddress_eq]
    exact congrArg (· &&& _) (slot hpre h 1336 0 (by decide) rfl)
  · rw [b80007114_x8 ht]; exact slot hpre h 1328 1 (by decide) rfl
  · rw [b80007114_x9 ht]; exact slot hpre h 1320 2 (by decide) rfl
  · rw [b80007114_x18 ht]; exact slot hpre h 1312 3 (by decide) rfl
  · rw [b80007114_x19 ht]; exact slot hpre h 1304 4 (by decide) rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [b80007114_x20 ht]; exact slot hpre h 1296 5 (by decide) rfl
    · rw [b80007114_x21 ht]; exact slot hpre h 1288 6 (by decide) rfl
    · rw [b80007114_x22 ht]; exact slot hpre h 1280 7 (by decide) rfl
    · rw [b80007114_x23 ht]; exact slot hpre h 1272 8 (by decide) rfl
    · rw [b80007114_x24 ht]; exact slot hpre h 1264 9 (by decide) rfl
    · rw [b80007114_x25 ht]; exact slot hpre h 1256 10 (by decide) rfl
    · rw [b80007114_x26 ht]; exact slot hpre h 1248 11 (by decide) rfl
    · rw [b80007114_x27 ht]; exact slot hpre h 1240 12 (by decide) rfl

/-- What every return leaves: the heap in shape, memory changed only where the contract allows,
the caller's registers. -/
structure Exit (s t : MachineState) : Prop where
  pc : t.pc = returnAddress s
  preserves : Preserves s t
  heap : HeapOk t
  mono : heapNext s ≤ heapNext t
  frame : DFrame s t (W s t)

/-- The epilogue from a state past the prologue. -/
theorem exit {s u : MachineState} (hpre : BusBalancePre s) (h : Inv s u) (hpc : u.pc = 0x80007114) :
    ∃ t, Reaches Image.code u t ∧ Exit s t ∧ ∀ a, t.getMem a = u.getMem a := by
  obtain ⟨t, hr, hpc', hp, hm⟩ := epilogue hpre h hpc
  have hn : heapNext t = heapNext u := by simp only [heapNext, hm]
  exact ⟨t, hr, ⟨hpc', hp, ⟨hn ▸ h.heap.lo, hn ▸ h.heap.hi⟩, hn ▸ h.mono,
    (h.frame.trans (DFrame.of_same hm fun _ ↦ False) fun _ h ↦ h.elim).mono fun a ha ↦
      W.mono hn.ge ha⟩, hm⟩

/-- The `Err` exit: `errNiche` in the result's first capacity. -/
theorem errExit {s u : MachineState} (hpre : BusBalancePre s) (h : Inv s u) (R : Regs s u)
    (hpc : u.pc = 0x80007104) :
    ∃ t, Reaches Image.code u t ∧ Exit s t ∧ vecCap t (s.getReg .x10) = errNiche := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have ho := hpre.out
  have hos := hpre.outStack
  have hof := hpre.outFree
  rw [stackLo_eq] at hos
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80007104_spec hpc (by
    rv_eval [R.x18]
    and_intros <;> exact Region.valid ho (by addr_omega [ho]) (by addr_omega [ho])
      (by addr_omega [ho]))
  have fr := DFrame.of_memFrame (b80007104_frame h₁ (by rw [R.x18]; addr_omega [ho]))
  rw [R.x18] at fr
  have hn : heapNext u₁ = heapNext u := by
    simp only [heapNext]
    exact congrArg BitVec.toNat (fr nextAddr fun i hi hw ↦ by addr_omega [hof.2, hw, hi])
  have I₁ : Inv s u₁ := h.step hpre fr (fun a ha ↦ ⟨Or.inl (by addr_omega [ha]),
      by addr_omega [ha, hos, hb1]⟩) ⟨hn ▸ h.heap.lo, hn ▸ h.heap.hi⟩ hn.ge
    (b80007104_keeps h₁ .x2 (by decide))
  obtain ⟨t, hr, ex, hm⟩ := exit hpre I₁ (b80007104_pc h₁)
  refine ⟨t, hr₁.trans hr, ex, ?_⟩
  rw [vecCap, hm, ← R.x18, b80007104_m_x18_0 h₁]
  rfl

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
