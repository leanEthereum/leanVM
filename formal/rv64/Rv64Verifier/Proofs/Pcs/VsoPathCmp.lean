import Rv64Verifier.Proofs.Pcs.VsoPathLeaf

/-!
# `verify_stacked_opening`'s Merkle checks: a path's root compared

`memcmp(S - 160, root, 32)` at `0x8000ab04` (after the climb, `0x8000ab18` taking the path back
from `s8` to `s6`) or at `0x8000b0a0` (no siblings, `0x8000b0b4`): a nonzero low word goes to the
`Err` at `0x8000b8d4`, zero on to the next path at `0x8000ab2c`, the node then the root's bytes.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem callMemcmp (hC : MemcmpSpec) {s t : MachineState} {R : Word} (hpre : VsoPre s)
    (hpc : t.pc = 0x800126b4) (hx10 : t.getReg .x10 = s.getReg .x2 - 160)
    (hx11 : t.getReg .x11 = R) (hx12 : t.getReg .x12 = 32) (hR : Region R 32) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨ (v.pc = returnAddress t ∧ Preserves t v ∧
      v.getReg .x10 = cmpBytes (Contracts.bytesAt t (s.getReg .x2 - 160) 32)
        (Contracts.bytesAt t R 32) ∧ ∀ a, v.getMem a = t.getMem a)) := by
  have hm := stack_mapped hpre
  have h32 : (t.getReg .x12).toNat = 32 := by rw [hx12]; rfl
  obtain ⟨v, hr, ⟨hpc', hpres, hpost⟩ | hdead⟩ := hC.call (Reaches.refl t) hpc
    ⟨by rw [hx10, h32]; addr_omega [hm], by rw [hx11, h32]; exact hR.1⟩
  · have hret := hpost.ret
    rw [hx10, hx11, h32] at hret
    exact ⟨v, hr, Or.inr ⟨hpc', hpres, hret, hpost.mem⟩⟩
  · exact ⟨v, hr, Or.inl hdead⟩

/-- The comparison's outcome: memory and the loop's registers kept, `Err` or the bytes equal. -/
def CmpOut (s t v : MachineState) (R x22 : Word) : Prop :=
  (∀ a, v.getMem a = t.getMem a) ∧ v.getReg .x2 = t.getReg .x2 ∧
    (∀ r ∈ [Reg.x9, .x25, .x26], v.getReg r = t.getReg r) ∧ v.getReg .x22 = x22 ∧
    (v.pc = 0x8000b8d4 ∨ (v.pc = 0x8000ab2c ∧
      Contracts.bytesAt t (s.getReg .x2 - 160) 32 = Contracts.bytesAt t R 32))

/-- After the climb. -/
theorem cmpA (hC : MemcmpSpec) {s t : MachineState} {R : Word} (hpre : VsoPre s)
    (hpc : t.pc = 0x8000ab04) (hsp : t.getReg .x2 = s.getReg .x2 - 1040)
    (hslot : t.getMem (s.getReg .x2 - 840) = R) (hR : Region R 32) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨ CmpOut s t v R (t.getReg .x24)) := by
  have hb := bounds hpre
  obtain ⟨t1, r1, h1⟩ := Sym.BlockSpec.reaches b8000ab04_spec hpc (by
    rv_eval [hsp]; valid_access hpre.stack.valid [hb])
  have k1 := b8000ab04_keeps h1
  have m1 := b8000ab04_mem_same h1
  obtain ⟨t2, r2, hv2⟩ := callMemcmp hC hpre (R := R) (b8000ab04_pc h1)
    (by rw [b8000ab04_x10 h1, hsp]; rv_eval [])
    (by rw [b8000ab04_x11 h1, hsp]; rv_eval [hslot])
    (b8000ab04_x12 h1) hR
  rcases hv2 with hd | ⟨pc2, pr2, x10₂, m2⟩
  · exact ⟨t2, r1.trans r2, Or.inl hd⟩
  have sp2 : t2.getReg .x2 = s.getReg .x2 - 1040 := by
    rw [pr2.reg .x2, k1 .x2 (by decide), hsp]
  obtain ⟨t3, r3, h3⟩ := Sym.BlockSpec.reaches b8000ab18_spec
    (by rw [pc2, returnAddress_eq, b8000ab04_x1 h1]; rfl) (by
      rv_eval [sp2]; and_intros <;> valid_access hpre.stack.valid [hb])
  have k3 := b8000ab18_keeps h3
  have m3 := b8000ab18_mem_same h3
  have hpc3 : t3.pc = if (Sym.BinOp.eval (.w .add) (t2.getReg .x10) 0 != 0) = true then
      0x8000b8d4 else 0x8000ab2c := h3.pc_eq rfl
  have e1 : ∀ a n, Contracts.bytesAt t1 a n = Contracts.bytesAt t a n := fun a n ↦ by
    simp only [Contracts.bytesAt, MachineState.getByte, m1]
  rw [e1, e1] at x10₂
  refine ⟨t3, r1.trans (r2.trans r3), Or.inr ⟨fun a ↦ by rw [m3, m2, m1],
    by rw [k3 .x2 (by decide), pr2.reg .x2, k1 .x2 (by decide)], fun r hr ↦ ?_,
    by rw [b8000ab18_x22 h3, pr2.reg .x24, k1 .x24 (by decide)], ?_⟩⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> rw [k3 _ (by decide), pr2.reg _, k1 _ (by decide)]
  · by_cases h0 : Sym.BinOp.eval (.w .add) (t2.getReg .x10) 0 = 0
    · rw [h0] at hpc3
      refine Or.inr ⟨by rw [hpc3]; rfl, cmp_eq (by simp [Contracts.bytesAt]) ?_⟩
      rw [← x10₂]
      exact h0
    · exact Or.inl (by rw [hpc3]; simp only [bne_iff_ne, ne_eq, h0, not_false_eq_true, ↓reduceIte])

/-- No siblings. -/
theorem cmpB (hC : MemcmpSpec) {s t : MachineState} {R : Word} (hpre : VsoPre s)
    (hpc : t.pc = 0x8000b0a0) (hsp : t.getReg .x2 = s.getReg .x2 - 1040)
    (hslot : t.getMem (s.getReg .x2 - 840) = R) (hR : Region R 32) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨ CmpOut s t v R (t.getReg .x22)) := by
  have hb := bounds hpre
  obtain ⟨t1, r1, h1⟩ := Sym.BlockSpec.reaches b8000b0a0_spec hpc (by
    rv_eval [hsp]; valid_access hpre.stack.valid [hb])
  have k1 := b8000b0a0_keeps h1
  have m1 := b8000b0a0_mem_same h1
  obtain ⟨t2, r2, hv2⟩ := callMemcmp hC hpre (R := R) (b8000b0a0_pc h1)
    (by rw [b8000b0a0_x10 h1, hsp]; rv_eval [])
    (by rw [b8000b0a0_x11 h1, hsp]; rv_eval [hslot])
    (b8000b0a0_x12 h1) hR
  rcases hv2 with hd | ⟨pc2, pr2, x10₂, m2⟩
  · exact ⟨t2, r1.trans r2, Or.inl hd⟩
  obtain ⟨t3, r3, h3⟩ := Sym.BlockSpec.reaches b8000b0b4_spec
    (by rw [pc2, returnAddress_eq, b8000b0a0_x1 h1]; rfl) trivial
  have k3 := b8000b0b4_keeps h3
  have m3 := b8000b0b4_mem_same h3
  have hpc3 : t3.pc = if (Sym.BinOp.eval (.w .add) (t2.getReg .x10) 0 == 0) = true then
      0x8000ab2c else 0x8000b0bc := h3.pc_eq rfl
  have e1 : ∀ a n, Contracts.bytesAt t1 a n = Contracts.bytesAt t a n := fun a n ↦ by
    simp only [Contracts.bytesAt, MachineState.getByte, m1]
  rw [e1, e1] at x10₂
  have kk : ∀ r ∈ [Reg.x2, .x9, .x22, .x25, .x26], t3.getReg r = t.getReg r := fun r hr ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> rw [k3 _ (by decide), pr2.reg _, k1 _ (by decide)]
  by_cases h0 : Sym.BinOp.eval (.w .add) (t2.getReg .x10) 0 = 0
  · rw [h0] at hpc3
    refine ⟨t3, r1.trans (r2.trans r3), Or.inr ⟨fun a ↦ by rw [m3, m2, m1], kk .x2 (by simp),
      fun r hr ↦ kk r (by simp only [List.mem_cons] at hr ⊢; tauto), kk .x22 (by simp),
      Or.inr ⟨by rw [hpc3]; rfl, cmp_eq (by simp [Contracts.bytesAt]) ?_⟩⟩⟩
    rw [← x10₂]
    exact h0
  · obtain ⟨t4, r4, h4⟩ := Sym.BlockSpec.reaches b8000b0bc_spec (by rw [hpc3]; simp only [beq_iff_eq, h0, ↓reduceIte]; rfl) trivial
    have k4 := b8000b0bc_keeps h4
    have m4 := b8000b0bc_mem_same h4
    refine ⟨t4, r1.trans (r2.trans (r3.trans r4)), Or.inr ⟨fun a ↦ by rw [m4, m3, m2, m1],
      by rw [k4 .x2 (by decide), kk .x2 (by simp)], fun r hr ↦ ?_,
      by rw [k4 .x22 (by decide), kk .x22 (by simp)], Or.inl (b8000b0bc_pc h4)⟩⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> rw [k4 _ (by decide), kk _ (by simp)]

end Rv64Verifier.Proofs.Pcs.Vso
