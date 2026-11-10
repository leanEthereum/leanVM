import Rv64Verifier.Proofs.Layout.ArithTail

/-!
# `flushes_arith`: `memory` and the return

`memory(sp' + 8, sp' + 320, cnt_c, sp' + 80)`; `0x80005c08` copies the `Flushes` to `a0`, restores
the registers and returns.
-/

namespace Rv64Verifier.Layout.Arith
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.FieldContracts
  Rv64Verifier.Blocks.F19 Rv64Verifier.Model.LayoutMirror
open Rv64Verifier.Layout.Limb (Held)

theorem finish (hK : MemorySpec) {s u0 u : MachineState} {L : Nat} {f0 f1 f2 : FormRust}
    (hpre : FlushesArithPre s) (hr : Reaches Image.code u0 u) (A : AtMemory s u L f0 f1 f2) :
    ∃ t, Reaches Image.code u0 t ∧ ((t.pc = returnAddress s ∧ Preserves s t ∧
      NewFlushes s t (s.getReg .x10) flushesArithStack ∧
      flushesOf t (s.getReg .x10) =
        (flCols (s.getReg .x11).toNat).memory (prodRust 1 4 0) 13 [f0, f1, f2]) ∨
      Dead Image.code t) := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have c := A.toInv
  have x2 := c.x2
  have e0 : s.getReg .x2 - 400 + BitVec.ofNat 64 (24 * 0) = s.getReg .x2 - 400 := by
    addr_omega [hsb]
  have e1 : s.getReg .x2 - 400 + BitVec.ofNat 64 (24 * 1) = s.getReg .x2 - 376 := by
    addr_omega [hsb]
  have e2 : s.getReg .x2 - 400 + BitVec.ofNat 64 (24 * 2) = s.getReg .x2 - 352 := by
    addr_omega [hsb]
  have hmp : MemoryPre u := {
    toFlushesPre := flushesPre hpre c A.fl A.x10 (by decide) (by decide) (by decide)
    address := by rw [A.x11]; valid_sub (stackValid hpre) [hsb]
    addressOk := by rw [A.x11]; exact A.addr.ok
    addressFree := by rw [A.x11]; addr_omega [hsb, hab, hnx]
    addressStack := by
      rw [A.x11]; simp only [stackLo, memoryStack, countedStack, colStack, powStack,
        Contracts.mulStack]; rw [x2]; addr_omega [hsb]
    values := by rw [A.x13]; valid_sub (stackValid hpre) [hsb]
    valuesOk := by
      rw [A.x13]
      intro i hi
      match i, hi with
      | 0, _ => rw [e0]; exact A.v0.ok
      | 1, _ => rw [e1]; exact A.v1.ok
      | 2, _ => rw [e2]; exact A.v2.ok
    valuesFree := by rw [A.x13]; addr_omega [hsb, hab, hnx]
    valuesStack := by
      rw [A.x13]; simp only [stackLo, memoryStack, countedStack, colStack, powStack,
        Contracts.mulStack]; rw [x2]; addr_omega [hsb] }
  obtain ⟨t₆, hr₆, ⟨hpc₆, hpres₆, hg₆, hval₆⟩ | hd⟩ := hK.call hr A.pc hmp
  swap
  · exact ⟨t₆, hr₆, Or.inr hd⟩
  rw [A.x10] at hg₆ hval₆
  obtain ⟨c₆, f₆⟩ := afterGrow hpre c A.fl A.hL (by decide) hpres₆ hg₆
  have hv : formsAt u (s.getReg .x2 - 400) 3 = [f0, f1, f2] := by
    show [formOf u (s.getReg .x2 - 400 + BitVec.ofNat 64 (24 * 0)),
      formOf u (s.getReg .x2 - 400 + BitVec.ofNat 64 (24 * 1)),
      formOf u (s.getReg .x2 - 400 + BitVec.ofNat 64 (24 * 2))] = _
    rw [e0, e1, e2, A.v0.val, A.v1.val, A.v2.val]
  rw [hval₆, A.fl.val, A.x11, A.addr.val, A.x12, A.x13, hv] at f₆
  -- the epilogue
  have hob := ValidMemRange.bounds hpre.out (by decide)
  have hos := hpre.outStack
  have hof := hpre.outFree
  simp only [flushesArithStack, memoryColsStack, memoryStack, countedStack, colStack, powStack,
    Contracts.mulStack, Nat.reduceAdd] at hos
  have x2₆ := c₆.x2
  have x8₆ := c₆.x8
  obtain ⟨t₇, hr₇, h₇⟩ := Sym.BlockSpec.reaches b80005c08_spec
    (by rw [hpc₆, returnAddress_eq, A.x1]; decide) (by
      rv_eval [x2₆, x8₆]
      and_intros <;> first
        | valid_access (stackValid hpre) [hsb]
        | valid_access hpre.out [hob]
        | addr_omega [hsb, hob, hos])
  have hm₇ := b80005c08_frame h₇ (by rw [x8₆]; addr_omega [hob])
  rw [x8₆] at hm₇
  have k₇ := b80005c08_keeps h₇
  have hn₇ : heapNext t₇ = heapNext t₆ := by
    simp only [heapNext]; rw [hm₇ _ (by addr_omega [hof])]
  have hh₆ := c₆.heap.hi
  have hm₆ := c₆.mono
  have hdeep (x : Word) (hx : flushesDeep t₆ (s.getReg .x2 - 472) x) :
      ¬ Within x (s.getReg .x10) 48 := by
    have := f₆.deep x hx
    intro h; simp only [Outside] at hof; addr_omega [h, this, hof, hh₆]
  have hmove := flushesOf_move hm₇.dframe f₆.ok
    (by have := b80005c08_m_x8_0 h₇; rw [x8₆, x2₆] at this; rv_eval [] at this ⊢; exact this)
    (by have := b80005c08_m_x8_8 h₇; rw [x8₆, x2₆] at this; rv_eval [] at this ⊢; exact this)
    (by have := b80005c08_m_x8_16 h₇; rw [x8₆, x2₆] at this; rv_eval [] at this ⊢; exact this)
    (by have := b80005c08_m_x8_24 h₇; rw [x8₆, x2₆] at this; rv_eval [] at this ⊢; exact this)
    (by have := b80005c08_m_x8_32 h₇; rw [x8₆, x2₆] at this; rv_eval [] at this ⊢; exact this)
    (by have := b80005c08_m_x8_40 h₇; rw [x8₆, x2₆] at this; rv_eval [] at this ⊢; exact this)
    hdeep (fun x hx hd ↦ hdeep x hd hx) c₆.heap hn₇.ge
  have r₁ := b80005c08_x1 h₇
  have r₂ := b80005c08_x2 h₇
  have r₈ := b80005c08_x8 h₇
  have r₉ := b80005c08_x9 h₇
  have r₁₈ := b80005c08_x18 h₇
  have r₁₉ := b80005c08_x19 h₇
  have r₂₀ := b80005c08_x20 h₇
  have r₂₁ := b80005c08_x21 h₇
  have r₂₂ := b80005c08_x22 h₇
  have pc₇ := b80005c08_pc h₇
  rw [x2₆] at r₁ r₂ r₈ r₉ r₁₈ r₁₉ r₂₀ r₂₁ r₂₂ pc₇
  rv_eval [] at r₁ r₂ r₈ r₉ r₁₈ r₁₉ r₂₀ r₂₁ r₂₂ pc₇
  rw [c₆.ra] at pc₇
  rw [c₆.s0] at r₈
  rw [c₆.s1] at r₉
  rw [c₆.s2] at r₁₈
  rw [c₆.s3] at r₁₉
  rw [c₆.s4] at r₂₀
  rw [c₆.s5] at r₂₁
  rw [c₆.s6] at r₂₂
  refine ⟨t₇, hr₆.trans hr₇, Or.inl ⟨pc₇.trans (returnAddress_eq s).symm,
    preserves_of r₂ r₈ r₉ r₁₈ r₁₉ fun r hr ↦ ?_, ?_, hmove.1.trans f₆.val⟩⟩
  · rcases List.mem_cons.mp hr with rfl | hr
    · exact r₂₀
    rcases List.mem_cons.mp hr with rfl | hr
    · exact r₂₁
    rcases List.mem_cons.mp hr with rfl | hr
    · exact r₂₂
    rw [k₇ r (mem_of_mem hr _), c₆.regs r hr]
  · exact {
      heap := ⟨hn₇ ▸ c₆.heap.lo, hn₇ ▸ hh₆⟩
      mono := by omega
      ok := hmove.2.1
      fresh := fun x hx ↦ by
        rw [hmove.2.2] at hx
        have := f₆.deep x hx
        simp only [Fresh]; omega
      frame := (c₆.frame.union hm₇.dframe).mono fun x hx ↦ by
        simp only [Scratch, Fresh] at hx
        rcases hx with (h | h | h) | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr ⟨h.1, by omega⟩))
        · exact Or.inl h }

end Rv64Verifier.Layout.Arith
