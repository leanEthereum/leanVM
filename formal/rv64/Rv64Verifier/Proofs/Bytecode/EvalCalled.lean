import Rv64Verifier.Proofs.Bytecode.EvalSetup

/-!
# `Bytecode::evaluate`: after the three calls

What holds when `vec![ZERO; 2048]` returns (`Called`), from the three contracts' postconditions
and the blocks between them: the eq tables and the buckets are fresh and hold their values, and
everything the prologue saved is in place.
-/

namespace Rv64Verifier.Proofs.Bytecode.Eval
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Contracts
  Rv64Verifier.Blocks.F84
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem limbs_zero : Model.limbs (0 : E) = (0, 0, 0) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem called_of {s t t₁ t₂ t₃ t₄ t₅ : MachineState} (hpre : EvaluatePre s) (hc : PreCall s t)
    (pres₁ : Preserves t t₁) (post₁ : EqKernelPost t t₁)
    (hm₂ : ∀ a, t₂.getMem a = t₁.getMem a) (x8₂ : t₂.getReg .x8 = t₁.getReg .x8)
    (e2₂ : t₂.getReg .x2 = s.getReg .x2 - 1968)
    (x10₂ : t₂.getReg .x10 = s.getReg .x2 - 1736)
    (x11₂ : t₂.getReg .x11 = s.getReg .x12 + BitVec.ofNat 64 (24 * min (s.getReg .x13).toNat 14))
    (x12₂ : (t₂.getReg .x12).toNat = (s.getReg .x13).toNat - min (s.getReg .x13).toNat 14)
    (pres₃ : Preserves t₂ t₃) (post₃ : EqKernelPost t₂ t₃) (h₄ : b80010ec8.Holds t₃ t₄)
    (pres₅ : Preserves t₄ t₅) (post₅ : FromElemPost t₄ t₅) :
    Called s t₅ (t₁.getMem (s.getReg .x2 - 1752)) (t₃.getMem (s.getReg .x2 - 1728))
      (t₅.getMem (s.getReg .x2 - 1704)) := by
  have hsp := sp_bounds hpre.stack
  have hstn := hpre.stack.next
  have hstr := hpre.stack.rodata
  have hpc' := hpre.pointClear
  have hpb : (s.getReg .x13).toNat = 0 ∨
      (s.getReg .x12).toNat + 24 * (s.getReg .x13).toNat ≤ 0xc0000008 := by
    by_cases h : (s.getReg .x13).toNat = 0
    · exact Or.inl h
    · have := ValidMemRange.bounds hpre.point (by omega); right; omega
  have hmin : min (s.getReg .x13).toNat 14 ≤ (s.getReg .x13).toNat := Nat.min_le_left _ _
  have e2 : t.getReg .x2 = s.getReg .x2 - 1968 := hc.saved.sp
  have e2₁ : t₁.getReg .x2 = s.getReg .x2 - 1968 := (pres₁.reg .x2).trans e2
  have e2₃ : t₃.getReg .x2 = s.getReg .x2 - 1968 := (pres₃.reg .x2).trans e2₂
  have k₄ := b80010ec8_keeps h₄
  have e2₄ : t₄.getReg .x2 = s.getReg .x2 - 1968 := (k₄ .x2 (by decide)).trans e2₃
  have hf₄ := b80010ec8_frame h₄ (by rw [e2₃]; addr_omega [hsp])
  rw [e2₃] at hf₄
  -- `NEXT` along the calls
  have hN : heapNext t = heapNext s := by
    simp only [heapNext]; rw [hc.mem _ (by addr_omega [hsp, hstn])]
  have hN₂ : heapNext t₂ = heapNext t₁ := by simp only [heapNext]; rw [hm₂]
  have hN₄ : heapNext t₄ = heapNext t₃ := by
    simp only [heapNext]; rw [hf₄ _ (by addr_omega [hsp, hstn])]
  have m₁ := post₁.mono
  have m₃ := post₃.mono
  have m₅ := post₅.mono
  have hi₅ := post₅.heap.hi
  have hlo := hpre.heap.lo
  simp only [heapNext] at hN hN₂ hN₄ m₁ m₃ m₅ hi₅ hlo
  simp only [heapStart, heapEnd] at hi₅ hlo
  -- the buffers
  have hx10 : t.getReg .x10 = s.getReg .x2 - 1760 := hc.x10
  have hL : (t.getReg .x12).toNat = min (s.getReg .x13).toNat 14 := hc.x12
  have f₁ := post₁.fresh
  have f₃ := post₃.fresh
  have f₅ := post₅.fresh
  simp only [vecPtr, hx10, x10₂, b80010ec8_x10 h₄, e2₃, hL, x12₂, b80010ec8_x12 h₄] at f₁ f₃ f₅
  rv_eval [] at f₁ f₃ f₅
  generalize hlow : t₁.getMem (s.getReg .x2 - 1752) = low at f₁ ⊢
  generalize hhigh : t₃.getMem (s.getReg .x2 - 1728) = high at f₃ ⊢
  generalize hbk : t₅.getMem (s.getReg .x2 - 1704) = bk at f₅ ⊢
  have hLpos : 0 < 2 ^ min (s.getReg .x13).toNat 14 := Nat.two_pow_pos _
  have hHpos : 0 < 2 ^ ((s.getReg .x13).toNat - min (s.getReg .x13).toNat 14) := Nat.two_pow_pos _
  generalize hLdef : 2 ^ min (s.getReg .x13).toNat 14 = L at f₁ hLpos ⊢
  generalize hHdef : 2 ^ ((s.getReg .x13).toNat - min (s.getReg .x13).toNat 14) = H at f₃ hHpos ⊢
  simp only [NewBuf, heapNext] at f₁ f₃ f₅
  -- the frames: from `t₁` (`t₃`) on, the callees' stack, the slots below the frame's out
  -- vectors, `NEXT`, and the heap from `t₁`'s (`t₃`'s) `NEXT` on
  have s₁ := pres₁.reg .x2
  have s₃ := pres₃.reg .x2
  have x10₄ := b80010ec8_x10 h₄
  have x12₄ := b80010ec8_x12 h₄
  have x11₄ := b80010ec8_x11 h₄
  have s₅ := pres₅.reg .x2
  have d₁ := post₁.frame.dw
  have d₃ := post₃.frame.dw
  have d₄ := DW.of_mem hf₄
  have d₅ := post₅.frame.dw
  simp only [stackLo, Fresh, heapNext, e2, hx10, e2₂, x10₂, e2₄, x10₄, e2₃, eqKernelStack,
    MultilinearContracts.fromElemStack, tryAllocStack, mulStack] at d₁ d₃ d₄ d₅
  have D₃ : DW t₃ t₅ (fun a ↦ Within a (s.getReg .x2 - 3200) 1232 ∨
      Within a (s.getReg .x2 - 1912) 16 ∨ Within a (s.getReg .x2 - 1760) 72 ∨
      Within a nextAddr 8 ∨ ((t₃.getMem nextAddr).toNat ≤ a.toNat ∧ a.toNat < (t₅.getMem nextAddr).toNat)) :=
    d₄.trans d₅ (fun a h ↦ by addr_omega [h, hsp])
      (fun a h ↦ by addr_omega [h, hsp, hN₄])
  have D₂ : DW t₂ t₅ (fun a ↦ Within a (s.getReg .x2 - 3200) 1232 ∨
      Within a (s.getReg .x2 - 1912) 16 ∨ Within a (s.getReg .x2 - 1760) 72 ∨
      Within a nextAddr 8 ∨ ((t₂.getMem nextAddr).toNat ≤ a.toNat ∧ a.toNat < (t₅.getMem nextAddr).toNat)) :=
    d₃.trans D₃ (fun a h ↦ by addr_omega [h, hsp, hN₄, m₅])
      (fun a h ↦ by addr_omega [h, hsp, m₃])
  have D₁ : DW t₁ t₅ (fun a ↦ Within a (s.getReg .x2 - 3200) 1232 ∨
      Within a (s.getReg .x2 - 1912) 16 ∨ Within a (s.getReg .x2 - 1760) 72 ∨
      Within a nextAddr 8 ∨ ((t₁.getMem nextAddr).toNat ≤ a.toNat ∧ a.toNat < (t₅.getMem nextAddr).toNat)) :=
    (DW.of_same hm₂ (fun _ ↦ False)).trans D₂ (fun _ h ↦ h.elim)
      (fun a h ↦ by addr_omega [h, hsp, hN₂])
  have D₀ : DW t t₅ (fun a ↦ Within a (s.getReg .x2 - 3200) 1232 ∨
      Within a (s.getReg .x2 - 1912) 16 ∨ Within a (s.getReg .x2 - 1760) 72 ∨
      Within a nextAddr 8 ∨ ((s.getMem nextAddr).toNat ≤ a.toNat ∧ a.toNat < (t₅.getMem nextAddr).toNat)) :=
    d₁.trans D₁ (fun a h ↦ by addr_omega [h, hsp, hN, hN₂, m₃, hN₄, m₅])
      (fun a h ↦ by addr_omega [h, hsp, hN, m₁])
  have hfr (u : MachineState) (V : Word → Prop) (h : DW u t₅ V) (a : Word)
      (ha : ∀ i < 8, ¬ V (a + BitVec.ofNat 64 i)) : t₅.getMem a = u.getMem a := h a ha
  -- `.rodata`
  have ro : RodataOk t := RodataOk.of_dwords hpre.rodata fun a ha ↦ hc.mem a (by addr_omega [ha, hsp, hstr])
  have ro₁ : RodataOk t₁ := RodataOk.of_byteFrame ro post₁.frame fun a ha hw ↦ by
    simp only [stackLo, Fresh, heapNext, e2, hx10, eqKernelStack, mulStack] at hw
    addr_omega [ha, hw, hsp, hstr, hN, m₁, hN₂, m₃, hN₄, m₅, hi₅]
  have ro₂ : RodataOk t₂ := RodataOk.of_dwords ro₁ fun a _ ↦ hm₂ a
  have ro₃ : RodataOk t₃ := RodataOk.of_byteFrame ro₂ post₃.frame fun a ha hw ↦ by
    simp only [stackLo, Fresh, heapNext, e2₂, x10₂, eqKernelStack, mulStack] at hw
    addr_omega [ha, hw, hsp, hstr, hN₄, m₅, hi₅]
  have ro₄ : RodataOk t₄ := RodataOk.frame ro₃ hf₄ (by addr_omega [hsp, hstr])
  have ro₅ : RodataOk t₅ := RodataOk.of_byteFrame ro₄ post₅.frame fun a ha hw ↦ by
    simp only [stackLo, Fresh, heapNext, e2₄, x10₄, e2₃, MultilinearContracts.fromElemStack, tryAllocStack] at hw
    addr_omega [ha, hw, hsp, hstr, hi₅]
  have hzero : eAt t₄ 0xa0000068 = 0 := by
    apply eAt_eq_of_limbs
    rw [limbs_zero, ro₄.word (a := 0xa0000068) (v := 0), ro₄.word (a := 0xa0000068 + 8) (v := 0),
      ro₄.word (a := 0xa0000068 + 16) (v := 0)]
  -- reading the stack after the calls
  have rd (a : Word) (h1 : (s.getReg .x2).toNat - 1968 ≤ a.toNat)
      (h2 : a.toNat + 8 ≤ (s.getReg .x2).toNat - 1912 ∨ ((s.getReg .x2).toNat - 1896 ≤ a.toNat ∧
        a.toNat + 8 ≤ (s.getReg .x2).toNat - 1760) ∨ ((s.getReg .x2).toNat - 1688 ≤ a.toNat ∧
        a.toNat + 8 ≤ (s.getReg .x2).toNat)) : t₅.getMem a = t.getMem a :=
    D₀ a fun i hi hw ↦ by beta_reduce at hw; addr_omega [hw, h1, h2, hi, hsp, hi₅, hstn]
  -- the out vectors' fields, read back
  have rd₃ (a : Word) (h1 : (s.getReg .x2).toNat - 1760 ≤ a.toNat)
      (h2 : a.toNat + 8 ≤ (s.getReg .x2).toNat - 1736) : t₃.getMem a = t₁.getMem a := by
    rw [d₃ a fun i hi hw ↦ by addr_omega [hw, h1, h2, hi, hsp, hi₅, hstn, hN₄, m₅, m₃], hm₂]
  have p₁ := post₁.len
  have p₃ := post₃.len
  have p₅ := post₅.len
  have q₁ := post₁.elems
  have q₃ := post₃.elems
  have q₅ := post₅.elems
  simp only [vecLen, vecPtr, vecEs, hx10, x10₂, x10₄, e2₃, hL, x12₂, x12₄, x11₄] at p₁ p₃ p₅ q₁ q₃ q₅
  rv_eval [hlow, hhigh, hbk, hLdef, hHdef] at p₁ p₃ p₅ q₁ q₃ q₅
  rw [p₁] at q₁
  rw [p₃] at q₃
  rw [p₅, hzero] at q₅
  have f₁' := f₁.2.resolve_left (by omega)
  have f₃' := f₃.2.resolve_left (by omega)
  have f₅' := f₅.2.resolve_left (by omega)
  have m₄ := b80010ec8_m_x2_56 h₄
  have m₄' := b80010ec8_m_x2_64 h₄
  rw [e2₃] at m₄ m₄'
  rv_eval [] at m₄ m₄'
  have h4₅ (a : Word) (h1 : (s.getReg .x2).toNat - 1968 ≤ a.toNat)
      (h2 : a.toNat + 8 ≤ (s.getReg .x2).toNat - 1712) : t₅.getMem a = t₄.getMem a :=
    d₅ a fun i hi hw ↦ by addr_omega [hw, h1, h2, hi, hsp, hi₅, hstn, hN₄, m₅, m₃]
  -- the point, read back
  have hpt₀ : eListAt t (s.getReg .x12) (min (s.getReg .x13).toNat 14) =
      eListAt s (s.getReg .x12) (min (s.getReg .x13).toNat 14) :=
    eListAt_congr fun i hi j hj ↦ hc.mem _ (by addr_omega [hpc', hpb, hi, hj, hsp, hmin])
  have bf₂ : ByteFrame s t₂ fun a ↦ Within a (stackLo s evalStack) evalStack ∨
      Within a nextAddr 8 ∨ ((s.getMem nextAddr).toNat ≤ a.toNat ∧ a.toNat < (t₂.getMem nextAddr).toNat) :=
    ((hc.bframe.mono fun _ h ↦ Or.inl h).trans post₁.frame fun a h ↦ by
        simp only [stackLo, Fresh, heapNext, e2, hx10, eqKernelStack, mulStack] at h
        addr_omega [h, hsp, hN, hN₂]).trans (ByteFrame.of_same hm₂ fun _ ↦ False)
      (fun _ h ↦ h.elim)
  have hpt₂ : eListAt t₂ (t₂.getReg .x11) ((s.getReg .x13).toNat - min (s.getReg .x13).toNat 14) =
      eListAt s (s.getReg .x12 + BitVec.ofNat 64 (24 * min (s.getReg .x13).toNat 14))
        ((s.getReg .x13).toNat - min (s.getReg .x13).toNat 14) := by
    rw [x11₂]
    exact eListAt_congr fun i hi j hj ↦ bf₂.dw _ fun k hk hw ↦ by
      addr_omega [hw, hpc', hpb, hi, hj, hk, hsp, hmin, hstn, hN, m₁, hN₂, hi₅, m₃, hN₄, m₅]
  have u₄ := h₄.unaligned (by rv_eval [e2₃]; and_intros <;> addr_omega [hsp])
  have bf₄ : ByteFrame t₃ t₄ (Within · (s.getReg .x2 - 1968 + 56) 16) :=
    ByteFrame.of_memFrame hf₄ (by addr_omega [hsp]) (by decide) u₄
  exact {
    saved := hc.saved.of_frame (by rw [s₅, k₄ .x2 (by decide), s₃, e2₂, e2])
      (fun a h1 h2 ↦ rd a (by omega) (by omega)) (by addr_omega [hsp])
    out := by rw [rd _ (by addr_omega [hsp]) (by addr_omega [hsp]), hc.out]
    short := hc.short
    len := hc.len
    x8 := by
      rw [pres₅.reg .x8, k₄ .x8 (by decide), pres₃.reg .x8, x8₂, pres₁.reg .x8, hc.x8]
    x9 := by
      rw [pres₅.reg .x9, b80010ec8_x9 h₄, e2₃]
      rv_eval []
      rw [rd₃ _ (by addr_omega [hsp]) (by addr_omega [hsp]), hlow]
    x18 := by
      rw [pres₅.reg .x18, b80010ec8_x18 h₄, e2₃]
      rv_eval []
      rw [rd₃ _ (by addr_omega [hsp]) (by addr_omega [hsp]), p₁, hLdef]
    c56 := by rw [h4₅ _ (by addr_omega [hsp]) (by addr_omega [hsp]), m₄, hhigh]
    c64 := by rw [h4₅ _ (by addr_omega [hsp]) (by addr_omega [hsp]), m₄', p₃, hHdef]
    c264 := hbk
    c272 := p₅
    heap := post₅.heap
    mono := by simp only [heapNext]; omega
    rodata := ro₅
    frame := by
      have F₂ : ByteFrame s t₂ fun a ↦ Within a (stackLo s evalStack) evalStack ∨
          Within a nextAddr 8 ∨ Fresh s t₅ a := bf₂.mono fun a h ↦ by
        simp only [Fresh, heapNext]; addr_omega [h, hN₂, m₃, hN₄, m₅]
      have F₃ := F₂.trans post₃.frame fun a h ↦ by
        simp only [stackLo, Fresh, heapNext, e2₂, x10₂, eqKernelStack, mulStack] at h ⊢
        addr_omega [h, hsp, hN, m₁, hN₂, hN₄, m₅]
      have F₄ := F₃.trans bf₄ fun a h ↦ by
        simp only [stackLo] at h ⊢; addr_omega [h, hsp]
      exact F₄.trans post₅.frame fun a h ↦ by
        simp only [stackLo, Fresh, heapNext, e2₄, x10₄, e2₃, MultilinearContracts.fromElemStack, tryAllocStack] at h ⊢
        addr_omega [h, hsp, hN, m₁, hN₂, m₃, hN₄]
    lowIn := by rw [hLdef]; exact ⟨by simp only [heapNext]; omega, by simp only [heapNext]; omega, f₁.1⟩
    highIn := by
      rw [hHdef]; exact ⟨by simp only [heapNext]; omega, by simp only [heapNext]; omega, f₃.1⟩
    bkIn := ⟨by simp only [heapNext]; omega, by simp only [heapNext]; omega, f₅.1⟩
    lowBk := by rw [hLdef]; addr_omega [f₁', f₅', hN₂, m₃, hN₄]
    highBk := by rw [hHdef]; addr_omega [f₃', f₅', hN₄]
    lowVals := by
      rw [hLdef, eListAt_congr (s := t₁) fun i hi j hj ↦ D₁ _ fun k hk hw ↦ by
          beta_reduce at hw; addr_omega [hw, f₁', hi, hj, hk, hsp, hstn, hi₅, hN₂, m₃, hN₄, m₅],
        q₁, hc.x11, hpt₀, ← eListAt_take _ _ hmin]
    highVals := by
      rw [hHdef, eListAt_congr (s := t₃) fun i hi j hj ↦ D₃ _ fun k hk hw ↦ by
          beta_reduce at hw; addr_omega [hw, f₃', hi, hj, hk, hsp, hstn, hi₅, hN₄, m₅],
        q₃, hpt₂, eListAt_drop]
    bkVals := q₅ }

end Rv64Verifier.Proofs.Bytecode.Eval
