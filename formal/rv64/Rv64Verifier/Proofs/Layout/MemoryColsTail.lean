import Rv64Verifier.Proofs.Layout.MemoryColsBase

/-!
# `Flushes::memory_cols`: from the three limbs to the return

`0x80005dd4` moves the last limb from `sp' + 144` to `sp' + 120` and `memcpy`s the three from
`sp' + 72` into `sp'`; `0x80005e00` calls `memory(self, address, count, sp')`; `0x80005e18` restores
and returns.
-/

namespace Rv64Verifier.Layout.MemoryCols
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.FieldContracts
  Rv64Verifier.Blocks.F20 Rv64Verifier.Model.LayoutMirror

/-- At the call to `memory`: the three limbs at `sp'`. -/
structure AtMemory (s t : MachineState) (f0 f1 f2 : FormRust) : Prop extends Inv s t where
  pc : t.pc = 0x800051b0
  x1 : t.getReg .x1 = 0x80005e18
  x10 : t.getReg .x10 = s.getReg .x10
  x11 : t.getReg .x11 = s.getReg .x11
  x12 : t.getReg .x12 = s.getReg .x12
  x13 : t.getReg .x13 = s.getReg .x2 - 240
  v0 : Built s t (s.getReg .x2 - 240) f0
  v1 : Built s t (s.getReg .x2 - 216) f1
  v2 : Built s t (s.getReg .x2 - 192) f2

/-- The last limb's move, the `memcpy`, and the arguments. -/
theorem toMemory (hM : MemcpySpec 0x800126e4) {s u0 u : MachineState} (hpre : MemoryColsPre s)
    (c : Inv s u) (hr : Reaches Image.code u0 u) (hpc : u.pc = 0x80005dd4) {f0 f1 f2 : FormRust}
    (b0 : Built s u (s.getReg .x2 - 168) f0) (b1 : Built s u (s.getReg .x2 - 144) f1)
    (b2 : Built s u (s.getReg .x2 - 96) f2) :
    ∃ t, Reaches Image.code u0 t ∧ (AtMemory s t f0 f1 f2 ∨ Dead Image.code t) := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have hhi := stack_high hpre
  have x2 := c.x2
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80005dd4_spec hpc (by
    rv_eval [x2]
    and_intros <;> valid_access hpre.stack.valid [hsb])
  have k₁ := b80005dd4_keeps h₁
  have hm₁ := b80005dd4_frame h₁ (by addr_omega [hsb, x2])
  rw [x2] at hm₁
  have hp₁ : Preserves u u₁ := fun r hr ↦ k₁ r (mem_of_mem hr _)
  have c₁ := c.block hpre hm₁ (by addr_omega [hsb]) (by addr_omega [hsb]) hp₁
  have b0₁ := b0.block hpre c hm₁ (by addr_omega [hsb]) (by addr_omega [hsb]) (by addr_omega [hsb])
    (by addr_omega [hsb])
  have b1₁ := b1.block hpre c hm₁ (by addr_omega [hsb]) (by addr_omega [hsb]) (by addr_omega [hsb])
    (by addr_omega [hsb])
  have b2₁ : Built s u₁ (s.getReg .x2 - 120) f2 := b2.blockMove hpre c hm₁ (by addr_omega [hsb])
    (by addr_omega [hsb])
    (by have := b80005dd4_m_x2_120 h₁; rw [x2] at this; rv_eval [] at this ⊢; exact this)
    (by have := b80005dd4_m_x2_128 h₁; rw [x2] at this; rv_eval [] at this ⊢; exact this)
    (by have := b80005dd4_m_x2_136 h₁; rw [x2] at this; rv_eval [] at this ⊢; exact this)
  have x2₁ : u₁.getReg .x2 = s.getReg .x2 - 240 := c₁.x2
  have x10₁ : u₁.getReg .x10 = s.getReg .x2 - 240 := by rw [b80005dd4_x10 h₁, x2]
  have x11₁ : u₁.getReg .x11 = s.getReg .x2 - 168 := by
    rw [b80005dd4_x11 h₁, x2]; rv_eval []
  have x12₁ := b80005dd4_x12 h₁
  have hmc : MemcpyPre u₁ := {
    dst := by rw [x10₁, x12₁]; addr_omega [hsb, hhi]
    src := by rw [x11₁, x12₁]; addr_omega [hsb, hhi]
    apart := by rw [x10₁, x11₁, x12₁]; addr_omega [hsb]
    stack := (hpre.stack.inner (k := 240) x2₁ (by decide) (by decide) (by decide) (by decide)
      (by decide)).toStackOk
    dstStack := by rw [x10₁, x12₁]; addr_omega [hsb, x2₁]
    srcStack := by rw [x11₁, x12₁]; addr_omega [hsb, x2₁] }
  obtain ⟨m, hr₂, ⟨hpc₂, hpres₂, hmp⟩ | hdead⟩ := hM.call hr₁ (b80005dd4_pc h₁) hmc
  swap
  · exact ⟨m, hr.trans hr₂, Or.inr hdead⟩
  have hmf := hmp.frame.dframe
  have hb := hmp.bytes
  rw [x10₁, x11₁, x12₁] at hb
  rw [x10₁, x12₁, show stackLo u₁ memcpyStack = s.getReg .x2 - 256 by
    simp only [stackLo, x2₁, memcpyStack]; rv_eval []] at hmf
  have hn₂ : heapNext m = heapNext u₁ := by
    simp only [heapNext]
    rw [hmf.getMem_of (fun x hx h ↦ by rcases h with h | h <;> addr_omega [hx, h, hsb, hnx])
      (by decide)]
  have hW : ∀ x, (Within x (s.getReg .x2 - 240) (BitVec.toNat (72 : Word)) ∨
      Within x (s.getReg .x2 - 256) 16) → heapEnd ≤ x.toNat ∨ heapNext u₁ ≤ x.toNat :=
    fun x h ↦ Or.inl (by rcases h with h | h <;> addr_omega [h, hsb, hab])
  have c₂ := c₁.step hpre hmf (fun x h ↦ Or.inl (by rcases h with h | h <;> addr_omega [h, hsb]))
    ⟨hn₂ ▸ c₁.heap.lo, hn₂ ▸ c₁.heap.hi⟩ hn₂.ge hpres₂
  have h8a : (s.getReg .x2 - 240).toNat % 8 = 0 := by addr_omega [hsb]
  have h8b : (s.getReg .x2 - 168).toNat % 8 = 0 := by addr_omega [hsb]
  have g (k : Nat) (hk : k % 8 = 0) (hkN : k + 8 ≤ 72) (a b : Word)
      (ha : a = s.getReg .x2 - 240 + BitVec.ofNat 64 k)
      (hb' : b = s.getReg .x2 - 168 + BitVec.ofNat 64 k) : m.getMem a = u₁.getMem b := by
    subst ha hb'
    exact getMem_eq_of_bytesAt hb h8a h8b hk hkN
  have v0 : Built s m (s.getReg .x2 - 240) f0 := b0₁.move hmf c₁.heap hn₂.ge hW
    (g 0 (by decide) (by decide) _ _ (by addr_omega [hsb]) (by addr_omega [hsb]))
    (g 8 (by decide) (by decide) _ _ (by addr_omega [hsb]) (by addr_omega [hsb]))
    (g 16 (by decide) (by decide) _ _ (by addr_omega [hsb]) (by addr_omega [hsb]))
  have v1 : Built s m (s.getReg .x2 - 216) f1 := b1₁.move hmf c₁.heap hn₂.ge hW
    (g 24 (by decide) (by decide) _ _ (by addr_omega [hsb]) (by addr_omega [hsb]))
    (g 32 (by decide) (by decide) _ _ (by addr_omega [hsb]) (by addr_omega [hsb]))
    (g 40 (by decide) (by decide) _ _ (by addr_omega [hsb]) (by addr_omega [hsb]))
  have v2 : Built s m (s.getReg .x2 - 192) f2 := b2₁.move hmf c₁.heap hn₂.ge hW
    (g 48 (by decide) (by decide) _ _ (by addr_omega [hsb]) (by addr_omega [hsb]))
    (g 56 (by decide) (by decide) _ _ (by addr_omega [hsb]) (by addr_omega [hsb]))
    (g 64 (by decide) (by decide) _ _ (by addr_omega [hsb]) (by addr_omega [hsb]))
  obtain ⟨w, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80005e00_spec
    (by rw [hpc₂, returnAddress_eq, b80005dd4_x1 h₁]; decide) trivial
  have k₃ := b80005e00_keeps h₃
  have hm₃ := b80005e00_mem_same h₃
  have c₃ := c₂.same hpre hm₃ fun r hr ↦ k₃ r (mem_of_mem hr _)
  have hheap := c₂.heap
  refine ⟨w, hr.trans (hr₂.trans hr₃), Or.inl {
    toInv := c₃
    pc := b80005e00_pc h₃
    x1 := b80005e00_x1 h₃
    x10 := by rw [b80005e00_x10 h₃, c₂.x18]
    x11 := by rw [b80005e00_x11 h₃, c₂.x9]
    x12 := by rw [b80005e00_x12 h₃, c₂.x8]
    x13 := by rw [b80005e00_x13 h₃, c₂.x2]
    v0 := v0.same hheap hm₃ (by addr_omega [hsb])
    v1 := v1.same hheap hm₃ (by addr_omega [hsb])
    v2 := v2.same hheap hm₃ (by addr_omega [hsb]) }⟩

/-- `memory` and the epilogue. -/
theorem finish (hK : MemorySpec) {s u : MachineState} (hpre : MemoryColsPre s)
    {f0 f1 f2 : FormRust} (A : AtMemory s u f0 f1 f2) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = returnAddress s ∧ Preserves s t ∧
      GrowFlushes s t (s.getReg .x10) memoryColsStack (fun _ ↦ False) ∧
      flushesOf t (s.getReg .x10) = (flushesOf s (s.getReg .x10)).memory
        (formOf s (s.getReg .x11)) (s.getReg .x12).toNat [f0, f1, f2]) ∨ Dead Image.code t) := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have hss := hpre.selfStack
  have hsf := hpre.selfFree
  have has := hpre.addressStack
  have haf := hpre.addressFree
  have hab' := ValidMemRange.bounds hpre.address (by decide)
  have hselfb := ValidMemRange.bounds hpre.self (by decide)
  simp only [memoryColsStack, memoryStack, countedStack, colStack, powStack, Contracts.mulStack,
    Nat.reduceAdd] at hss has
  have hheap := hpre.heap
  have hhs := hheap.hi
  have hm := A.mono
  have hh := A.heap.hi
  have x2 := A.x2
  have hkeep := flushesOf_keep A.frame hpre.ok hheap hm hh hab hsf hss (by addr_omega [hselfb])
  have hA := formOf_keep A.frame hpre.addressOk hheap hm hh hab haf has (by addr_omega [hab'])
  have e0 : s.getReg .x2 - 240 + BitVec.ofNat 64 (24 * 0) = s.getReg .x2 - 240 := by
    addr_omega [hsb]
  have e1 : s.getReg .x2 - 240 + BitVec.ofNat 64 (24 * 1) = s.getReg .x2 - 216 := by
    addr_omega [hsb]
  have e2 : s.getReg .x2 - 240 + BitVec.ofNat 64 (24 * 2) = s.getReg .x2 - 192 := by
    addr_omega [hsb]
  have hmp : MemoryPre u := {
    heap := A.heap
    stack := hpre.stack.inner (k := 240) x2 (by decide) (by decide) (by decide) (by decide)
      (by decide)
    self := by rw [A.x10]; exact hpre.self
    ok := by rw [A.x10]; exact hkeep.2.1
    selfFree := by rw [A.x10]; addr_omega [hsf, hm]
    selfStack := by rw [A.x10]; addr_omega [hss, hsb, x2]
    rodata := A.rodata
    address := by rw [A.x11]; exact hpre.address
    addressOk := by rw [A.x11]; exact hA.2.1
    addressFree := by rw [A.x11]; addr_omega [haf, hm]
    addressStack := by rw [A.x11]; addr_omega [has, hsb, x2]
    values := by rw [A.x13]; valid_sub hpre.stack.valid [hsb]
    valuesOk := by
      rw [A.x13]
      intro i hi
      match i, hi with
      | 0, _ => rw [e0]; exact A.v0.ok
      | 1, _ => rw [e1]; exact A.v1.ok
      | 2, _ => rw [e2]; exact A.v2.ok
    valuesFree := by rw [A.x13]; addr_omega [hsb, hab, hnx]
    valuesStack := by rw [A.x13]; addr_omega [hsb, x2] }
  obtain ⟨t₆, hr₆, ⟨hpc₆, hpres₆, hgrow₆, hval₆⟩ | hdead⟩ := hK u A.pc hmp
  swap
  · exact ⟨t₆, hr₆, Or.inr hdead⟩
  rw [A.x10, A.x11, A.x12, A.x13] at hval₆
  rw [A.x10] at hgrow₆
  have x2₆ : t₆.getReg .x2 = s.getReg .x2 - 240 := (hpres₆.reg .x2).trans x2
  obtain ⟨t₇, hr₇, h₇⟩ := Sym.BlockSpec.reaches b80005e18_spec
    (by rw [hpc₆, returnAddress_eq, A.x1]; decide) (by
      rv_eval [x2₆]
      and_intros <;> valid_access hpre.stack.valid [hsb])
  have hm₇ := b80005e18_mem_same h₇
  have hn₆ := hgrow₆.mono
  have hh₆ := hgrow₆.heap.hi
  have hg₆ := hgrow₆.frame
  rw [hkeep.2.2.2] at hg₆
  have hbb : ∀ x, flushesBuf s (s.getReg .x10) x → x.toNat < heapNext s := fun x h ↦
    (hpre.ok.buf_below h).2
  have hsave (a : Word) (ha₁ : (s.getReg .x2).toNat - 48 ≤ a.toNat)
      (ha₂ : a.toNat + 8 ≤ (s.getReg .x2).toNat) : t₆.getMem a = u.getMem a := by
    refine hg₆.getMem_of (fun x hx hw ↦ ?_) (by addr_omega [hsb, ha₂])
    rcases hw with hw | hw | hw | hw | hw
    · addr_omega [hx, hw, hss, hsb, ha₁, ha₂]
    · have h1 := hbb x hw; addr_omega [hx, h1, hhs, hsb, hab, ha₁, ha₂]
    · addr_omega [hx, hw, hsb, x2, ha₁, ha₂]
    · addr_omega [hx, hw, hnx, hsb, ha₁, ha₂]
    · simp only [Fresh] at hw; addr_omega [hx, hw, hh₆, hab, hsb, ha₁, ha₂]
  have pc₇ := b80005e18_pc h₇
  have r₁ := b80005e18_x1 h₇
  have r₂ := b80005e18_x2 h₇
  have r₈ := b80005e18_x8 h₇
  have r₉ := b80005e18_x9 h₇
  have r₁₈ := b80005e18_x18 h₇
  have r₁₉ := b80005e18_x19 h₇
  have r₂₀ := b80005e18_x20 h₇
  have k₇ := b80005e18_keeps h₇
  rw [x2₆] at pc₇ r₁ r₂ r₈ r₉ r₁₈ r₁₉ r₂₀
  rv_eval [] at pc₇ r₁ r₂ r₈ r₉ r₁₈ r₁₉ r₂₀
  rw [hsave _ (by addr_omega [hsb]) (by addr_omega [hsb]), A.ra] at pc₇ r₁
  rw [hsave _ (by addr_omega [hsb]) (by addr_omega [hsb]), A.s0] at r₈
  rw [hsave _ (by addr_omega [hsb]) (by addr_omega [hsb]), A.s1] at r₉
  rw [hsave _ (by addr_omega [hsb]) (by addr_omega [hsb]), A.s2] at r₁₈
  rw [hsave _ (by addr_omega [hsb]) (by addr_omega [hsb]), A.s3] at r₁₉
  rw [hsave _ (by addr_omega [hsb]) (by addr_omega [hsb]), A.s4] at r₂₀
  have hn₇ : heapNext t₇ = heapNext t₆ := by simp only [heapNext, hm₇]
  have hfin := flushesOf_frame (DFrame.of_same hm₇ fun _ ↦ False) hgrow₆.ok (fun _ _ h ↦ h)
    (fun _ _ h ↦ h) (by addr_omega [hselfb]) hgrow₆.heap hn₇.ge
  have hv : formsAt u (s.getReg .x2 - 240) 3 = [f0, f1, f2] := by
    show [formOf u (s.getReg .x2 - 240 + BitVec.ofNat 64 (24 * 0)),
      formOf u (s.getReg .x2 - 240 + BitVec.ofNat 64 (24 * 1)),
      formOf u (s.getReg .x2 - 240 + BitVec.ofNat 64 (24 * 2))] = _
    rw [e0, e1, e2, A.v0.val, A.v1.val, A.v2.val]
  refine ⟨t₇, hr₆.trans hr₇, Or.inl ⟨pc₇.trans (returnAddress_eq s).symm,
    preserves_of r₂ r₈ r₉ r₁₈ r₁₉ fun r hr ↦ ?_, ?_, ?_⟩⟩
  · rcases List.mem_cons.mp hr with rfl | hr
    · exact r₂₀
    · rw [k₇ r (mem_of_mem hr _), hpres₆ r (mem_of_mem hr _), A.regs r hr]
  · exact {
      heap := ⟨hn₇ ▸ hgrow₆.heap.lo, hn₇ ▸ hh₆⟩
      mono := by omega
      ok := hfin.2.1
      deep := fun x hx ↦ by
        rw [hfin.2.2.1] at hx
        rcases hgrow₆.deep x hx with h | h | h
        · rw [hkeep.2.2.1] at h; exact Or.inl h
        · exact h.elim
        · simp only [Fresh] at h ⊢
          exact Or.inr (Or.inr ⟨by omega, by omega⟩)
      frame := ((A.frame.union hg₆).union (DFrame.of_same hm₇ fun _ ↦ False)).mono fun x hx ↦ by
        simp only [Scratch] at hx
        rcases hx with ((hx | hx | hx) | hx | hx | hx | hx | hx) | hx
        · exact Or.inr (Or.inr (Or.inl (by addr_omega [hx, hsb])))
        · exact Or.inr (Or.inr (Or.inr (Or.inl hx)))
        · simp only [Fresh] at hx ⊢; exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hx.1, by omega⟩)))
        · exact Or.inl hx
        · exact Or.inr (Or.inl hx)
        · exact Or.inr (Or.inr (Or.inl (by addr_omega [hx, hsb, x2])))
        · exact Or.inr (Or.inr (Or.inr (Or.inl hx)))
        · simp only [Fresh] at hx ⊢
          exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))
        · exact hx.elim }
  · rw [hfin.1, hval₆, hkeep.1, hA.1, hv]

end Rv64Verifier.Layout.MemoryCols
