import Rv64Verifier.Proofs.Layout.Keep
import Rv64Verifier.Blocks.F8

/-!
# `Flushes::state_step`, at `0x80004a90`

```rust
fn state_step(&mut self, pc: usize, fp: usize) {
    self.state_derived(pc, fp, col(pc, 1), col(fp, 0));
}
```

compiled for `pc = 0`, `fp = 1` (`Blocks/F8.lean`): `0x80004a90` saves `ra`, `s0` in a 64-byte
frame and calls `col(sp', 0, 1)`; `0x80004ab4` calls `col(sp' + 24, 1, 0)`; `0x80004ac8` calls
`state_derived(self, sp', sp' + 24)`; `0x80004adc` restores and returns.
-/

namespace Rv64Verifier.Layout.StateStep
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.FieldContracts
  Rv64Verifier.Blocks.F8 Rv64Verifier.Model.LayoutMirror

/-- The state at the call to `state_derived`. -/
structure AtCall (s t : MachineState) : Prop where
  pc : t.pc = 0x80005e38
  ra : t.getReg .x1 = 0x80004adc
  x2 : t.getReg .x2 = s.getReg .x2 - 64
  x10 : t.getReg .x10 = s.getReg .x10
  x11 : t.getReg .x11 = s.getReg .x2 - 64
  x12 : t.getReg .x12 = s.getReg .x2 - 40
  regs : ∀ r ∈ [Reg.x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27],
    t.getReg r = s.getReg r
  pre : StateDerivedPre t
  ra' : t.getMem (s.getReg .x2 - 8) = s.getReg .x1
  s0 : t.getMem (s.getReg .x2 - 16) = s.getReg .x8
  frame : DFrame s t (Scratch s t (stackLo s 1376) 1376)
  mono : heapNext s ≤ heapNext t
  keep : flushesOf t (s.getReg .x10) = flushesOf s (s.getReg .x10) ∧
    flushesDeep t (s.getReg .x10) = flushesDeep s (s.getReg .x10) ∧
    flushesBuf t (s.getReg .x10) = flushesBuf s (s.getReg .x10)
  bufs : ∀ x, formBuf t (s.getReg .x2 - 64) x ∨ formBuf t (s.getReg .x2 - 40) x → Fresh s t x
  npc : formOf t (s.getReg .x2 - 64) = colRust 0 1
  nfp : formOf t (s.getReg .x2 - 40) = colRust 1 0

/-- The two `col`s. -/
theorem toCall (hC : ColSpec) {s : MachineState} (hpc : s.pc = 0x80004a90)
    (hpre : FlushesPre stateStepStack s) :
    ∃ t, Reaches Image.code s t ∧ (AtCall s t ∨ Dead Image.code t) := by
  have hsb := hpre.stack.bounds (by decide) (by decide)
  have hab := hpre.stack.above
  have hnx := hpre.stack.next
  have hro := hpre.stack.rodata
  have hss := hpre.selfStack
  have hsf := hpre.selfFree
  have hselfb := ValidMemRange.bounds hpre.self (by decide)
  have hheap := hpre.heap
  simp only [stateStepStack, stateDerivedStack, colStack, powStack, Contracts.mulStack,
    Nat.reduceAdd] at hsb hab hnx hro hss
  have hlo : heapEnd ≤ (stackLo s 1376).toNat := hab
  -- the frame, and `col(sp', 0, 1)`
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80004a90_spec hpc (by
    rv_eval []
    and_intros <;> valid_access hpre.stack.valid [hsb])
  have k₁ := b80004a90_keeps h₁
  have hm₁ := b80004a90_frame h₁ (by addr_omega [hsb])
  have x2₁ := b80004a90_x2 h₁
  have x10₁ := b80004a90_x10 h₁
  have hn₁ : heapNext t₁ = heapNext s := by
    simp only [heapNext]; rw [hm₁ _ (by addr_omega [hnx, hsb])]
  have hcol₁ : ColPre t₁ := {
    heap := ⟨hn₁ ▸ hheap.lo, hn₁ ▸ hheap.hi⟩
    stack := hpre.stack.inner (k := 64) x2₁ (by decide) (by decide) (by decide) (by decide)
      (by decide)
    out := by rw [x10₁]; valid_sub hpre.stack.valid [hsb]
    outFree := by rw [x10₁]; addr_omega [hsb, hab, hnx]
    outStack := by rw [x10₁]; addr_omega [hsb, x2₁]
    rodata := hpre.rodata.frame hm₁ (by addr_omega [hsb, hro]) }
  obtain ⟨t₂, hr₂, ⟨hpc₂, hpres₂, hnew₂, hval₂⟩ | hdead⟩ := hC.call hr₁ (b80004a90_pc h₁) hcol₁
  swap
  · exact ⟨t₂, hr₂, Or.inr hdead⟩
  rw [x10₁, b80004a90_x11 h₁, b80004a90_x12 h₁] at hval₂
  rw [x10₁] at hnew₂
  have x2₂ : t₂.getReg .x2 = s.getReg .x2 - 64 := (hpres₂.reg .x2).trans x2₁
  -- `col(sp' + 24, 1, 0)`
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80004ab4_spec
    (by rw [hpc₂, returnAddress_eq, b80004a90_x1 h₁]; decide) trivial
  have k₃ := b80004ab4_keeps h₃
  have hm₃ := b80004ab4_mem_same h₃
  have x2₃ : t₃.getReg .x2 = s.getReg .x2 - 64 := (k₃ .x2 (by decide)).trans x2₂
  have x10₃ : t₃.getReg .x10 = s.getReg .x2 - 40 := by rw [b80004ab4_x10 h₃, x2₂]; rv_eval []
  have hnpc₃ := hnew₂.same hm₃ (by addr_omega [hsb])
  have hn₃ := hnpc₃.1.mono
  have hh₃ := hnpc₃.1.heap.hi

  have hf₃ : DFrame t₁ t₃ (Scratch t₁ t₃ (stackLo s 1376) 1360) :=
    hnpc₃.1.frame.mono fun x hx ↦ by
      rcases hx with hx | hx | hx | hx
      · exact Or.inl (by addr_omega [hx, hsb])
      · exact Or.inl (by addr_omega [hx, hsb, x2₁])
      · exact Or.inr (Or.inl hx)
      · exact Or.inr (Or.inr hx)
  have hcol₃ : ColPre t₃ := {
    heap := hnpc₃.1.heap
    stack := hpre.stack.inner (k := 64) x2₃ (by decide) (by decide) (by decide) (by decide)
      (by decide)
    out := by rw [x10₃]; valid_sub hpre.stack.valid [hsb]
    outFree := by rw [x10₃]; addr_omega [hsb, hab, hnx]
    outStack := by rw [x10₃]; addr_omega [hsb, x2₃]
    rodata := RodataOk.dframe hcol₁.rodata hf₃ fun x hx ↦
      not_rodata_of_scratch (by addr_omega [hro]) hh₃ hx }
  obtain ⟨t₄, hr₄, ⟨hpc₄, hpres₄, hnew₄, hval₄⟩ | hdead⟩ :=
    hC.call hr₃ (b80004ab4_pc h₃) hcol₃
  swap
  · exact ⟨t₄, hr₂.trans hr₄, Or.inr hdead⟩
  rw [x10₃, b80004ab4_x11 h₃, b80004ab4_x12 h₃] at hval₄
  rw [x10₃] at hnew₄
  have x2₄ : t₄.getReg .x2 = s.getReg .x2 - 64 := (hpres₄.reg .x2).trans x2₃
  -- `state_derived(self, sp', sp' + 24)`
  obtain ⟨t₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b80004ac8_spec
    (by rw [hpc₄, returnAddress_eq, b80004ab4_x1 h₃]; decide) trivial
  have k₅ := b80004ac8_keeps h₅
  have hm₅ := b80004ac8_mem_same h₅
  have x2₅ : t₅.getReg .x2 = s.getReg .x2 - 64 := (k₅ .x2 (by decide)).trans x2₄
  have x8₅ : t₅.getReg .x8 = s.getReg .x10 := by
    rw [k₅ .x8 (by decide), hpres₄.reg .x8, k₃ .x8 (by decide), hpres₂.reg .x8, b80004a90_x8 h₁]
  have x10₅ : t₅.getReg .x10 = s.getReg .x10 := by
    rw [b80004ac8_x10 h₅, ← k₅ .x8 (by decide), x8₅]
  have x11₅ : t₅.getReg .x11 = s.getReg .x2 - 64 := by rw [b80004ac8_x11 h₅, x2₄]
  have x12₅ : t₅.getReg .x12 = s.getReg .x2 - 40 := by rw [b80004ac8_x12 h₅, x2₄]; rv_eval []
  have hnfp := hnew₄.same hm₅ (by addr_omega [hsb])
  have hn₅ := hnfp.1.mono
  have hh₅ := hnfp.1.heap.hi
  have hf₄₅ : DFrame t₃ t₅ fun x ↦ Within x (s.getReg .x2 - 40) 24 ∨
      Within x (stackLo t₃ colStack) colStack ∨ Within x nextAddr 8 ∨ Fresh t₃ t₅ x :=
    hnfp.1.frame
  have hf₁₅ : DFrame t₁ t₅ (Scratch t₁ t₅ (stackLo s 1376) 1360) :=
    hf₃.scratch_trans (hf₄₅.mono fun x hx ↦ by
      rcases hx with hx | hx | hx | hx
      · exact Or.inl (by addr_omega [hx, hsb])
      · exact Or.inl (by addr_omega [hx, hsb, x2₃])
      · exact Or.inr (Or.inl hx)
      · exact Or.inr (Or.inr hx)) hn₃ hn₅
  have hmono₅ : heapNext s ≤ heapNext t₅ := by omega
  have hf₅ : DFrame s t₅ (Scratch s t₅ (stackLo s 1376) 1376) :=
    (hm₁.dframe.union hf₁₅).mono fun x hx ↦ by
      simp only [Scratch, Fresh] at hx ⊢
      rcases hx with hx | hx | hx | hx
      · exact Or.inl (by addr_omega [hx, hsb])
      · exact Or.inl (by addr_omega [hx, hsb])
      · exact Or.inr (Or.inl hx)
      · exact Or.inr (Or.inr ⟨by omega, hx.2⟩)
  have hkeep := flushesOf_keep hf₅ hpre.ok hheap hmono₅ hh₅ hlo hsf hss (by addr_omega [hselfb])
  -- the two forms at the call
  have hb₃ : ∀ x, formBuf t₃ (s.getReg .x2 - 64) x → x.toNat < heapNext t₃ :=
    fun x hx ↦ (hnpc₃.1.ok.buf_below hx).2
  have hnpc := formOf_frame hf₄₅ hnpc₃.1.ok
    (fun x hx hw ↦ by
      rcases hw with hw | hw | hw | hw
      · addr_omega [hx, hw, hsb]
      · addr_omega [hx, hw, hsb, x2₃]
      · addr_omega [hx, hw, hsb, hnx]
      · simp only [Fresh] at hw; addr_omega [hx, hw, hsb, hab, hh₅])
    (fun x hx hw ↦ by
      have hx' := hb₃ x hx
      rcases hw with hw | hw | hw | hw
      · addr_omega [hx', hw, hsb, hab, hh₃]
      · addr_omega [hx', hw, hsb, hab, hh₃, x2₃]
      · addr_omega [hx', hw, hh₃]
      · simp only [Fresh] at hw; omega)
    (by addr_omega [hsb]) hnpc₃.1.heap hn₅
  have hbuf₂ : ∀ x, formBuf t₅ (s.getReg .x2 - 64) x → Fresh s t₅ x := by
    intro x hx
    rw [formBuf_frame hf₄₅ (fun y hy hw ↦ by
      rcases hw with hw | hw | hw | hw
      · addr_omega [hy, hw, hsb]
      · addr_omega [hy, hw, hsb, x2₃]
      · addr_omega [hy, hw, hsb, hnx]
      · simp only [Fresh] at hw; addr_omega [hy, hw, hsb, hab, hh₅]) (by addr_omega [hsb])] at hx
    have := hnpc₃.1.fresh
    simp only [NewBuf, formBuf, Within] at this hx
    simp only [Fresh]
    omega
  have hbuf₄ : ∀ x, formBuf t₅ (s.getReg .x2 - 40) x → Fresh s t₅ x := by
    intro x hx
    have := hnfp.1.fresh
    simp only [NewBuf, formBuf, Within] at this hx
    simp only [Fresh]
    omega
  have hbb : ∀ x, flushesBuf s (s.getReg .x10) x → x.toNat < heapNext s := fun x h ↦
    (hpre.ok.buf_below h).2
  have hsd : StateDerivedPre t₅ := {
    heap := ⟨by have := hheap.lo; omega, hh₅⟩
    stack := hpre.stack.inner (k := 64) x2₅ (by decide) (by decide) (by decide) (by decide)
      (by decide)
    self := by rw [x10₅]; exact hpre.self
    ok := by rw [x10₅]; exact hkeep.2.1
    selfFree := by rw [x10₅]; addr_omega [hsf, hmono₅]
    selfStack := by rw [x10₅]; addr_omega [hss, hsb, x2₅]
    rodata := RodataOk.dframe hpre.rodata hf₅ fun x hx ↦ not_rodata_of_scratch hro hh₅ hx
    npc := by rw [x11₅]; valid_sub hpre.stack.valid [hsb]
    nfp := by rw [x12₅]; valid_sub hpre.stack.valid [hsb]
    npcOk := by rw [x11₅]; exact hnpc.2
    nfpOk := by rw [x12₅]; exact hnfp.1.ok
    npcFree := by rw [x11₅]; addr_omega [hsb, hab, hnx]
    nfpFree := by rw [x12₅]; addr_omega [hsb, hab, hnx]
    npcStack := by rw [x11₅]; addr_omega [hsb, x2₅]
    nfpStack := by rw [x12₅]; addr_omega [hsb, x2₅]
    apart := by
      rw [x10₅, x11₅, x12₅, hkeep.2.2.2]
      intro x hx hw
      rcases hx with hx | hx | hx | hx
      · rcases hw with hw | hw
        · addr_omega [hx, hw, hss, hsb]
        · have := hbb x hw; addr_omega [hx, this, hsb, hab, hheap.hi]
      · have hx' := hbuf₂ x hx
        simp only [Fresh] at hx'
        rcases hw with hw | hw
        · addr_omega [hx', hw, hsf, hh₅]
        · have := hbb x hw; omega
      · rcases hw with hw | hw
        · addr_omega [hx, hw, hss, hsb]
        · have := hbb x hw; addr_omega [hx, this, hsb, hab, hheap.hi]
      · have hx' := hbuf₄ x hx
        simp only [Fresh] at hx'
        rcases hw with hw | hw
        · addr_omega [hx', hw, hsf, hh₅]
        · have := hbb x hw; omega }
  have hslot (a : Word) (ha₁ : (s.getReg .x2).toNat - 16 ≤ a.toNat)
      (ha₂ : a.toNat + 8 ≤ (s.getReg .x2).toNat) : t₅.getMem a = t₁.getMem a := by
    refine hf₁₅.getMem_of (fun x hx hw ↦ ?_) (by addr_omega [hsb, ha₂])
    simp only [Scratch, Fresh] at hw
    rcases hw with hw | hw | hw <;> addr_omega [hx, hw, hsb, hnx, hab, hh₅, ha₁, ha₂]
  refine ⟨t₅, hr₂.trans (hr₄.trans hr₅), Or.inl {
    pc := b80004ac8_pc h₅
    ra := b80004ac8_x1 h₅
    x2 := x2₅
    x10 := x10₅
    x11 := x11₅
    x12 := x12₅
    regs := fun r hr ↦ by
      rw [k₅ r (mem_of_mem hr _), hpres₄ r (mem_of_mem hr _),
        k₃ r (mem_of_mem hr _), hpres₂ r (mem_of_mem hr _),
        k₁ r (mem_of_mem hr _)]
    pre := hsd
    ra' := by
      rw [hslot _ (by addr_omega [hsb]) (by addr_omega [hsb])]; exact b80004a90_m_x2_n8 h₁
    s0 := by
      rw [hslot _ (by addr_omega [hsb]) (by addr_omega [hsb])]; exact b80004a90_m_x2_n16 h₁
    frame := hf₅
    mono := hmono₅
    keep := ⟨hkeep.1, hkeep.2.2.1, hkeep.2.2.2⟩
    bufs := fun x hx ↦ hx.elim (hbuf₂ x) (hbuf₄ x)
    npc := by rw [hnpc.1, hnpc₃.2, hval₂]; rfl
    nfp := by rw [hnfp.2, hval₄]; rfl }⟩

/-- **`Flushes::state_step` meets its contract**, given `col`'s and `state_derived`'s. -/
theorem state_step_spec (hC : ColSpec) (hD : StateDerivedSpec) : StateStepSpec := by
  intro s hpc hpre
  obtain ⟨t₅, hr₅, A | hdead⟩ := toCall hC hpc hpre
  swap
  · exact ⟨t₅, hr₅, Or.inr hdead⟩
  have hsb := hpre.stack.bounds (by decide) (by decide)
  have hab := hpre.stack.above
  have hnx := hpre.stack.next
  have hss := hpre.selfStack
  have hsf := hpre.selfFree
  have hselfb := ValidMemRange.bounds hpre.self (by decide)
  have hheap := hpre.heap
  simp only [stateStepStack, stateDerivedStack, colStack, powStack, Contracts.mulStack,
    Nat.reduceAdd] at hsb hab hnx hss
  have hh₅ := A.pre.heap.hi
  have hm₅ := A.mono
  have hbb : ∀ x, flushesBuf s (s.getReg .x10) x → x.toNat < heapNext s := fun x h ↦
    (hpre.ok.buf_below h).2
  obtain ⟨t₆, hr₆, ⟨hpc₆, hpres₆, hgrow₆, hval₆⟩ | hdead⟩ :=
    hD.call hr₅ A.pc A.pre
  swap
  · exact ⟨t₆, hr₆, Or.inr hdead⟩
  rw [A.x10, A.x11, A.x12] at hval₆ hgrow₆
  -- the epilogue
  have x2₆ : t₆.getReg .x2 = s.getReg .x2 - 64 := (hpres₆.reg .x2).trans A.x2
  obtain ⟨t₇, hr₇, h₇⟩ := Sym.BlockSpec.reaches b80004adc_spec
    (by rw [hpc₆, returnAddress_eq, A.ra]; decide) (by
      rv_eval [x2₆]
      and_intros <;> valid_access hpre.stack.valid [hsb])
  have hm₇ := b80004adc_mem_same h₇
  have hn₆ := hgrow₆.mono
  have hh₆ := hgrow₆.heap.hi
  have hg₆ := hgrow₆.frame
  rw [A.keep.2.2] at hg₆
  have hsave (a : Word) (ha₁ : (s.getReg .x2).toNat - 16 ≤ a.toNat)
      (ha₂ : a.toNat + 8 ≤ (s.getReg .x2).toNat) : t₆.getMem a = t₅.getMem a := by
    refine hg₆.getMem_of (fun x hx hw ↦ ?_) (by addr_omega [hsb, ha₂])
    rcases hw with hw | hw | hw | hw | hw
    · addr_omega [hx, hw, hss, hsb, ha₁, ha₂]
    · have := hbb x hw; addr_omega [hx, this, hsb, hab, hheap.hi, ha₁, ha₂]
    · addr_omega [hx, hw, hsb, A.x2, ha₁, ha₂]
    · addr_omega [hx, hw, hnx, hsb, ha₁, ha₂]
    · simp only [Fresh] at hw; addr_omega [hx, hw, hh₆, hab, hsb, ha₁, ha₂]
  have pc₇ := b80004adc_pc h₇
  have r₁ := b80004adc_x1 h₇
  have r₂ := b80004adc_x2 h₇
  have r₈ := b80004adc_x8 h₇
  have k₇ := b80004adc_keeps h₇
  rw [x2₆] at pc₇ r₁ r₂ r₈
  rv_eval [] at pc₇ r₁ r₂ r₈
  rw [hsave _ (by addr_omega [hsb]) (by addr_omega [hsb]), A.ra'] at pc₇ r₁
  rw [hsave _ (by addr_omega [hsb]) (by addr_omega [hsb]), A.s0] at r₈
  have hn₇ : heapNext t₇ = heapNext t₆ := by simp only [heapNext, hm₇]
  have hfin := flushesOf_frame (DFrame.of_same hm₇ fun _ ↦ False) hgrow₆.ok (fun _ _ h ↦ h)
    (fun _ _ h ↦ h) (by addr_omega [hselfb]) hgrow₆.heap hn₇.ge
  refine ⟨t₇, hr₆.trans hr₇, Or.inl ⟨pc₇.trans (returnAddress_eq s).symm,
    preserves_of r₂ r₈ ?_ ?_ ?_ fun r hr ↦ ?_, ?_, ?_⟩⟩
  · rw [k₇ .x9 (by decide), hpres₆.reg .x9, A.regs .x9 (by decide)]
  · rw [k₇ .x18 (by decide), hpres₆.reg .x18, A.regs .x18 (by decide)]
  · rw [k₇ .x19 (by decide), hpres₆.reg .x19, A.regs .x19 (by decide)]
  · rw [k₇ r (mem_of_mem hr _), hpres₆ r (mem_of_mem hr _),
      A.regs r (mem_of_mem hr _)]
  · exact {
      heap := ⟨hn₇ ▸ hgrow₆.heap.lo, hn₇ ▸ hh₆⟩
      mono := by omega
      ok := hfin.2.1
      deep := fun x hx ↦ by
        rw [hfin.2.2.1] at hx
        rcases hgrow₆.deep x hx with h | h | h
        · rw [A.keep.2.1] at h; exact Or.inl h
        · have h' : Fresh s t₅ x := A.bufs x h
          simp only [Fresh] at h' ⊢
          exact Or.inr (Or.inr ⟨h'.1, by omega⟩)
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
        · exact Or.inr (Or.inr (Or.inl (by addr_omega [hx, hsb, A.x2])))
        · exact Or.inr (Or.inr (Or.inr (Or.inl hx)))
        · simp only [Fresh] at hx ⊢; exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))
        · exact hx.elim }
  · rw [hfin.1, hval₆, A.keep.1, A.npc, A.nfp]
    rfl

end Rv64Verifier.Layout.StateStep
