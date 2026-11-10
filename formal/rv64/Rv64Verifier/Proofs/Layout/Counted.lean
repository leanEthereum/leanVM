import Rv64Verifier.Proofs.Layout.Keep
import Rv64Verifier.Proofs.Layout.ContractsFlushes
import Rv64Verifier.Blocks.F17

/-!
# `Flushes::counted`, at `0x8000525c`

```rust
fn counted(&mut self, prefix: &[Form; 2], counter: Form, count: usize, suffix: &[Form]) {
    let side = |counter: Form| [&prefix[..], &[counter], suffix].concat();
    self.pair(side(counter), side(col(count, 0)));
}
```

compiled (`Blocks/F17.lean`), `sp'` the entry's `sp - 192`: `0x8000525c` saves `ra`, `s0`..`s7`,
copies the counter's header to `sp' + 96`, writes the three slices at `sp' + 48` and calls
`concat(sp', sp' + 48)`; `0x800052e4` calls `col(sp' + 96, count, 0)` over the counter's copy;
`0x800052f8` writes the slices again and calls `concat(sp' + 24, sp' + 48)`; `0x80005320` calls
`pair(self, sp', sp' + 24)`; `0x80005334` restores and returns.
-/

namespace Rv64Verifier.Layout.Counted
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.FieldContracts
  Rv64Verifier.Blocks.F17 Rv64Verifier.Model.LayoutMirror

/-- One side of the pair: the prefix, `c`, the suffix, as the entry holds them. -/
def side (s : MachineState) (c : FormRust) : List FormRust :=
  formsAt s (s.getReg .x11) 2 ++ [c] ++ formsAt s (s.getReg .x14) (s.getReg .x15).toNat

/-- What every phase after the first `concat` keeps: the registers, the slots, `self`, `.rodata` and
the first `Vec` (at `sp'`), whose buffers are allocated from the entry's `NEXT` to `P`. -/
structure Inv (s u : MachineState) (P : Nat) : Prop where
  x2 : u.getReg .x2 = s.getReg .x2 - 192
  x8 : u.getReg .x8 = s.getReg .x15
  x9 : u.getReg .x9 = s.getReg .x14
  x18 : u.getReg .x18 = s.getReg .x13
  x19 : u.getReg .x19 = s.getReg .x11
  x20 : u.getReg .x20 = s.getReg .x10
  x21 : u.getReg .x21 = 2
  x22 : u.getReg .x22 = s.getReg .x2 - 96
  x23 : u.getReg .x23 = 1
  regs : ∀ r ∈ [Reg.x24, .x25, .x26, .x27], u.getReg r = s.getReg r
  ra : u.getMem (s.getReg .x2 - 8) = s.getReg .x1
  s0 : u.getMem (s.getReg .x2 - 16) = s.getReg .x8
  s1 : u.getMem (s.getReg .x2 - 24) = s.getReg .x9
  s2 : u.getMem (s.getReg .x2 - 32) = s.getReg .x18
  s3 : u.getMem (s.getReg .x2 - 40) = s.getReg .x19
  s4 : u.getMem (s.getReg .x2 - 48) = s.getReg .x20
  s5 : u.getMem (s.getReg .x2 - 56) = s.getReg .x21
  s6 : u.getMem (s.getReg .x2 - 64) = s.getReg .x22
  s7 : u.getMem (s.getReg .x2 - 72) = s.getReg .x23
  heap : HeapOk u
  lo : heapNext s ≤ P
  hi : P ≤ heapNext u
  rodata : RodataOk u
  frame : DFrame s u (Scratch s u (stackLo s 1392) 1392)
  keep : flushesOf u (s.getReg .x10) = flushesOf s (s.getReg .x10) ∧ FlushesOk u (s.getReg .x10) ∧
    flushesDeep u (s.getReg .x10) = flushesDeep s (s.getReg .x10) ∧
    flushesBuf u (s.getReg .x10) = flushesBuf s (s.getReg .x10)
  push : FormVecOk u (s.getReg .x2 - 192)
  pushVal : formVecOf u (s.getReg .x2 - 192) = side s (formOf s (s.getReg .x12))
  pushDeep : ∀ x, formVecDeep u (s.getReg .x2 - 192) x → heapNext s ≤ x.toNat ∧ x.toNat < P

/-- A step that writes only the callees' stack, the frame's locals from `sp' + 24`, `NEXT` and the
heap from `P` on keeps `Inv`. -/
theorem Inv.step {s u v : MachineState} {P : Nat} (hpre : CountedPre s) (c : Inv s u P)
    {W : Word → Prop} (hf : DFrame u v W)
    (hW : ∀ x, W x → Within x (s.getReg .x2 - 1392) 1200 ∨ Within x (s.getReg .x2 - 168) 96 ∨
      Within x nextAddr 8 ∨ (P ≤ x.toNat ∧ x.toNat < heapNext v))
    (hheap : HeapOk v) (hmono : heapNext u ≤ heapNext v)
    (hregs : ∀ r ∈ calleeSaved, v.getReg r = u.getReg r) : Inv s v P := by
  have hsb := hpre.stack.bounds (by decide) (by decide)
  have hab := hpre.stack.above
  have hnx := hpre.stack.next
  have hro := hpre.stack.rodata
  have hss := hpre.selfStack
  have hsf := hpre.selfFree
  simp only [countedStack, colStack, powStack, Contracts.mulStack,
    Nat.reduceAdd] at hsb hab hnx hro hss
  have hhv := hheap.hi
  have hlo := c.lo
  have hhi := c.hi
  have hslot (a : Word) (ha₁ : (s.getReg .x2).toNat - 72 ≤ a.toNat)
      (ha₂ : a.toNat + 8 ≤ (s.getReg .x2).toNat) : v.getMem a = u.getMem a :=
    hf.getMem_of (fun x hx hw ↦ by
      rcases hW x hw with h | h | h | h <;> addr_omega [hx, h, hsb, hab, hnx, hhv, ha₁, ha₂])
      (by addr_omega [hsb, ha₂])
  have hbelow : ∀ x, x.toNat < P → ¬ W x := fun x hx hw ↦ by
    rcases hW x hw with h | h | h | h <;> addr_omega [hx, h, hsb, hab, hnx, hhv, hhi, hmono]
  have hk := flushesOf_frame hf c.keep.2.1
    (fun x hx hw ↦ by
      rcases hW x hw with h | h | h | h <;> addr_omega [hx, h, hss, hsb, hsf, hlo, hhv])
    (fun x hx ↦ hbelow x (by
      rw [c.keep.2.2.1] at hx; have := (hpre.ok.deep_below hx).2; omega))
    (by have := ValidMemRange.bounds hpre.self (by decide); addr_omega [this]) c.heap hmono
  have hp := formVecOf_frame' hf c.push
    (fun x hx hw ↦ by
      rcases hW x hw with h | h | h | h <;> addr_omega [hx, h, hsb, hab, hnx, hhv, hhi, hmono])
    (fun x hx ↦ hbelow x (c.pushDeep x hx).2) (by addr_omega [hsb]) c.heap hmono
  have r (q : Reg) (hq : q ∈ calleeSaved := by decide) := hregs q hq
  exact {
    x2 := (r .x2).trans c.x2
    x8 := (r .x8).trans c.x8
    x9 := (r .x9).trans c.x9
    x18 := (r .x18).trans c.x18
    x19 := (r .x19).trans c.x19
    x20 := (r .x20).trans c.x20
    x21 := (r .x21).trans c.x21
    x22 := (r .x22).trans c.x22
    x23 := (r .x23).trans c.x23
    regs := fun q hq ↦ (hregs q (mem_of_mem hq _)).trans (c.regs q hq)
    ra := (hslot (s.getReg .x2 - 8) (by addr_omega [hsb]) (by addr_omega [hsb])).trans c.ra
    s0 := (hslot (s.getReg .x2 - 16) (by addr_omega [hsb]) (by addr_omega [hsb])).trans c.s0
    s1 := (hslot (s.getReg .x2 - 24) (by addr_omega [hsb]) (by addr_omega [hsb])).trans c.s1
    s2 := (hslot (s.getReg .x2 - 32) (by addr_omega [hsb]) (by addr_omega [hsb])).trans c.s2
    s3 := (hslot (s.getReg .x2 - 40) (by addr_omega [hsb]) (by addr_omega [hsb])).trans c.s3
    s4 := (hslot (s.getReg .x2 - 48) (by addr_omega [hsb]) (by addr_omega [hsb])).trans c.s4
    s5 := (hslot (s.getReg .x2 - 56) (by addr_omega [hsb]) (by addr_omega [hsb])).trans c.s5
    s6 := (hslot (s.getReg .x2 - 64) (by addr_omega [hsb]) (by addr_omega [hsb])).trans c.s6
    s7 := (hslot (s.getReg .x2 - 72) (by addr_omega [hsb]) (by addr_omega [hsb])).trans c.s7
    heap := hheap
    lo := hlo
    hi := by omega
    rodata := RodataOk.dframe c.rodata hf fun x hw h ↦ by
      rcases hW x hw with h' | h' | h' | h' <;> addr_omega [h, h', hsb, hro, hhv, hhi, hmono]
    frame := (c.frame.union hf).mono fun x hx ↦ by
      simp only [Scratch, Fresh] at hx ⊢
      rcases hx with (h | h | h) | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨h.1, by omega⟩)
      · rcases hW x h with h | h | h | h
        · exact Or.inl (by addr_omega [h, hsb])
        · exact Or.inl (by addr_omega [h, hsb])
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr ⟨by omega, h.2⟩)
    keep := ⟨hk.1.trans c.keep.1, hk.2.1, hk.2.2.1.trans c.keep.2.2.1, hk.2.2.2.trans c.keep.2.2.2⟩
    push := hp.2.1
    pushVal := hp.1.trans c.pushVal
    pushDeep := fun x hx ↦ c.pushDeep x (by rwa [hp.2.2] at hx) }

/-- After the first `concat`. -/
structure First (s t : MachineState) : Prop extends Inv s t (heapNext t) where
  pc : t.pc = 0x800052e4

/-- The counter's copy and the first `concat`. -/
theorem first (hS : ConcatSpec) {s : MachineState} (hpc : s.pc = 0x8000525c)
    (hpre : CountedPre s) : ∃ t, Reaches Image.code s t ∧ (First s t ∨ Dead Image.code t) := by
  have hsb := hpre.stack.bounds (by decide) (by decide)
  have hab := hpre.stack.above
  have hnx := hpre.stack.next
  have hro := hpre.stack.rodata
  have hss := hpre.selfStack
  have hsf := hpre.selfFree
  have hpb := ValidMemRange.bounds hpre.pre (by decide)
  have hcb := ValidMemRange.bounds hpre.counter (by decide)
  have hps := hpre.preStack
  have hcs := hpre.counterStack
  have hus := hpre.sufStack
  have hpf := hpre.preFree
  have hcf := hpre.counterFree
  have huf := hpre.sufFree
  have hheap := hpre.heap
  simp only [countedStack, colStack, powStack, Contracts.mulStack,
    Nat.reduceAdd] at hsb hab hnx hro hss hps hcs hus
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000525c_spec hpc (by
    rv_eval []
    and_intros
    all_goals (try valid_access hpre.stack.valid [hsb])
    all_goals (try valid_access hpre.counter [hcb])
    all_goals addr_omega [hsb, hcb, hcs])
  have k₁ := b8000525c_keeps h₁
  have hm₁ := b8000525c_frame h₁ (by addr_omega [hsb])
  have x2₁ := b8000525c_x2 h₁
  have x10₁ := b8000525c_x10 h₁
  have x11₁ := b8000525c_x11 h₁
  have hn₁ : heapNext t₁ = heapNext s := by
    simp only [heapNext]; rw [hm₁ _ (by addr_omega [hnx, hsb])]
  have hf₁ : DFrame s t₁ (Scratch s t₁ (stackLo s 1392) 1392) :=
    hm₁.dframe.mono fun x hx ↦ Or.inl (by addr_omega [hx, hsb])
  have hh₁ : heapNext t₁ ≤ heapEnd := hn₁ ▸ hheap.hi
  -- the slices
  have sp0 : slicePtr t₁ (s.getReg .x2 - 144) 0 = s.getReg .x11 := by
    show t₁.getMem (s.getReg .x2 - 144 + BitVec.ofNat 64 (16 * 0)) = _
    rw [show s.getReg .x2 - 144 + BitVec.ofNat 64 (16 * 0) = s.getReg .x2 - 144 by addr_omega [hsb]]
    exact b8000525c_m_x2_n144 h₁
  have sl0 : sliceLen t₁ (s.getReg .x2 - 144) 0 = 2 := by
    show (t₁.getMem (s.getReg .x2 - 144 + BitVec.ofNat 64 (16 * 0 + 8))).toNat = 2
    rw [show s.getReg .x2 - 144 + BitVec.ofNat 64 (16 * 0 + 8) = s.getReg .x2 - 136 by
      addr_omega [hsb], b8000525c_m_x2_n136 h₁]
    rfl
  have sp1 : slicePtr t₁ (s.getReg .x2 - 144) 1 = s.getReg .x2 - 96 := by
    show t₁.getMem (s.getReg .x2 - 144 + BitVec.ofNat 64 (16 * 1)) = _
    rw [show s.getReg .x2 - 144 + BitVec.ofNat 64 (16 * 1) = s.getReg .x2 - 128 by addr_omega [hsb]]
    exact b8000525c_m_x2_n128 h₁
  have sl1 : sliceLen t₁ (s.getReg .x2 - 144) 1 = 1 := by
    show (t₁.getMem (s.getReg .x2 - 144 + BitVec.ofNat 64 (16 * 1 + 8))).toNat = 1
    rw [show s.getReg .x2 - 144 + BitVec.ofNat 64 (16 * 1 + 8) = s.getReg .x2 - 120 by
      addr_omega [hsb], b8000525c_m_x2_n120 h₁]
    rfl
  have sp2 : slicePtr t₁ (s.getReg .x2 - 144) 2 = s.getReg .x14 := by
    show t₁.getMem (s.getReg .x2 - 144 + BitVec.ofNat 64 (16 * 2)) = _
    rw [show s.getReg .x2 - 144 + BitVec.ofNat 64 (16 * 2) = s.getReg .x2 - 112 by addr_omega [hsb]]
    exact b8000525c_m_x2_n112 h₁
  have sl2 : sliceLen t₁ (s.getReg .x2 - 144) 2 = (s.getReg .x15).toNat := by
    show (t₁.getMem (s.getReg .x2 - 144 + BitVec.ofNat 64 (16 * 2 + 8))).toNat = _
    rw [show s.getReg .x2 - 144 + BitVec.ofNat 64 (16 * 2 + 8) = s.getReg .x2 - 104 by
      addr_omega [hsb], b8000525c_m_x2_n104 h₁]
  -- the forms the slices hold
  have hP := formsAt_keep hf₁ hpre.preOk hheap hn₁.ge hh₁ hab hpf hps (by addr_omega [hpb])
  have hub : (s.getReg .x14).toNat + 24 * (s.getReg .x15).toNat ≤ 2 ^ 64 := by
    rcases Nat.eq_zero_or_pos (s.getReg .x15).toNat with h0 | h0
    · rw [h0]; have := (s.getReg .x14).isLt; omega
    · have := ValidMemRange.bounds hpre.suf (by omega); omega
  have hU := formsAt_keep hf₁ hpre.sufOk hheap hn₁.ge hh₁ hab huf hus hub
  have hC := formOf_move hf₁ hpre.counterOk (e := s.getReg .x2 - 96) (b8000525c_m_x2_n96 h₁)
    (by rw [show s.getReg .x2 - 96 + 8 = s.getReg .x2 - 88 by rv_eval []]
        exact b8000525c_m_x2_n88 h₁)
    (by rw [show s.getReg .x2 - 96 + 16 = s.getReg .x2 - 80 by rv_eval []]
        exact b8000525c_m_x2_n80 h₁)
    (fun x hx ↦ not_scratch hab hheap.hi (hpre.counterOk.buf_below hx).2) hheap hn₁.ge
  have hC1 : formsAt t₁ (s.getReg .x2 - 96) 1 = [formOf s (s.getReg .x12)] := by
    rw [← hC.1]; simp [formsAt]
  have hcc : ConcatPre t₁ := {
    heap := ⟨hn₁ ▸ hheap.lo, hh₁⟩
    stack := hpre.stack.inner (k := 192) x2₁ (by decide) (by decide) (by decide) (by decide)
      (by decide)
    out := by rw [x10₁]; valid_sub hpre.stack.valid [hsb]
    slices := by rw [x11₁]; valid_sub hpre.stack.valid [hsb]
    outFree := by rw [x10₁]; addr_omega [hsb, hab, hnx]
    slicesFree := by rw [x11₁]; addr_omega [hsb, hab, hnx]
    outStack := by rw [x10₁]; addr_omega [hsb, x2₁]
    slicesStack := by rw [x11₁]; addr_omega [hsb, x2₁]
    src := by
      rw [x11₁]
      intro i hi
      match i, hi with
      | 0, _ => rw [sp0, sl0]; exact hpre.pre
      | 1, _ => rw [sp1, sl1]; valid_sub hpre.stack.valid [hsb]
      | 2, _ => rw [sp2, sl2]; exact hpre.suf
    srcOk := by
      rw [x11₁]
      intro i hi
      match i, hi with
      | 0, _ => rw [sp0, sl0]; exact hP.2.1
      | 1, _ =>
        rw [sp1, sl1]
        intro j hj
        obtain rfl : j = 0 := by omega
        simpa using hC.2.1
      | 2, _ => rw [sp2, sl2]; exact hU.2.1
    srcFree := by
      rw [x11₁]
      intro i hi
      match i, hi with
      | 0, _ => rw [sp0, sl0]; simp only [Outside, hn₁]; exact hpf
      | 1, _ => rw [sp1, sl1]; addr_omega [hsb, hab, hnx]
      | 2, _ => rw [sp2, sl2]; simp only [Outside, hn₁]; exact huf
    srcStack := by
      rw [x11₁]
      intro i hi
      match i, hi with
      | 0, _ => rw [sp0, sl0]; addr_omega [hps, hsb, x2₁, hpb]
      | 1, _ => rw [sp1, sl1]; addr_omega [hsb, x2₁]
      | 2, _ => rw [sp2, sl2]; addr_omega [hus, hsb, x2₁, hub] }
  obtain ⟨t₂, hr₂, ⟨hpc₂, hpres₂, hnew₂, hval₂⟩ | hdead⟩ := hS.call hr₁ (b8000525c_pc h₁) hcc
  swap
  · exact ⟨t₂, hr₂, Or.inr hdead⟩
  rw [x10₁] at hnew₂ hval₂
  rw [x11₁, sp0, sl0, sp1, sl1, sp2, sl2, hP.1, hC1, hU.1] at hval₂
  have hn₂ := hnew₂.mono
  have hh₂ := hnew₂.heap.hi
  have hf₂ : DFrame t₁ t₂ (Scratch t₁ t₂ (stackLo s 1392) 1320) :=
    hnew₂.frame.mono fun x hx ↦ by
      rcases hx with hx | hx | hx | hx
      · exact Or.inl (by addr_omega [hx, hsb])
      · exact Or.inl (by addr_omega [hx, hsb, x2₁])
      · exact Or.inr (Or.inl hx)
      · exact Or.inr (Or.inr hx)
  have hf : DFrame s t₂ (Scratch s t₂ (stackLo s 1392) 1392) :=
    hf₁.scratch_trans (hf₂.mono fun x hx ↦ by
      simp only [Scratch] at hx ⊢
      rcases hx with hx | hx | hx
      · exact Or.inl (by addr_omega [hx, hsb])
      · exact Or.inr (Or.inl hx)
      · exact Or.inr (Or.inr hx)) hn₁.ge hn₂
  have hmono : heapNext s ≤ heapNext t₂ := by omega
  have hslot (a : Word) (ha₁ : (s.getReg .x2).toNat - 72 ≤ a.toNat)
      (ha₂ : a.toNat + 8 ≤ (s.getReg .x2).toNat) : t₂.getMem a = t₁.getMem a := by
    refine hf₂.getMem_of (fun x hx hw ↦ ?_) (by addr_omega [hsb, ha₂])
    simp only [Scratch, Fresh] at hw
    rcases hw with hw | hw | hw <;> addr_omega [hx, hw, hsb, hnx, hab, hh₂, ha₁, ha₂]
  have r (q : Reg) (hq : q ∈ calleeSaved := by decide) := hpres₂ q hq
  refine ⟨t₂, hr₂, Or.inl {
    x2 := (r .x2).trans x2₁
    x8 := (r .x8).trans (b8000525c_x8 h₁)
    x9 := (r .x9).trans (b8000525c_x9 h₁)
    x18 := (r .x18).trans (b8000525c_x18 h₁)
    x19 := (r .x19).trans (b8000525c_x19 h₁)
    x20 := (r .x20).trans (b8000525c_x20 h₁)
    x21 := (r .x21).trans (b8000525c_x21 h₁)
    x22 := (r .x22).trans (b8000525c_x22 h₁)
    x23 := (r .x23).trans (b8000525c_x23 h₁)
    regs := fun q hq ↦ (hpres₂ q (mem_of_mem hq _)).trans (k₁ q (mem_of_mem hq _))
    ra := (hslot _ (by addr_omega [hsb]) (by addr_omega [hsb])).trans (b8000525c_m_x2_n8 h₁)
    s0 := (hslot _ (by addr_omega [hsb]) (by addr_omega [hsb])).trans (b8000525c_m_x2_n16 h₁)
    s1 := (hslot _ (by addr_omega [hsb]) (by addr_omega [hsb])).trans (b8000525c_m_x2_n24 h₁)
    s2 := (hslot _ (by addr_omega [hsb]) (by addr_omega [hsb])).trans (b8000525c_m_x2_n32 h₁)
    s3 := (hslot _ (by addr_omega [hsb]) (by addr_omega [hsb])).trans (b8000525c_m_x2_n40 h₁)
    s4 := (hslot _ (by addr_omega [hsb]) (by addr_omega [hsb])).trans (b8000525c_m_x2_n48 h₁)
    s5 := (hslot _ (by addr_omega [hsb]) (by addr_omega [hsb])).trans (b8000525c_m_x2_n56 h₁)
    s6 := (hslot _ (by addr_omega [hsb]) (by addr_omega [hsb])).trans (b8000525c_m_x2_n64 h₁)
    s7 := (hslot _ (by addr_omega [hsb]) (by addr_omega [hsb])).trans (b8000525c_m_x2_n72 h₁)
    heap := hnew₂.heap
    lo := hmono
    hi := Nat.le_refl _
    rodata := RodataOk.dframe hpre.rodata hf fun x hx ↦ not_rodata_of_scratch hro hh₂ hx
    frame := hf
    keep := flushesOf_keep hf hpre.ok hheap hmono hh₂ hab hsf hss
      (by have := ValidMemRange.bounds hpre.self (by decide); addr_omega [this])
    push := hnew₂.ok
    pushVal := hval₂
    pushDeep := fun x hx ↦ by
      have := hnew₂.fresh x hx
      simp only [Fresh] at this
      omega
    pc := by rw [hpc₂, returnAddress_eq, b8000525c_x1 h₁]; decide }⟩

/-- At the second `concat`: the counter's column built over its copy, the slices written again. -/
structure AtConcat (s t : MachineState) (P : Nat) : Prop extends Inv s t P where
  pc : t.pc = 0x80011cb0
  x1 : t.getReg .x1 = 0x80005320
  x10 : t.getReg .x10 = s.getReg .x2 - 168
  x11 : t.getReg .x11 = s.getReg .x2 - 144
  q : P ≤ heapNext t
  ok : FormOk t (s.getReg .x2 - 96)
  val : formOf t (s.getReg .x2 - 96) = colRust (s.getReg .x13).toNat 0
  buf : ∀ x, formBuf t (s.getReg .x2 - 96) x → P ≤ x.toNat ∧ x.toNat < heapNext t
  m0 : t.getMem (s.getReg .x2 - 144) = s.getReg .x11
  m1 : t.getMem (s.getReg .x2 - 136) = 2
  m2 : t.getMem (s.getReg .x2 - 128) = s.getReg .x2 - 96
  m3 : t.getMem (s.getReg .x2 - 120) = 1
  m4 : t.getMem (s.getReg .x2 - 112) = s.getReg .x14
  m5 : t.getMem (s.getReg .x2 - 104) = s.getReg .x15

/-- `col(sp' + 96, count, 0)` and the slices. -/
theorem second (hC : ColSpec) {s u : MachineState} (hpre : CountedPre s) (c : First s u) :
    ∃ t, Reaches Image.code u t ∧ (AtConcat s t (heapNext u) ∨ Dead Image.code t) := by
  have hsb := hpre.stack.bounds (by decide) (by decide)
  have hab := hpre.stack.above
  have hnx := hpre.stack.next
  simp only [countedStack, colStack, powStack, Contracts.mulStack, Nat.reduceAdd] at hsb hab hnx
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800052e4_spec c.pc trivial
  have k₁ := b800052e4_keeps h₁
  have hm₁ := b800052e4_mem_same h₁
  have hn₁ : heapNext u₁ = heapNext u := by simp only [heapNext, hm₁]
  have c₁ := c.step hpre (DFrame.of_same hm₁ fun _ ↦ False) (fun _ h ↦ h.elim)
    ⟨hn₁ ▸ c.heap.lo, hn₁ ▸ c.heap.hi⟩ hn₁.ge fun r hr ↦ k₁ r (mem_of_mem hr _)
  have x10₁ : u₁.getReg .x10 = s.getReg .x2 - 96 := by rw [b800052e4_x10 h₁, c.x2]; rv_eval []
  have hcol : ColPre u₁ := {
    heap := c₁.heap
    stack := hpre.stack.inner (k := 192) c₁.x2 (by decide) (by decide) (by decide) (by decide)
      (by decide)
    out := by rw [x10₁]; valid_sub hpre.stack.valid [hsb]
    outFree := by rw [x10₁]; addr_omega [hsb, hab, hnx]
    outStack := by rw [x10₁]; addr_omega [hsb, c₁.x2]
    rodata := c₁.rodata }
  obtain ⟨u₂, hr₂, ⟨hpc₂, hpres₂, hnew₂, hval₂⟩ | hdead⟩ := hC.call hr₁ (b800052e4_pc h₁) hcol
  swap
  · exact ⟨u₂, hr₂, Or.inr hdead⟩
  rw [x10₁, b800052e4_x11 h₁, b800052e4_x12 h₁, c.x18] at hval₂
  rw [x10₁] at hnew₂
  have hn₂ := hnew₂.mono
  have c₂ := c₁.step hpre hnew₂.frame (fun x hx ↦ by
      simp only [Fresh] at hx
      rcases hx with hx | hx | hx | hx
      · exact Or.inr (Or.inl (by addr_omega [hx, hsb]))
      · exact Or.inl (by addr_omega [hx, hsb, c₁.x2])
      · exact Or.inr (Or.inr (Or.inl hx))
      · exact Or.inr (Or.inr (Or.inr ⟨by omega, hx.2⟩)))
    hnew₂.heap hn₂ hpres₂
  -- the slices again
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b800052f8_spec
    (by rw [hpc₂, returnAddress_eq, b800052e4_x1 h₁]; decide) (by
      rv_eval [c₂.x2]
      and_intros <;> valid_access hpre.stack.valid [hsb])
  have k₃ := b800052f8_keeps h₃
  have hm₃ := b800052f8_frame h₃ (by addr_omega [hsb, c₂.x2])
  rw [c₂.x2] at hm₃
  have hn₃ : heapNext u₃ = heapNext u₂ := by
    simp only [heapNext]; rw [hm₃ _ (by addr_omega [hnx, hsb])]
  have c₃ := c₂.step hpre hm₃.dframe (fun x hx ↦ Or.inr (Or.inl (by addr_omega [hx, hsb])))
    ⟨hn₃ ▸ c₂.heap.lo, hn₃ ▸ c₂.heap.hi⟩ hn₃.ge fun r hr ↦ k₃ r (mem_of_mem hr _)
  have hF := formOf_frame hm₃.dframe hnew₂.ok (fun x hx hw ↦ by addr_omega [hx, hw, hsb])
    (fun x hx hw ↦ by
      have := (hnew₂.ok.buf_below hx).2
      have h2 := hnew₂.heap.hi
      addr_omega [this, hw, hsb, hab, h2]) (by addr_omega [hsb]) hnew₂.heap hn₃.ge
  have hB := formBuf_frame hm₃.dframe (e := s.getReg .x2 - 96) (fun x hx hw ↦ by
    addr_omega [hx, hw, hsb]) (by addr_omega [hsb])
  have hm0 := b800052f8_m_x2_48 h₃
  have hm1 := b800052f8_m_x2_56 h₃
  have hm2 := b800052f8_m_x2_64 h₃
  have hm3 := b800052f8_m_x2_72 h₃
  have hm4 := b800052f8_m_x2_80 h₃
  have hm5 := b800052f8_m_x2_88 h₃
  rw [c₂.x2] at hm0 hm1 hm2 hm3 hm4 hm5
  rv_eval [] at hm0 hm1 hm2 hm3 hm4 hm5
  refine ⟨u₃, hr₂.trans hr₃, Or.inl {
    toInv := c₃
    pc := b800052f8_pc h₃
    x1 := b800052f8_x1 h₃
    x10 := by rw [b800052f8_x10 h₃, c₂.x2]; rv_eval []
    x11 := by rw [b800052f8_x11 h₃, c₂.x2]; rv_eval []
    q := by rw [hn₃]; omega
    ok := hF.2
    val := by rw [hF.1, hval₂]; rfl
    buf := fun x hx ↦ by
      rw [hB] at hx
      have hb := hnew₂.fresh
      simp only [NewBuf, formBuf, Within] at hb hx
      omega
    m0 := by rw [hm0, c₂.x19]
    m1 := by rw [hm1, c₂.x21]
    m2 := by rw [hm2, c₂.x22]
    m3 := by rw [hm3, c₂.x23]
    m4 := by rw [hm4, c₂.x9]
    m5 := by rw [hm5, c₂.x8] }⟩

/-- At the call to `pair`: both `Vec`s built. -/
structure AtPair (s t : MachineState) (P : Nat) : Prop extends Inv s t P where
  pc : t.pc = 0x80011b98
  x1 : t.getReg .x1 = 0x80005334
  pre : PairPre t
  x10 : t.getReg .x10 = s.getReg .x10
  x11 : t.getReg .x11 = s.getReg .x2 - 192
  x12 : t.getReg .x12 = s.getReg .x2 - 168
  pullVal : formVecOf t (s.getReg .x2 - 168) = side s (colRust (s.getReg .x13).toNat 0)
  pullDeep : ∀ y, formVecDeep t (s.getReg .x2 - 168) y → P ≤ y.toNat ∧ y.toNat < heapNext t

/-- The second `concat`, and `pair`'s precondition. -/
theorem third (hS : ConcatSpec) {s u : MachineState} {P : Nat} (hpre : CountedPre s)
    (c : AtConcat s u P) : ∃ t, Reaches Image.code u t ∧ (AtPair s t P ∨ Dead Image.code t) := by
  have hsb := hpre.stack.bounds (by decide) (by decide)
  have hab := hpre.stack.above
  have hnx := hpre.stack.next
  have hss := hpre.selfStack
  have hsf := hpre.selfFree
  have hpb := ValidMemRange.bounds hpre.pre (by decide)
  have hps := hpre.preStack
  have hus := hpre.sufStack
  have hheap := hpre.heap
  simp only [countedStack, colStack, powStack, Contracts.mulStack,
    Nat.reduceAdd] at hsb hab hnx hss hps hus
  have hub : (s.getReg .x14).toNat + 24 * (s.getReg .x15).toNat ≤ 2 ^ 64 := by
    rcases Nat.eq_zero_or_pos (s.getReg .x15).toNat with h0 | h0
    · rw [h0]; have := (s.getReg .x14).isLt; omega
    · have := ValidMemRange.bounds hpre.suf (by omega); omega
  have hhu := c.heap.hi
  have hmu : heapNext s ≤ heapNext u := by have := c.lo; have := c.hi; omega
  have hP := formsAt_keep c.frame hpre.preOk hheap hmu hhu hab hpre.preFree hps (by addr_omega [hpb])
  have hU := formsAt_keep c.frame hpre.sufOk hheap hmu hhu hab hpre.sufFree hus hub
  have sp0 : slicePtr u (s.getReg .x2 - 144) 0 = s.getReg .x11 := by
    show u.getMem (s.getReg .x2 - 144 + BitVec.ofNat 64 (16 * 0)) = _
    rw [show s.getReg .x2 - 144 + BitVec.ofNat 64 (16 * 0) = s.getReg .x2 - 144 by addr_omega [hsb]]
    exact c.m0
  have sl0 : sliceLen u (s.getReg .x2 - 144) 0 = 2 := by
    show (u.getMem (s.getReg .x2 - 144 + BitVec.ofNat 64 (16 * 0 + 8))).toNat = 2
    rw [show s.getReg .x2 - 144 + BitVec.ofNat 64 (16 * 0 + 8) = s.getReg .x2 - 136 by
      addr_omega [hsb], c.m1]
    rfl
  have sp1 : slicePtr u (s.getReg .x2 - 144) 1 = s.getReg .x2 - 96 := by
    show u.getMem (s.getReg .x2 - 144 + BitVec.ofNat 64 (16 * 1)) = _
    rw [show s.getReg .x2 - 144 + BitVec.ofNat 64 (16 * 1) = s.getReg .x2 - 128 by addr_omega [hsb]]
    exact c.m2
  have sl1 : sliceLen u (s.getReg .x2 - 144) 1 = 1 := by
    show (u.getMem (s.getReg .x2 - 144 + BitVec.ofNat 64 (16 * 1 + 8))).toNat = 1
    rw [show s.getReg .x2 - 144 + BitVec.ofNat 64 (16 * 1 + 8) = s.getReg .x2 - 120 by
      addr_omega [hsb], c.m3]
    rfl
  have sp2 : slicePtr u (s.getReg .x2 - 144) 2 = s.getReg .x14 := by
    show u.getMem (s.getReg .x2 - 144 + BitVec.ofNat 64 (16 * 2)) = _
    rw [show s.getReg .x2 - 144 + BitVec.ofNat 64 (16 * 2) = s.getReg .x2 - 112 by addr_omega [hsb]]
    exact c.m4
  have sl2 : sliceLen u (s.getReg .x2 - 144) 2 = (s.getReg .x15).toNat := by
    show (u.getMem (s.getReg .x2 - 144 + BitVec.ofNat 64 (16 * 2 + 8))).toNat = _
    rw [show s.getReg .x2 - 144 + BitVec.ofNat 64 (16 * 2 + 8) = s.getReg .x2 - 104 by
      addr_omega [hsb], c.m5]
  have hC1 : formsAt u (s.getReg .x2 - 96) 1 = [colRust (s.getReg .x13).toNat 0] := by
    rw [← c.val]; simp [formsAt]
  have hcc : ConcatPre u := {
    heap := c.heap
    stack := hpre.stack.inner (k := 192) c.x2 (by decide) (by decide) (by decide) (by decide)
      (by decide)
    out := by rw [c.x10]; valid_sub hpre.stack.valid [hsb]
    slices := by rw [c.x11]; valid_sub hpre.stack.valid [hsb]
    outFree := by rw [c.x10]; addr_omega [hsb, hab, hnx]
    slicesFree := by rw [c.x11]; addr_omega [hsb, hab, hnx]
    outStack := by rw [c.x10]; addr_omega [hsb, c.x2]
    slicesStack := by rw [c.x11]; addr_omega [hsb, c.x2]
    src := by
      rw [c.x11]
      intro i hi
      match i, hi with
      | 0, _ => rw [sp0, sl0]; exact hpre.pre
      | 1, _ => rw [sp1, sl1]; valid_sub hpre.stack.valid [hsb]
      | 2, _ => rw [sp2, sl2]; exact hpre.suf
    srcOk := by
      rw [c.x11]
      intro i hi
      match i, hi with
      | 0, _ => rw [sp0, sl0]; exact hP.2.1
      | 1, _ =>
        rw [sp1, sl1]
        intro j hj
        obtain rfl : j = 0 := by omega
        simpa using c.ok
      | 2, _ => rw [sp2, sl2]; exact hU.2.1
    srcFree := by
      rw [c.x11]
      intro i hi
      match i, hi with
      | 0, _ => rw [sp0, sl0]; have := hpre.preFree; addr_omega [this, hmu]
      | 1, _ => rw [sp1, sl1]; addr_omega [hsb, hab, hnx]
      | 2, _ => rw [sp2, sl2]; have := hpre.sufFree; addr_omega [this, hmu]
    srcStack := by
      rw [c.x11]
      intro i hi
      match i, hi with
      | 0, _ => rw [sp0, sl0]; addr_omega [hps, hsb, c.x2, hpb]
      | 1, _ => rw [sp1, sl1]; addr_omega [hsb, c.x2]
      | 2, _ => rw [sp2, sl2]; addr_omega [hus, hsb, c.x2, hub] }
  obtain ⟨u₁, hr₁, ⟨hpc₁, hpres₁, hnew₁, hval₁⟩ | hdead⟩ :=
    hS.call (Reaches.refl u) c.pc hcc
  swap
  · exact ⟨u₁, hr₁, Or.inr hdead⟩
  rw [c.x10] at hnew₁ hval₁
  rw [c.x11, sp0, sl0, sp1, sl1, sp2, sl2, hP.1, hC1, hU.1] at hval₁
  have hn₁ := hnew₁.mono
  have c₁ := c.step hpre hnew₁.frame (fun x hx ↦ by
      simp only [Fresh] at hx
      rcases hx with hx | hx | hx | hx
      · exact Or.inr (Or.inl (by addr_omega [hx, hsb]))
      · exact Or.inl (by addr_omega [hx, hsb, c.x2])
      · exact Or.inr (Or.inr (Or.inl hx))
      · exact Or.inr (Or.inr (Or.inr ⟨by have := c.q; omega, hx.2⟩)))
    hnew₁.heap hn₁ hpres₁
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80005320_spec
    (by rw [hpc₁, returnAddress_eq, c.x1]; decide) trivial
  have k₂ := b80005320_keeps h₂
  have hm₂ := b80005320_mem_same h₂
  have hn₂ : heapNext u₂ = heapNext u₁ := by simp only [heapNext, hm₂]
  have c₂ := c₁.step hpre (DFrame.of_same hm₂ fun _ ↦ False) (fun _ h ↦ h.elim)
    ⟨hn₂ ▸ c₁.heap.lo, hn₂ ▸ c₁.heap.hi⟩ hn₂.ge fun r hr ↦ k₂ r (mem_of_mem hr _)
  have hq := c.q
  have hpl := formVecOf_frame' (DFrame.of_same hm₂ fun _ ↦ False) hnew₁.ok (fun _ _ h ↦ h)
    (fun _ _ h ↦ h) (by addr_omega [hsb]) hnew₁.heap hn₂.ge
  have hpull : ∀ y, formVecDeep u₂ (s.getReg .x2 - 168) y → P ≤ y.toNat ∧ y.toNat < heapNext u₂ := by
    intro y hy
    rw [hpl.2.2] at hy
    have := hnew₁.fresh y hy
    simp only [Fresh] at this
    omega
  have hhu₂ := c₂.heap.hi
  have hbb : ∀ y, flushesBuf u₂ (s.getReg .x10) y → y.toNat < heapNext s := fun y hy ↦ by
    rw [c₂.keep.2.2.2] at hy; exact (hpre.ok.buf_below hy).2
  have hfresh : ∀ y, heapNext s ≤ y.toNat → y.toNat < heapNext u₂ →
      ¬ (Within y (s.getReg .x10) 48 ∨ flushesBuf u₂ (s.getReg .x10) y) := by
    intro y h1 h2 hy
    rcases hy with hy | hy
    · addr_omega [hy, h1, h2, hsf, hhu₂]
    · have := hbb y hy; omega
  have hx10 : u₂.getReg .x10 = s.getReg .x10 := by rw [b80005320_x10 h₂, c₁.x20]
  have hx11 : u₂.getReg .x11 = s.getReg .x2 - 192 := by rw [b80005320_x11 h₂, c₁.x2]
  have hx12 : u₂.getReg .x12 = s.getReg .x2 - 168 := by rw [b80005320_x12 h₂, c₁.x2]; rv_eval []
  have x2₂ := c₂.x2
  have hlo := c₂.lo
  have hhi := c₂.hi
  refine ⟨u₂, hr₁.trans hr₂, Or.inl {
    toInv := c₂
    pc := b80005320_pc h₂
    x1 := b80005320_x1 h₂
    x10 := hx10
    x11 := hx11
    x12 := hx12
    pullVal := by rw [hpl.1, hval₁]; rfl
    pullDeep := hpull
    pre := {
      heap := c₂.heap
      stack := hpre.stack.inner (k := 192) x2₂ (by decide) (by decide) (by decide) (by decide)
        (by decide)
      self := by rw [hx10]; exact hpre.self
      ok := by rw [hx10]; exact c₂.keep.2.1
      push := by rw [hx11]; valid_sub hpre.stack.valid [hsb]
      pull := by rw [hx12]; valid_sub hpre.stack.valid [hsb]
      pushOk := by rw [hx11]; exact c₂.push
      pullOk := by rw [hx12]; exact hpl.2.1
      selfFree := by rw [hx10]; addr_omega [hsf, hlo, hhi]
      pushFree := by rw [hx11]; addr_omega [hsb, hab, hnx]
      pullFree := by rw [hx12]; addr_omega [hsb, hab, hnx]
      selfStack := by rw [hx10]; addr_omega [hss, hsb, x2₂]
      pushStack := by rw [hx11]; addr_omega [hsb, x2₂]
      pullStack := by rw [hx12]; addr_omega [hsb, x2₂]
      apart := fun y hy hw ↦ by
        rw [hx11, hx12] at hy
        rw [hx10] at hw
        rcases hy with hy | hy | hy | hy
        · rcases hw with h | h
          · addr_omega [hy, h, hss, hsb]
          · have h1 := hbb y h; have h2 := hheap.hi; addr_omega [hy, h1, h2, hsb, hab]
        · have := c₂.pushDeep y hy
          exact hfresh y this.1 (by omega) hw
        · rcases hw with h | h
          · addr_omega [hy, h, hss, hsb]
          · have h1 := hbb y h; have h2 := hheap.hi; addr_omega [hy, h1, h2, hsb, hab]
        · have := hpull y hy
          exact hfresh y (by omega) this.2 hw } }⟩

/-- What `pair` and the epilogue leave, from the call at `x` to `z`. -/
theorem finish {s x y z : MachineState} {P : Nat} (hpre : CountedPre s) (X : AtPair s x P)
    (Y : PairPost x y) (hz : ∀ a, z.getMem a = y.getMem a) :
    GrowFlushes s z (s.getReg .x10) countedStack (fun _ ↦ False) ∧
      flushesOf z (s.getReg .x10) = (flushesOf s (s.getReg .x10)).counted
        (formsAt s (s.getReg .x11) 2) (formOf s (s.getReg .x12)) (s.getReg .x13).toNat
        (formsAt s (s.getReg .x14) (s.getReg .x15).toNat) := by
  have hsb := hpre.stack.bounds (by decide) (by decide)
  have hselfb := ValidMemRange.bounds hpre.self (by decide)
  simp only [countedStack, colStack, powStack, Contracts.mulStack, Nat.reduceAdd] at hsb
  have hval := Y.value
  have hdeep := Y.deep
  have hfr := Y.frame
  rw [X.x10, X.x11, X.x12] at hval hdeep
  rw [X.x10, X.keep.2.2.2] at hfr
  have Yok := Y.ok
  rw [X.x10] at Yok
  have hn : heapNext z = heapNext y := by simp only [heapNext, hz]
  have hfin := flushesOf_frame (DFrame.of_same hz fun _ ↦ False) Yok (fun _ _ h ↦ h)
    (fun _ _ h ↦ h) (by addr_omega [hselfb]) Y.heap hn.ge
  have hm := Y.mono
  have hlo := X.lo
  have hhi := X.hi
  refine ⟨{
    heap := ⟨hn ▸ Y.heap.lo, hn ▸ Y.heap.hi⟩
    mono := by omega
    ok := hfin.2.1
    deep := fun q hq ↦ by
      rw [hfin.2.2.1] at hq
      rcases hdeep q hq with h | h | h | h
      · rw [X.keep.2.2.1] at h; exact Or.inl h
      · have := X.pushDeep q h
        simp only [Fresh]; exact Or.inr (Or.inr ⟨this.1, by omega⟩)
      · have := X.pullDeep q h
        simp only [Fresh]; exact Or.inr (Or.inr ⟨by omega, by omega⟩)
      · simp only [Fresh] at h ⊢; exact Or.inr (Or.inr ⟨by omega, by omega⟩)
    frame := ((X.frame.union hfr).union (DFrame.of_same hz fun _ ↦ False)).mono fun q hq ↦ by
      simp only [Scratch] at hq
      rcases hq with ((hq | hq | hq) | hq | hq | hq | hq | hq) | hq
      · exact Or.inr (Or.inr (Or.inl (by addr_omega [hq, hsb])))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hq)))
      · simp only [Fresh] at hq ⊢; exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hq.1, by omega⟩)))
      · exact Or.inl hq
      · exact Or.inr (Or.inl hq)
      · exact Or.inr (Or.inr (Or.inl (by addr_omega [hq, hsb, X.x2])))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hq)))
      · simp only [Fresh] at hq ⊢; exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))
      · exact hq.elim }, ?_⟩
  rw [hfin.1, hval, X.keep.1, X.pushVal, X.pullVal]
  rfl

/-- **`Flushes::counted` meets its contract**, given `concat`'s, `col`'s and `Flushes::pair`'s. -/
theorem counted_spec (hS : ConcatSpec) (hC : ColSpec) (hP : PairSpec) : CountedSpec := by
  intro s hpc hpre
  obtain ⟨u, hru, U | hdead⟩ := first hS hpc hpre
  swap
  · exact ⟨u, hru, Or.inr hdead⟩
  obtain ⟨v, hrv, V | hdead⟩ := second hC hpre U
  swap
  · exact ⟨v, hru.trans hrv, Or.inr hdead⟩
  obtain ⟨x, hrx, X | hdead⟩ := third hS hpre V
  swap
  · exact ⟨x, hru.trans (hrv.trans hrx), Or.inr hdead⟩
  obtain ⟨y, hry, ⟨hpcy, hpresy, Y⟩ | hdead⟩ := hP.call (Reaches.refl x) X.pc X.pre
  swap
  · exact ⟨y, hru.trans (hrv.trans (hrx.trans hry)), Or.inr hdead⟩
  have hsb := hpre.stack.bounds (by decide) (by decide)
  have hab := hpre.stack.above
  have hnx := hpre.stack.next
  have hss := hpre.selfStack
  simp only [countedStack, colStack, powStack, Contracts.mulStack,
    Nat.reduceAdd] at hsb hab hnx hss
  have x2y : y.getReg .x2 = s.getReg .x2 - 192 := (hpresy.reg .x2).trans X.x2
  obtain ⟨z, hrz, hz⟩ := Sym.BlockSpec.reaches b80005334_spec
    (by rw [hpcy, returnAddress_eq, X.x1]; decide) (by
      rv_eval [x2y]
      and_intros <;> valid_access hpre.stack.valid [hsb])
  have hfr := Y.frame
  rw [X.x10, X.keep.2.2.2] at hfr
  have hhy := Y.heap.hi
  have hsave (a : Word) (ha₁ : (s.getReg .x2).toNat - 72 ≤ a.toNat)
      (ha₂ : a.toNat + 8 ≤ (s.getReg .x2).toNat) : y.getMem a = x.getMem a := by
    refine hfr.getMem_of (fun q hq hw ↦ ?_) (by addr_omega [hsb, ha₂])
    rcases hw with hw | hw | hw | hw | hw
    · addr_omega [hq, hw, hss, hsb, ha₁, ha₂]
    · have h1 := (hpre.ok.buf_below hw).2
      have h2 := hpre.heap.hi
      addr_omega [hq, h1, h2, hsb, hab, ha₁, ha₂]
    · addr_omega [hq, hw, hsb, X.x2, ha₁, ha₂]
    · addr_omega [hq, hw, hnx, hsb, ha₁, ha₂]
    · simp only [Fresh] at hw; addr_omega [hq, hw, hhy, hab, hsb, ha₁, ha₂]
  have pcz := b80005334_pc hz
  have r₁ := b80005334_x1 hz
  have r₂ := b80005334_x2 hz
  have r₈ := b80005334_x8 hz
  have r₉ := b80005334_x9 hz
  have r₁₈ := b80005334_x18 hz
  have r₁₉ := b80005334_x19 hz
  have r₂₀ := b80005334_x20 hz
  have r₂₁ := b80005334_x21 hz
  have r₂₂ := b80005334_x22 hz
  have r₂₃ := b80005334_x23 hz
  have kz := b80005334_keeps hz
  rw [x2y] at pcz r₁ r₂ r₈ r₉ r₁₈ r₁₉ r₂₀ r₂₁ r₂₂ r₂₃
  rv_eval [] at pcz r₁ r₂ r₈ r₉ r₁₈ r₁₉ r₂₀ r₂₁ r₂₂ r₂₃
  rw [hsave _ (by addr_omega [hsb]) (by addr_omega [hsb]), X.ra] at pcz r₁
  rw [hsave _ (by addr_omega [hsb]) (by addr_omega [hsb]), X.s0] at r₈
  rw [hsave _ (by addr_omega [hsb]) (by addr_omega [hsb]), X.s1] at r₉
  rw [hsave _ (by addr_omega [hsb]) (by addr_omega [hsb]), X.s2] at r₁₈
  rw [hsave _ (by addr_omega [hsb]) (by addr_omega [hsb]), X.s3] at r₁₉
  rw [hsave _ (by addr_omega [hsb]) (by addr_omega [hsb]), X.s4] at r₂₀
  rw [hsave _ (by addr_omega [hsb]) (by addr_omega [hsb]), X.s5] at r₂₁
  rw [hsave _ (by addr_omega [hsb]) (by addr_omega [hsb]), X.s6] at r₂₂
  rw [hsave _ (by addr_omega [hsb]) (by addr_omega [hsb]), X.s7] at r₂₃
  refine ⟨z, hru.trans (hrv.trans (hrx.trans (hry.trans hrz))), Or.inl ⟨
    pcz.trans (returnAddress_eq s).symm, preserves_of r₂ r₈ r₉ r₁₈ r₁₉ fun r hr ↦ ?_,
    finish hpre X Y (b80005334_mem_same hz)⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | hr
  · exact r₂₀
  · exact r₂₁
  · exact r₂₂
  · exact r₂₃
  · have hr' : r ∈ [Reg.x24, .x25, .x26, .x27] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; exact hr
    rw [kz r (mem_of_mem hr' _), hpresy r (mem_of_mem hr' _), X.regs r hr']

end Rv64Verifier.Layout.Counted
