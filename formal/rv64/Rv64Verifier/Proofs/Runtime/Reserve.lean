import Rv64Verifier.Proofs.Runtime.GrowOne

/-!
# `Vec<T>::reserve`, six copies

```rust
if self.buf.needs_to_grow(self.len, additional) {        // cap - len < additional
    if let Err(err) = self.buf.grow_amortized(self.len, additional) { handle_error(err) }
}
```

As for `grow_one` (`GrowOne.lean`), every copy is the same eighteen words but for the element's
alignment and size and the call's offset: at `e`, `cap - len` against `a1`, to `e + 16` (return)
or `e + 20`; at `e + 20`, a 16-byte frame and the call `grow_amortized(self, len, additional)`; at
`e + 52`, restore, then `e + 16` if it returned `-1`, else the trap at `e + 68`. One proof
(`reserve_of`) covers the copies.
-/

namespace Rv64Verifier.Runtime.Reserve
open RiscvZkvm.Rv64 Rv64Verifier.Sym Rv64Verifier.Runtime.GrowOne
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- `cap - len`, as the code computes it. -/
def room : E := .bin .sub (.ld (.reg .x10)) (.ld (.bin .add (.reg .x10) (.c 16)))

/-- At `e`: is there room? -/
def resA (e : Word) : Expect where
  steps := 4
  pc := .ite .ltu room (.reg .x11) (.c (e + 20)) (.c (e + 16))
  regs := [(.x1, .reg .x1), (.x2, .reg .x2), (.x10, .reg .x10), (.x11, .reg .x11), (.x12, room),
    (.x15, .ld (.bin .add (.reg .x10) (.c 16)))] ++ saved.map fun r ↦ (r, .reg r)
  mem := []
  writes := []
  obl := [.valid ⟨some (.reg .x10), 16⟩ 8, .valid ⟨some (.reg .x10), 0⟩ 8]

/-- At `e + 16`: return. -/
def resB : Expect where
  steps := 1
  pc := .bin .and (.reg .x1) (.c 0xfffffffffffffffe)
  regs := [(.x2, .reg .x2), (.x10, .reg .x10)] ++ saved.map fun r ↦ (r, .reg r)
  mem := []
  writes := []
  obl := []

/-- At `e + 20`: the frame, the arguments, the call. -/
def resC (e al sz : Word) : Expect where
  steps := 8
  pc := .c 0x8000c184
  regs := [(.x1, .c (e + 52)), (.x2, .bin .add (.reg .x2) (.c 0xfffffffffffffff0)),
    (.x10, .reg .x10), (.x11, .reg .x15), (.x12, .reg .x11), (.x13, .c al), (.x14, .c sz)] ++
    saved.map fun r ↦ (r, .reg r)
  mem := [(⟨some (.reg .x2), 0xfffffffffffffff8⟩, .reg .x1)]
  writes := [⟨some (.reg .x2), 0xfffffffffffffff8⟩]
  obl := [.valid ⟨some (.reg .x2), 0xfffffffffffffff8⟩ 8]

/-- At `e + 52`: restore; return if `grow_amortized` returned `-1`, else the trap. -/
def resD (e : Word) : Expect where
  steps := 4
  pc := .ite .eq (.reg .x10) (.c 0xffffffffffffffff) (.c (e + 16)) (.c (e + 68))
  regs := [(.x1, .ld (.bin .add (.reg .x2) (.c 8))), (.x2, .bin .add (.reg .x2) (.c 16)),
    (.x10, .reg .x10)] ++ saved.map fun r ↦ (r, .reg r)
  mem := []
  writes := []
  obl := [.valid ⟨some (.reg .x2), 8⟩ 8]

theorem _root_.Rv64Verifier.Runtime.ReservePre.bounds {size align : Nat} {s : MachineState}
    (h : ReservePre size align s) :
    0x780000a0 ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000008 ∧
      (s.getReg .x2).toNat % 16 = 0 ∧ (s.getReg .x10).toNat % 8 = 0 ∧
      (s.getReg .x10).toNat + 24 ≤ 0xc0000008 := by
  have := h.stack.bounds (by decide) (by decide)
  have ha := h.stack.above
  have ho := ValidMemRange.bounds h.self (by decide)
  simp only [reserveStack, stackLo, heapEnd] at this ha
  rw [this.2.2.2] at ha
  omega

/-- **Every copy of `reserve` meets its contract**, its buffer the same or a new one, given
`grow_amortized`'s, from its four blocks. -/
theorem reserve_of (hG : GrowSpec) {e : Word} {size align : Nat}
    (hal : 0 < align ∧ align ≤ 2 ^ 32) (hsz : 0 < size ∧ size < 2 ^ 32)
    (hA : Spec e (resA e)) (hB : Spec (e + 16) resB)
    (hC : Spec (e + 20) (resC e (BitVec.ofNat 64 align) (BitVec.ofNat 64 size)))
    (hD : Spec (e + 52) (resD e))
    (hret : (e + 52) &&& 0xfffffffffffffffe = e + 52)
    (htrap : Image.code.fetch (e + 68) = none) : ReserveFreshSpec e size align := by
  intro s hpc hpre
  have hb := hpre.bounds
  have hst := hpre.stack
  have hss := hpre.selfStack
  have hsf := hpre.selfFree
  have hnx8 := hst.next
  have hab := hst.above
  have hvec := hpre.vec
  have hraw := hvec.raw
  simp only [RawVecOk, Buf, vecPtr, vecCap] at hraw
  have hlen := hvec.len
  simp only [vecLen, vecCap] at hlen
  obtain ⟨t₀, hr₀, h₀⟩ := hA.reaches hpc (by
    rv_eval []
    and_intros <;> valid_access hpre.self [hb])
  have pc₀ := h₀.pc
  have x15₀ := h₀.reg .x15 rfl
  have k₀ := h₀.keeps (rs := [.x1, .x2, .x10, .x11] ++ saved) rfl
  have hm₀ (a : Word) : t₀.getMem a = s.getMem a := h₀.frame a (by simp [resA])
  rv_eval [room] at pc₀ x15₀
  have hroom : (s.getMem (s.getReg .x10) - s.getMem (s.getReg .x10 + 16)).toNat =
      (s.getMem (s.getReg .x10)).toNat - (s.getMem (s.getReg .x10 + 16)).toNat := by
    rw [BitVec.toNat_sub]; omega
  rcases eq_ite_cases pc₀ with ⟨hlt, pc₀⟩ | ⟨hge, pc₀⟩
  swap
  · -- room enough: return
    obtain ⟨t, hr, h⟩ := hB.reaches pc₀ trivial
    have pc := h.pc
    rv_eval [k₀ .x1 (by decide)] at pc
    have k := h.keeps (rs := [.x2, .x10] ++ saved) rfl
    have hm (a : Word) : t.getMem a = s.getMem a := (h.frame a (by simp [resB])).trans (hm₀ a)
    have hn : heapNext t = heapNext s := by simp only [heapNext, hm]
    simp only [BitVec.ult, decide_eq_true_eq, Nat.not_lt, hroom] at hge
    refine ⟨t, hr₀.trans hr, Or.inl ⟨pc.trans (returnAddress_eq s).symm, fun r hr' ↦ ?_,
      ⟨⟨hn ▸ hpre.heap.lo, hn ▸ hpre.heap.hi⟩, hn.ge, ?_, ?_, ?_, ?_, ByteFrame.of_same hm _⟩,
      Or.inl ⟨by simp only [vecPtr, hm], by simp only [vecCap, hm]⟩⟩⟩
    · rw [k r (mem_of_mem hr' _), k₀ r (mem_of_mem hr' _)]
    · simp only [vecLen, vecCap, hm]; omega
    · exact ⟨by simp only [RawVecOk, Buf, vecPtr, vecCap, hm, hn]; exact hraw,
        by simp only [vecCap, vecLen, hm]; exact hlen⟩
    · simp only [vecLen, hm]
    · simp only [vecPtr, vecCap, hm]
      exact (ByteFrame.of_same hm fun _ ↦ False).bytesAt fun _ _ h ↦ h
  -- grow
  have hss' : Apart (s.getReg .x10) 16 (stackLo s reserveStack) reserveStack := by addr_omega [hss]
  obtain ⟨t₁, hr₁, h₁⟩ := hC.reaches pc₀ (by
    rv_eval [k₀ .x2 (by decide)]
    valid_access hst.valid [hb])
  have x1 := h₁.reg .x1 rfl
  have x2 := h₁.reg .x2 rfl
  have x10 := h₁.reg .x10 rfl
  have x11 := h₁.reg .x11 rfl
  have x12 := h₁.reg .x12 rfl
  have x13 := h₁.reg .x13 rfl
  have x14 := h₁.reg .x14 rfl
  have pc₁ := h₁.pc
  have m₁ := h₁.memAt 0 (by exact Nat.zero_lt_one)
  rv_eval [k₀ .x1 (by decide), k₀ .x2 (by decide), k₀ .x10 (by decide), k₀ .x11 (by decide),
    x15₀] at x1 x2 x10 x11 x12 x13 x14 pc₁ m₁
  have hm₁ (a : Word) (ha : a ≠ s.getReg .x2 - 8) : t₁.getMem a = s.getMem a :=
    (h₁.frame a (by rv_eval [k₀ .x2 (by decide)]; exact ha)).trans (hm₀ a)
  have hn₁ : t₁.getMem nextAddr = s.getMem nextAddr := hm₁ _ (by addr_omega [hb, hnx8])
  have hheap₁ : HeapOk t₁ := ⟨by simp only [heapNext, hn₁]; exact hpre.heap.lo,
    by simp only [heapNext, hn₁]; exact hpre.heap.hi⟩
  have hsl : stackLo t₁ growStack = stackLo s reserveStack := by
    simp only [stackLo, growStack, reserveStack, x2]
    rw [Sym.sub_sub_lit]; rfl
  have hself : t₁.getMem (s.getReg .x10) = s.getMem (s.getReg .x10) := hm₁ _ (by addr_omega [hb, hss])
  have hself8 : t₁.getMem (s.getReg .x10 + 8) = s.getMem (s.getReg .x10 + 8) :=
    hm₁ _ (by addr_omega [hb, hss])
  have hself16 : t₁.getMem (s.getReg .x10 + 16) = s.getMem (s.getReg .x10 + 16) :=
    hm₁ _ (by addr_omega [hb, hss])
  have hv₁ : ValidMemRange (stackLo t₁ growStack) (growStack / 8) := by
    rw [hsl]
    exact ValidMemRange.sub hst.valid (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb])
  have hro := hst.rodata
  have hpre₁ : GrowPre t₁ := {
    heap := hheap₁
    self := by
      rw [x10]
      exact ValidMemRange.sub hpre.self (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb])
    align := by rw [x13, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hal
    size := by rw [x14, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hsz.1
    raw := by
      rw [x10, x13, x14, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega)]
      simp only [RawVecOk, Buf, vecPtr, vecCap, hself, hself8, heapNext, hn₁]
      exact hraw
    stack := ⟨⟨hv₁, by rw [x2]; addr_omega [hb]⟩, by rw [hsl]; exact hab,
      by rw [hsl]; addr_omega [hnx8, hb], by rw [hsl]; addr_omega [hro, hb]⟩
    selfFree := by
      rw [x10]
      simp only [Outside, heapNext, hn₁] at hsf ⊢
      exact ⟨by omega, by addr_omega [hsf.2]⟩
    selfStack := by rw [x10, hsl]; addr_omega [hss] }
  obtain ⟨t₂, hr₂, ⟨hpc₂, hpres₂, hpost⟩ | hdead⟩ := hG.call hr₁ pc₁ hpre₁
  swap
  · exact ⟨t₂, hr₀.trans hr₂, Or.inr hdead⟩
  have hpc₂' : t₂.pc = e + 52 := by rw [hpc₂, returnAddress_eq, x1]; exact hret
  have hsp₂ : t₂.getReg .x2 = s.getReg .x2 - 16 := by rw [hpres₂.reg .x2, x2]
  obtain ⟨t₃, hr₃, h₃⟩ := hD.reaches hpc₂' (by
    rv_eval [hsp₂]
    valid_access hst.valid [hb])
  have pc₃ := h₃.pc
  have x1₃ := h₃.reg .x1 rfl
  have x2₃ := h₃.reg .x2 rfl
  rv_eval [hsp₂] at pc₃ x1₃ x2₃
  have hm₃ (a : Word) : t₃.getMem a = t₂.getMem a := h₃.frame a (by simp [resD])
  rcases eq_ite_cases pc₃ with ⟨hok, pc₃⟩ | ⟨-, pc₃⟩
  swap
  · exact ⟨t₃, hr₀.trans (hr₂.trans hr₃), Or.inr (dead_of_fetch (by rw [pc₃]; exact htrap))⟩
  have hok' : t₂.getReg .x10 = 0xffffffffffffffff := by simpa using hok
  obtain ⟨t₄, hr₄, h₄⟩ := hB.reaches pc₃ trivial
  have pc₄ := h₄.pc
  rv_eval [x1₃] at pc₄
  have hm₄ (a : Word) : t₄.getMem a = t₃.getMem a := h₄.frame a (by simp [resB])
  have hfr := hpost.frame
  rw [x10, hsl] at hfr
  have hheap₂ := hpost.heap
  have hra : t₂.getMem (s.getReg .x2 - 8) = s.getReg .x1 := by
    rw [hfr.getMem fun i hi ha ↦ ?_, m₁]
    have := hheap₂.hi
    simp only [Fresh, heapNext] at ha this
    rcases ha with ha | ha | ha | ha
    · addr_omega [ha, hi, hss, hb]
    · addr_omega [ha, hi, hb]
    · addr_omega [ha, hi, hb, hnx8]
    · addr_omega [ha.2, hi, hb, hab, this]
  rw [hra] at pc₄
  have hlen₂ : t₂.getMem (s.getReg .x10 + 16) = s.getMem (s.getReg .x10 + 16) := by
    rw [hfr.getMem fun i hi ha ↦ ?_, hself16]
    have := hheap₂.hi
    have hsf' := hsf
    simp only [Fresh, heapNext, Outside] at ha this hsf'
    rcases ha with ha | ha | ha | ha
    · addr_omega [ha, hi, hb]
    · addr_omega [ha, hi, hb, hss]
    · addr_omega [ha, hi, hb, hsf'.2]
    · addr_omega [ha, hi, hb, hsf'.1, this, hn₁]
  have hsz' : (BitVec.ofNat 64 size).toNat = size := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hal' : (BitVec.ofNat 64 align).toNat = align := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hmt (a : Word) : t₄.getMem a = t₂.getMem a := (hm₄ a).trans (hm₃ a)
  have hn₄ : heapNext t₄ = heapNext t₂ := by simp only [heapNext, hmt]
  have hn₁' : heapNext t₁ = heapNext s := by simp only [heapNext, hn₁]
  obtain ⟨hcap, hraw', hby⟩ := hpost.ok hok'
  rw [x11, x12, x10] at hcap
  rw [x10, x13, x14, hsz', hal'] at hraw'
  rw [x10, x14, hsz'] at hby
  have hcap' : (vecLen s (s.getReg .x10)).toNat + (s.getReg .x11).toNat ≤
      (vecCap t₄ (s.getReg .x10)).toNat := by
    simp only [vecLen, vecCap, hmt]; exact hcap
  refine ⟨t₄, hr₀.trans (hr₂.trans (hr₃.trans hr₄)), Or.inl ⟨pc₄.trans (returnAddress_eq s).symm,
    ?_, ⟨⟨hn₄ ▸ hheap₂.lo, hn₄ ▸ hheap₂.hi⟩, ?_, hcap', ⟨?_, ?_⟩, ?_, ?_, ?_⟩, Or.inr ?_⟩⟩
  · have kC := h₁.keeps (rs := saved) rfl
    have kD := h₃.keeps (rs := saved) rfl
    have kB := h₄.keeps (rs := saved) rfl
    have kB2 := h₄.keeps (rs := [.x2]) rfl
    intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | hr
    · rw [kB2 .x2 (by decide), x2₃]
    · have hr' : r ∈ saved := by simp only [saved, List.mem_cons, List.not_mem_nil, or_false]; exact hr
      rw [kB r hr', kD r hr', hpres₂ r (mem_of_mem hr' _), kC r hr', k₀ r (mem_of_mem hr' _)]
  · rw [hn₄, ← hn₁']; exact hpost.mono
  · simp only [RawVecOk, Buf, vecCap, vecPtr, hmt, hn₄] at hraw' ⊢
    exact hraw'
  · simp only [vecLen, vecCap, hmt, hlen₂] at hcap ⊢; omega
  · simp only [vecLen, hmt, hlen₂]
  · simp only [vecCap, vecPtr, hmt, hself, hself8] at hby ⊢
    rw [(ByteFrame.of_same hmt fun _ ↦ False).bytesAt fun _ _ h ↦ h, hby]
    rcases hraw.2 with h0 | h0
    · simp only [h0]; rfl
    · exact bytesAt_of_below (lo := s.getReg .x2 - 8) (N := 8)
        (fun a ha ↦ hm₁ a fun h' ↦ ha (by rw [h']; addr_omega [hb]))
        (by have := hpre.heap.hi; addr_omega [h0, this, hab, hb])
  · have bf₁ := ByteFrame.of_single (s := s) (t := t₁) (by addr_omega [hb]) hm₁
    refine ((bf₁.mono (w' := fun a ↦ Within a (s.getReg .x10) 16 ∨
      Within a (stackLo s reserveStack) reserveStack ∨ Within a nextAddr 8 ∨ Fresh s t₄ a)
      fun a ha ↦ Or.inr (Or.inl (by addr_omega [ha, hb]))).trans hfr fun a ha ↦ ?_).trans
      (ByteFrame.of_same hmt _) fun _ h ↦ h
    rcases ha with ha | ha | ha | ha
    · exact Or.inl ha
    · exact Or.inr (Or.inl (by addr_omega [ha, hb]))
    · exact Or.inr (Or.inr (Or.inl ha))
    · exact Or.inr (Or.inr (Or.inr (by simp only [Fresh, hn₁', hn₄] at ha ⊢; exact ha)))
  · have hf := hpost.fresh hok'
    rw [x10, x13, x14, hsz', hal'] at hf
    simp only [NewBuf, vecCap, vecPtr, hmt, hn₄, hn₁'] at hf ⊢
    exact hf

/-- **`reserve` with room enough** returns at once, writing nothing, from its first two blocks. -/
theorem reserve_fast_of {e : Word} (hA : Spec e (resA e)) (hB : Spec (e + 16) resB) :
    ReserveFastSpec e := by
  intro u hpc ⟨hval, hroom⟩
  simp only [vecLen, vecCap] at hroom
  have hb := ValidMemRange.bounds hval (by decide)
  obtain ⟨t₀, hr₀, h₀⟩ := hA.reaches hpc (by
    rv_eval []
    and_intros <;> valid_access hval [hb])
  have pc₀ := h₀.pc
  have k₀ := h₀.keeps (rs := [.x1, .x2, .x10, .x11] ++ saved) rfl
  have hm₀ (a : Word) : t₀.getMem a = u.getMem a := h₀.frame a (by simp [resA])
  rv_eval [room] at pc₀
  have hroom' : (u.getMem (u.getReg .x10) - u.getMem (u.getReg .x10 + 16)).toNat =
      (u.getMem (u.getReg .x10)).toNat - (u.getMem (u.getReg .x10 + 16)).toNat := by
    rw [BitVec.toNat_sub]; omega
  rcases eq_ite_cases pc₀ with ⟨hlt, -⟩ | ⟨-, pc₀⟩
  · simp only [BitVec.ult, decide_eq_true_eq, hroom'] at hlt
    omega
  obtain ⟨t, hr, h⟩ := hB.reaches pc₀ trivial
  have pc := h.pc
  rv_eval [k₀ .x1 (by decide)] at pc
  have k := h.keeps (rs := [.x2, .x10] ++ saved) rfl
  refine ⟨t, hr₀.trans hr, Or.inl ⟨pc.trans (returnAddress_eq u).symm, fun r hr' ↦ ?_,
    (k .x10 (by decide)).trans (k₀ .x10 (by decide)),
    fun a ↦ (h.frame a (by simp [resB])).trans (hm₀ a)⟩⟩
  rw [k r (mem_of_mem hr' _), k₀ r (mem_of_mem hr' _)]

/-! ## The copies -/

/-- `Vec<Form>::reserve`. -/
theorem reserve_80004aec (hG : GrowSpec) : ReserveFreshSpec 0x80004aec 24 8 :=
  reserve_of hG (by decide) (by decide)
    (spec_of 4795 4 (by decide +kernel) (by decide +kernel) (by decide) (by decide))
    (spec_of 4799 1 (by decide +kernel) (by decide +kernel) (by decide) (by decide))
    (spec_of 4800 8 (by decide +kernel) (by decide +kernel) (by decide) (by decide))
    (spec_of 4808 4 (by decide +kernel) (by decide +kernel) (by decide) (by decide))
    (by decide) (trap (by decide +kernel))

/-- `Vec<BusBlock>::reserve`. -/
theorem reserve_800060bc (hG : GrowSpec) : ReserveFreshSpec 0x800060bc 48 8 :=
  reserve_of hG (by decide) (by decide)
    (spec_of 6191 4 (by decide +kernel) (by decide +kernel) (by decide) (by decide))
    (spec_of 6195 1 (by decide +kernel) (by decide +kernel) (by decide) (by decide))
    (spec_of 6196 8 (by decide +kernel) (by decide +kernel) (by decide) (by decide))
    (spec_of 6204 4 (by decide +kernel) (by decide +kernel) (by decide) (by decide))
    (by decide) (trap (by decide +kernel))

/-- `Vec<E>::reserve`. -/
theorem reserve_80008a10 (hG : GrowSpec) : ReserveFreshSpec 0x80008a10 24 8 :=
  reserve_of hG (by decide) (by decide)
    (spec_of 8836 4 (by decide +kernel) (by decide +kernel) (by decide) (by decide))
    (spec_of 8840 1 (by decide +kernel) (by decide +kernel) (by decide) (by decide))
    (spec_of 8841 8 (by decide +kernel) (by decide +kernel) (by decide) (by decide))
    (spec_of 8849 4 (by decide +kernel) (by decide +kernel) (by decide) (by decide))
    (by decide) (trap (by decide +kernel))

/-- `Vec<u8>::reserve`. -/
theorem reserve_8000c898 (hG : GrowSpec) : ReserveFreshSpec 0x8000c898 1 1 :=
  reserve_of hG (by decide) (by decide)
    (spec_of 12838 4 (by decide +kernel) (by decide +kernel) (by decide) (by decide))
    (spec_of 12842 1 (by decide +kernel) (by decide +kernel) (by decide) (by decide))
    (spec_of 12843 8 (by decide +kernel) (by decide +kernel) (by decide) (by decide))
    (spec_of 12851 4 (by decide +kernel) (by decide +kernel) (by decide) (by decide))
    (by decide) (trap (by decide +kernel))

/-- `Vec<K>::reserve`. -/
theorem reserve_8000d628 (hG : GrowSpec) : ReserveFreshSpec 0x8000d628 8 8 :=
  reserve_of hG (by decide) (by decide)
    (spec_of 13706 4 (by decide +kernel) (by decide +kernel) (by decide) (by decide))
    (spec_of 13710 1 (by decide +kernel) (by decide +kernel) (by decide) (by decide))
    (spec_of 13711 8 (by decide +kernel) (by decide +kernel) (by decide) (by decide))
    (spec_of 13719 4 (by decide +kernel) (by decide +kernel) (by decide) (by decide))
    (by decide) (trap (by decide +kernel))

/-- `Vec<Option<E>>::reserve`. -/
theorem reserve_8001086c (hG : GrowSpec) : ReserveFreshSpec 0x8001086c 32 8 :=
  reserve_of hG (by decide) (by decide)
    (spec_of 16923 4 (by decide +kernel) (by decide +kernel) (by decide) (by decide))
    (spec_of 16927 1 (by decide +kernel) (by decide +kernel) (by decide) (by decide))
    (spec_of 16928 8 (by decide +kernel) (by decide +kernel) (by decide) (by decide))
    (spec_of 16936 4 (by decide +kernel) (by decide +kernel) (by decide) (by decide))
    (by decide) (trap (by decide +kernel))

theorem reserve_fast_80004aec : ReserveFastSpec 0x80004aec :=
  reserve_fast_of
    (spec_of 4795 4 (by decide +kernel) (by decide +kernel) (by decide) (by decide))
    (spec_of 4799 1 (by decide +kernel) (by decide +kernel) (by decide) (by decide))

theorem reserve_fast_800060bc : ReserveFastSpec 0x800060bc :=
  reserve_fast_of
    (spec_of 6191 4 (by decide +kernel) (by decide +kernel) (by decide) (by decide))
    (spec_of 6195 1 (by decide +kernel) (by decide +kernel) (by decide) (by decide))

theorem reserve_fast_80008a10 : ReserveFastSpec 0x80008a10 :=
  reserve_fast_of
    (spec_of 8836 4 (by decide +kernel) (by decide +kernel) (by decide) (by decide))
    (spec_of 8840 1 (by decide +kernel) (by decide +kernel) (by decide) (by decide))

theorem reserve_fast_8000c898 : ReserveFastSpec 0x8000c898 :=
  reserve_fast_of
    (spec_of 12838 4 (by decide +kernel) (by decide +kernel) (by decide) (by decide))
    (spec_of 12842 1 (by decide +kernel) (by decide +kernel) (by decide) (by decide))

theorem reserve_fast_8000d628 : ReserveFastSpec 0x8000d628 :=
  reserve_fast_of
    (spec_of 13706 4 (by decide +kernel) (by decide +kernel) (by decide) (by decide))
    (spec_of 13710 1 (by decide +kernel) (by decide +kernel) (by decide) (by decide))

theorem reserve_fast_8001086c : ReserveFastSpec 0x8001086c :=
  reserve_fast_of
    (spec_of 16923 4 (by decide +kernel) (by decide +kernel) (by decide) (by decide))
    (spec_of 16927 1 (by decide +kernel) (by decide +kernel) (by decide) (by decide))

end Rv64Verifier.Runtime.Reserve
