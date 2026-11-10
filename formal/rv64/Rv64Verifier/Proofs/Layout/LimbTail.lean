import Rv64Verifier.Proofs.Layout.LimbHead

/-!
# `flushes_keccak`'s `limb` closure: the result and the return

`finish` is the epilogue `0x80005080` once the result is at `a0`. `none` is `a` and `b` both
`None` (`0x8000504c`: `constant(ZERO)` at `sp'`, moved to `a0` by `0x80005068`); `equal` is `a == b`
(`0x80004e88`: the eager `constant(ZERO)`, then `col(a, 0)` into `a0`).
-/

namespace Rv64Verifier.Layout.Limb
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.FieldContracts
  Rv64Verifier.Blocks.F13 Rv64Verifier.Model.LayoutMirror

/-- The epilogue, the result held at `a0` with its buffer allocated since the entry. -/
theorem finish {s x y : MachineState} (hpre : LimbPre s) (c : Inv s x) {W : Word → Prop}
    (hf : DFrame x y W)
    (hW : ∀ a, W a → Within a (s.getReg .x10) 24 ∨ Within a (stackLo s 1408) 1344 ∨
      Within a nextAddr 8 ∨ Fresh x y a)
    (hheap : HeapOk y) (hmono : heapNext x ≤ heapNext y)
    (hr : ∀ r ∈ [Reg.x2, .x8, .x23, .x24, .x25, .x26, .x27], y.getReg r = x.getReg r)
    (hpc : y.pc = 0x80005080) {f : FormRust}
    (hb : Held y (s.getReg .x10) f (heapNext s) (heapNext y)) :
    ∃ t, Reaches Image.code y t ∧ t.pc = returnAddress s ∧ Preserves s t ∧
      NewForm s t (s.getReg .x10) limbStack ∧ formOf t (s.getReg .x10) = f := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have hos := hpre.outStack
  have hof := hpre.outFree
  have hob := ValidMemRange.bounds hpre.out (by decide)
  simp only [limbStack, colStack, powStack, Contracts.mulStack, Nat.reduceAdd] at hos
  have hhy := hheap.hi
  have hL : limbStack = 1408 := by simp only [limbStack, colStack, powStack, Contracts.mulStack]
  have hslot (a : Word) (ha₁ : (s.getReg .x2).toNat - 64 ≤ a.toNat)
      (ha₂ : a.toNat + 8 ≤ (s.getReg .x2).toNat) : y.getMem a = x.getMem a :=
    hf.getMem_of (fun z hz hw ↦ by
      rcases hW z hw with h | h | h | h
      · addr_omega [hz, h, hos, hsb, ha₁, ha₂]
      · addr_omega [hz, h, hsb, ha₁, ha₂]
      · addr_omega [hz, h, hsb, hnx, ha₁, ha₂]
      · simp only [Fresh] at h; addr_omega [hz, h, hsb, hab, hhy, ha₁, ha₂])
      (by addr_omega [hsb, ha₂])
  have x2 : y.getReg .x2 = s.getReg .x2 - 208 := (hr .x2 (by decide)).trans c.x2
  obtain ⟨t, hrt, h⟩ := Sym.BlockSpec.reaches b80005080_spec hpc (by
    rv_eval [x2]; and_intros <;> valid_access hpre.stack.valid [hsb])
  have k := b80005080_keeps h
  have hmt := b80005080_mem_same h
  have hn : heapNext t = heapNext y := by simp only [heapNext, hmt]
  have reg (r : Reg) (o : Nat) (hv : t.getReg r = y.getMem (y.getReg .x2 + BitVec.ofNat 64 (208 - o)))
      (ho : 8 ≤ o) (ho' : o ≤ 64) (ho8 : o % 8 = 0) (w : Word)
      (hw : x.getMem (s.getReg .x2 - BitVec.ofNat 64 o) = w) : t.getReg r = w := by
    rw [hv, x2, show s.getReg .x2 - 208 + BitVec.ofNat 64 (208 - o) = s.getReg .x2 - BitVec.ofNat 64 o by
      addr_omega [hsb, ho, ho']]
    rw [hslot _ (by addr_omega [hsb, ho, ho']) (by addr_omega [hsb, ho, ho'])]
    exact hw
  have r1 := reg .x1 8 (b80005080_x1 h) (by decide) (by decide) (by decide) _ c.ra
  have r8 := reg .x8 16 (b80005080_x8 h) (by decide) (by decide) (by decide) _ c.s0
  have r9 := reg .x9 24 (b80005080_x9 h) (by decide) (by decide) (by decide) _ c.s1
  have r18 := reg .x18 32 (b80005080_x18 h) (by decide) (by decide) (by decide) _ c.s2
  have r19 := reg .x19 40 (b80005080_x19 h) (by decide) (by decide) (by decide) _ c.s3
  have r20 := reg .x20 48 (b80005080_x20 h) (by decide) (by decide) (by decide) _ c.s4
  have r21 := reg .x21 56 (b80005080_x21 h) (by decide) (by decide) (by decide) _ c.s5
  have r22 := reg .x22 64 (b80005080_x22 h) (by decide) (by decide) (by decide) _ c.s6
  have hpct := b80005080_pc h
  rw [show y.getMem (y.getReg .x2 + (200 : Word)) = t.getReg .x1 by rw [b80005080_x1 h]] at hpct
  have r2 : t.getReg .x2 = s.getReg .x2 := by rw [b80005080_x2 h, x2]; addr_omega [hsb]
  have hcm := c.mono
  refine ⟨t, hrt, by rw [hpct, r1]; rfl, preserves_of r2 r8 r9 r18 r19 fun r hr ↦ ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact r20
    · exact r21
    · exact r22
    all_goals rw [k _ (by decide), hr _ (by decide)]; exact c.regs _ (by decide)
  · have hok := hb.ok
    have hbuf := hb.buf
    have hraw := hok.vec.raw
    exact {
      heap := ⟨hn ▸ hheap.lo, hn ▸ hheap.hi⟩
      mono := by omega
      ok := (formOf_frame (DFrame.of_same hmt fun _ ↦ False) hok (fun _ _ h ↦ h) (fun _ _ h ↦ h)
        (by addr_omega [hob]) hheap hn.ge).2
      fresh := by
        simp only [NewBuf, vecPtr, vecCap, hmt, hn]
        simp only [RawVecOk, Buf, vecPtr, vecCap] at hraw
        refine ⟨hraw.1, ?_⟩
        rcases Nat.eq_zero_or_pos (y.getMem (s.getReg .x10)).toNat with h0 | h0
        · left; omega
        · right
          have h1 := hbuf (y.getMem (s.getReg .x10 + 8)) (by
            simp only [formBuf, vecPtr, vecCap]; addr_omega [h0, hraw, hhy])
          have h2 := hbuf (y.getMem (s.getReg .x10 + 8) +
              BitVec.ofNat 64 (48 * (y.getMem (s.getReg .x10)).toNat - 1)) (by
            simp only [formBuf, vecPtr, vecCap]
            rcases hraw.2 with h3 | h3
            · omega
            · addr_omega [h0, h3, hhy])
          rcases hraw.2 with h3 | h3
          · omega
          · simp only [heapEnd] at hhy
            have := toNat_add_ofNat (x := y.getMem (s.getReg .x10 + 8))
              (n := 48 * (y.getMem (s.getReg .x10)).toNat - 1) (by omega)
            rw [this] at h2
            omega
      frame := ((c.frame.union hf).union (DFrame.of_same hmt fun _ ↦ False)).mono fun a ha ↦ by
        simp only [Scratch, Fresh] at ha ⊢
        rw [hL]
        rcases ha with ((h | h | h) | h) | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr ⟨h.1, by omega⟩))
        · rcases hW a h with h | h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl (by addr_omega [h, hsb]))
          · exact Or.inr (Or.inr (Or.inl h))
          · simp only [Fresh] at h; exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))
        · exact h.elim }
  · exact (formOf_frame (DFrame.of_same hmt fun _ ↦ False) hb.ok (fun _ _ h ↦ h) (fun _ _ h ↦ h)
      (by addr_omega [hob]) hheap hn.ge).1.trans hb.val

end Rv64Verifier.Layout.Limb
