import Rv64Verifier.Proofs.Layout.BytecodeOps

/-!
# `Flushes::bytecode` meets its contract

`counted(self, sp', sp' + 72, count, suffix)` and the epilogue, after `BytecodeHead.lean`,
`BytecodeStart.lean` and `BytecodeOps.lean`.
-/

namespace Rv64Verifier.Layout.Bytecode
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.FieldContracts
  Rv64Verifier.Blocks.F11 Rv64Verifier.Model.LayoutMirror
open Rv64Verifier.Layout.MemoryCols (Built)

theorem finish (hK : CountedSpec) {s u : MachineState} (hpre : BytecodePre s) (A : AtCounted s u)
    (hpc : u.pc = 0x80004ccc) (hr : Reaches Image.code s u) :
    ∃ t, Reaches Image.code s t ∧ ((t.pc = returnAddress s ∧ Preserves s t ∧
      (GrowFlushes s t (s.getReg .x10) bytecodeStack (fun _ ↦ False) ∧
        flushesOf t (s.getReg .x10) = (flushesOf s (s.getReg .x10)).bytecode 0
          (s.getReg .x11).toNat (s.getReg .x12).toNat (formVecOf s (s.getReg .x13)))) ∨
      Dead Image.code t) := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have hss := hpre.selfStack
  have hsf := hpre.selfFree
  have hselfb := ValidMemRange.bounds hpre.self (by decide)
  simp only [bytecodeStack, countedStack, colStack, powStack, Contracts.mulStack,
    Nat.reduceAdd] at hss
  have hheap := hpre.heap
  have hhs := hheap.hi
  have x2 := A.x2
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80004ccc_spec hpc (by
    rv_eval [x2]
    and_intros <;> valid_access hpre.stack.valid [hsb])
  have hm₁ := b80004ccc_mem_same h₁
  obtain ⟨c₁, kb₁, kv₁⟩ := A.toInv.same hpre hm₁ fun r hr ↦ b80004ccc_keeps h₁ r (mem_of_mem hr _)
  have p0 := kb₁ _ _ A.p0 (by addr_omega [hsb])
  have p1 := kb₁ _ _ A.p1 (by addr_omega [hsb])
  have cnt := kb₁ _ _ A.cnt (by addr_omega [hsb])
  have vv := kv₁ _ _ A.v (by addr_omega [hsb])
  have hm := c₁.mono
  have hh := c₁.heap.hi
  have hkeep := flushesOf_keep c₁.frame hpre.ok hheap hm hh hab hsf hss (by addr_omega [hselfb])
  have x2₁ := c₁.x2
  have x10₁ : u₁.getReg .x10 = s.getReg .x10 := by rw [b80004ccc_x10 h₁, A.x9]
  have x11₁ : u₁.getReg .x11 = s.getReg .x2 - 144 := by rw [b80004ccc_x11 h₁, x2]
  have x12₁ : u₁.getReg .x12 = s.getReg .x2 - 72 := by rw [b80004ccc_x12 h₁, x2]; rv_eval []
  have x13₁ : u₁.getReg .x13 = s.getReg .x11 := by rw [b80004ccc_x13 h₁, A.x8]
  have x14₁ : u₁.getReg .x14 = vecPtr u₁ (s.getReg .x2 - 96) := by
    rw [b80004ccc_x14 h₁, x2, vecPtr, hm₁]; rv_eval []
  have x15₁ : u₁.getReg .x15 = vecLen u₁ (s.getReg .x2 - 96) := by
    rw [b80004ccc_x15 h₁, x2, vecLen, hm₁]; rv_eval []
  have hlen : 1 ≤ (vecLen u₁ (s.getReg .x2 - 96)).toNat := by
    have := congrArg List.length vv.val
    simp only [formVecOf, formsAt, List.length_map, List.length_range, List.length_append,
      List.length_cons, List.length_nil] at this
    omega
  have hvraw := vv.ok.vec.raw
  have hvlen := vv.ok.vec.len
  simp only [RawVecOk, Buf] at hvraw
  have hvb : heapStart ≤ (vecPtr u₁ (s.getReg .x2 - 96)).toNat ∧
      (vecPtr u₁ (s.getReg .x2 - 96)).toNat + 24 * (vecLen u₁ (s.getReg .x2 - 96)).toNat ≤
        heapNext u₁ := by
    rcases hvraw.2 with h0 | h0
    · rw [Nat.mul_eq_zero] at h0; omega
    · exact ⟨h0.1, by omega⟩
  have e0 : s.getReg .x2 - 144 + BitVec.ofNat 64 (24 * 0) = s.getReg .x2 - 144 := by
    addr_omega [hsb]
  have e1 : s.getReg .x2 - 144 + BitVec.ofNat 64 (24 * 1) = s.getReg .x2 - 120 := by
    addr_omega [hsb]
  have hcp : CountedPre u₁ := {
    heap := c₁.heap
    stack := hpre.stack.inner (k := 144) x2₁ (by decide) (by decide) (by decide) (by decide)
      (by decide)
    self := by rw [x10₁]; exact hpre.self
    ok := by rw [x10₁]; exact hkeep.2.1
    selfFree := by rw [x10₁]; addr_omega [hsf, hm]
    selfStack := by rw [x10₁]; addr_omega [hss, hsb, x2₁]
    rodata := c₁.rodata
    pre := by rw [x11₁]; valid_sub hpre.stack.valid [hsb]
    preOk := by
      rw [x11₁]
      intro i hi
      match i, hi with
      | 0, _ => rw [e0]; exact p0.ok
      | 1, _ => rw [e1]; exact p1.ok
    preFree := by rw [x11₁]; addr_omega [hsb, hab, hnx]
    preStack := by rw [x11₁]; addr_omega [hsb, x2₁]
    counter := by rw [x12₁]; valid_sub hpre.stack.valid [hsb]
    counterOk := by rw [x12₁]; exact cnt.ok
    counterFree := by rw [x12₁]; addr_omega [hsb, hab, hnx]
    counterStack := by rw [x12₁]; addr_omega [hsb, x2₁]
    suf := by
      rw [x14₁, x15₁]
      exact validMemRange_of (by have := hvraw.1; omega) (Or.inl ⟨by
        simp only [heapStart] at hvb; omega, by simp only [heapEnd] at hh; omega⟩)
    sufOk := by rw [x14₁, x15₁]; exact vv.ok.forms
    sufFree := by rw [x14₁, x15₁]; addr_omega [hvb, hh]
    sufStack := by rw [x14₁, x15₁]; addr_omega [hvb, hh, hsb, hab, x2₁] }
  obtain ⟨t₆, hr₆, ⟨hpc₆, hpres₆, hgrow₆, hval₆⟩ | hdead⟩ := hK.call hr₁ (b80004ccc_pc h₁) hcp
  swap
  · exact ⟨t₆, hr.trans hr₆, Or.inr hdead⟩
  rw [x10₁, x11₁, x12₁, x13₁, x14₁, x15₁] at hval₆
  rw [x10₁] at hgrow₆
  have x2₆ : t₆.getReg .x2 = s.getReg .x2 - 144 := (hpres₆.reg .x2).trans x2₁
  obtain ⟨t₇, hr₇, h₇⟩ := Sym.BlockSpec.reaches b80004cec_spec
    (by rw [hpc₆, returnAddress_eq, b80004ccc_x1 h₁]; decide) (by
      rv_eval [x2₆]
      and_intros <;> valid_access hpre.stack.valid [hsb])
  have hm₇ := b80004cec_mem_same h₇
  have hn₆ := hgrow₆.mono
  have hh₆ := hgrow₆.heap.hi
  have hg₆ := hgrow₆.frame
  rw [hkeep.2.2.2] at hg₆
  have hbb : ∀ x, flushesBuf s (s.getReg .x10) x → x.toNat < heapNext s := fun x h ↦
    (hpre.ok.buf_below h).2
  have hsave (a : Word) (ha₁ : (s.getReg .x2).toNat - 48 ≤ a.toNat)
      (ha₂ : a.toNat + 8 ≤ (s.getReg .x2).toNat) : t₆.getMem a = u₁.getMem a := by
    refine hg₆.getMem_of (fun x hx hw ↦ ?_) (by addr_omega [hsb, ha₂])
    rcases hw with hw | hw | hw | hw | hw
    · addr_omega [hx, hw, hss, hsb, ha₁, ha₂]
    · have h1 := hbb x hw; addr_omega [hx, h1, hhs, hsb, hab, ha₁, ha₂]
    · addr_omega [hx, hw, hsb, x2₁, ha₁, ha₂]
    · addr_omega [hx, hw, hnx, hsb, ha₁, ha₂]
    · simp only [Fresh] at hw; addr_omega [hx, hw, hh₆, hab, hsb, ha₁, ha₂]
  have pc₇ := b80004cec_pc h₇
  have r₁ := b80004cec_x1 h₇
  have r₂ := b80004cec_x2 h₇
  have r₈ := b80004cec_x8 h₇
  have r₉ := b80004cec_x9 h₇
  have r₁₈ := b80004cec_x18 h₇
  have r₁₉ := b80004cec_x19 h₇
  have r₂₀ := b80004cec_x20 h₇
  have k₇ := b80004cec_keeps h₇
  rw [x2₆] at pc₇ r₁ r₂ r₈ r₉ r₁₈ r₁₉ r₂₀
  rv_eval [] at pc₇ r₁ r₂ r₈ r₉ r₁₈ r₁₉ r₂₀
  rw [hsave _ (by addr_omega [hsb]) (by addr_omega [hsb]), c₁.ra] at pc₇ r₁
  rw [hsave _ (by addr_omega [hsb]) (by addr_omega [hsb]), c₁.s0] at r₈
  rw [hsave _ (by addr_omega [hsb]) (by addr_omega [hsb]), c₁.s1] at r₉
  rw [hsave _ (by addr_omega [hsb]) (by addr_omega [hsb]), c₁.s2] at r₁₈
  rw [hsave _ (by addr_omega [hsb]) (by addr_omega [hsb]), c₁.s3] at r₁₉
  rw [hsave _ (by addr_omega [hsb]) (by addr_omega [hsb]), c₁.s4] at r₂₀
  have hn₇ : heapNext t₇ = heapNext t₆ := by simp only [heapNext, hm₇]
  have hfin := flushesOf_frame (DFrame.of_same hm₇ fun _ ↦ False) hgrow₆.ok (fun _ _ h ↦ h)
    (fun _ _ h ↦ h) (by addr_omega [hselfb]) hgrow₆.heap hn₇.ge
  have hpv : formsAt u₁ (s.getReg .x2 - 144) 2 = [constantRust sepBytecodeRust, colRust 0 0] := by
    show [formOf u₁ (s.getReg .x2 - 144 + BitVec.ofNat 64 (24 * 0)),
      formOf u₁ (s.getReg .x2 - 144 + BitVec.ofNat 64 (24 * 1))] = _
    rw [e0, e1, p0.val, p1.val]
  have hsv : formsAt u₁ (vecPtr u₁ (s.getReg .x2 - 96)) (vecLen u₁ (s.getReg .x2 - 96)).toNat =
      [constantRust (gpowRust (s.getReg .x12).toNat)] ++ formVecOf s (s.getReg .x13) := vv.val
  refine ⟨t₇, hr.trans (hr₆.trans hr₇), Or.inl ⟨pc₇.trans (returnAddress_eq s).symm,
    preserves_of r₂ r₈ r₉ r₁₈ r₁₉ fun r hr ↦ ?_, ?_, ?_⟩⟩
  · rcases List.mem_cons.mp hr with rfl | hr
    · exact r₂₀
    · rw [k₇ r (mem_of_mem hr _), hpres₆ r (mem_of_mem hr _),
        b80004ccc_keeps h₁ r (mem_of_mem hr _), A.regs r hr]
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
      frame := ((c₁.frame.union hg₆).union (DFrame.of_same hm₇ fun _ ↦ False)).mono fun x hx ↦ by
        simp only [Scratch] at hx
        rcases hx with ((hx | hx | hx) | hx | hx | hx | hx | hx) | hx
        · exact Or.inr (Or.inr (Or.inl (by addr_omega [hx, hsb])))
        · exact Or.inr (Or.inr (Or.inr (Or.inl hx)))
        · simp only [Fresh] at hx ⊢; exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hx.1, by omega⟩)))
        · exact Or.inl hx
        · exact Or.inr (Or.inl hx)
        · exact Or.inr (Or.inr (Or.inl (by addr_omega [hx, hsb, x2₁])))
        · exact Or.inr (Or.inr (Or.inr (Or.inl hx)))
        · simp only [Fresh] at hx ⊢
          exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))
        · exact hx.elim }
  · rw [hfin.1, hval₆, hkeep.1, hpv, cnt.val, hsv]
    rfl

/-- **`Flushes::bytecode` meets its contract**, given `alloc`'s, `pow`'s, `Form::term`'s,
`try_allocate_in`'s, `spec_extend`'s, `col`'s and `counted`'s. -/
theorem bytecode_spec (hA : AllocSpec) (hP : PowSpec) (hT : TermSpec) (hTA : TryAllocZeroedSpec)
    (hS : SpecExtendSpec) (hC : ColSpec) (hK : CountedSpec) : BytecodeSpec := by
  intro s hpc hpre
  obtain ⟨t, B, hr, A | hd⟩ := head hA hP hT hpc hpre
  swap
  · exact ⟨t, hr, Or.inr hd⟩
  obtain ⟨t₂, hr₂, A₂ | hd⟩ := start hTA hS hpre A hr
  swap
  · exact ⟨t₂, hr₂, Or.inr hd⟩
  obtain ⟨t₃, hr₃, ⟨hpc₃, A₃⟩ | hd⟩ := toCounted hS hT hC hpre A₂ hr₂
  swap
  · exact ⟨t₃, hr₃, Or.inr hd⟩
  exact finish hK hpre A₃ hpc₃ hr₃

end Rv64Verifier.Layout.Bytecode
