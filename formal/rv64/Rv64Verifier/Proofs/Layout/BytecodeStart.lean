import Rv64Verifier.Proofs.Layout.BytecodeHead

/-!
# `Flushes::bytecode`: the suffix's `Vec` with the opcode's form

`try_allocate_in(sp', len + 1, 0, 8, 24)`, the error trap, the `Vec` at `sp' + 48` and the first
`spec_extend`, from `B`.
-/

namespace Rv64Verifier.Layout.Bytecode
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.FieldContracts
  Rv64Verifier.Blocks.F11 Rv64Verifier.Model.LayoutMirror
open Rv64Verifier.Layout.MemoryCols (Built)

/-- At the second `spec_extend`: the opcode's form in the suffix's `Vec`. -/
structure AtOps (s t : MachineState) : Prop extends Inv s t where
  pc : t.pc = 0x80004c68
  x19 : t.getReg .x19 = vecPtr s (s.getReg .x13)
  x20 : t.getReg .x20 = vecLen s (s.getReg .x13)
  v : VBuilt s t (s.getReg .x2 - 96) [constantRust (gpowRust (s.getReg .x12).toNat)]

theorem start (hTA : TryAllocZeroedSpec) (hS : SpecExtendSpec) {s u0 u : MachineState} {B : Word}
    (hpre : BytecodePre s) (A : AtTry s u B) (hr : Reaches Image.code u0 u) :
    ∃ t, Reaches Image.code u0 t ∧ (AtOps s t ∨ Dead Image.code t) := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have hob := ValidMemRange.bounds hpre.ops (by decide)
  have hlo₀ := hpre.heap.lo
  have hAm := A.mono
  have hAhi := A.heap.hi
  have hBlo := A.lo
  have hBhi := A.hi
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80004c14_spec A.pc (by
    rv_eval [A.x19]
    and_intros <;> valid_access hpre.ops [hob])
  have hm₁ := b80004c14_mem_same h₁
  have k₁ := b80004c14_keeps h₁
  obtain ⟨c₁, kb₁, -⟩ := A.toInv.same hpre hm₁ fun r hr ↦ k₁ r (mem_of_mem hr _)
  have b₁ := kb₁ _ _ A.b (by omega)
  have hn₁ : heapNext t₁ = heapNext u := by simp only [heapNext, hm₁]
  have hptr : u.getMem (s.getReg .x13 + 8) = vecPtr s (s.getReg .x13) := A.ops hpre (k := 8) (by decide)
  have hlen : u.getMem (s.getReg .x13 + 16) = vecLen s (s.getReg .x13) :=
    A.ops hpre (k := 16) (by decide)
  have x10₁ : t₁.getReg .x10 = s.getReg .x2 - 144 := by rw [b80004c14_x10 h₁, A.x2]
  have x11₁ : t₁.getReg .x11 = vecLen s (s.getReg .x13) + 1 := by
    rw [b80004c14_x11 h₁, A.x19, hlen]
  have x2₁ := c₁.x2
  have hta : TryAllocPre .x13 .x14 t₁ := {
    heap := c₁.heap
    out := by rw [x10₁]; valid_sub hpre.stack.valid [hsb]
    align := by rw [b80004c14_x13 h₁]; decide
    size := by rw [b80004c14_x14 h₁]; decide
    stack := hpre.stack.inner (k := 144) x2₁ (by decide) (by decide) (by decide) (by decide)
      (by decide)
    outFree := by rw [x10₁]; addr_omega [hsb, hab, hnx]
    outStack := by rw [x10₁]; addr_omega [hsb, x2₁] }
  obtain ⟨w, hr₂, ⟨hpc₂, hpres₂, hpost, -⟩ | hdead⟩ := hTA.call hr₁ (b80004c14_pc h₁) hta
  swap
  · exact ⟨w, hr.trans hr₂, Or.inr hdead⟩
  have hwf := hpost.frame.dframe
  rw [x10₁, show stackLo t₁ tryAllocStack = s.getReg .x2 - 192 by
    simp only [stackLo, x2₁, tryAllocStack]; rv_eval []] at hwf
  have hm₂ := hpost.mono
  have hW : ∀ x, (Within x (s.getReg .x2 - 144) 24 ∨ Within x (s.getReg .x2 - 192) 48 ∨
      Within x nextAddr 8 ∨ Fresh t₁ w x) → heapEnd ≤ x.toNat ∨ heapNext t₁ ≤ x.toNat :=
    fun x h ↦ by
      rcases h with h | h | h | h
      · exact Or.inl (by addr_omega [h, hsb, hab])
      · exact Or.inl (by addr_omega [h, hsb, hab])
      · exact Or.inl (by addr_omega [h])
      · exact Or.inr h.1
  have c₂ := c₁.step hpre hwf (fun x h ↦ by
      rcases h with h | h | h | h
      · exact Or.inl (by addr_omega [h, hsb])
      · exact Or.inl (by addr_omega [h, hsb])
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨by simp only [Fresh] at h; omega, h.2⟩))
    hpost.heap hm₂ (keepRegs_of hpres₂)
  have hBh : B.toNat + 24 ≤ heapNext t₁ := by omega
  have heB : ∀ x, Within x B 24 → ¬ (Within x (s.getReg .x2 - 144) 24 ∨
      Within x (s.getReg .x2 - 192) 48 ∨ Within x nextAddr 8 ∨ Fresh t₁ w x) := fun x hx h ↦ by
    rcases h with h | h | h | h
    · addr_omega [hx, h, hsb, hab, hBh, hAhi, hn₁]
    · addr_omega [hx, h, hsb, hab, hBh, hAhi, hn₁]
    · addr_omega [hx, h, hBh, hAhi, hn₁]
    · simp only [Fresh] at h; addr_omega [hx, h, hBh]
  have hBw : B.toNat + 24 ≤ 2 ^ 64 := by addr_omega [hBh, hAhi, hn₁]
  have b₂ := b₁.step hwf c₁.heap hm₂ hW heB hBw
  have fb₂ := formBuf_frame hwf heB hBw
  -- the error check
  have x2₂ : w.getReg .x2 = s.getReg .x2 - 144 := c₂.x2
  obtain ⟨w₂, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80004c38_spec
    (by rw [hpc₂, returnAddress_eq, b80004c14_x1 h₁]; decide) (by
      rv_eval [x2₂]
      valid_access hpre.stack.valid [hsb])
  by_cases htag : w.getMem (s.getReg .x2 - 144) = 0
  swap
  · exact ⟨w₂, hr.trans (hr₂.trans hr₃), Or.inr (dead_of_fetch (by
      rw [b80004c38_pc_taken h₃ (by rw [x2₂]; exact htag)]; exact trap))⟩
  have hok := hpost.ok
  rw [x10₁] at hok
  obtain ⟨hcap₂, hnew₂⟩ := hok htag
  rw [x11₁, b80004c14_x14 h₁, b80004c14_x13 h₁, show (24 : Word).toNat = 24 from rfl,
    show (8 : Word).toNat = 8 from rfl] at hnew₂
  rw [x11₁] at hcap₂
  have hm₃ := b80004c38_mem_same h₃
  have k₃ := b80004c38_keeps h₃
  obtain ⟨c₃, kb₃, -⟩ := c₂.same hpre hm₃ fun r hr ↦ k₃ r (mem_of_mem hr _)
  have b₃ := kb₃ _ _ b₂ hBw
  have fb₃ := formBuf_frame (DFrame.of_same hm₃ fun _ ↦ False) (e := B) (fun _ _ h ↦ h) hBw
  -- the `Vec` at `sp' + 48`, and `spec_extend` from `B`
  have x2₃ := c₃.x2
  obtain ⟨e, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80004c40_spec
    (b80004c38_pc_not_taken h₃ (by rw [x2₂]; exact htag)) (by
      rv_eval [x2₃]
      and_intros <;> valid_access hpre.stack.valid [hsb])
  have hm₄ := b80004c40_frame h₄ (by addr_omega [hsb, x2₃])
  rw [x2₃] at hm₄
  have k₄ := b80004c40_keeps h₄
  obtain ⟨c₄, kb₄, -, hn₄⟩ := c₃.block hpre hm₄ (by addr_omega [hsb]) (by addr_omega [hsb])
    fun r hr ↦ k₄ r (mem_of_mem hr _)
  have b₄ := kb₄ _ _ b₃ (by addr_omega [hBh, hAhi, hn₁, hsb, hab]) hBw
  have fb₄ := formBuf_frame hm₄.dframe (e := B) (fun x hx h ↦ by
    addr_omega [hx, h, hBh, hAhi, hn₁, hsb, hab]) hBw
  obtain ⟨P, hP⟩ : ∃ P, P = w.getMem (s.getReg .x2 - 144 + 16) := ⟨_, rfl⟩
  rw [← hP] at hnew₂
  have hcap0 : vecCap e (s.getReg .x2 - 96) = vecLen s (s.getReg .x13) + 1 := by
    have := b80004c40_m_x2_48 h₄; rw [x2₃] at this; rv_eval [] at this
    simp only [vecCap]; rw [this, hm₃]
    rw [show s.getReg .x2 - 136 = s.getReg .x2 - 144 + 8 by rv_eval []]; exact hcap₂
  have hptr0 : vecPtr e (s.getReg .x2 - 96) = P := by
    have := b80004c40_m_x2_56 h₄; rw [x2₃] at this; rv_eval [] at this
    simp only [vecPtr]; rw [show s.getReg .x2 - 96 + 8 = s.getReg .x2 - 88 by rv_eval [], this, hm₃,
      hP, show s.getReg .x2 - 144 + 16 = s.getReg .x2 - 128 by rv_eval []]
  have hlen0 : vecLen e (s.getReg .x2 - 96) = 0 := by
    have := b80004c40_m_x2_64 h₄; rw [x2₃] at this; rv_eval [] at this
    simp only [vecLen]; rw [show s.getReg .x2 - 96 + 16 = s.getReg .x2 - 80 by rv_eval []]; exact this
  have hnb := hnew₂
  simp only [NewBuf] at hnb
  have hn₃ : heapNext w₂ = heapNext w := by simp only [heapNext, hm₃]
  have heh := c₄.heap.hi
  have v₀ : VBuilt s e (s.getReg .x2 - 96) [] := {
    ok := ⟨⟨by
        simp only [RawVecOk, Buf, hptr0, hcap0, hn₄, hn₃]
        refine ⟨hnb.1, hnb.2.imp id fun h' ↦ ⟨?_, h'.2⟩⟩
        simp only [heapStart] at hlo₀ ⊢; omega,
      by rw [hlen0]; simp⟩, fun i hi ↦ by rw [hlen0] at hi; simp at hi,
      fun x ⟨i, hi, _⟩ ↦ by rw [hlen0] at hi; simp at hi⟩
    val := by simp only [formVecOf, formsAt, hlen0]; rfl
    deep := fun x hx ↦ by
      rcases hx with hx | ⟨i, hi, _⟩
      · simp only [formVecBuf, hptr0, hcap0, Within] at hx
        rw [hn₄, hn₃]
        rcases hnb.2 with h0 | h0
        · rw [Nat.mul_eq_zero] at h0; omega
        · omega
      · rw [hlen0] at hi; simp at hi }
  have x18₄ : e.getReg .x11 = B := by
    rw [b80004c40_x11 h₄, k₃ .x18 (by decide), hpres₂.reg .x18, k₁ .x18 (by decide), A.x18]
  have heb := ValidMemRange.bounds hpre.self (by decide)
  obtain ⟨v, hr₅, ⟨hpc₅, hpres₅, c₅, v₅⟩ | hdead⟩ := extendCall hS hpre c₄ (hr.trans (hr₂.trans (hr₃.trans hr₄)))
    (b80004c40_pc h₄) v₀ (p := B) (n := 1)
    (by rw [b80004c40_x10 h₄, x2₃]; rv_eval []) x18₄
    (by rw [b80004c40_x12 h₄, k₃ .x18 (by decide), hpres₂.reg .x18, k₁ .x18 (by decide), A.x18]; rfl)
    (validMemRange_of A.al (Or.inl ⟨by simp only [heapStart] at hlo₀; omega,
      by simp only [heapEnd] at heh; omega⟩))
    (fun i hi ↦ by
      rcases i with _ | i
      · simpa using b₄.ok
      · omega)
    (by addr_omega [hBh, hAhi, hn₁, heh, hn₄, hn₃, hm₂])
    (by addr_omega [hBh, hAhi, hn₁, hsb, hab])
    (fun x hx h ↦ by
      simp only [formVecBuf, hptr0, hcap0, Within] at h
      rcases hnb.2 with h0 | h0
      · rw [Nat.mul_eq_zero] at h0; omega
      · rcases hx with hx | ⟨i, hi, hx⟩
        · addr_omega [hx, h, h0, hBh]
        · rcases i with _ | i
          · have hx' : formBuf t₁ B x := by
              rw [← fb₂, ← fb₃, ← fb₄]; simpa using hx
            have := b₁.buf x hx'
            omega
          · omega)
    (by addr_omega [hBh, hAhi, hn₁])
  swap
  · exact ⟨v, hr₅, Or.inr hdead⟩
  refine ⟨v, hr₅, Or.inl {
    toInv := c₅
    pc := by rw [hpc₅, returnAddress_eq, b80004c40_x1 h₄]; decide
    x19 := by
      rw [hpres₅.reg .x19, k₄ .x19 (by decide), k₃ .x19 (by decide), hpres₂.reg .x19,
        b80004c14_x19 h₁, A.x19, hptr]
    x20 := by
      rw [hpres₅.reg .x20, k₄ .x20 (by decide), k₃ .x20 (by decide), hpres₂.reg .x20,
        b80004c14_x20 h₁, A.x19, hlen]
    v := by
      have hf : formsAt e B 1 = [formOf e B] := by simp [formsAt]
      rw [hf, b₄.val] at v₅
      exact v₅ }⟩

end Rv64Verifier.Layout.Bytecode
