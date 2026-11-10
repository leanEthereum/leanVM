import Rv64Verifier.Proofs.Transcript.SumcheckPush

/-!
# `transcript::sumcheck`'s setup

The frame, `try_allocate_in(n)` (a trap on its error), the `Vec` at `S - 200`, then the loop head
with no round done, or the exit when there is no equality.
-/

namespace Rv64Verifier.Transcript.Sumcheck
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F76
  Rv64Verifier.Contracts
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

theorem pre_zero (s : MachineState) (T : TState) :
    (pre s 0).run T = some (([], eAt s (s.getReg .x12)), T) := by
  simp only [pre, List.take_zero, List.foldlM_nil]
  rfl

set_option maxHeartbeats 4000000 in
/-- The frame, `try_allocate_in(n)`, the `Vec`. -/
theorem setup (hT : TryAllocZeroedSpec) {s : MachineState} (hpc : s.pc = 0x80010538)
    (hpre : SumcheckPre s) :
    ∃ v, Reaches Image.code s v ∧ (Dead Image.code v ∨ ∃ ptr,
      (v.pc = 0x8001062c ∧ Inv s v ptr 0) ∨ (v.pc = 0x80010698 ∧ Exit s v ptr)) := by
  have hb := bounds hpre
  have hS : 208 ≤ (s.getReg .x2).toNat := by addr_omega [hb]
  have hst := hpre.stack
  have hnxt := hst.next
  have hab := hst.above
  have hlo := hpre.heap.lo
  have hhi := hpre.heap.hi
  have hcl := hpre.claim
  have hnl := n_lt hpre
  obtain ⟨c, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80010538_spec hpc (by
    rv_eval []
    and_intros <;> valid_access hst.valid [hb])
  have k₁ := b80010538_keeps h₁
  have x2₁ := b80010538_x2 h₁
  have x10₁ : c.getReg .x10 = s.getReg .x2 - 128 := b80010538_x10 h₁
  have x11₁ := b80010538_x11 h₁
  have x13₁ := b80010538_x13 h₁
  have x14₁ := b80010538_x14 h₁
  have f₁ := b80010538_frame h₁ (by addr_omega [hb])
  have nx₁ : c.getMem nextAddr = s.getMem nextAddr := f₁ _ (by addr_omega [hnxt, hb])
  have hheap₁ : HeapOk c := ⟨by simp only [heapNext, nx₁]; exact hlo,
    by simp only [heapNext, nx₁]; exact hhi⟩
  have hta : TryAllocPre .x13 .x14 c := {
    heap := hheap₁
    out := by rw [x10₁]; valid_sub hst.valid [hb]
    align := by rw [x13₁]; decide
    size := by rw [x14₁]; decide
    stack := hst.sub 208 x2₁ (by decide) (by decide) (by decide) (by decide) (by decide)
    outFree := by
      rw [x10₁]; simp only [Outside, heapNext, nx₁]
      exact ⟨Or.inr (by addr_omega [hab, hb]), by addr_omega [hnxt, hb]⟩
    outStack := by rw [x10₁]; simp only [stackLo, x2₁]; addr_omega [hb] }
  obtain ⟨t₀, hr₂, ⟨hpc₂, hpres₂, hpost₂, -⟩ | hd⟩ := hT.call hr₁ (b80010538_pc h₁) hta
  swap
  · exact ⟨_, hr₂, Or.inl hd⟩
  have G₂ := DFrame.of_byteFrame hpost₂.frame
  rw [x10₁] at G₂
  simp only [stackLo, x2₁] at G₂
  have k2 (r : Reg) (hr : r ∈ calleeSaved) : t₀.getReg r = c.getReg r := hpres₂ r hr
  have x2₂ : t₀.getReg .x2 = s.getReg .x2 - 208 := (k2 .x2 (by decide)).trans x2₁
  obtain ⟨t₁, hr₃, h₃⟩ := Sym.BlockSpec.reaches b800105a4_spec
    (by rw [hpc₂, returnAddress_eq, b80010538_x1 h₁]; decide) (by
      rv_eval [x2₂]
      valid_access hst.valid [hb])
  have e80 : s.getReg .x2 - 208 + 80 = s.getReg .x2 - 128 := by ring
  by_cases herr : t₀.getMem (s.getReg .x2 - 128) = 0
  swap
  · refine ⟨t₁, hr₂.trans hr₃, Or.inl (dead_of_fetch ?_)⟩
    rw [b800105a4_pc_taken h₃ (by rw [x2₂, e80]; exact herr)]
    exact Option.isNone_iff_eq_none.mp (by decide +kernel)
  obtain ⟨hcap₂, hnew₂⟩ := hpost₂.ok (by rw [x10₁]; exact herr)
  rw [x10₁, x11₁] at hcap₂ hnew₂
  rw [x14₁, x13₁, show (24 : Word).toNat = 24 from rfl, show (8 : Word).toNat = 8 from rfl] at hnew₂
  have k₃ := b800105a4_keeps h₃
  have hm₃ := b800105a4_mem_same h₃
  have x2₃ : t₁.getReg .x2 = s.getReg .x2 - 208 := (k₃ .x2 (by decide)).trans x2₂
  obtain ⟨t₂, hr₄, h₄⟩ := Sym.BlockSpec.reaches b800105ac_spec
    (b800105a4_pc_not_taken h₃ (by rw [x2₂, e80]; exact herr)) (by
      rv_eval [x2₃]
      and_intros <;> valid_access hst.valid [hb])
  have k₄ := b800105ac_keeps h₄
  have m0 := b800105ac_m_x2_0 h₄
  have m8 := b800105ac_m_x2_8 h₄
  have m16 := b800105ac_m_x2_16 h₄
  have m24 := b800105ac_m_x2_24 h₄
  have x24₄ := b800105ac_x24 h₄
  have f₄ := b800105ac_frame h₄ (by rw [x2₃]; addr_omega [hb])
  rw [x2₃] at m0 m8 m16 m24 x24₄ f₄
  rw [show s.getReg .x2 - 208 + 8 = s.getReg .x2 - 200 by ring, hm₃,
    show s.getReg .x2 - 208 + 88 = s.getReg .x2 - 128 + 8 by ring, hcap₂] at m8
  rw [show s.getReg .x2 - 208 + 16 = s.getReg .x2 - 192 by ring, hm₃,
    show s.getReg .x2 - 208 + 96 = s.getReg .x2 - 128 + 16 by ring] at m16
  rw [show s.getReg .x2 - 208 + 24 = s.getReg .x2 - 184 by ring] at m24
  rw [hm₃, show s.getReg .x2 - 208 + 96 = s.getReg .x2 - 128 + 16 by ring] at x24₄
  rw [k₃ .x8 (by decide), k2 .x8 (by decide), b80010538_x8 h₁] at m0
  -- the frames
  have nxc : heapNext c = heapNext s := by simp only [heapNext, nx₁]
  have nx₄ : heapNext t₂ = heapNext t₀ := by
    simp only [heapNext]; rw [f₄ _ (by addr_omega [hnxt, hb]), hm₃]
  have hhi₀ := hpost₂.heap.hi
  have hmono₀ := hpost₂.mono
  have Gs : DFrame s t₂ fun a ↦ Within a (stackLo s sumcheckStack) sumcheckStack ∨
      Within a nextAddr 8 ∨ (heapNext s ≤ a.toNat ∧ a.toNat < heapNext t₂) := by
    refine ((((DFrame.of_memFrame f₁).mono fun a ha ↦ Or.inl (by addr_omega [ha, hb])).trans G₂ ?_).trans
      (DFrame.of_same hm₃ _) fun _ h ↦ h).trans (DFrame.of_memFrame f₄) ?_
    · intro a ha
      rcases ha with ha | ha | ha | ha
      · exact Or.inl (by addr_omega [ha, hb])
      · exact Or.inl (by addr_omega [ha, hb])
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr ⟨by simp only [Fresh] at ha; omega, by
          simp only [Fresh] at ha; rw [nx₄]; omega⟩)
    · intro a ha
      exact Or.inl (by addr_omega [ha, hb])
  have hSelf := hpre.self.self
  have S₁ : Saved s c := ⟨x2₁, b80010538_m_x2_n8 h₁, b80010538_m_x2_n16 h₁, b80010538_m_x2_n24 h₁,
    b80010538_m_x2_n32 h₁, b80010538_m_x2_n40 h₁, b80010538_m_x2_n48 h₁, b80010538_m_x2_n56 h₁,
    b80010538_m_x2_n64 h₁, b80010538_m_x2_n72 h₁, b80010538_m_x2_n80 h₁, b80010538_m_x2_n88 h₁,
    b80010538_m_x2_n96 h₁, b80010538_m_x2_n104 h₁⟩
  have F : Fr s t₂ := {
    saved := S₁.step (by omega) ((k₄ .x2 (by decide)).trans (x2₃.trans x2₁.symm)) fun y h1 h2 ↦ by
      rw [f₄ y (by addr_omega [h1, h2, hb]), hm₃, G₂ y fun j hj hw ↦ by
        rcases hw with hw | hw | hw | hw <;> addr_omega [hw, hj, h1, h2, hb, hnxt, hab, hhi₀]]
    heap := ⟨nx₄ ▸ hpost₂.heap.lo, nx₄ ▸ hhi₀⟩
    mono := by rw [nx₄, ← nxc]; exact hmono₀
    frame := Gs.mono fun a ha ↦ by
      rcases ha with ha | ha | ha
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ha))) }
  have rk (r : Reg) (hr : r ∈ calleeSaved) (h3 : r ∈ [Reg.x8, .x9, .x18, .x19, .x20, .x21]) :
      t₂.getReg r = c.getReg r := by
    rw [k₄ r (mem_of_mem h3 _), k₃ r (mem_of_mem h3 _), k2 r hr]
  have x21₃ : t₁.getReg .x21 = s.getReg .x15 := by
    rw [k₃ .x21 (by decide), k2 .x21 (by decide), b80010538_x21 h₁]
  have ck : eAt t₂ (s.getReg .x12) = eAt s (s.getReg .x12) := Gs.eAt fun j hj hw ↦ by
    rcases hw with hw | hw | hw <;>
      addr_omega [hw, hj, hcl, hpre.claimStack, hpre.claimFree, hb, F.heap.hi]
  have tv (T : TState) (hT : TranscriptAt s (s.getReg .x11) T) : TranscriptAt t₂ (s.getReg .x11) T :=
    Low.transcriptAt hpre (hi := heapNext t₂) (by rw [nx₄]; exact hhi₀) hhi (DFrame.refl s _)
      (Gs.mono fun a ha ↦ by
        rcases ha with ha | ha | ha
        · exact Or.inr (Or.inl ha)
        · exact Or.inr (Or.inr (Or.inl ha))
        · exact Or.inr (Or.inr (Or.inr ha))) hT
  have buf : NewBuf s t₂ (t₀.getMem (s.getReg .x2 - 128 + 16)) ((s.getReg .x15).toNat * 24) 8 := by
    simp only [NewBuf, nx₄, ← nxc] at hnew₂ ⊢; exact hnew₂
  have x9₂ : t₂.getReg .x9 = s.getReg .x12 := by
    rw [rk .x9 (by decide) (by decide), b80010538_x9 h₁]
  by_cases hn0 : s.getReg .x15 = 0
  · have hn0' : (s.getReg .x15).toNat = 0 := by rw [hn0]; rfl
    refine ⟨t₂, hr₂.trans (hr₃.trans hr₄), Or.inr ⟨_, Or.inr ⟨b800105ac_pc_taken h₄ (by rw [x21₃, hn0]),
      F, x9₂, m0, m8, m16, by rw [m24, hn0], buf, fun T hT ↦ ⟨T, ?_, tv T hT⟩⟩⟩⟩
    rw [hn0', pre_zero, ck]
    rfl
  obtain ⟨t₃, hr₅, h₅⟩ := Sym.BlockSpec.reaches b800105c8_spec
    (b800105ac_pc_not_taken h₄ (by rw [x21₃]; exact hn0)) trivial
  have k₅ := b800105c8_keeps h₅
  have hm₅ := b800105c8_mem_same h₅
  have hn0' : 0 < (s.getReg .x15).toNat := by
    rcases Nat.eq_zero_or_pos (s.getReg .x15).toNat with h0 | h0
    · exact absurd (BitVec.eq_of_toNat_eq (by rw [h0]; rfl)) hn0
    · exact h0
  have keep5 (y : Word) : t₃.getMem y = t₂.getMem y := hm₅ y
  refine ⟨t₃, hr₂.trans (hr₃.trans (hr₄.trans hr₅)), Or.inr ⟨_, Or.inl ⟨b800105c8_pc h₅, ⟨⟨
    F.same (by omega) (k₅ .x2 (by decide)) hm₅, b800105c8_x8 h₅, ?_, ?_, ?_, ?_, ?_, ?_, b800105c8_x25 h₅,
    b800105c8_x26 h₅, ?_, by rw [keep5, m0], by rw [keep5, m8], by rw [keep5, m16],
    by rw [keep5, m24]; rfl, ?_, hn0'⟩, fun T hT ↦ ⟨T, ?_, (tv T hT).congr hm₅⟩⟩⟩⟩⟩
  · rw [k₅ .x9 (by decide), x9₂]
  · rw [k₅ .x18 (by decide), rk .x18 (by decide) (by decide), b80010538_x18 h₁]; simp
  · rw [k₅ .x19 (by decide), rk .x19 (by decide) (by decide), b80010538_x19 h₁]
  · rw [k₅ .x20 (by decide), rk .x20 (by decide) (by decide), b80010538_x20 h₁]
  · rw [b800105c8_x21 h₅, rk .x20 (by decide) (by decide), b80010538_x20 h₁]
  · rw [k₅ .x24 (by decide), x24₄]
  · rw [b800105c8_x27 h₅, rk .x21 (by decide) (by decide), b80010538_x21 h₁]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, show (32 : Word).toNat = 32 from rfl, Nat.sub_zero]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  · simp only [NewBuf] at buf ⊢
    rw [show heapNext t₃ = heapNext t₂ by simp only [heapNext, hm₅]]
    exact buf
  · rw [pre_zero, (DFrame.of_same hm₅ fun _ ↦ False).eAt fun _ _ h ↦ h, ck]
    rfl

end Rv64Verifier.Transcript.Sumcheck
