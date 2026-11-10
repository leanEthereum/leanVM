import Rv64Verifier.Proofs.Transcript.RoundPolySomeSum
import Rv64Verifier.Proofs.Transcript.RoundPolyFinish

/-!
# `sumcheck_round_poly`'s `Some` path: the head

`0x8000c428`: the sum to `S - 152`, `eq_factor` times it into `S - 104` (`mul`), plus the claim
into the new buffer, the two `Vec`s to `S - 152` (`Ready`, with one element).
-/

namespace Rv64Verifier.Transcript.RoundPoly
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F44
  Rv64Verifier.Contracts LeanVM.Protocol.Verifier
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

theorem Region.vmr {a x : Word} {n m : Nat} (h : Region a n) (h1 : a.toNat ≤ x.toNat)
    (h2 : x.toNat + 8 * m ≤ a.toNat + n) (h3 : x.toNat % 8 = 0) : ValidMemRange x m := by
  intro i hi
  have hR := h
  simp only [Region, Mapped] at hR
  exact h.valid (by addr_omega [h1, h2, hi, hR]) (by addr_omega [h1, h2, hi, hR])
    (by addr_omega [h3, h2, hi, hR])

theorem ofNat_toNat_self (x : Word) : BitVec.ofNat 64 x.toNat = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt]

set_option maxHeartbeats 2000000 in
theorem someMul (hM : MulSpec) {s w : MachineState} (hpre : RoundPolyPre s)
    (htag : s.getMem (s.getReg .x14) ≠ 0) (hpc : w.pc = 0x8000c428) (h : AtMul s w) :
    ∃ u, Reaches Image.code w u ∧ ((u.pc = 0x8000c5b4 ∧ Ready s u (w.getReg .x9) 1
      (w.getReg .x22) (w.getReg .x21) (w.getReg .x20).toNat) ∨ Done s u) := by
  have hb := bounds hpre
  have hS : 80 ≤ (s.getReg .x2).toNat := by addr_omega [hb]
  have hst := hpre.stack
  have hro := hst.rodata
  have hef := hpre.eqFactor
  have hSelf := hpre.self.self
  have x2 := h.fr.saved.x2
  obtain ⟨w₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000c428_spec hpc (by
    rv_eval [x2]
    and_intros <;> valid_access hpre.stack.valid [hb])
  have k₁ := b8000c428_keeps h₁
  have f₁ := b8000c428_frame h₁ (by rw [x2]; addr_omega [hb])
  rw [x2, show s.getReg .x2 - 160 + 8 = s.getReg .x2 - 152 by ring] at f₁
  have m8 := b8000c428_m_x2_8 h₁
  have m16 := b8000c428_m_x2_16 h₁
  have m24 := b8000c428_m_x2_24 h₁
  rw [x2, show s.getReg .x2 - 160 + 8 = s.getReg .x2 - 152 by ring] at m8
  rw [x2, show s.getReg .x2 - 160 + 16 = s.getReg .x2 - 152 + 8 by ring] at m16
  rw [x2, show s.getReg .x2 - 160 + 24 = s.getReg .x2 - 152 + 16 by ring] at m24
  have x2₁ : w₁.getReg .x2 = s.getReg .x2 - 160 := (k₁ .x2 (by decide)).trans x2
  have x10₁ : w₁.getReg .x10 = s.getReg .x2 - 104 := by
    rw [b8000c428_x10 h₁, x2]; ring
  have x11₁ : w₁.getReg .x11 = s.getReg .x14 + 8 := (k₁ .x11 (by decide)).trans h.x11
  have x12₁ : w₁.getReg .x12 = s.getReg .x2 - 152 := by
    rw [b8000c428_x12 h₁, x2]; ring
  have Fw₁ : DFrame s w₁ (V s w₁) :=
    (h.fr.frame.mono fun a h ↦ V.mono (by simp only [heapNext]; rw [f₁ _ (by
      addr_omega [hb, hst.next])]) h).trans (DFrame.of_memFrame f₁) fun a ha ↦
      Or.inr (Or.inl (by addr_omega [ha, hb]))
  have nx₁ : heapNext w₁ = heapNext w := by
    simp only [heapNext]; rw [f₁ _ (by addr_omega [hb, hst.next])]
  have hhi₁ : heapNext w₁ ≤ heapEnd := nx₁ ▸ h.fr.heap.hi
  have hmp : MulPre w₁ := {
    out := by rw [x10₁]; valid_sub hpre.stack.valid [hb]
    lhs := by
      rw [x11₁]
      refine Region.vmr (x := s.getReg .x14 + 8) (m := 3) hef ?_ ?_ ?_ <;> addr_omega [hef]
    rhs := by rw [x12₁]; valid_sub hpre.stack.valid [hb]
    stack := ⟨by valid_sub hpre.stack.valid [hb, x2₁], by rw [x2₁]; addr_omega [hb]⟩
    outLhs := by rw [x10₁, x11₁]; addr_omega [hb, hef, hpre.eqFactorStack]
    outRhs := by rw [x10₁, x12₁]; addr_omega [hb]
    outStack := by rw [x10₁]; simp only [stackLo, x2₁]; addr_omega [hb]
    lhsStack := by rw [x11₁]; simp only [stackLo, x2₁]; addr_omega [hb, hef, hpre.eqFactorStack]
    rhsStack := by rw [x12₁]; simp only [stackLo, x2₁]; addr_omega [hb]
    rodata := hpre.rodata.dframe Fw₁ fun a ha hw ↦ by
      rcases hw with hw | hw | hw | hw <;>
        addr_omega [ha, hw, hro, hb, hpre.selfRodata, hSelf, hhi₁]
    stackRodata := by simp only [stackLo, x2₁]; addr_omega [hb, hro] }
  obtain ⟨t₂, hr₂, ⟨hpc₂, hpres₂, hpost₂⟩ | hd⟩ := hM.call hr₁ (b8000c428_pc h₁) hmp
  swap
  · exact ⟨t₂, hr₂, Or.inr (Or.inr hd)⟩
  have val := hpost₂.value
  rw [x10₁, x11₁, x12₁] at val
  have G₂ := DFrame.of_two hpost₂.frame
  rw [x10₁] at G₂
  simp only [stackLo, x2₁] at G₂
  have x2₂ : t₂.getReg .x2 = s.getReg .x2 - 160 := (hpres₂.reg .x2).trans x2₁
  have x9₂ : t₂.getReg .x9 = w.getReg .x9 := by rw [hpres₂.reg .x9, k₁ .x9 (by decide)]
  have hB := h.bAl
  have hBn := h.bNext
  have hBlo := h.bLo
  have hBhi : (w.getReg .x9).toNat + 24 ≤ heapEnd := hBn ▸ h.fr.heap.hi
  have hlo := hpre.heap.lo
  obtain ⟨u, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000c444_spec
    (by rw [hpc₂, returnAddress_eq, b8000c428_x1 h₁]; decide) (by
      rv_eval [x2₂, x9₂]
      and_intros <;> first
        | addr_omega [hb, hB, hBlo, hBhi, hlo]
        | valid_access hpre.stack.valid [hb]
        | (refine Samples.heap_valid ?_ ?_ ?_ <;> addr_omega [hB, hBlo, hBhi, hlo, h.fr.mono]))
  have fr₃ (a : Word) (h1 : ¬ Within a (s.getReg .x2 - 152) 48)
      (h2 : ¬ Within a (w.getReg .x9) 24) : u.getMem a = t₂.getMem a :=
    h₃.frame a (by
      rv_eval [x2₂, x9₂]
      and_intros <;> addr_omega [h1, h2, hb, hBhi])
  have G₃ := DFrame.of_two fr₃
  -- what the head reads
  have k₃ := b8000c444_keeps h₃
  have hu (r : Reg) (hr : r ∈ [Reg.x18, .x20, .x21, .x22, .x23, .x24]) : t₂.getReg r = w.getReg r := by
    rw [hpres₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
  have x2₃ : u.getReg .x2 = w.getReg .x2 := by
    rw [k₃ .x2 (by decide), hpres₂.reg .x2, k₁ .x2 (by decide)]
  have n8 := b8000c444_m_x2_8 h₃
  have n16 := b8000c444_m_x2_16 h₃
  have n24 := b8000c444_m_x2_24 h₃
  have n32 := b8000c444_m_x2_32 h₃
  have n40 := b8000c444_m_x2_40 h₃
  have n48 := b8000c444_m_x2_48 h₃
  have b0 := b8000c444_m_x9_0 h₃
  have b8 := b8000c444_m_x9_8 h₃
  have b16 := b8000c444_m_x9_16 h₃
  rw [x2₂] at n8 n16 n24 n32 n40 n48 b0 b8 b16
  rw [x9₂] at n16 b0 b8 b16
  rw [show s.getReg .x2 - 160 + 56 = s.getReg .x2 - 104 by ring, hu .x23 (by simp), h.x23] at b0
  rw [show s.getReg .x2 - 160 + 64 = s.getReg .x2 - 104 + 8 by ring, hu .x24 (by simp), h.x24] at b8
  rw [show s.getReg .x2 - 160 + 72 = s.getReg .x2 - 104 + 16 by ring, hu .x18 (by simp), h.x18] at b16
  -- what the three steps write, from `w`
  have Gw : DFrame w u fun a ↦ Within a (stackLo s roundPolyStack) roundPolyStack ∨
      Within a (w.getReg .x9) 24 :=
    (((DFrame.of_memFrame f₁).mono fun a ha ↦ Or.inl (by addr_omega [ha, hb])).trans G₂
      fun a hw ↦ by rcases hw with hw | hw <;> exact Or.inl (by addr_omega [hw, hb])).trans G₃
      fun a hw ↦ by
        rcases hw with hw | hw
        · exact Or.inl (by addr_omega [hw, hb])
        · exact Or.inr hw
  have nxu : heapNext u = heapNext w := by
    simp only [heapNext]
    rw [Gw _ fun i hi hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hi, hst.next, hBhi, hb, hlo, hBlo]]
  have hbf := h.buf
  have hroom := h.room
  have tailU : eListAt u (w.getReg .x21) (w.getReg .x20).toNat =
      eListAt w (w.getReg .x21) (w.getReg .x20).toNat :=
    Gw.eListAt fun i hi hw ↦ by
      rcases hbf.2 with h0 | h0
      · omega
      · rcases hw with hw | hw <;> addr_omega [hw, hi, h0, hroom, hb, hst.above, hBhi]
  have ef : eAt w₁ (s.getReg .x14 + 8) = eAt s (s.getReg .x14 + 8) :=
    Fw₁.eAt fun i hi hw ↦ by
      rcases hw with hw | hw | hw | hw <;>
        addr_omega [hw, hi, hef, hpre.eqFactorSelf, hpre.eqFactorStack, hpre.eqFactorFree, hSelf,
          hhi₁, nx₁]
  have esum : eAt w₁ (s.getReg .x2 - 152) =
      sumE (eListAt w (w.getReg .x21) (w.getReg .x20).toNat) :=
    eAt_eq_of_limbs (by rw [m8, m16, m24, h.x13, h.x12, h.x10])
  have ehead : eAt u (w.getReg .x9) = eAt s (s.getReg .x13) +
      eAt s (s.getReg .x14 + 8) * sumE (eListAt w (w.getReg .x21) (w.getReg .x20).toNat) := by
    rw [← ef, ← esum, ← val]
    apply eAt_eq_of_limbs
    rw [b0, b8, b16, limbs_add, limbs_eAt, limbs_eAt]
    simp only [Prod.mk.injEq]
    exact ⟨BitVec.xor_comm _ _, BitVec.xor_comm _ _, BitVec.xor_comm _ _⟩
  have hmw := h.fr.mono
  refine ⟨u, hr₂.trans hr₃, Or.inl ⟨b8000c444_pc h₃, {
    fr := {
      saved := h.fr.saved.step hS x2₃
        (fun r hr ↦ by rw [k₃ r (mem_of_mem hr _), hpres₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)])
        fun y h1 h2 ↦ by
          rw [fr₃ y (by addr_omega [h1, h2, hb]) (by addr_omega [h1, h2, hb, hBhi, hst.above]),
            G₂ y (fun i hi hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hi, h1, h2, hb]),
            f₁ y (by addr_omega [h1, h2, hb])]
      x8 := by rw [k₃ .x8 (by decide), hpres₂.reg .x8, k₁ .x8 (by decide), h.fr.x8]
      heap := ⟨by rw [nxu]; exact h.fr.heap.lo, by rw [nxu]; exact h.fr.heap.hi⟩
      mono := by rw [nxu]; exact hmw
      frame := (h.fr.frame.mono fun a h ↦ V.mono (Nat.le_of_eq nxu.symm) h).trans Gw fun a hw ↦ by
        rcases hw with hw | hw
        · exact Or.inr (Or.inl hw)
        · exact Or.inr (Or.inr (Or.inr ⟨by addr_omega [hw, hBlo], by rw [nxu, hBn]; addr_omega [hw]⟩)) }
    lc := by rw [show s.getReg .x2 - 152 = s.getReg .x2 - 160 + 8 by ring, n8]; rfl
    lp := by rw [show s.getReg .x2 - 144 = s.getReg .x2 - 160 + 16 by ring, n16]
    ll := by rw [show s.getReg .x2 - 136 = s.getReg .x2 - 160 + 24 by ring, n24]; rfl
    rc := by rw [show s.getReg .x2 - 128 = s.getReg .x2 - 160 + 32 by ring, n32, hu .x22 (by simp)]
    rp := by rw [show s.getReg .x2 - 120 = s.getReg .x2 - 160 + 40 by ring, n40, hu .x21 (by simp)]
    rl := by
      rw [show s.getReg .x2 - 112 = s.getReg .x2 - 160 + 48 by ring, n48, hu .x20 (by simp),
        ofNat_toNat_self]
    m2 := by decide
    bufB := by simp only [NewBuf]; refine ⟨hB, Or.inr ⟨hBlo, ?_⟩⟩; rw [nxu, hBn]
    room := hroom
    buf := by
      simp only [NewBuf]
      refine ⟨hbf.1, ?_⟩
      rcases hbf.2 with h0 | h0
      · exact Or.inl h0
      · exact Or.inr ⟨h0.1, by rw [nxu, hBn]; omega⟩
    value := fun T hT ↦ by
      obtain ⟨T', h1, h2⟩ := h.value T hT
      refine ⟨T', ?_, Fr.transcriptAt hpre h.fr (by rw [nxu]; exact h.fr.heap.hi)
        (Gw.mono fun a hw ↦ by
          rcases hw with hw | hw
          · exact Or.inl hw
          · exact Or.inr (Or.inr ⟨by addr_omega [hw, hBlo], by rw [nxu, hBn]; addr_omega [hw]⟩)) h2⟩
      rw [mirror_some htag, h1, tailU]
      simp only [Option.bind_some, eListAt, List.range_one, List.map_cons, List.map_nil,
        Nat.mul_zero, add_ofNat_zero]
      rw [ehead]
      rfl }⟩⟩

end Rv64Verifier.Transcript.RoundPoly
