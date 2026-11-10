import Rv64Verifier.Proofs.Pcs.VsoGlueInvsLoop

/-!
# `verify_stacked_opening`'s final level: the roots' inverses

`0x8000bdc0` calls `try_allocate_in(S - 464, n + 1, 0, 8, 8)` (a trap on `Err` at `0x8000bddc`),
`0x8000bde4` turns the result into an empty `Vec<K>` at `S - 464` and calls `reserve(S - 464, n + 1)`,
which has room; `0x8000be08` keeps the buffer at `S - 784` and sets the loop up (`IL`, `invStep`).
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  Rv64Verifier.FieldContracts LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- From `0x8000bdc0` to the loop's head, the inverses' buffer allocated. -/
theorem invSetup (hT : TryAllocZeroedSpec) (hR : ReserveFastSpec 0x8000d628) {s v w : MachineState}
    {n : ℕ} {rs : List K} (hpre : VsoPre s) (hB : QB s v w n rs) :
    ∃ t, Reaches Image.code w t ∧
      (Dead Image.code t ∨ ∃ ip, IL s v w t n ip 0 ∧ t.pc = 0x8000be28) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hsp := hB.gs.sp
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hab := hpre.stack.above
  rw [stackLo_vso] at hab
  simp only [heapEnd] at hab
  have hhw := hB.gs.heap.hi
  simp only [heapEnd] at hhw
  obtain ⟨hr8, hr1, hr2⟩ := hB.x21
  have hn1 : n + 1 < 2 ^ 64 := by omega
  -- `0x8000bdc0`
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b8000bdc0_spec hB.pc trivial
  have hm₁ := b8000bdc0_mem_same h₁
  have k₁ := b8000bdc0_keeps h₁
  have G₁ := hB.gs.same hpre hm₁ (k₁ .x2 (by decide))
  have sp₁ : t₁.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := G₁.sp
  have x10₁ : t₁.getReg .x10 = s.getReg .x2 - 464 := by rw [b8000bdc0_x10 h₁, hsp]; rv_eval []
  have x11₁ : t₁.getReg .x11 = BitVec.ofNat 64 (n + 1) := by rw [b8000bdc0_x11 h₁, hB.x20]
  have hsl : stackLo t₁ tryAllocStack = s.getReg .x2 - 1088 := by
    simp only [stackLo, tryAllocStack, sp₁]; rv_eval []
  have hnx' := hst.next
  have hab' := hst.above
  simp only [vso_stack] at hnx' hab'
  have hpreT : TryAllocPre .x13 .x14 t₁ := {
    heap := G₁.heap
    out := by rw [x10₁]; valid_sub hst.valid [hb]
    align := by rw [b8000bdc0_x13 h₁]; decide
    size := by rw [b8000bdc0_x14 h₁]; decide
    stack := hst.sub 1040 sp₁ (by decide) (by decide) (by decide) (by decide) (by decide)
    outFree := by
      rw [x10₁]
      simp only [Outside]
      exact ⟨Or.inr (by addr_omega [hab', hb]), by addr_omega [hnx', hb]⟩
    outStack := by rw [x10₁, hsl]; addr_omega [hb] }
  obtain ⟨t₂, r₂, ⟨hpc₂, hpres₂, hpost₂, -⟩ | hdead⟩ := hT.call (Reaches.refl t₁) (b8000bdc0_pc h₁) hpreT
  swap
  · exact ⟨t₂, r₁.trans r₂, Or.inl hdead⟩
  have hok := hpost₂.ok
  have X₂ := DFrame.of_byteFrame hpost₂.frame
  rw [x10₁, b8000bdc0_x13 h₁, b8000bdc0_x14 h₁, x11₁] at hok
  rw [x10₁, hsl] at X₂
  have hn₁ : heapNext t₁ = heapNext w := by simp only [heapNext, hm₁]
  have hmo₂ := hpost₂.mono
  have hhi₂ := hpost₂.heap.hi
  simp only [heapEnd] at hhi₂
  have hX₂ (a : Word) (ha : Within a (s.getReg .x2 - 464) 24 ∨ Within a (s.getReg .x2 - 1088) 48 ∨
      Within a nextAddr 8 ∨ Fresh t₁ t₂ a) : GLW s (heapNext w) (t₂.getMem nextAddr) a := by
    rcases ha with ha | ha | ha | ha
    · exact Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb])))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb])))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha)))))
    · simp only [Fresh] at ha
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, ha.2⟩)))))
  have G₂ := G₁.step hpre X₂ (fun a ha ↦ by rw [hn₁]; exact hX₂ a ha) hpost₂.heap hmo₂
    (hpres₂ .x2 (by decide))
  have sp₂ : t₂.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := G₂.sp
  -- `0x8000bddc`
  obtain ⟨t₃, r₃, h₃⟩ := Sym.BlockSpec.reaches b8000bddc_spec
    (by rw [hpc₂, returnAddress_eq, b8000bdc0_x1 h₁]; decide) (by
      rv_eval [sp₂]; valid_access hst.valid [hb])
  have e576 : t₂.getMem (t₂.getReg .x2 + 576) = t₂.getMem (s.getReg .x2 - 464) := by
    rw [sp₂]; rv_eval []
  by_cases herr : t₂.getMem (s.getReg .x2 - 464) ≠ 0
  · refine ⟨t₃, r₁.trans (r₂.trans r₃), Or.inl (dead_of_fetch ?_)⟩
    rw [b8000bddc_pc_taken h₃ (by rw [e576]; exact herr)]
    exact trap
  have herr' : t₂.getMem (s.getReg .x2 - 464) = 0 := by simpa using herr
  obtain ⟨hcap, hnb⟩ := hok herr'
  rw [show s.getReg .x2 - 464 + 8 = s.getReg .x2 - 456 by rv_eval []] at hcap
  rw [show s.getReg .x2 - 464 + 16 = s.getReg .x2 - 448 by rv_eval [],
    show (8 : Word).toNat = 8 from rfl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn1] at hnb
  have hm₃ := b8000bddc_mem_same h₃
  have k₃ := b8000bddc_keeps h₃
  have G₃ := G₂.same hpre hm₃ (k₃ .x2 (by decide))
  have sp₃ : t₃.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := G₃.sp
  -- `0x8000bde4`
  obtain ⟨t₄, r₄, h₄⟩ := Sym.BlockSpec.reaches b8000bde4_spec
    (b8000bddc_pc_not_taken h₃ (by rw [e576]; exact herr')) (by
      rv_eval [sp₃]; and_intros <;> valid_access hst.valid [hb])
  have k₄ := b8000bde4_keeps h₄
  have X₄ : DFrame t₃ t₄ fun y ↦ Within y (s.getReg .x2 - 464) 24 := by
    have := DFrame.of_memFrame (b8000bde4_frame h₄ (by rw [sp₃]; addr_omega [hb]))
    rw [sp₃] at this
    exact this.mono fun y hy ↦ by addr_omega [hy, hb]
  obtain ⟨G₄, n₄⟩ := G₃.stepS hpre X₄ (fun y hy ↦ Or.inr (Or.inr (Or.inl (by addr_omega [hy, hb]))))
    (k₄ .x2 (by decide))
  have sp₄ : t₄.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := G₄.sp
  have m592 := b8000bde4_m_x2_592 h₄
  have m584 := b8000bde4_m_x2_584 h₄
  have m576 := b8000bde4_m_x2_576 h₄
  rw [sp₃] at m592 m584 m576
  rv_eval [hm₃] at m592 m584 m576
  rw [hcap] at m576
  -- `reserve(S - 464, n + 1)`, which has room
  have x10₄ : t₄.getReg .x10 = s.getReg .x2 - 464 := by rw [b8000bde4_x10 h₄, sp₃]; rv_eval []
  have x11₄ : t₄.getReg .x11 = BitVec.ofNat 64 (n + 1) := by
    rw [b8000bde4_x11 h₄, k₃ .x20 (by decide), hpres₂ .x20 (by decide), k₁ .x20 (by decide), hB.x20]
  obtain ⟨t₅, r₅, ⟨hpc₅, hpres₅, -, hm₅⟩ | hdead⟩ := hR.call (Reaches.refl t₄) (b8000bde4_pc h₄)
    ⟨by rw [x10₄]; valid_sub hst.valid [hb], by
      rw [x10₄, x11₄]
      simp only [vecLen, vecCap]
      rw [show s.getReg .x2 - 464 + 16 = s.getReg .x2 - 448 by rv_eval [], m592, m576]
      simp⟩
  swap
  · exact ⟨t₅, r₁.trans (r₂.trans (r₃.trans (r₄.trans r₅))), Or.inl hdead⟩
  have G₅ := G₄.same hpre hm₅ (hpres₅ .x2 (by decide))
  have sp₅ : t₅.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := G₅.sp
  -- `0x8000be08`
  obtain ⟨t₆, r₆, h₆⟩ := Sym.BlockSpec.reaches b8000be08_spec
    (by rw [hpc₅, returnAddress_eq, b8000bde4_x1 h₄]; decide) (by
      rv_eval [sp₅]; and_intros <;> valid_access hst.valid [hb])
  have k₆ := b8000be08_keeps h₆
  have X₆ : DFrame t₅ t₆ fun y ↦ Within y (s.getReg .x2 - 784) 8 := by
    have := DFrame.of_memFrame (b8000be08_frame h₆ (by rw [sp₅]; addr_omega [hb]))
    rw [sp₅] at this
    exact this.mono fun y hy ↦ by addr_omega [hy, hb]
  obtain ⟨G₆, n₆⟩ := G₅.stepS hpre X₆ (fun y hy ↦ Or.inr (Or.inl (by addr_omega [hy, hb])))
    (k₆ .x2 (by decide))
  -- the buffer
  generalize hip : t₂.getMem (s.getReg .x2 - 448) = ip at hnb m584
  have hn₆ : heapNext t₆ = heapNext t₂ := by simp only [heapNext, n₆, hm₅, n₄, hm₃]
  have hnb2 := hnb.2
  rcases hnb2 with h0 | h0
  · omega
  have m784 : t₆.getMem (s.getReg .x2 - 784) = ip := by
    have := b8000be08_m_x2_256 h₆
    rw [sp₅] at this; rv_eval [hm₅, m584] at this; exact this
  have e584 : t₅.getMem (s.getReg .x2 - 456) = ip := by rw [hm₅]; exact m584
  have e592 : t₅.getMem (s.getReg .x2 - 448) = 0 := by rw [hm₅]; exact m592
  -- what the setup kept
  have kw (y : Word) (hy : GK2 s y) : t₆.getMem y = w.getMem y := by
    simp only [GK2, GK] at hy
    have H : ¬ Within y (s.getReg .x2 - 784) 8 ∧ ¬ Within y (s.getReg .x2 - 464) 24 ∧
        ¬ Within y (s.getReg .x2 - 1088) 48 ∧ ¬ Within y nextAddr 8 ∧
        y.toNat % 8 = 0 ∧ heapEnd ≤ y.toNat := by
      rcases hy with (hy | hy | hy | hy | hy | hy | hy | hy | hy) | hy | hy | hy | hy <;> subst hy <;>
        exact ⟨by addr_omega [hb], by addr_omega [hb], by addr_omega [hb], by addr_omega [hb, hnx],
          by addr_omega [hb], by simp only [heapEnd]; addr_omega [hb, hab]⟩
    obtain ⟨H1, H2, H3, H4, H5, H6⟩ := H
    simp only [heapEnd] at H6
    rw [X₆ y fun i hi hw ↦ H1 (by addr_omega [hw, hi, H5, hb]), hm₅,
      X₄ y fun i hi hw ↦ H2 (by addr_omega [hw, hi, H5, hb]), hm₃,
      X₂ y fun i hi hw ↦ by
        rcases hw with hw | hw | hw | hw
        · exact H2 (by addr_omega [hw, hi, H5, hb])
        · exact H3 (by addr_omega [hw, hi, H5, hb])
        · exact H4 (by addr_omega [hw, hi, H5, hnx])
        · simp only [Fresh] at hw; addr_omega [hw.2, hi, H5, H6, hhi₂], hm₁]
  -- the frame from `w`
  have F : DFrame w t₆ (GLW s (heapNext w) (t₆.getMem nextAddr)) := by
    have e : t₆.getMem nextAddr = t₂.getMem nextAddr := by rw [n₆, hm₅, n₄, hm₃]
    rw [e]
    refine (((((DFrame.of_same hm₁ _).trans X₂ fun a ha ↦ hX₂ a ha).trans
      (DFrame.of_same hm₃ _) fun _ h ↦ h).trans X₄ fun a ha ↦ ?_).trans
      (DFrame.of_same hm₅ _) fun _ h ↦ h).trans X₆ fun a ha ↦ ?_
    · exact Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb])))
    · exact Or.inr (Or.inl (by addr_omega [ha, hb]))
  have hreg (r : Reg) (h6 : r ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x11, .x12, .x13, .x14, .x15,
      .x16, .x17, .x19, .x20, .x21, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] : List Reg))
      (h5 : r ∈ calleeSaved) (h4 : r ∈ ([.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x12, .x13, .x14,
      .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30,
      .x31] : List Reg)) (h3 : r ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x11, .x12, .x13,
      .x14, .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29,
      .x30, .x31] : List Reg)) (h2 : r ∈ calleeSaved) (h1 : r ∈ ([.x2, .x3, .x4, .x5, .x6, .x7, .x8,
      .x9, .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29,
      .x30, .x31] : List Reg)) : t₆.getReg r = w.getReg r := by
    rw [k₆ r h6, hpres₅ r h5, k₄ r h4, k₃ r h3, hpres₂ r h2, k₁ r h1]
  have x21₆ : t₆.getReg .x21 = w.getReg .x21 := hreg .x21 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  refine ⟨t₆, r₁.trans (r₂.trans (r₃.trans (r₄.trans (r₅.trans r₆)))), Or.inr ⟨ip, {
    gs := G₆
    fr := F
    wt := by rw [hn₆]; omega
    kle := by omega
    x8 := by rw [b8000be08_x8 h₆, sp₅]; rv_eval [e584, e592]; simp
    x18 := by rw [b8000be08_x18 h₆, hpres₅ .x21 (by decide), k₄ .x21 (by decide),
      k₃ .x21 (by decide), hpres₂ .x21 (by decide), k₁ .x21 (by decide)]; simp
    x9 := by
      rw [b8000be08_x9 h₆, hpres₅ .x21 (by decide), k₄ .x21 (by decide), k₃ .x21 (by decide),
        hpres₂ .x21 (by decide), k₁ .x21 (by decide), hpres₅ .x20 (by decide), k₄ .x20 (by decide),
        k₃ .x20 (by decide), hpres₂ .x20 (by decide), k₁ .x20 (by decide), hB.x20]
      congr 1
      have h8 : 8 * (n + 1) < 2 ^ 64 := by omega
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (8 : Word).toNat = 8 from rfl,
        Nat.mod_eq_of_lt hn1, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt h8]
      omega
    x19 := hreg .x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    x20 := hreg .x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    x21 := x21₆
    x23 := hreg .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    x26 := hreg .x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    x22 := by rw [b8000be08_x22 h₆, sp₅]; rv_eval [e592]
    m784 := m784
    ipb := ⟨hnb.1, by omega, by rw [hn₆]; omega⟩
    done := fun i hi ↦ absurd hi (Nat.not_lt_zero _)
    keep := kw }, b8000be08_pc h₆⟩⟩

/-- The loop, from `k` inverses to all `n + 1`. -/
theorem invLoop (hK : KInvSpec) {s v w : MachineState} {n : ℕ} {rs : List K} {ip : Word}
    (hpre : VsoPre s) (hB : QB s v w n rs) :
    ∀ m k t, n + 1 - k = m → IL s v w t n ip k →
      t.pc = (if k = n + 1 then 0x8000be44 else 0x8000be28) →
      ∃ t', Reaches Image.code t t' ∧
        (Dead Image.code t' ∨ (IL s v w t' n ip (n + 1) ∧ t'.pc = 0x8000be44)) := by
  intro m
  induction m with
  | zero =>
    intro k t hm h hpc
    have hk : k = n + 1 := by have := h.kle; omega
    subst hk
    exact ⟨t, Reaches.refl t, Or.inr ⟨h, by simpa using hpc⟩⟩
  | succ m ih =>
    intro k t hm h hpc
    have hk : k < n + 1 := by omega
    have hpc' : t.pc = 0x8000be28 := by rw [hpc]; simp only [Nat.ne_of_lt hk, ↓reduceIte]
    obtain ⟨t', r, hout⟩ := invStep hK hpre hB h hpc' hk
    rcases hout with hd | ⟨h', hpc''⟩
    · exact ⟨t', r, Or.inl hd⟩
    obtain ⟨t'', r', hout'⟩ := ih (k + 1) t' (by omega) h' hpc''
    exact ⟨t'', r.trans r', hout'⟩

/-- **The roots' inverses**: `0x8000bdc0` to `0x8000be44`. -/
theorem invs_spec (hT : TryAllocZeroedSpec) (hR : ReserveFastSpec 0x8000d628) (hK : KInvSpec) :
    InvsSpec := by
  intro s v w n rs hpre hB
  obtain ⟨t, r, hout⟩ := invSetup hT hR hpre hB
  rcases hout with hd | ⟨ip, h, hpc⟩
  · exact ⟨t, r, Or.inl hd⟩
  obtain ⟨t', r', hout'⟩ := invLoop hK hpre hB (n + 1 - 0) 0 t rfl h (by simp only [hpc]; simp)
  rcases hout' with hd | ⟨h', hpc'⟩
  · exact ⟨t', r.trans r', Or.inl hd⟩
  refine ⟨t', r.trans r', Or.inr {
    gs := h'.gs
    fr := h'.fr
    pc := hpc'
    x19 := h'.x19
    x20 := h'.x20
    x21 := h'.x21
    x23 := h'.x23
    x26 := h'.x26
    x22 := h'.x22
    ip := by rw [h'.m784]; exact h'.ipb
    imem := by
      rw [h'.m784, ← hB.rmem]
      simp only [kListAt, List.map_map]
      apply List.map_congr_left
      intro i hi
      simp only [List.mem_range] at hi
      exact h'.done i hi
    keep := h'.keep }⟩

end Rv64Verifier.Proofs.Pcs.Vso

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.invs_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.invs_spec
