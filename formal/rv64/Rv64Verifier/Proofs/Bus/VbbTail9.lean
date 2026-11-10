import Rv64Verifier.Proofs.Bus.VbbTail8

/-!
# `verify_bus_balance` past the GKR loop: the second and third copies

`copy2` (`0x80006d50`'s call, the new `Vec` in `s3`, `s7`) and `copy3` (`0x80006dd8`'s, in `s11`,
`s8`; the point's buffer and `push`'s are first saved at `S - 1256` and `S - 1272`).
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem copy2 (hT : TryAllocZeroedSpec) (hM : MemcpySpec 0x800126e4) {s u : MachineState}
    (hpre : BusBalancePre s) (h : Inv s u) (hpc : u.pc = 0x800049ac)
    (hx1 : u.getReg .x1 = 0x80006d8c) (h10 : u.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 608)
    (h13 : u.getReg .x13 = 8) (h14 : u.getReg .x14 = 24) {n cap ptr len : Word} {xs : List E}
    (h9 : u.getReg .x9 = n) (h11 : u.getReg .x11 = n) (h18 : u.getReg .x18 = n * 16 + n * 8)
    (h27 : u.getReg .x27 = ptr) (hp : NewVecR s u cap ptr len xs) (hn : n.toNat ≤ len.toNat) :
    ∃ w, Reaches Image.code u w ∧ (Dead Image.code w ∨ (w.pc = 0x80006db4 ∧ Inv s w ∧
      StepS s u w (Within · (s.getReg .x2 - BitVec.ofNat 64 608) 24) ∧
      (∀ r ∈ ([.x8, .x9, .x18, .x20, .x21, .x22, .x24, .x25, .x26, .x27] : List Reg),
        w.getReg r = u.getReg r) ∧
      NewVecR s w (w.getReg .x19) (w.getReg .x23) n (xs.take n.toNat))) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  obtain ⟨v, hrv, ⟨hpcv, hpv, st, J, ok⟩ | hd⟩ := tryAllocCall hT hpre h (Reaches.refl u) hpc h10 h13 h14
  swap
  · exact ⟨v, hrv, Or.inl hd⟩
  have sp := J.sp
  have hpc' : v.pc = 0x80006d8c := by rw [hpcv, returnAddress_eq, hx1]; decide
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80006d8c_spec hpc' (by
    rv_eval [sp]
    valid_access hval [hb1])
  have k₂ := b80006d8c_keeps h₂
  have m₂ := b80006d8c_mem_same h₂
  have e736 : s.getReg .x2 - 1344 + 736 = s.getReg .x2 - BitVec.ofNat 64 608 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  by_cases ht : v.getMem (s.getReg .x2 - BitVec.ofNat 64 608) = 0
  swap
  · have pc₂ := b80006d8c_pc_taken h₂ (by rw [sp, e736]; exact ht)
    exact ⟨u₂, hrv.trans hr₂, Or.inl (dead_of_fetch (by
      rw [pc₂]; exact Option.isNone_iff_eq_none.mp (by decide +kernel)))⟩
  obtain ⟨hcap, hP⟩ := ok ht
  rw [h11] at hcap hP
  have pc₂ := b80006d8c_pc_not_taken h₂ (by rw [sp, e736]; exact ht)
  have I₂ := J.same m₂ (k₂ .x2 (by decide))
  have sp₂ : u₂.getReg .x2 = s.getReg .x2 - 1344 := I₂.sp
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80006d94_spec pc₂ (by
    rv_eval [sp₂]
    and_intros <;> valid_access hval [hb1])
  have k₃ := b80006d94_keeps h₃
  have m₃ := b80006d94_mem_same h₃
  have I₃ := I₂.same m₃ (k₃ .x2 (by decide))
  have x9₂ : u₂.getReg .x9 = n := by rw [k₂ .x9 (by decide), hpv .x9 (by decide), h9]
  have x19₃ : u₃.getReg .x19 = n := by
    rw [b80006d94_x19 h₃, sp₂, m₂, show s.getReg .x2 - 1344 + 744 =
      s.getReg .x2 - BitVec.ofNat 64 608 + 8 by apply BitVec.eq_of_toNat_eq; addr_omega [hb1]]
    exact hcap
  have x23₃ : u₃.getReg .x23 = v.getMem (s.getReg .x2 - BitVec.ofNat 64 608 + 16) := by
    rw [b80006d94_x23 h₃, sp₂, m₂, show s.getReg .x2 - 1344 + 752 =
      s.getReg .x2 - BitVec.ofNat 64 608 + 16 by apply BitVec.eq_of_toNat_eq; addr_omega [hb1]]
  have st₃ : StepS s u u₃ (Within · (s.getReg .x2 - BitVec.ofNat 64 608) 24) :=
    ((st.toS.trans (StepS.same m₂ J.heap (k₂ .x2 (by decide)))).trans
      (StepS.same m₃ I₂.heap (k₃ .x2 (by decide)))).weaken fun a ha ↦ by
        rcases ha with (ha | ha) | ha
        · exact ha
        · exact False.elim ha
        · exact False.elim ha
  have hn₃ : heapNext u₃ = heapNext v := by simp only [heapNext, m₃, m₂]
  have rg (r : Reg) (hr : r ∈ ([.x8, .x9, .x18, .x20, .x21, .x22, .x24, .x25, .x26, .x27] :
      List Reg)) : u₃.getReg r = u.getReg r := by
    rw [k₃ r (mem_of_mem hr _), k₂ r (mem_of_mem hr _), hpv r (mem_of_mem hr _)]
  by_cases hz : n = 0
  · refine ⟨u₃, hrv.trans (hr₂.trans hr₃), Or.inr ⟨b80006d94_pc_taken h₃ (by rw [x9₂]; exact hz),
      I₃, st₃, rg, ?_⟩⟩
    rw [x19₃, x23₃]
    have hz' : n.toNat = 0 := by rw [hz]; rfl
    refine ⟨Nat.le_refl _, ⟨hP.1, Or.inl (by rw [hz'])⟩, ?_⟩
    rw [hz']; rfl
  have pc₃ := b80006d94_pc_not_taken h₃ (by rw [x9₂]; exact hz)
  obtain ⟨u₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80006da0_spec pc₃ trivial
  have k₄ := b80006da0_keeps h₄
  have m₄ := b80006da0_mem_same h₄
  have I₄ := I₃.same m₄ (k₄ .x2 (by decide))
  have st₄ := (st₃.trans (StepS.same m₄ I₃.heap (k₄ .x2 (by decide)))).weaken fun a ha ↦ by
    rcases ha with ha | ha
    · exact ha
    · exact False.elim ha
  have hn₄ : heapNext u₄ = heapNext v := by rw [← hn₃]; simp only [heapNext, m₄]
  have hP₄ : NewBuf u u₄ (v.getMem (s.getReg .x2 - BitVec.ofNat 64 608 + 16)) (n.toNat * 24) 8 := by
    simp only [NewBuf] at hP ⊢; rw [hn₄]; exact hP
  obtain ⟨w, hrw, ⟨hpcw, hpw, Iw, stw, hw, -⟩ | hd⟩ := copyTail hM hpre I₄ (b80006da0_pc h₄)
    (frameW_slot hpre (k := 608) (n := 24) (by omega) (by omega)) st₄ hp hn hz
    hP₄ (by rw [b80006da0_x10 h₄, x23₃]) (by rw [b80006da0_x11 h₄, rg .x27 (by decide), h27])
    (by rw [b80006da0_x12 h₄, rg .x18 (by decide), h18])
  swap
  · exact ⟨w, hrv.trans (hr₂.trans (hr₃.trans (hr₄.trans hrw))), Or.inl hd⟩
  refine ⟨w, hrv.trans (hr₂.trans (hr₃.trans (hr₄.trans hrw))), Or.inr ⟨by
    rw [hpcw, returnAddress_eq, b80006da0_x1 h₄]; decide, Iw, stw, fun r hr ↦ ?_, ?_⟩⟩
  · rw [hpw r (by unfold calleeSaved; exact mem_of_mem hr _), k₄ r (mem_of_mem hr _), rg r hr]
  · rw [hpw .x19 (by decide), hpw .x23 (by decide), k₄ .x19 (by decide), k₄ .x23 (by decide),
      x19₃, x23₃]
    exact hw

/-- What `copy3`'s block saves in the frame: the point's buffer, `push`'s. -/
def Copy3W (s : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - BitVec.ofNat 64 608) 24 ∨ Within a (s.getReg .x2 - 1272) 8 ∨
    Within a (s.getReg .x2 - 1256) 8

theorem copy3 (hT : TryAllocZeroedSpec) (hM : MemcpySpec 0x800126e4) {s u : MachineState}
    (hpre : BusBalancePre s) (h : Inv s u) (hpc : u.pc = 0x800049ac)
    (hx1 : u.getReg .x1 = 0x80006e14) (h10 : u.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 608)
    (h13 : u.getReg .x13 = 8) (h14 : u.getReg .x14 = 24) {n cap ptr len : Word} {xs : List E}
    (h9 : u.getReg .x9 = n) (h11 : u.getReg .x11 = n) (h18 : u.getReg .x18 = n * 16 + n * 8)
    (h27 : u.getReg .x27 = ptr) (hp : NewVecR s u cap ptr len xs) (hn : n.toNat ≤ len.toNat) :
    ∃ w, Reaches Image.code u w ∧ (Dead Image.code w ∨ (w.pc = 0x80006e44 ∧ Inv s w ∧
      StepS s u w (Copy3W s) ∧
      (∀ r ∈ ([.x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x25, .x26] : List Reg),
        w.getReg r = u.getReg r) ∧
      w.getMem (s.getReg .x2 - 1256) = ptr ∧ w.getMem (s.getReg .x2 - 1272) = u.getReg .x24 ∧
      NewVecR s w (w.getReg .x27) (w.getReg .x24) n (xs.take n.toNat))) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have fC : FrameW s (Copy3W s) := fun a ha ↦ by rcases ha with ha | ha | ha <;> addr_omega [ha, hb1]
  obtain ⟨v, hrv, ⟨hpcv, hpv, st, J, ok⟩ | hd⟩ := tryAllocCall hT hpre h (Reaches.refl u) hpc h10 h13 h14
  swap
  · exact ⟨v, hrv, Or.inl hd⟩
  have sp := J.sp
  have hpc' : v.pc = 0x80006e14 := by rw [hpcv, returnAddress_eq, hx1]; decide
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80006e14_spec hpc' (by
    rv_eval [sp]
    valid_access hval [hb1])
  have k₂ := b80006e14_keeps h₂
  have m₂ := b80006e14_mem_same h₂
  have e736 : s.getReg .x2 - 1344 + 736 = s.getReg .x2 - BitVec.ofNat 64 608 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  by_cases ht : v.getMem (s.getReg .x2 - BitVec.ofNat 64 608) = 0
  swap
  · have pc₂ := b80006e14_pc_taken h₂ (by rw [sp, e736]; exact ht)
    exact ⟨u₂, hrv.trans hr₂, Or.inl (dead_of_fetch (by
      rw [pc₂]; exact Option.isNone_iff_eq_none.mp (by decide +kernel)))⟩
  obtain ⟨hcap, hP⟩ := ok ht
  rw [h11] at hcap hP
  have pc₂ := b80006e14_pc_not_taken h₂ (by rw [sp, e736]; exact ht)
  have I₂ := J.same m₂ (k₂ .x2 (by decide))
  have sp₂ : u₂.getReg .x2 = s.getReg .x2 - 1344 := I₂.sp
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80006e1c_spec pc₂ (by
    rv_eval [sp₂]
    and_intros <;> valid_access hval [hb1])
  have k₃ := b80006e1c_keeps h₃
  have fr₃ : DFrame u₂ u₃ fun a ↦ Within a (s.getReg .x2 - 1272) 8 ∨
      Within a (s.getReg .x2 - 1256) 8 := fun a ha ↦
    h₃.frame a (by
      rv_eval [sp₂]
      and_intros <;> intro he <;> exact ha 0 (by decide) (by
        rw [add_ofNat_zero, he]; addr_omega [hb1]))
  have st₃' : StepS s u₂ u₃ (Copy3W s) :=
    StepS.ofDFrame I₂.heap fr₃ (fun a ha ↦ Or.inr ha) (fun i hi hw ↦ by
      rcases hw with hw | hw <;> addr_omega [hw, hi, hb1]) (k₃ .x2 (by decide))
  have I₃ := I₂.afterR hpre fC st₃'.toR
  have x9₂ : u₂.getReg .x9 = n := by rw [k₂ .x9 (by decide), hpv .x9 (by decide), h9]
  have x27₃ : u₃.getReg .x27 = n := by
    rw [b80006e1c_x27 h₃, sp₂, m₂, show s.getReg .x2 - 1344 + 744 =
      s.getReg .x2 - BitVec.ofNat 64 608 + 8 by apply BitVec.eq_of_toNat_eq; addr_omega [hb1]]
    exact hcap
  have x24₃ : u₃.getReg .x24 = v.getMem (s.getReg .x2 - BitVec.ofNat 64 608 + 16) := by
    rw [b80006e1c_x24 h₃, sp₂, m₂, show s.getReg .x2 - 1344 + 752 =
      s.getReg .x2 - BitVec.ofNat 64 608 + 16 by apply BitVec.eq_of_toNat_eq; addr_omega [hb1]]
  have m88 : u₃.getMem (s.getReg .x2 - 1256) = ptr := by
    have := b80006e1c_m_x2_88 h₃
    rw [sp₂, show s.getReg .x2 - 1344 + 88 = s.getReg .x2 - 1256 by
      apply BitVec.eq_of_toNat_eq; addr_omega [hb1], k₂ .x27 (by decide), hpv .x27 (by decide),
      h27] at this
    exact this
  have m72 : u₃.getMem (s.getReg .x2 - 1272) = u.getReg .x24 := by
    have := b80006e1c_m_x2_72 h₃
    rw [sp₂, show s.getReg .x2 - 1344 + 72 = s.getReg .x2 - 1272 by
      apply BitVec.eq_of_toNat_eq; addr_omega [hb1], k₂ .x24 (by decide),
      hpv .x24 (by decide)] at this
    exact this
  have st₃ : StepS s u u₃ (Copy3W s) :=
    ((st.toS.trans (StepS.same m₂ J.heap (k₂ .x2 (by decide)))).trans st₃').weaken
      fun a ha ↦ by
        rcases ha with (ha | ha) | ha
        · exact Or.inl ha
        · exact False.elim ha
        · exact ha
  have hn₃ : heapNext u₃ = heapNext v := by
    rw [← show heapNext u₂ = heapNext v by simp only [heapNext, m₂]]
    simp only [heapNext]
    exact congrArg BitVec.toNat (fr₃ nextAddr fun i hi hw ↦ by
      rcases hw with hw | hw <;> addr_omega [hw, hi, hb1])
  have rg (r : Reg) (hr : r ∈ ([.x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x25, .x26] :
      List Reg)) : u₃.getReg r = u.getReg r := by
    rw [k₃ r (mem_of_mem hr _), k₂ r (mem_of_mem hr _), hpv r (mem_of_mem hr _)]
  by_cases hz : n = 0
  · refine ⟨u₃, hrv.trans (hr₂.trans hr₃), Or.inr ⟨b80006e1c_pc_taken h₃ (by rw [x9₂]; exact hz),
      I₃, st₃, rg, m88, m72, ?_⟩⟩
    rw [x27₃, x24₃]
    have hz' : n.toNat = 0 := by rw [hz]; rfl
    refine ⟨Nat.le_refl _, ⟨hP.1, Or.inl (by rw [hz'])⟩, ?_⟩
    rw [hz']; rfl
  have pc₃ := b80006e1c_pc_not_taken h₃ (by rw [x9₂]; exact hz)
  obtain ⟨u₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80006e30_spec pc₃ (by
    rv_eval [k₃ .x2 (by decide), sp₂]
    valid_access hval [hb1])
  have k₄ := b80006e30_keeps h₄
  have m₄ := b80006e30_mem_same h₄
  have I₄ := I₃.same m₄ (k₄ .x2 (by decide))
  have st₄ := (st₃.trans (StepS.same m₄ I₃.heap (k₄ .x2 (by decide)))).weaken fun a ha ↦ by
    rcases ha with ha | ha
    · exact ha
    · exact False.elim ha
  have hn₄ : heapNext u₄ = heapNext v := by rw [← hn₃]; simp only [heapNext, m₄]
  have hP₄ : NewBuf u u₄ (v.getMem (s.getReg .x2 - BitVec.ofNat 64 608 + 16)) (n.toNat * 24) 8 := by
    simp only [NewBuf] at hP ⊢; rw [hn₄]; exact hP
  have sp₃ : u₃.getReg .x2 = s.getReg .x2 - 1344 := I₃.sp
  obtain ⟨w, hrw, ⟨hpcw, hpw, Iw, stw, hw, hkw⟩ | hd⟩ := copyTail hM hpre I₄ (b80006e30_pc h₄) fC st₄
    hp hn hz hP₄ (by rw [b80006e30_x10 h₄, x24₃])
    (by rw [b80006e30_x11 h₄, sp₃, show s.getReg .x2 - 1344 + 88 = s.getReg .x2 - 1256 by
      apply BitVec.eq_of_toNat_eq; addr_omega [hb1], m88])
    (by rw [b80006e30_x12 h₄, rg .x18 (by decide), h18])
  swap
  · exact ⟨w, hrv.trans (hr₂.trans (hr₃.trans (hr₄.trans hrw))), Or.inl hd⟩
  refine ⟨w, hrv.trans (hr₂.trans (hr₃.trans (hr₄.trans hrw))), Or.inr ⟨by
    rw [hpcw, returnAddress_eq, b80006e30_x1 h₄]; decide, Iw, stw, fun r hr ↦ ?_, ?_, ?_, ?_⟩⟩
  · rw [hpw r (by unfold calleeSaved; exact mem_of_mem hr _), k₄ r (mem_of_mem hr _), rg r hr]
  · rw [hkw _ (by addr_omega [hb1]) (by addr_omega [hb1]), m₄]; exact m88
  · rw [hkw _ (by addr_omega [hb1]) (by addr_omega [hb1]), m₄]; exact m72
  · rw [hpw .x27 (by decide), hpw .x24 (by decide), k₄ .x27 (by decide), k₄ .x24 (by decide),
      x27₃, x24₃]
    exact hw

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
