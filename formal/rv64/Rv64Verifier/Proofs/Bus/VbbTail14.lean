import Rv64Verifier.Proofs.Bus.VbbTail13

/-!
# `verify_bus_balance` past the GKR loop: the points of `memory_final`'s and `bytecode_final`'s
claims

`copy4` is `point[..log_memory].to_vec()` at `0x80006f4c`'s call (the new `Vec` in `s1`, `s3`;
`s5`, `s7`, `s11` reloaded with the result's address, `log_bytecode` and the point's buffer),
`copy5` is `point[..log_bytecode].to_vec()` at `0x80006fd8`'s (the new `Vec` in `s1`, `s2`).
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem copy4 (hT : TryAllocZeroedSpec) (hM : MemcpySpec 0x800126e4) {s u : MachineState}
    (hpre : BusBalancePre s) (h : Inv s u) (hpc : u.pc = 0x800049ac)
    (hx1 : u.getReg .x1 = 0x80006f54) (h10 : u.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 608)
    (h13 : u.getReg .x13 = 8) (h14 : u.getReg .x14 = 24) {n cap ptr len : Word} {xs : List E}
    (h11 : u.getReg .x11 = n) (h24 : u.getReg .x24 = n) (h18 : u.getReg .x18 = n * 16 + n * 8)
    (h88 : u.getMem (s.getReg .x2 - 1256) = ptr) (hp : NewVecR s u cap ptr len xs)
    (hn : n.toNat ≤ len.toNat) :
    ∃ w, Reaches Image.code u w ∧ (Dead Image.code w ∨ (w.pc = 0x80006f88 ∧ Inv s w ∧
      StepS s u w (Within · (s.getReg .x2 - BitVec.ofNat 64 608) 24) ∧
      (∀ r ∈ ([.x8, .x18, .x20, .x22, .x24, .x25, .x26] : List Reg), w.getReg r = u.getReg r) ∧
      w.getReg .x21 = u.getMem (s.getReg .x2 - 1312) ∧
      w.getReg .x23 = u.getMem (s.getReg .x2 - 1152) ∧ w.getReg .x27 = ptr ∧
      NewVecR s w (w.getReg .x9) (w.getReg .x19) n (xs.take n.toNat))) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  obtain ⟨v, hrv, ⟨hpcv, hpv, st, J, ok⟩ | hd⟩ := tryAllocCall hT hpre h (Reaches.refl u) hpc h10 h13 h14
  swap
  · exact ⟨v, hrv, Or.inl hd⟩
  have sp := J.sp
  have hpc' : v.pc = 0x80006f54 := by rw [hpcv, returnAddress_eq, hx1]; decide
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80006f54_spec hpc' (by
    rv_eval [sp]
    valid_access hval [hb1])
  have k₂ := b80006f54_keeps h₂
  have m₂ := b80006f54_mem_same h₂
  have e736 : s.getReg .x2 - 1344 + 736 = s.getReg .x2 - BitVec.ofNat 64 608 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  by_cases ht : v.getMem (s.getReg .x2 - BitVec.ofNat 64 608) = 0
  swap
  · have pc₂ := b80006f54_pc_taken h₂ (by rw [sp, e736]; exact ht)
    exact ⟨u₂, hrv.trans hr₂, Or.inl (dead_of_fetch (by
      rw [pc₂]; exact Option.isNone_iff_eq_none.mp (by decide +kernel)))⟩
  obtain ⟨hcap, hP⟩ := ok ht
  rw [h11] at hcap hP
  have pc₂ := b80006f54_pc_not_taken h₂ (by rw [sp, e736]; exact ht)
  have I₂ := J.same m₂ (k₂ .x2 (by decide))
  have sp₂ : u₂.getReg .x2 = s.getReg .x2 - 1344 := I₂.sp
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80006f5c_spec pc₂ (by
    rv_eval [sp₂]
    and_intros <;> valid_access hval [hb1])
  have k₃ := b80006f5c_keeps h₃
  have m₃ := b80006f5c_mem_same h₃
  have I₃ := I₂.same m₃ (k₃ .x2 (by decide))
  have sl (j : Nat) (hj1 : 616 ≤ j) (hj2 : j ≤ 1344) :
      v.getMem (s.getReg .x2 - BitVec.ofNat 64 j) = u.getMem (s.getReg .x2 - BitVec.ofNat 64 j) :=
    st.toS.slot hpre (fun y hy h' ↦ by addr_omega [hy, h', hb1, hj1, hj2])
      (by constructor <;> addr_omega [hb1, hj1, hj2])
  have ld (j k : Nat) (hjk : j + k = 1344) (hj1 : 616 ≤ k) (hj2 : k ≤ 1344) :
      v.getMem (s.getReg .x2 - 1344 + BitVec.ofNat 64 j) =
        u.getMem (s.getReg .x2 - BitVec.ofNat 64 k) := by
    rw [← sl k hj1 hj2]
    exact congrArg v.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hjk])
  have x24₂ : u₂.getReg .x24 = n := by rw [k₂ .x24 (by decide), hpv .x24 (by decide), h24]
  have x9₃ : u₃.getReg .x9 = n := by
    rw [b80006f5c_x9 h₃, sp₂, m₂, show s.getReg .x2 - 1344 + 744 =
      s.getReg .x2 - BitVec.ofNat 64 608 + 8 by apply BitVec.eq_of_toNat_eq; addr_omega [hb1]]
    exact hcap
  have x19₃ : u₃.getReg .x19 = v.getMem (s.getReg .x2 - BitVec.ofNat 64 608 + 16) := by
    rw [b80006f5c_x19 h₃, sp₂, m₂, show s.getReg .x2 - 1344 + 752 =
      s.getReg .x2 - BitVec.ofNat 64 608 + 16 by apply BitVec.eq_of_toNat_eq; addr_omega [hb1]]
  have x21₃ : u₃.getReg .x21 = u.getMem (s.getReg .x2 - 1312) := by
    rw [b80006f5c_x21 h₃, sp₂, m₂]; exact ld 32 1312 rfl (by omega) (by omega)
  have x23₃ : u₃.getReg .x23 = u.getMem (s.getReg .x2 - 1152) := by
    rw [b80006f5c_x23 h₃, sp₂, m₂]; exact ld 192 1152 rfl (by omega) (by omega)
  have x27₃ : u₃.getReg .x27 = ptr := by
    rw [b80006f5c_x27 h₃, sp₂, m₂]; exact (ld 88 1256 rfl (by omega) (by omega)).trans h88
  have st₃ : StepS s u u₃ (Within · (s.getReg .x2 - BitVec.ofNat 64 608) 24) :=
    ((st.toS.trans (StepS.same m₂ J.heap (k₂ .x2 (by decide)))).trans
      (StepS.same m₃ I₂.heap (k₃ .x2 (by decide)))).weaken fun a ha ↦ by
        rcases ha with (ha | ha) | ha
        · exact ha
        · exact False.elim ha
        · exact False.elim ha
  have hn₃ : heapNext u₃ = heapNext v := by simp only [heapNext, m₃, m₂]
  have rg (r : Reg) (hr : r ∈ ([.x8, .x18, .x20, .x22, .x24, .x25, .x26] : List Reg)) :
      u₃.getReg r = u.getReg r := by
    rw [k₃ r (mem_of_mem hr _), k₂ r (mem_of_mem hr _), hpv r (mem_of_mem hr _)]
  by_cases hz : n = 0
  · refine ⟨u₃, hrv.trans (hr₂.trans hr₃), Or.inr ⟨b80006f5c_pc_taken h₃ (by rw [x24₂]; exact hz),
      I₃, st₃, rg, x21₃, x23₃, x27₃, ?_⟩⟩
    rw [x9₃, x19₃]
    have hz' : n.toNat = 0 := by rw [hz]; rfl
    refine ⟨Nat.le_refl _, ⟨hP.1, Or.inl (by rw [hz'])⟩, ?_⟩
    rw [hz']; rfl
  have pc₃ := b80006f5c_pc_not_taken h₃ (by rw [x24₂]; exact hz)
  obtain ⟨u₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80006f74_spec pc₃ trivial
  have k₄ := b80006f74_keeps h₄
  have m₄ := b80006f74_mem_same h₄
  have I₄ := I₃.same m₄ (k₄ .x2 (by decide))
  have st₄ := (st₃.trans (StepS.same m₄ I₃.heap (k₄ .x2 (by decide)))).weaken fun a ha ↦ by
    rcases ha with ha | ha
    · exact ha
    · exact False.elim ha
  have hn₄ : heapNext u₄ = heapNext v := by rw [← hn₃]; simp only [heapNext, m₄]
  have hP₄ : NewBuf u u₄ (v.getMem (s.getReg .x2 - BitVec.ofNat 64 608 + 16)) (n.toNat * 24) 8 := by
    simp only [NewBuf] at hP ⊢; rw [hn₄]; exact hP
  obtain ⟨w, hrw, ⟨hpcw, hpw, Iw, stw, hw, -⟩ | hd⟩ := copyTail hM hpre I₄ (b80006f74_pc h₄)
    (frameW_slot hpre (k := 608) (n := 24) (by omega) (by omega)) st₄ hp hn hz
    hP₄ (by rw [b80006f74_x10 h₄, x19₃]) (by rw [b80006f74_x11 h₄, x27₃])
    (by rw [b80006f74_x12 h₄, rg .x18 (by decide), h18])
  swap
  · exact ⟨w, hrv.trans (hr₂.trans (hr₃.trans (hr₄.trans hrw))), Or.inl hd⟩
  have pw (r : Reg) (hr : r ∈ calleeSaved) : w.getReg r = u₃.getReg r := by
    rw [hpw r hr, k₄ r (mem_of_mem hr _)]
  refine ⟨w, hrv.trans (hr₂.trans (hr₃.trans (hr₄.trans hrw))), Or.inr ⟨by
    rw [hpcw, returnAddress_eq, b80006f74_x1 h₄]; decide, Iw, stw, fun r hr ↦ ?_,
    by rw [pw .x21 (by decide), x21₃], by rw [pw .x23 (by decide), x23₃],
    by rw [pw .x27 (by decide), x27₃], ?_⟩⟩
  · rw [pw r (by unfold calleeSaved; exact mem_of_mem hr _), rg r hr]
  · rw [pw .x9 (by decide), pw .x19 (by decide), x9₃, x19₃]
    exact hw

theorem copy5 (hT : TryAllocZeroedSpec) (hM : MemcpySpec 0x800126e4) {s u : MachineState}
    (hpre : BusBalancePre s) (h : Inv s u) (hpc : u.pc = 0x800049ac)
    (hx1 : u.getReg .x1 = 0x80006fe0) (h10 : u.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 608)
    (h13 : u.getReg .x13 = 8) (h14 : u.getReg .x14 = 24) {n cap ptr len : Word} {xs : List E}
    (h11 : u.getReg .x11 = n) (h23 : u.getReg .x23 = n) (h27 : u.getReg .x27 = ptr)
    (hp : NewVecR s u cap ptr len xs) (hn : n.toNat ≤ len.toNat) :
    ∃ w, Reaches Image.code u w ∧ (Dead Image.code w ∨ (w.pc = 0x80007010 ∧ Inv s w ∧
      StepS s u w (Within · (s.getReg .x2 - BitVec.ofNat 64 608) 24) ∧
      (∀ r ∈ ([.x8, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27] : List Reg),
        w.getReg r = u.getReg r) ∧
      NewVecR s w (w.getReg .x9) (w.getReg .x18) n (xs.take n.toNat) ∧
      NewBuf u w (w.getReg .x18) (n.toNat * 24) 8 ∧ w.getReg .x9 = n)) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  obtain ⟨v, hrv, ⟨hpcv, hpv, st, J, ok⟩ | hd⟩ := tryAllocCall hT hpre h (Reaches.refl u) hpc h10 h13 h14
  swap
  · exact ⟨v, hrv, Or.inl hd⟩
  have sp := J.sp
  have hpc' : v.pc = 0x80006fe0 := by rw [hpcv, returnAddress_eq, hx1]; decide
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80006fe0_spec hpc' (by
    rv_eval [sp]
    valid_access hval [hb1])
  have k₂ := b80006fe0_keeps h₂
  have m₂ := b80006fe0_mem_same h₂
  have e736 : s.getReg .x2 - 1344 + 736 = s.getReg .x2 - BitVec.ofNat 64 608 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  by_cases ht : v.getMem (s.getReg .x2 - BitVec.ofNat 64 608) = 0
  swap
  · have pc₂ := b80006fe0_pc_taken h₂ (by rw [sp, e736]; exact ht)
    exact ⟨u₂, hrv.trans hr₂, Or.inl (dead_of_fetch (by
      rw [pc₂]; exact Option.isNone_iff_eq_none.mp (by decide +kernel)))⟩
  obtain ⟨hcap, hP⟩ := ok ht
  rw [h11] at hcap hP
  have pc₂ := b80006fe0_pc_not_taken h₂ (by rw [sp, e736]; exact ht)
  have I₂ := J.same m₂ (k₂ .x2 (by decide))
  have sp₂ : u₂.getReg .x2 = s.getReg .x2 - 1344 := I₂.sp
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80006fe8_spec pc₂ (by
    rv_eval [sp₂]
    and_intros <;> valid_access hval [hb1])
  have k₃ := b80006fe8_keeps h₃
  have m₃ := b80006fe8_mem_same h₃
  have I₃ := I₂.same m₃ (k₃ .x2 (by decide))
  have x23₂ : u₂.getReg .x23 = n := by rw [k₂ .x23 (by decide), hpv .x23 (by decide), h23]
  have x9₃ : u₃.getReg .x9 = n := by
    rw [b80006fe8_x9 h₃, sp₂, m₂, show s.getReg .x2 - 1344 + 744 =
      s.getReg .x2 - BitVec.ofNat 64 608 + 8 by apply BitVec.eq_of_toNat_eq; addr_omega [hb1]]
    exact hcap
  have x18₃ : u₃.getReg .x18 = v.getMem (s.getReg .x2 - BitVec.ofNat 64 608 + 16) := by
    rw [b80006fe8_x18 h₃, sp₂, m₂, show s.getReg .x2 - 1344 + 752 =
      s.getReg .x2 - BitVec.ofNat 64 608 + 16 by apply BitVec.eq_of_toNat_eq; addr_omega [hb1]]
  have st₃ : StepS s u u₃ (Within · (s.getReg .x2 - BitVec.ofNat 64 608) 24) :=
    ((st.toS.trans (StepS.same m₂ J.heap (k₂ .x2 (by decide)))).trans
      (StepS.same m₃ I₂.heap (k₃ .x2 (by decide)))).weaken fun a ha ↦ by
        rcases ha with (ha | ha) | ha
        · exact ha
        · exact False.elim ha
        · exact False.elim ha
  have hn₃ : heapNext u₃ = heapNext v := by simp only [heapNext, m₃, m₂]
  have rg (r : Reg) (hr : r ∈ ([.x8, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27] :
      List Reg)) : u₃.getReg r = u.getReg r := by
    rw [k₃ r (mem_of_mem hr _), k₂ r (mem_of_mem hr _), hpv r (mem_of_mem hr _)]
  by_cases hz : n = 0
  · refine ⟨u₃, hrv.trans (hr₂.trans hr₃), Or.inr ⟨b80006fe8_pc_taken h₃ (by rw [x23₂]; exact hz),
      I₃, st₃, rg, ?_, ?_, x9₃⟩⟩
    · rw [x9₃, x18₃]
      have hz' : n.toNat = 0 := by rw [hz]; rfl
      refine ⟨Nat.le_refl _, ⟨hP.1, Or.inl (by rw [hz'])⟩, ?_⟩
      rw [hz']; rfl
    · rw [x18₃]
      have hz' : n.toNat = 0 := by rw [hz]; rfl
      exact ⟨hP.1, Or.inl (by rw [hz'])⟩
  have pc₃ := b80006fe8_pc_not_taken h₃ (by rw [x23₂]; exact hz)
  obtain ⟨u₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80006ff4_spec pc₃ trivial
  have k₄ := b80006ff4_keeps h₄
  have m₄ := b80006ff4_mem_same h₄
  have I₄ := I₃.same m₄ (k₄ .x2 (by decide))
  have st₄ := (st₃.trans (StepS.same m₄ I₃.heap (k₄ .x2 (by decide)))).weaken fun a ha ↦ by
    rcases ha with ha | ha
    · exact ha
    · exact False.elim ha
  have hn₄ : heapNext u₄ = heapNext v := by rw [← hn₃]; simp only [heapNext, m₄]
  have hP₄ : NewBuf u u₄ (v.getMem (s.getReg .x2 - BitVec.ofNat 64 608 + 16)) (n.toNat * 24) 8 := by
    simp only [NewBuf] at hP ⊢; rw [hn₄]; exact hP
  obtain ⟨w, hrw, ⟨hpcw, hpw, Iw, stw, hw, -⟩ | hd⟩ := copyTail hM hpre I₄ (b80006ff4_pc h₄)
    (frameW_slot hpre (k := 608) (n := 24) (by omega) (by omega)) st₄ hp hn hz
    hP₄ (by rw [b80006ff4_x10 h₄, x18₃]) (by rw [b80006ff4_x11 h₄, rg .x27 (by decide), h27])
    (by rw [b80006ff4_x12 h₄, rg .x23 (by decide), h23])
  swap
  · exact ⟨w, hrv.trans (hr₂.trans (hr₃.trans (hr₄.trans hrw))), Or.inl hd⟩
  have pw (r : Reg) (hr : r ∈ calleeSaved) : w.getReg r = u₃.getReg r := by
    rw [hpw r hr, k₄ r (mem_of_mem hr _)]
  refine ⟨w, hrv.trans (hr₂.trans (hr₃.trans (hr₄.trans hrw))), Or.inr ⟨by
    rw [hpcw, returnAddress_eq, b80006ff4_x1 h₄]; decide, Iw, stw, fun r hr ↦ ?_, ?_, ?_,
    by rw [pw .x9 (by decide), x9₃]⟩⟩
  · rw [pw r (by unfold calleeSaved; exact mem_of_mem hr _), rg r hr]
  · rw [pw .x9 (by decide), pw .x18 (by decide), x9₃, x18₃]
    exact hw
  · rw [pw .x18 (by decide), x18₃]
    have hm := stw.mono
    have hb := hw.buf
    simp only [NewBuf] at hP₄ hb ⊢
    refine ⟨hP₄.1, hP₄.2.imp_right fun h' ↦ ⟨h'.1, ?_⟩⟩
    rcases hb.2 with h0 | ⟨-, b2⟩
    · have : n.toNat = 0 := by omega
      exact absurd (BitVec.eq_of_toNat_eq this) hz
    · omega

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
