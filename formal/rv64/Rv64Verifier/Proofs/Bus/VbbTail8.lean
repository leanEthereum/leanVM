import Rv64Verifier.Proofs.Bus.VbbTail7

/-!
# `verify_bus_balance` past the GKR loop: copies of the point's prefix

`point[..n].to_vec()`, inlined: `try_allocate_in` into `S - 608` (an `Err` traps), the capacity
and the buffer loaded into registers, and for `n ≠ 0` a `memcpy` of `24 n` bytes from the point's
buffer (`copyTail`). `copy1` is the first site (`0x80006cb8`'s call, the new `Vec` in `s0`, `s5`).
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem toNat_mul24 {n : Word} (h : n.toNat * 24 < 2 ^ 64) :
    (n * 16 + n * 8).toNat = 24 * n.toNat := by
  simp only [BitVec.toNat_add, BitVec.toNat_mul]
  have e16 : (16 : Word).toNat = 16 := rfl
  have e8 : (8 : Word).toNat = 8 := rfl
  rw [e16, e8]
  omega

/-- The `memcpy` of `n` elements of a point into a buffer allocated since `y`. -/
theorem copyTail (hM : MemcpySpec 0x800126e4) {s y u : MachineState} (hpre : BusBalancePre s)
    (h : Inv s u) (hpc : u.pc = 0x800126e4) {A : Word → Prop} (hA : FrameW s A)
    (st : StepS s y u A) {n cap ptr len P : Word} {xs : List E} (hp : NewVecR s y cap ptr len xs)
    (hn : n.toNat ≤ len.toNat) (hn0 : n ≠ 0) (hP : NewBuf y u P (n.toNat * 24) 8)
    (h10 : u.getReg .x10 = P) (h11 : u.getReg .x11 = ptr) (h12 : u.getReg .x12 = n * 16 + n * 8) :
    ∃ w, Reaches Image.code u w ∧ ((w.pc = returnAddress u ∧ Preserves u w ∧ Inv s w ∧
      StepS s y w A ∧ NewVecR s w n P n (xs.take n.toNat) ∧
      ∀ x, (s.getReg .x2 - 1344).toNat ≤ x.toNat → x.toNat + 8 ≤ (s.getReg .x2).toNat →
        w.getMem x = u.getMem x) ∨ Dead Image.code w) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hle := hp.le
  have hbuf := hp.buf
  have hpos : 0 < n.toNat := by
    rcases Nat.eq_zero_or_pos n.toNat with h0 | h0
    · exact absurd (BitVec.eq_of_toNat_eq h0) hn0
    · exact h0
  have hhi := h.heap.hi
  have hlo := hpre.heap.lo
  have hmu := st.mono
  simp only [NewBuf] at hbuf hP
  obtain ⟨b0, b1, b2⟩ : ptr.toNat % 8 = 0 ∧ heapNext s ≤ ptr.toNat ∧
      ptr.toNat + cap.toNat * 24 ≤ heapNext y := by
    rcases hbuf.2 with h0 | h0
    · omega
    · exact ⟨hbuf.1, h0⟩
  obtain ⟨p0, p1, p2⟩ : P.toNat % 8 = 0 ∧ heapNext y ≤ P.toNat ∧
      P.toNat + n.toNat * 24 ≤ heapNext u := by
    rcases hP.2 with h0 | h0
    · omega
    · exact ⟨hP.1, h0⟩
  simp only [heapNext, heapEnd, heapStart] at hhi hlo hmu b1 b2 p1 p2
  have e12 : (u.getReg .x12).toNat = 24 * n.toNat := by rw [h12]; exact toNat_mul24 (by omega)
  obtain ⟨w, hrw, ⟨hpcw, hpw, fr, hnx, hsp, hel⟩ | hd⟩ := memcpyCall hM hpre h (Reaches.refl u) hpc
    (y := y) e12 (by rw [h10]; simp only [heapNext]; omega)
    (by rw [h10]; simp only [heapNext]; omega)
    (by rw [h11]; simp only [heapStart]; omega) (by rw [h11]; simp only [heapNext]; omega)
    (by rw [h10]; exact p0) (by rw [h11]; exact b0)
  swap
  · exact ⟨w, hrw, Or.inr hd⟩
  rw [h10] at fr
  rw [h10, h11] at hel
  have hn' : heapNext w = heapNext u := hnx
  have stw : StepS s y w A :=
    st.copy (d := P) (m := 24 * n.toNat) (by simp only [heapNext]; omega)
      (by simp only [heapNext]; omega) fr (by omega) hnx hsp
  have hos := hpre.stack.above
  rw [stackLo_eq] at hos
  simp only [heapEnd] at hos
  have I : Inv s w := h.step hpre fr (fun a ha ↦ by
      rcases ha with ha | ha
      · refine ⟨Or.inr (Or.inr (Or.inr (Or.inr ?_))), by addr_omega [ha, p2, hhi, hb1]⟩
        show heapNext s ≤ a.toNat ∧ a.toNat < heapNext w
        simp only [Within, heapNext] at ha hn' ⊢
        omega
      · exact ⟨Or.inr (Or.inr (Or.inl (by rw [stackLo_eq]; addr_omega [ha, hb1]))),
          by addr_omega [ha, hb1]⟩)
    ⟨by rw [hn']; exact h.heap.lo, by rw [hn']; exact h.heap.hi⟩ (by rw [hn']) hsp
  refine ⟨w, hrw, Or.inl ⟨hpcw, hpw, I, stw, ⟨Nat.le_refl _, ?_, ?_⟩, fun x h1 h2 ↦
    fr x fun i hi hw ↦ ?_⟩⟩
  · simp only [NewBuf, heapNext] at hn' ⊢
    exact ⟨p0, Or.inr ⟨by omega, by omega⟩⟩
  · rw [hel, st.toR.eListAt hpre hA hp.buf (by omega),
      eListAt_take _ _ hn, hp.elems]
  · rcases hw with hw | hw
    · addr_omega [hw, hi, h1, h2, p2, hhi, hos, hb1]
    · addr_omega [hw, hi, h1, h2, hb1]

/-- The first copy, `memory_low.to_vec()` for `memory[0]`'s claim. -/
theorem copy1 (hT : TryAllocZeroedSpec) (hM : MemcpySpec 0x800126e4) {s u : MachineState}
    (hpre : BusBalancePre s) (h : Inv s u) (hpc : u.pc = 0x800049ac)
    (hx1 : u.getReg .x1 = 0x80006cf8) (h10 : u.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 608)
    (h13 : u.getReg .x13 = 8) (h14 : u.getReg .x14 = 24) {n cap ptr len : Word} {xs : List E}
    (h9 : u.getReg .x9 = n) (h11 : u.getReg .x11 = n) (h27 : u.getReg .x27 = ptr)
    (hp : NewVecR s u cap ptr len xs) (hn : n.toNat ≤ len.toNat) :
    ∃ w, Reaches Image.code u w ∧ (Dead Image.code w ∨ (w.pc = 0x80006d2c ∧ Inv s w ∧
      StepS s u w (Within · (s.getReg .x2 - BitVec.ofNat 64 608) 24) ∧
      (∀ r ∈ ([.x9, .x19, .x20, .x22, .x23, .x24, .x25, .x26, .x27] : List Reg),
        w.getReg r = u.getReg r) ∧
      w.getReg .x18 = n * 16 + n * 8 ∧
      NewVecR s w (w.getReg .x8) (w.getReg .x21) n (xs.take n.toNat))) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  obtain ⟨v, hrv, ⟨hpcv, hpv, st, J, ok⟩ | hd⟩ := tryAllocCall hT hpre h (Reaches.refl u) hpc h10 h13 h14
  swap
  · exact ⟨v, hrv, Or.inl hd⟩
  have sp := J.sp
  have hpc' : v.pc = 0x80006cf8 := by rw [hpcv, returnAddress_eq, hx1]; decide
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80006cf8_spec hpc' (by
    rv_eval [sp]
    valid_access hval [hb1])
  have k₂ := b80006cf8_keeps h₂
  have m₂ := b80006cf8_mem_same h₂
  have e736 : s.getReg .x2 - 1344 + 736 = s.getReg .x2 - BitVec.ofNat 64 608 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  by_cases ht : v.getMem (s.getReg .x2 - BitVec.ofNat 64 608) = 0
  swap
  · have pc₂ := b80006cf8_pc_taken h₂ (by rw [sp, e736]; exact ht)
    exact ⟨u₂, hrv.trans hr₂, Or.inl (dead_of_fetch (by
      rw [pc₂]; exact Option.isNone_iff_eq_none.mp (by decide +kernel)))⟩
  obtain ⟨hcap, hP⟩ := ok ht
  rw [h11] at hcap hP
  have pc₂ := b80006cf8_pc_not_taken h₂ (by rw [sp, e736]; exact ht)
  have I₂ := J.same m₂ (k₂ .x2 (by decide))
  have sp₂ : u₂.getReg .x2 = s.getReg .x2 - 1344 := I₂.sp
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80006d00_spec pc₂ (by
    rv_eval [sp₂]
    and_intros <;> valid_access hval [hb1])
  have k₃ := b80006d00_keeps h₃
  have m₃ := b80006d00_mem_same h₃
  have I₃ := I₂.same m₃ (k₃ .x2 (by decide))
  have x9₂ : u₂.getReg .x9 = n := by rw [k₂ .x9 (by decide), hpv .x9 (by decide), h9]
  have x8₃ : u₃.getReg .x8 = n := by
    rw [b80006d00_x8 h₃, sp₂, m₂, show s.getReg .x2 - 1344 + 744 =
      s.getReg .x2 - BitVec.ofNat 64 608 + 8 by apply BitVec.eq_of_toNat_eq; addr_omega [hb1]]
    exact hcap
  have x21₃ : u₃.getReg .x21 = v.getMem (s.getReg .x2 - BitVec.ofNat 64 608 + 16) := by
    rw [b80006d00_x21 h₃, sp₂, m₂, show s.getReg .x2 - 1344 + 752 =
      s.getReg .x2 - BitVec.ofNat 64 608 + 16 by apply BitVec.eq_of_toNat_eq; addr_omega [hb1]]
  have x18₃ : u₃.getReg .x18 = n * 16 + n * 8 := by rw [b80006d00_x18 h₃, x9₂]
  have st₃ : StepS s u u₃ (Within · (s.getReg .x2 - BitVec.ofNat 64 608) 24) :=
    ((st.toS.trans (StepS.same m₂ J.heap (k₂ .x2 (by decide)))).trans
      (StepS.same m₃ I₂.heap (k₃ .x2 (by decide)))).weaken fun a ha ↦ by
        rcases ha with (ha | ha) | ha
        · exact ha
        · exact False.elim ha
        · exact False.elim ha
  have hn₃ : heapNext u₃ = heapNext v := by simp only [heapNext, m₃, m₂]
  have rg (r : Reg) (hr : r ∈ ([.x9, .x19, .x20, .x22, .x23, .x24, .x25, .x26, .x27] : List Reg)) :
      u₃.getReg r = u.getReg r := by
    rw [k₃ r (mem_of_mem hr _), k₂ r (mem_of_mem hr _), hpv r (mem_of_mem hr _)]
  by_cases hz : n = 0
  · refine ⟨u₃, hrv.trans (hr₂.trans hr₃), Or.inr ⟨b80006d00_pc_taken h₃ (by rw [x9₂]; exact hz),
      I₃, st₃, rg, x18₃, ?_⟩⟩
    rw [x8₃, x21₃]
    have hz' : n.toNat = 0 := by rw [hz]; rfl
    refine ⟨Nat.le_refl _, ⟨hP.1, Or.inl (by rw [hz'])⟩, ?_⟩
    rw [hz']; rfl
  have pc₃ := b80006d00_pc_not_taken h₃ (by rw [x9₂]; exact hz)
  obtain ⟨u₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80006d18_spec pc₃ trivial
  have k₄ := b80006d18_keeps h₄
  have m₄ := b80006d18_mem_same h₄
  have I₄ := I₃.same m₄ (k₄ .x2 (by decide))
  have st₄ := (st₃.trans (StepS.same m₄ I₃.heap (k₄ .x2 (by decide)))).weaken fun a ha ↦ by
    rcases ha with ha | ha
    · exact ha
    · exact False.elim ha
  have hn₄ : heapNext u₄ = heapNext v := by rw [← hn₃]; simp only [heapNext, m₄]
  have hP₄ : NewBuf u u₄ (v.getMem (s.getReg .x2 - BitVec.ofNat 64 608 + 16)) (n.toNat * 24) 8 := by
    simp only [NewBuf] at hP ⊢; rw [hn₄]; exact hP
  obtain ⟨w, hrw, ⟨hpcw, hpw, Iw, stw, hw, -⟩ | hd⟩ := copyTail hM hpre I₄ (b80006d18_pc h₄)
    (frameW_slot hpre (k := 608) (n := 24) (by omega) (by omega)) st₄ hp hn hz
    hP₄ (by rw [b80006d18_x10 h₄, x21₃]) (by rw [b80006d18_x11 h₄, k₃ .x27 (by decide),
      k₂ .x27 (by decide), hpv .x27 (by decide), h27])
    (by rw [b80006d18_x12 h₄, x18₃])
  swap
  · exact ⟨w, hrv.trans (hr₂.trans (hr₃.trans (hr₄.trans hrw))), Or.inl hd⟩
  refine ⟨w, hrv.trans (hr₂.trans (hr₃.trans (hr₄.trans hrw))), Or.inr ⟨by
    rw [hpcw, returnAddress_eq, b80006d18_x1 h₄]; decide, Iw, stw, fun r hr ↦ ?_, ?_, ?_⟩⟩
  · rw [hpw r (by unfold calleeSaved; exact mem_of_mem hr _), k₄ r (mem_of_mem hr _), rg r hr]
  · rw [hpw .x18 (by decide), k₄ .x18 (by decide), x18₃]
  · rw [hpw .x8 (by decide), hpw .x21 (by decide), k₄ .x8 (by decide), k₄ .x21 (by decide), x8₃,
      x21₃]
    exact hw

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
