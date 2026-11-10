import Rv64Verifier.Proofs.Bus.VbbTail15

/-!
# `verify_bus_balance` past the GKR loop: `memory_final`'s claim

From `0x80006f88` (`Cl3`): `grow_one` on the claims' `Vec` (three claims at capacity three), the
claim of `memory_final` written to the new buffer (`0x80006f94`), then `copy5`, to `0x80007010`
(`Cl4`). The new buffer is allocated past `0x80006f88`, so the claims' writes extend a `StepS`
from there (`StepS.extend`).
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- A `Vec<E>` in registers whose buffer a step misses. -/
theorem NewVecR.keepD {s v w : MachineState} {B : Word → Prop} {cap ptr len : Word}
    {xs : List E} (h : NewVecR s v cap ptr len xs) (fr : DFrame v w B)
    (hm : heapNext v ≤ heapNext w) (hbuf : ∀ y, Within y ptr (cap.toNat * 24) → ¬ B y) :
    NewVecR s w cap ptr len xs := by
  have hb := h.buf
  have hle := h.le
  have hbd : ptr.toNat + cap.toNat * 24 ≤ 2 ^ 64 := by
    simp only [NewBuf, heapNext] at hb
    rcases hb.2 with h0 | ⟨b1, b2⟩
    · omega
    · have := (v.getMem nextAddr).isLt; omega
  refine ⟨hle, ?_, ?_⟩
  · simp only [NewBuf] at hb ⊢
    exact ⟨hb.1, hb.2.imp_right fun h' ↦ ⟨h'.1, by omega⟩⟩
  · rw [← h.elems]
    refine eListAt_congr fun i hi ↦ ?_
    have bw (j : Nat) (hj : j + 8 ≤ 24) : w.getMem (ptr + BitVec.ofNat 64 (24 * i) +
        BitVec.ofNat 64 j) = v.getMem (ptr + BitVec.ofNat 64 (24 * i) + BitVec.ofNat 64 j) :=
      fr _ fun k hk ↦ hbuf _ (by addr_omega [hbd, hi, hle, hj, hk])
    exact eAt_congr (by simpa using bw 0 (by omega)) (bw 8 (by omega)) (bw 16 (by omega))

/-- A step writing `A'` and heap allocated since `u` extends a `StepS` from `u`. -/
theorem StepS.extend {s u v w : MachineState} {A A' : Word → Prop} (st : StepS s u v A)
    (fr : DFrame v w fun a ↦ A' a ∨ (heapNext u ≤ a.toNat ∧ a.toNat < heapNext v))
    (hn : heapNext w = heapNext v) (sp : w.getReg .x2 = v.getReg .x2) :
    StepS s u w fun a ↦ A a ∨ A' a where
  frame := (st.frame.mono fun a ha ↦ by
      rcases ha with ha | ha | ha | ⟨f1, f2⟩
      · exact Or.inl (Or.inl ha)
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr ⟨f1, by rw [hn]; exact f2⟩))).trans fr fun a ha ↦ by
    rcases ha with ha | ⟨f1, f2⟩
    · exact Or.inl (Or.inr ha)
    · exact Or.inr (Or.inr (Or.inr ⟨f1, by rw [hn]; exact f2⟩))
  heap := ⟨hn ▸ st.heap.lo, hn ▸ st.heap.hi⟩
  mono := by rw [hn]; exact st.mono
  sp := sp.trans st.sp

/-- At `0x80007010`, four claims written, `point[..log_bytecode]` copied into `s1`, `s2`; the
claims' buffer, allocated past `0x80006f88`, in `s0`. -/
structure Cl4 (bev : MachineState → Word → List E → Option E) (s w y : MachineState) (k : Start)
    (state : GkrState) (mem : List E) (mf bf : E) : Prop where
  inv : Inv s y
  step : StepS s w y fun a ↦ Within a (s.getReg .x2 - 840) 24 ∨
    Within a (s.getReg .x2 - BitVec.ofNat 64 608) 24
  fresh : heapNext w ≤ (y.getMem (s.getReg .x2 - 832)).toNat
  claims : ClaimsOk s y (y.getMem (s.getReg .x2 - 840)) (y.getMem (s.getReg .x2 - 832))
    (y.getMem (s.getReg .x2 - 824))
    (memClaims s state mem ++ [⟨memoryFinalCounters, state.point.take (logMem s).toNat, mf⟩])
  len : y.getMem (s.getReg .x2 - 824) = 4
  x8 : y.getReg .x8 = y.getMem (s.getReg .x2 - 832)
  c4 : NewVecR s y (y.getReg .x9) (y.getReg .x18) (logBc s) (state.point.take (logBc s).toNat)
  c4Lo : PtrLo y (y.getReg .x18) (logBc s)
  apart4 : Apart (y.getReg .x18) ((y.getReg .x9).toNat * 24) (y.getMem (s.getReg .x2 - 832))
    (56 * (y.getMem (s.getReg .x2 - 840)).toNat)
  regs : ∀ r ∈ ([.x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27] : List Reg),
    y.getReg r = w.getReg r

theorem claim4 (hG : GrowOneFreshSpec 0x8000c0a4 56 8) (hT : TryAllocZeroedSpec)
    (hM : MemcpySpec 0x800126e4) {bev : MachineState → Word → List E → Option E}
    {s w : MachineState} {k : Start} {state : GkrState} {mem : List E} {mf bf : E}
    (hpre : BusBalancePre s) (C : Cl3 bev s w k state mem mf bf) (hpc : w.pc = 0x80006f88) :
    ∃ y, Reaches Image.code w y ∧ (Dead Image.code y ∨
      (y.pc = 0x80007010 ∧ Cl4 bev s w y k state mem mf bf)) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have sp := C.inv.sp
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80006f88_spec hpc trivial
  have k₁ := b80006f88_keeps h₁
  have m₁ := b80006f88_mem_same h₁
  have I₁ := C.inv.same m₁ (k₁ .x2 (by decide))
  have a8 : s.getReg .x2 - BitVec.ofNat 64 840 + 8 = s.getReg .x2 - 832 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have CL : ClaimsOk s u₁ (vecCap u₁ (s.getReg .x2 - BitVec.ofNat 64 840))
      (vecPtr u₁ (s.getReg .x2 - BitVec.ofNat 64 840)) 3 (memClaims s state mem) := by
    have := C.claims.keepR hpre (StepR.same (A := fun _ ↦ False) m₁ C.inv.heap (k₁ .x2 (by decide)))
      (fun _ h ↦ h.elim)
    rw [C.len] at this
    simp only [vecCap, vecPtr, m₁, a8]
    exact this
  have hraw : RawVecOk u₁ (s.getReg .x2 - BitVec.ofNat 64 840) 56 8 := by
    have hb := CL.claims.buf
    have hlo := hpre.heap.lo
    simp only [RawVecOk, Buf, NewBuf] at hb ⊢
    refine ⟨hb.1, hb.2.imp (by omega) fun h' ↦ ⟨by omega, by omega⟩⟩
  obtain ⟨v, hrv, ⟨hpcv, hpv, stv, Iv, hcap, hby, hfresh⟩ | hd⟩ := growOneCall hG hpre I₁
    (Reaches.refl u₁) (b80006f88_pc h₁)
    (by rw [b80006f88_x10 h₁, sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
    hraw
  swap
  · exact ⟨v, hr₁.trans hrv, Or.inl hd⟩
  have hpc' : v.pc = 0x80006f94 := by rw [hpcv, returnAddress_eq, b80006f88_x1 h₁]; decide
  have spv : v.getReg .x2 = s.getReg .x2 - 1344 := Iv.sp
  have f16 : FrameW s (Within · (s.getReg .x2 - BitVec.ofNat 64 840) 16) := fun a ha ↦ by
    addr_omega [ha, hb1]
  have G := CL.grow hpre stv.toR f16 (by omega) hby hfresh I₁.mono
  have hle3 := CL.claims.le
  have h3 : (3 : Word).toNat = 3 := rfl
  rw [h3] at hle3
  -- the new buffer
  have hlo := hpre.heap.lo
  have hhi := Iv.heap.hi
  have hmo := I₁.mono
  have hnw : heapNext u₁ = heapNext w := by simp only [heapNext, m₁]
  obtain ⟨P', eP⟩ : ∃ P', vecPtr v (s.getReg .x2 - BitVec.ofNat 64 840) = P' := ⟨_, rfl⟩
  obtain ⟨C', eC⟩ : ∃ C', vecCap v (s.getReg .x2 - BitVec.ofNat 64 840) = C' := ⟨_, rfl⟩
  rw [eP, eC] at G hfresh
  rw [eC] at hcap
  obtain ⟨q0, q1, q2⟩ : P'.toNat % 8 = 0 ∧ heapNext u₁ ≤ P'.toNat ∧
      P'.toNat + C'.toNat * 56 ≤ heapNext v := by
    simp only [NewBuf] at hfresh
    rcases hfresh.2 with h0 | h0
    · omega
    · exact ⟨hfresh.1, h0⟩
  simp only [heapNext, heapEnd, heapStart] at hlo hhi hmo q1 q2 hnw
  have hheap : ValidMemRange P' 28 :=
    heapRange q0 (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega)
  have m512 : v.getMem (s.getReg .x2 - 832) = P' := by rw [← eP, vecPtr, a8]
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80006f94_spec hpc' (by
    rv_eval [spv, m512]
    and_intros <;> first
      | valid_access hval [hb1]
      | valid_access hheap [q0, q1, q2, hcap, hle3, hhi]
      | addr_omega [hb1, q1, q2, hcap, hle3, hhi, hlo, hmo])
  have k₂ := b80006f94_keeps h₂
  have fr₂ : DFrame v u₂ fun a ↦ Within a (s.getReg .x2 - 824) 8 ∨
      Within a (P' + BitVec.ofNat 64 (56 * 3)) 56 := fun a ha ↦
    h₂.frame a (by
      rv_eval [spv, m512]
      and_intros <;> intro he <;> exact ha 0 (by decide) (by
        rw [add_ofNat_zero, he]; addr_omega [hb1, q1, q2, hcap, hle3, hhi]))
  have hx := hpre.stack.next
  rw [stackLo_eq] at hx
  have hnz : u₂.getMem nextAddr = v.getMem nextAddr :=
    fr₂ nextAddr fun i hi hw ↦ by
      rcases hw with hw | hw <;> addr_omega [hw, hi, hx, hb1, q1, q2, hcap, hle3, hhi]
  have hn₂ : heapNext u₂ = heapNext v := by simp only [heapNext, hnz]
  have st₂ : StepS s u₁ u₂ fun a ↦ Within a (s.getReg .x2 - BitVec.ofNat 64 840) 16 ∨
      Within a (s.getReg .x2 - 824) 8 :=
    stv.extend (fr₂.mono fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inl ha
      · exact Or.inr ⟨by simp only [heapNext]; addr_omega [ha, q1, q2, hhi, hcap, hle3],
          by simp only [heapNext]; addr_omega [ha, q1, q2, hhi, hcap, hle3]⟩) hn₂
      ((k₂ .x2 (by decide)))
  have f2 : FrameW s fun a ↦ Within a (s.getReg .x2 - BitVec.ofNat 64 840) 16 ∨
      Within a (s.getReg .x2 - 824) 8 := fun a ha ↦ by
    rcases ha with ha | ha <;> addr_omega [ha, hb1]
  have I₂ := I₁.afterR hpre f2 st₂.toR
  have sm₁ : ∀ {A : Word → Prop}, StepR s w u₁ A := StepR.same m₁ C.inv.heap (k₁ .x2 (by decide))
  have c3₂ := (C.c3.keepR hpre sm₁ (A := fun _ ↦ False) (fun _ h ↦ h.elim)).keepR hpre st₂.toR f2
  have pt₂ := (C.point.keepR hpre sm₁ (A := fun _ ↦ False) (fun _ h ↦ h.elim)).keepR hpre st₂.toR f2
  have mb {j val : Word} (h : u₂.getMem (v.getMem (v.getReg .x2 + 512) + j) = val) :
      u₂.getMem (P' + j) = val := by
    rwa [spv, show s.getReg .x2 - 1344 + 512 = s.getReg .x2 - 832 by
      apply BitVec.eq_of_toNat_eq; addr_omega [hb1], m512] at h
  have rv (r : Reg) (hr : r ∈ ([.x9, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27] :
      List Reg)) : v.getReg r = w.getReg r := by
    rw [hpv r (by unfold calleeSaved; exact mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
  have e0 : u₂.getMem (P' + BitVec.ofNat 64 (56 * 3)) = w.getReg .x9 :=
    (mb (b80006f94_m7 h₂)).trans (rv .x9 (by decide))
  have e8 : u₂.getMem (P' + BitVec.ofNat 64 (56 * 3 + 8)) = w.getReg .x19 :=
    (mb (b80006f94_m6 h₂)).trans (rv .x19 (by decide))
  have hc3 : ClaimAt s u₂ (P' + BitVec.ofNat 64 (56 * 3))
      ⟨memoryFinalCounters, state.point.take (logMem s).toNat, mf⟩ := by
    refine c3₂.claimAt' hpre.heap.lo
      (C.c3Lo.mono ((sm₁ (A := fun _ ↦ False)).mono.trans st₂.mono)) e0 e8 ((mb (b80006f94_m5 h₂)).trans ((rv .x24 (by decide)).trans C.x24))
      ((congrArg BitVec.toNat (mb (b80006f94_m4 h₂))).trans rfl) ?_
    rw [eAt_eOf3, C.mfEq, ← rv .x25 (by decide), ← rv .x22 (by decide)]
    congr 1
    · exact mb (b80006f94_m3 h₂)
    · rw [show P' + BitVec.ofNat 64 (56 * 3 + 32) + 8 = P' + 208 by rw [BitVec.add_assoc]; rfl]
      exact mb (b80006f94_m2 h₂)
    · rw [show P' + BitVec.ofNat 64 (56 * 3 + 32) + 16 = P' + 216 by rw [BitVec.add_assoc]; rfl,
        mb (b80006f94_m1 h₂), spv]
      exact (congrArg v.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])).trans
        ((stv.slot hpre (fun z hz h' ↦ by addr_omega [hz, h', hb1])
          (by constructor <;> addr_omega [hb1])).trans (m₁ _))
  have hca : Apart (vecPtr u₂ (P' + BitVec.ofNat 64 (56 * 3)))
      ((vecCap u₂ (P' + BitVec.ofNat 64 (56 * 3))).toNat * 24) P' (56 * C'.toNat) := by
    simp only [vecPtr, vecCap]
    rw [e0, show P' + BitVec.ofNat 64 (56 * 3) + 8 = P' + BitVec.ofNat 64 (56 * 3 + 8) by
      rw [BitVec.add_assoc]; rfl, e8]
    have hb := C.c3.buf
    simp only [NewBuf, heapNext] at hb
    simp only [Apart]
    rcases hb.2 with h0 | ⟨b1, b2⟩
    · exact Or.inl h0
    · exact Or.inr (Or.inr (Or.inl (by omega)))
  have l4 : u₂.getMem (s.getReg .x2 - 824) = 4 := by
    rw [show s.getReg .x2 - 824 = v.getReg .x2 + 520 by
      rw [spv]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]]
    exact b80006f94_m_x2_520 h₂
  have CS4 := G.push hpre Iv.heap (by rw [h3]; omega) fr₂ (fun a ha ↦ by addr_omega [ha, hb1]) hn₂
    (by rw [h3]; exact hc3) (by rw [h3]; exact hca) (len' := u₂.getMem (s.getReg .x2 - 824))
    (by rw [l4, h3]; rfl)
  have hlen : state.point.length = (w.getMem (s.getReg .x2 - 1144)).toNat := by
    rw [← C.point.elems, eListAt_length]
  have lb₂ : v.getReg .x23 = logBc s := (rv .x23 (by decide)).trans C.x23
  obtain ⟨y, hry, hd | ⟨hpcy, Iy, sty, rgy, c4, c4Lo, fresh4, x9y⟩⟩ := copy5 hT hM hpre I₂
    (b80006f94_pc h₂) (b80006f94_x1 h₂)
    (by rw [b80006f94_x10 h₂, spv]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
    (b80006f94_x13 h₂) (b80006f94_x14 h₂) ((b80006f94_x11 h₂).trans lb₂)
    ((k₂ .x23 (by decide)).trans lb₂)
    ((k₂ .x27 (by decide)).trans ((rv .x27 (by decide)).trans C.x27)) pt₂
    (by rw [← hlen]; exact C.lb)
  · exact ⟨y, hr₁.trans (hrv.trans (hr₂.trans hry)), Or.inl hd⟩
  have f608 : FrameW s (Within · (s.getReg .x2 - BitVec.ofNat 64 608) 24) := fun a ha ↦ by
    addr_omega [ha, hb1]
  have sy (x : Word) (hx : (s.getReg .x2 - 1344).toNat ≤ x.toNat ∧
      x.toNat + 8 ≤ (s.getReg .x2 - 608).toNat) : y.getMem x = u₂.getMem x :=
    sty.slot hpre (fun z hz h' ↦ by addr_omega [hz, h', hx, hb1])
      (by constructor <;> addr_omega [hb1, hx])
  have y832 : y.getMem (s.getReg .x2 - 832) = P' := by
    rw [sy _ (by constructor <;> addr_omega [hb1]), fr₂ _ fun i hi hw ↦ by
      rcases hw with hw | hw <;> addr_omega [hw, hi, hb1, q1, q2, hcap, hle3, hhi]]
    exact m512
  have y840 : y.getMem (s.getReg .x2 - 840) = C' := by
    rw [sy _ (by constructor <;> addr_omega [hb1]), fr₂ _ fun i hi hw ↦ by
      rcases hw with hw | hw <;> addr_omega [hw, hi, hb1, q1, q2, hcap, hle3, hhi], ← eC]
    rfl
  have y824 : y.getMem (s.getReg .x2 - 824) = 4 := by
    rw [sy _ (by constructor <;> addr_omega [hb1])]; exact l4
  have hn₃ := sty.mono
  refine ⟨y, hr₁.trans (hrv.trans (hr₂.trans hry)), Or.inr ⟨hpcy, {
    inv := Iy
    step := (((StepS.same m₁ C.inv.heap (k₁ .x2 (by decide))).trans st₂).trans sty).weaken
      fun a ha ↦ by
        rcases ha with (ha | ha | ha) | ha
        · exact False.elim ha
        · exact Or.inl (by addr_omega [ha, hb1])
        · exact Or.inl (by addr_omega [ha, hb1])
        · exact Or.inr ha
    fresh := by rw [y832]; simp only [heapNext]; omega
    claims := by
      rw [y840, y832, sy _ (by constructor <;> addr_omega [hb1])]
      exact CS4.keepR hpre sty.toR f608
    len := y824
    x8 := by
      rw [y832, rgy .x8 (by decide), b80006f94_x8 h₂, spv,
        show s.getReg .x2 - 1344 + 512 = s.getReg .x2 - 832 by
          apply BitVec.eq_of_toNat_eq; addr_omega [hb1]]
      exact m512
    c4 := c4
    c4Lo := c4Lo
    apart4 := by
      rw [y832, y840, x9y]
      have hb := fresh4
      simp only [NewBuf, heapNext] at hb
      simp only [Apart]
      rcases hb.2 with h0 | ⟨b1, b2⟩
      · exact Or.inl h0
      · simp only [heapNext] at hn₂
        exact Or.inr (Or.inr (Or.inr (by omega)))
    regs := fun r hr ↦ by
      rw [rgy r (mem_of_mem hr _), k₂ r (mem_of_mem hr _), rv r (mem_of_mem hr _)] }⟩⟩

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
