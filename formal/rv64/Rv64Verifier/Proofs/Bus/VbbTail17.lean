import Rv64Verifier.Proofs.Bus.VbbTail16

/-!
# `verify_bus_balance` past the GKR loop: `bytecode_final`'s claim

From `0x80007010` (`Cl4`) to `0x8000702c` (`to702c`): `grow_one` when the four claims fill their
buffer, the buffer in `s0`. There the claim of `bytecode_final` is written (`claim5`) and
`index_mle(point[..log_memory])` called.
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The four claims before `bytecode_final`'s. -/
def claims4 (s : MachineState) (state : GkrState) (mem : List E) (mf : E) : List ColumnClaim :=
  memClaims s state mem ++ [⟨memoryFinalCounters, state.point.take (logMem s).toNat, mf⟩]

/-- At `0x8000702c`, the claims' buffer in `s0` with room for a fifth. -/
structure At702c (s w z : MachineState) (state : GkrState) (mem : List E) (mf : E) : Prop where
  inv : Inv s z
  step : StepS s w z fun a ↦ Within a (s.getReg .x2 - 840) 24 ∨
    Within a (s.getReg .x2 - BitVec.ofNat 64 608) 24
  fresh : heapNext w ≤ (z.getReg .x8).toNat
  claims : ClaimsOk s z (z.getMem (s.getReg .x2 - 840)) (z.getReg .x8) 4 (claims4 s state mem mf)
  ptr : z.getMem (s.getReg .x2 - 832) = z.getReg .x8
  len : z.getMem (s.getReg .x2 - 824) = 4
  lt : 4 < (z.getMem (s.getReg .x2 - 840)).toNat
  c4 : NewVecR s z (z.getReg .x9) (z.getReg .x18) (logBc s) (state.point.take (logBc s).toNat)
  apart4 : Apart (z.getReg .x18) ((z.getReg .x9).toNat * 24) (z.getReg .x8)
    (56 * (z.getMem (s.getReg .x2 - 840)).toNat)
  x19 : z.getReg .x19 = 4
  regs : ∀ r ∈ ([.x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27] : List Reg),
    z.getReg r = w.getReg r

theorem to702c (hG : GrowOneFreshSpec 0x8000c0a4 56 8)
    {bev : MachineState → Word → List E → Option E} {s w y : MachineState} {k : Start}
    {state : GkrState} {mem : List E} {mf bf : E} (hpre : BusBalancePre s)
    (C : Cl4 bev s w y k state mem mf bf) (hpc : y.pc = 0x80007010) :
    ∃ z, Reaches Image.code y z ∧ (Dead Image.code z ∨
      (z.pc = 0x8000702c ∧ At702c s w z state mem mf)) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have sp := C.inv.sp
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80007010_spec hpc (by
    rv_eval [sp]
    valid_access hval [hb1])
  have k₁ := b80007010_keeps h₁
  have m₁ := b80007010_mem_same h₁
  have I₁ := C.inv.same m₁ (k₁ .x2 (by decide))
  have CL := C.claims
  rw [C.len, ← C.x8] at CL
  have hle4 := CL.claims.le
  have h4 : (4 : Word).toNat = 4 := rfl
  rw [h4] at hle4
  have e504 : y.getMem (y.getReg .x2 + 504) = y.getMem (s.getReg .x2 - 840) := by
    rw [sp]; exact congrArg y.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
  have sm₁ : ∀ {A : Word → Prop}, StepR s y u₁ A := StepR.same m₁ C.inv.heap (k₁ .x2 (by decide))
  by_cases hc : y.getMem (s.getReg .x2 - 840) = 4
  swap
  · -- room left
    have pc₁ := b80007010_pc_taken h₁ (by rw [e504]; exact hc)
    have hlt : 4 < (y.getMem (s.getReg .x2 - 840)).toNat := by
      rcases Nat.lt_or_ge 4 (y.getMem (s.getReg .x2 - 840)).toNat with h0 | h0
      · exact h0
      · exact absurd (BitVec.eq_of_toNat_eq (by rw [h4]; omega)) hc
    refine ⟨u₁, hr₁, Or.inr ⟨pc₁, {
      inv := I₁
      step := C.step.trans (StepS.same m₁ C.inv.heap (k₁ .x2 (by decide))) |>.weaken
        fun a ha ↦ by rcases ha with ha | ha; exact ha; exact False.elim ha
      fresh := by rw [k₁ .x8 (by decide), C.x8]; exact C.fresh
      claims := by
        simp only [m₁]; rw [k₁ .x8 (by decide)]
        exact CL.keepR hpre (sm₁ (A := fun _ ↦ False)) (fun _ h ↦ h.elim)
      ptr := by rw [m₁, k₁ .x8 (by decide)]; exact C.x8.symm
      len := by rw [m₁]; exact C.len
      lt := by rw [m₁]; exact hlt
      c4 := by
        rw [k₁ .x9 (by decide), k₁ .x18 (by decide)]
        exact C.c4.keepR hpre (sm₁ (A := fun _ ↦ False)) (fun _ h ↦ h.elim)
      apart4 := by
        rw [k₁ .x9 (by decide), k₁ .x18 (by decide), k₁ .x8 (by decide), m₁, C.x8]
        exact C.apart4
      x19 := b80007010_x19 h₁
      regs := fun r hr ↦ by rw [k₁ r (mem_of_mem hr _)]; exact C.regs r hr }⟩⟩
  -- full: `grow_one`
  have pc₁ := b80007010_pc_not_taken h₁ (by rw [e504]; exact hc)
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000701c_spec pc₁ trivial
  have k₂ := b8000701c_keeps h₂
  have m₂ := b8000701c_mem_same h₂
  have I₂ := I₁.same m₂ (k₂ .x2 (by decide))
  have a8 : s.getReg .x2 - BitVec.ofNat 64 840 + 8 = s.getReg .x2 - 832 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have m12 (a : Word) : u₂.getMem a = y.getMem a := by rw [m₂, m₁]
  have CL₂ : ClaimsOk s u₂ (vecCap u₂ (s.getReg .x2 - BitVec.ofNat 64 840))
      (vecPtr u₂ (s.getReg .x2 - BitVec.ofNat 64 840)) 4 (claims4 s state mem mf) := by
    have := C.claims.keepR hpre (StepR.same (A := fun _ ↦ False) m12 C.inv.heap
      (by rw [k₂ .x2 (by decide), k₁ .x2 (by decide)])) (fun _ h ↦ h.elim)
    rw [C.len] at this
    simp only [vecCap, vecPtr, m12, a8]
    exact this
  have hraw : RawVecOk u₂ (s.getReg .x2 - BitVec.ofNat 64 840) 56 8 := by
    have hb := CL₂.claims.buf
    have hlo := hpre.heap.lo
    simp only [RawVecOk, Buf, NewBuf] at hb ⊢
    refine ⟨hb.1, hb.2.imp (by omega) fun h' ↦ ⟨by omega, by omega⟩⟩
  obtain ⟨v, hrv, ⟨hpcv, hpv, stv, Iv, hcap, hby, hfresh⟩ | hd⟩ := growOneCall hG hpre I₂
    (Reaches.refl u₂) (b8000701c_pc h₂)
    (by rw [b8000701c_x10 h₂, k₁ .x2 (by decide), sp]; apply BitVec.eq_of_toNat_eq
        addr_omega [hb1])
    hraw
  swap
  · exact ⟨v, hr₁.trans (hr₂.trans hrv), Or.inl hd⟩
  have hpc' : v.pc = 0x80007028 := by rw [hpcv, returnAddress_eq, b8000701c_x1 h₂]; decide
  have spv : v.getReg .x2 = s.getReg .x2 - 1344 := Iv.sp
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80007028_spec hpc' (by
    rv_eval [spv]
    valid_access hval [hb1])
  have k₃ := b80007028_keeps h₃
  have m₃ := b80007028_mem_same h₃
  have I₃ := Iv.same m₃ (k₃ .x2 (by decide))
  have f16 : FrameW s (Within · (s.getReg .x2 - BitVec.ofNat 64 840) 16) := fun a ha ↦ by
    addr_omega [ha, hb1]
  have hm₂ : heapNext u₂ = heapNext y := by simp only [heapNext, m12]
  have G := CL₂.grow hpre stv.toR f16 (by omega) hby hfresh I₂.mono
  obtain ⟨P', eP⟩ : ∃ P', vecPtr v (s.getReg .x2 - BitVec.ofNat 64 840) = P' := ⟨_, rfl⟩
  obtain ⟨C', eC⟩ : ∃ C', vecCap v (s.getReg .x2 - BitVec.ofNat 64 840) = C' := ⟨_, rfl⟩
  rw [eP, eC] at G hfresh
  rw [eC] at hcap
  have hcap4 : vecCap u₂ (s.getReg .x2 - BitVec.ofNat 64 840) = 4 := by
    simp only [vecCap, m12]; exact hc
  rw [hcap4, h4] at hcap
  obtain ⟨q0, q1, q2⟩ : P'.toNat % 8 = 0 ∧ heapNext u₂ ≤ P'.toNat ∧
      P'.toNat + C'.toNat * 56 ≤ heapNext v := by
    simp only [NewBuf] at hfresh
    rcases hfresh.2 with h0 | h0
    · omega
    · exact ⟨hfresh.1, h0⟩
  have x8₃ : u₃.getReg .x8 = P' := by
    rw [b80007028_x8 h₃, spv, show s.getReg .x2 - 1344 + 512 = s.getReg .x2 - BitVec.ofNat 64 840 + 8
      by apply BitVec.eq_of_toNat_eq; addr_omega [hb1], ← eP]
    rfl
  have m3v (a : Word) : u₃.getMem a = v.getMem a := m₃ a
  have st₃ : StepS s y u₃ (Within · (s.getReg .x2 - BitVec.ofNat 64 840) 16) :=
    (((StepS.same m12 C.inv.heap (by rw [k₂ .x2 (by decide), k₁ .x2 (by decide)])).trans stv).trans
      (StepS.same m₃ Iv.heap (k₃ .x2 (by decide)))).weaken fun a ha ↦ by
        rcases ha with (ha | ha) | ha
        · exact False.elim ha
        · exact ha
        · exact False.elim ha
  have rg (r : Reg) (hr : r ∈ ([.x9, .x18, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27] :
      List Reg)) : u₃.getReg r = y.getReg r := by
    rw [k₃ r (mem_of_mem hr _), hpv r (by unfold calleeSaved; exact mem_of_mem hr _),
      k₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
  have y840 : u₃.getMem (s.getReg .x2 - 840) = C' := by rw [m3v, ← eC]; rfl
  have hfr := C.fresh
  have hstm := C.step.mono
  have hm3 : heapNext u₃ = heapNext v := by simp only [heapNext, m3v]
  simp only [heapNext] at q1 q2 hm₂ hfr hstm hm3
  refine ⟨u₃, hr₁.trans (hr₂.trans (hrv.trans hr₃)), Or.inr ⟨b80007028_pc h₃, {
    inv := I₃
    step := (C.step.trans st₃).weaken fun a ha ↦ by
      rcases ha with ha | ha
      · exact ha
      · exact Or.inl (by addr_omega [ha, hb1])
    fresh := by rw [x8₃]; simp only [heapNext]; omega
    claims := by
      rw [y840, x8₃]
      exact G.keepR hpre (StepR.same (A := fun _ ↦ False) m₃ Iv.heap (k₃ .x2 (by decide)))
        (fun _ h ↦ h.elim)
    ptr := by
      rw [x8₃, m3v, ← eP]
      exact congrArg v.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
    len := by
      rw [m3v, stv.slot hpre (fun z hz h' ↦ by addr_omega [hz, h', hb1])
        (by constructor <;> addr_omega [hb1]), m12]
      exact C.len
    lt := by rw [y840]; omega
    c4 := by
      rw [rg .x9 (by decide), rg .x18 (by decide)]
      exact C.c4.keepR hpre st₃.toR f16
    apart4 := by
      rw [rg .x9 (by decide), rg .x18 (by decide), x8₃, y840]
      have hb := C.c4.buf
      simp only [NewBuf, heapNext] at hb
      simp only [Apart]
      rcases hb.2 with h0 | ⟨b1, b2⟩
      · exact Or.inl h0
      · exact Or.inr (Or.inr (Or.inl (by omega)))
    x19 := by rw [k₃ .x19 (by decide), hpv .x19 (by decide), k₂ .x19 (by decide)]
              exact b80007010_x19 h₁
    regs := fun r hr ↦ by rw [rg r (mem_of_mem hr _)]; exact C.regs r hr }⟩⟩

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
