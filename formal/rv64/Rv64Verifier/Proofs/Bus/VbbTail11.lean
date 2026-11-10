import Rv64Verifier.Proofs.Bus.VbbTail10

/-!
# `verify_bus_balance` past the GKR loop: `memory[1]`'s and `memory[2]`'s claims' points

From `0x80006d2c` to `0x80006db4` (`ptsB`): `memory[0]` kept at `S - 720` (a `memory` shorter
than two traps), `memory[1]` read to `S - 248`, then `copy2`. From there to `0x80006e44`
(`ptsC`): `memory[1]` kept at `S - 128` (shorter than three traps), `memory[2]` read to
`S - 248`, then `copy3`.
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- `memory`'s buffer, of at least `n` elements, in the heap: valid, below the stack. -/
theorem memBuf {s w : MachineState} (hpre : BusBalancePre s) (h : Inv s w) {mem : List E}
    (hmem : NewVecE s w (s.getReg .x2 - 864) mem) {n : Nat} (hn : 0 < n)
    (hl : n ≤ (vecLen w (s.getReg .x2 - 864)).toNat) :
    0x20000000 ≤ (vecPtr w (s.getReg .x2 - 864)).toNat ∧
      (vecPtr w (s.getReg .x2 - 864)).toNat + 24 * n ≤ 0x78000000 ∧
      ValidMemRange (vecPtr w (s.getReg .x2 - 864)) (3 * n) := by
  have hlo := hpre.heap.lo
  have hhi := h.heap.hi
  have hm := h.mono
  obtain ⟨i1, i2, i3⟩ : heapNext s ≤ (vecPtr w (s.getReg .x2 - 864)).toNat ∧
      (vecPtr w (s.getReg .x2 - 864)).toNat + 24 * (vecLen w (s.getReg .x2 - 864)).toNat ≤
        heapNext w ∧ (vecPtr w (s.getReg .x2 - 864)).toNat % 8 = 0 := by
    rcases NewVecE.inHeap hpre hmem with h0 | h0
    · omega
    · exact h0
  simp only [heapNext, heapEnd, heapStart] at hlo hhi i1 i2 hm
  exact ⟨by omega, by omega,
    heapRange i3 (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega)⟩

/-- At `0x80006db4`, past `memory[1]` and the second copy. -/
structure PtsB (s w y : MachineState) (xs : List E) : Prop where
  inv : Inv s y
  step : StepS s w y fun a ↦ Within a (s.getReg .x2 - 720) 24 ∨
    Within a (s.getReg .x2 - 248) 24 ∨ Within a (s.getReg .x2 - 608) 24
  regs : ∀ r ∈ ([.x8, .x18, .x20, .x21, .x22, .x24, .x25, .x26, .x27] : List Reg),
    y.getReg r = w.getReg r
  x9 : y.getReg .x9 = logMem s
  c1 : NewVecR s y (y.getReg .x19) (y.getReg .x23) (logMem s) (xs.take (logMem s).toNat)
  c1Lo : PtrLo y (y.getReg .x23) (logMem s)
  m0 : eAt y (s.getReg .x2 - 720) = eAt w (s.getReg .x2 - 248)
  m1 : eAt y (s.getReg .x2 - 248) = eAt w (vecPtr w (s.getReg .x2 - 864) + 24)
  len : 2 ≤ (vecLen w (s.getReg .x2 - 864)).toNat

theorem ptsB (hT : TryAllocZeroedSpec) (hM : MemcpySpec 0x800126e4) {s w : MachineState}
    {mem : List E} (hpre : BusBalancePre s) (h : Inv s w) (hpc : w.pc = 0x80006d2c)
    (hlm : w.getMem (s.getReg .x2 - 1136) = logMem s)
    (hmem : NewVecE s w (s.getReg .x2 - 864) mem)
    (h18 : w.getReg .x18 = logMem s * 16 + logMem s * 8) {cap ptr len : Word} {xs : List E}
    (h27 : w.getReg .x27 = ptr) (hp : NewVecR s w cap ptr len xs)
    (hn : (logMem s).toNat ≤ len.toNat) :
    ∃ y, Reaches Image.code w y ∧ (Dead Image.code y ∨ (y.pc = 0x80006db4 ∧ PtsB s w y xs)) := by
  obtain ⟨hb1, hb2, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have sp := h.sp
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80006d2c_spec hpc (by
    rv_eval [sp]
    and_intros <;> valid_access hval [hb1])
  have k₁ := b80006d2c_keeps h₁
  have fr₁ : DFrame w u₁ (Within · (s.getReg .x2 - 720) 24) :=
    (DFrame.of_memFrame (b80006d2c_frame h₁ (by rw [sp]; addr_omega [hb1, hb2]))).mono
      fun a ha ↦ by rw [sp] at ha; addr_omega [ha, hb1]
  have st₁ : StepS s w u₁ (Within · (s.getReg .x2 - 720) 24) :=
    StepS.ofDFrame h.heap fr₁ (fun _ h ↦ h) (fun i hi hw ↦ by addr_omega [hw, hi, hb1])
      (k₁ .x2 (by decide))
  have I₁ := h.afterR hpre (fun a ha ↦ by addr_omega [ha, hb1]) st₁.toR
  have e496 : w.getMem (w.getReg .x2 + 496) = vecLen w (s.getReg .x2 - 864) := by
    rw [sp, vecLen, show s.getReg .x2 - 1344 + 496 = s.getReg .x2 - 864 + 16 by
      apply BitVec.eq_of_toNat_eq; addr_omega [hb1]]
  by_cases hl : 2 ≤ (vecLen w (s.getReg .x2 - 864)).toNat
  swap
  · have pc₁ := b80006d2c_pc_taken h₁ (by rw [e496]; show _ < 2; omega)
    exact ⟨u₁, hr₁, Or.inl (dead_of_fetch (by
      rw [pc₁]; exact Option.isNone_iff_eq_none.mp (by decide +kernel)))⟩
  have pc₁ := b80006d2c_pc_not_taken h₁ (by rw [e496]; show 2 ≤ _; omega)
  have sp₁ : u₁.getReg .x2 = s.getReg .x2 - 1344 := I₁.sp
  obtain ⟨j1, j2, hvm⟩ := memBuf hpre h hmem (n := 2) (by omega) hl
  have m856 : u₁.getMem (s.getReg .x2 - 856) = vecPtr w (s.getReg .x2 - 864) := by
    rw [st₁.slot hpre (fun y hy h' ↦ by addr_omega [hy, h', hb1])
      (by constructor <;> addr_omega [hb1]), vecPtr]
    exact congrArg w.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80006d50_spec pc₁ (by
    rv_eval [sp₁, m856]
    and_intros
    all_goals first
      | valid_access hval [hb1]
      | valid_access hvm [j1, j2])
  have k₂ := b80006d50_keeps h₂
  have fr₂ : DFrame u₁ u₂ (Within · (s.getReg .x2 - 248) 24) :=
    (DFrame.of_memFrame (b80006d50_frame h₂ (by rw [sp₁]; addr_omega [hb1, hb2]))).mono
      fun a ha ↦ by rw [sp₁] at ha; addr_omega [ha, hb1]
  have st₂ : StepS s u₁ u₂ (Within · (s.getReg .x2 - 248) 24) :=
    StepS.ofDFrame I₁.heap fr₂ (fun _ h ↦ h) (fun i hi hw ↦ by addr_omega [hw, hi, hb1])
      (k₂ .x2 (by decide))
  have I₂ := I₁.afterR hpre (fun a ha ↦ by addr_omega [ha, hb1]) st₂.toR
  have lm₁ : u₁.getMem (s.getReg .x2 - 1344 + 208) = logMem s := by
    rw [show s.getReg .x2 - 1344 + 208 = s.getReg .x2 - 1136 by
        apply BitVec.eq_of_toNat_eq; addr_omega [hb1],
      st₁.slot hpre (fun y hy h' ↦ by addr_omega [hy, h', hb1])
        (by constructor <;> addr_omega [hb1])]
    exact hlm
  have x9₂ : u₂.getReg .x9 = logMem s := by rw [b80006d50_x9 h₂, sp₁, lm₁]
  have x11₂ : u₂.getReg .x11 = logMem s := by rw [b80006d50_x11 h₂, sp₁, lm₁]
  have x10₂ : u₂.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 608 := by
    rw [b80006d50_x10 h₂, sp₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have rg₂ (r : Reg) (hr : r ∈ ([.x8, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27] :
      List Reg)) : u₂.getReg r = w.getReg r := by
    rw [k₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
  have st₁₂ := st₁.trans st₂
  have hp₂ := hp.keepR hpre st₁₂.toR (fun a ha ↦ by rcases ha with ha | ha <;> addr_omega [ha, hb1])
  obtain ⟨y, hry, hd | ⟨hpcy, Iy, sty, rgy, c1, c1Lo⟩⟩ := copy2 hT hM hpre I₂ (b80006d50_pc h₂)
    (b80006d50_x1 h₂) x10₂ (b80006d50_x13 h₂) (b80006d50_x14 h₂) x9₂ x11₂
    ((rg₂ .x18 (by decide)).trans h18) ((rg₂ .x27 (by decide)).trans h27) hp₂ hn
  · exact ⟨y, hr₁.trans (hr₂.trans hry), Or.inl hd⟩
  have a0 := b80006d50_m_x2_1096 h₂
  have a1 := b80006d50_m_x2_1104 h₂
  have a2 := b80006d50_m_x2_1112 h₂
  rw [sp₁, show s.getReg .x2 - 1344 + 488 = s.getReg .x2 - 856 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1], m856] at a0 a1 a2
  have mh (j : Nat) (hj : j ≤ 40) : u₁.getMem (vecPtr w (s.getReg .x2 - 864) + BitVec.ofNat 64 j) =
      w.getMem (vecPtr w (s.getReg .x2 - 864) + BitVec.ofNat 64 j) :=
    fr₁ _ fun i hi hw ↦ by addr_omega [hw, hi, hb1, j1, j2, hj]
  have c0 := b80006d2c_m_x2_624 h₁
  have c8 := b80006d2c_m_x2_632 h₁
  have c16 := b80006d2c_m_x2_640 h₁
  rw [sp] at c0 c8 c16
  refine ⟨y, hr₁.trans (hr₂.trans hry), Or.inr ⟨hpcy, {
    inv := Iy
    step := (st₁₂.trans sty).weaken fun a ha ↦ by
      rcases ha with (ha | ha) | ha
      · exact Or.inl ha
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr (by addr_omega [ha, hb1]))
    regs := fun r hr ↦ by rw [rgy r (mem_of_mem hr _), rg₂ r (mem_of_mem hr _)]
    x9 := by rw [rgy .x9 (by decide), x9₂]
    c1 := c1
    c1Lo := c1Lo
    m0 := by
      rw [sty.eSlot hpre (fun y hy h' ↦ by addr_omega [hy, h', hb1])
          (by constructor <;> addr_omega [hb1]),
        st₂.eSlot hpre (fun y hy h' ↦ by addr_omega [hy, h', hb1])
          (by constructor <;> addr_omega [hb1])]
      refine eAt_congr ?_ ?_ ?_
      · rw [show s.getReg .x2 - 720 = s.getReg .x2 - 1344 + 624 by
          apply BitVec.eq_of_toNat_eq; addr_omega [hb1], c0]
        exact congrArg w.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
      · rw [show s.getReg .x2 - 720 + 8 = s.getReg .x2 - 1344 + 632 by
          apply BitVec.eq_of_toNat_eq; addr_omega [hb1], c8]
        exact congrArg w.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
      · rw [show s.getReg .x2 - 720 + 16 = s.getReg .x2 - 1344 + 640 by
          apply BitVec.eq_of_toNat_eq; addr_omega [hb1], c16]
        exact congrArg w.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
    m1 := by
      rw [sty.eSlot hpre (fun y hy h' ↦ by addr_omega [hy, h', hb1])
          (by constructor <;> addr_omega [hb1])]
      refine eAt_congr ?_ ?_ ?_
      · rw [show s.getReg .x2 - 248 = s.getReg .x2 - 1344 + 1096 by
          apply BitVec.eq_of_toNat_eq; addr_omega [hb1], a0]
        exact mh 24 (by omega)
      · rw [show s.getReg .x2 - 248 + 8 = s.getReg .x2 - 1344 + 1104 by
          apply BitVec.eq_of_toNat_eq; addr_omega [hb1], a1,
          show vecPtr w (s.getReg .x2 - 864) + 24 + 8 =
            vecPtr w (s.getReg .x2 - 864) + BitVec.ofNat 64 32 by rw [BitVec.add_assoc]; rfl]
        exact mh 32 (by omega)
      · rw [show s.getReg .x2 - 248 + 16 = s.getReg .x2 - 1344 + 1112 by
          apply BitVec.eq_of_toNat_eq; addr_omega [hb1], a2,
          show vecPtr w (s.getReg .x2 - 864) + 24 + 16 =
            vecPtr w (s.getReg .x2 - 864) + BitVec.ofNat 64 40 by rw [BitVec.add_assoc]; rfl]
        exact mh 40 (by omega)
    len := hl }⟩⟩

/-- At `0x80006e44`, past `memory[2]` and the third copy. -/
structure PtsC (s w y : MachineState) (ptr : Word) (xs : List E) : Prop where
  inv : Inv s y
  step : StepS s w y fun a ↦ Within a (s.getReg .x2 - 128) 24 ∨
    Within a (s.getReg .x2 - 248) 24 ∨ Copy3W s a
  regs : ∀ r ∈ ([.x8, .x18, .x19, .x20, .x21, .x22, .x23, .x25, .x26] : List Reg),
    y.getReg r = w.getReg r
  x9 : y.getReg .x9 = logMem s
  c2 : NewVecR s y (y.getReg .x27) (y.getReg .x24) (logMem s) (xs.take (logMem s).toNat)
  c2Lo : PtrLo y (y.getReg .x24) (logMem s)
  m1 : eAt y (s.getReg .x2 - 128) = eAt w (s.getReg .x2 - 248)
  m2 : eAt y (s.getReg .x2 - 248) = eAt w (vecPtr w (s.getReg .x2 - 864) + 48)
  pointPtr : y.getMem (s.getReg .x2 - 1256) = ptr
  pushPtr : y.getMem (s.getReg .x2 - 1272) = w.getReg .x24
  len : 3 ≤ (vecLen w (s.getReg .x2 - 864)).toNat

theorem ptsC (hT : TryAllocZeroedSpec) (hM : MemcpySpec 0x800126e4) {s w : MachineState}
    {mem : List E} (hpre : BusBalancePre s) (h : Inv s w) (hpc : w.pc = 0x80006db4)
    (hlm : w.getMem (s.getReg .x2 - 1136) = logMem s)
    (hmem : NewVecE s w (s.getReg .x2 - 864) mem)
    (h18 : w.getReg .x18 = logMem s * 16 + logMem s * 8) {cap ptr len : Word} {xs : List E}
    (h27 : w.getReg .x27 = ptr) (hp : NewVecR s w cap ptr len xs)
    (hn : (logMem s).toNat ≤ len.toNat) :
    ∃ y, Reaches Image.code w y ∧ (Dead Image.code y ∨ (y.pc = 0x80006e44 ∧ PtsC s w y ptr xs)) := by
  obtain ⟨hb1, hb2, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have sp := h.sp
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80006db4_spec hpc (by
    rv_eval [sp]
    and_intros <;> valid_access hval [hb1])
  have k₁ := b80006db4_keeps h₁
  have fr₁ : DFrame w u₁ (Within · (s.getReg .x2 - 128) 24) :=
    (DFrame.of_memFrame (b80006db4_frame h₁ (by rw [sp]; addr_omega [hb1, hb2]))).mono
      fun a ha ↦ by rw [sp] at ha; addr_omega [ha, hb1]
  have st₁ : StepS s w u₁ (Within · (s.getReg .x2 - 128) 24) :=
    StepS.ofDFrame h.heap fr₁ (fun _ h ↦ h) (fun i hi hw ↦ by addr_omega [hw, hi, hb1])
      (k₁ .x2 (by decide))
  have I₁ := h.afterR hpre (fun a ha ↦ by addr_omega [ha, hb1]) st₁.toR
  have e496 : w.getMem (w.getReg .x2 + 496) = vecLen w (s.getReg .x2 - 864) := by
    rw [sp, vecLen, show s.getReg .x2 - 1344 + 496 = s.getReg .x2 - 864 + 16 by
      apply BitVec.eq_of_toNat_eq; addr_omega [hb1]]
  by_cases hl : 3 ≤ (vecLen w (s.getReg .x2 - 864)).toNat
  swap
  · have pc₁ := b80006db4_pc_taken h₁ (by rw [e496]; show _ < 3; omega)
    exact ⟨u₁, hr₁, Or.inl (dead_of_fetch (by
      rw [pc₁]; exact Option.isNone_iff_eq_none.mp (by decide +kernel)))⟩
  have pc₁ := b80006db4_pc_not_taken h₁ (by rw [e496]; show 3 ≤ _; omega)
  have sp₁ : u₁.getReg .x2 = s.getReg .x2 - 1344 := I₁.sp
  obtain ⟨j1, j2, hvm⟩ := memBuf hpre h hmem (n := 3) (by omega) hl
  have m856 : u₁.getMem (s.getReg .x2 - 856) = vecPtr w (s.getReg .x2 - 864) := by
    rw [st₁.slot hpre (fun y hy h' ↦ by addr_omega [hy, h', hb1])
      (by constructor <;> addr_omega [hb1]), vecPtr]
    exact congrArg w.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80006dd8_spec pc₁ (by
    rv_eval [sp₁, m856]
    and_intros
    all_goals first
      | valid_access hval [hb1]
      | valid_access hvm [j1, j2])
  have k₂ := b80006dd8_keeps h₂
  have fr₂ : DFrame u₁ u₂ (Within · (s.getReg .x2 - 248) 24) :=
    (DFrame.of_memFrame (b80006dd8_frame h₂ (by rw [sp₁]; addr_omega [hb1, hb2]))).mono
      fun a ha ↦ by rw [sp₁] at ha; addr_omega [ha, hb1]
  have st₂ : StepS s u₁ u₂ (Within · (s.getReg .x2 - 248) 24) :=
    StepS.ofDFrame I₁.heap fr₂ (fun _ h ↦ h) (fun i hi hw ↦ by addr_omega [hw, hi, hb1])
      (k₂ .x2 (by decide))
  have I₂ := I₁.afterR hpre (fun a ha ↦ by addr_omega [ha, hb1]) st₂.toR
  have lm₁ : u₁.getMem (s.getReg .x2 - 1344 + 208) = logMem s := by
    rw [show s.getReg .x2 - 1344 + 208 = s.getReg .x2 - 1136 by
        apply BitVec.eq_of_toNat_eq; addr_omega [hb1],
      st₁.slot hpre (fun y hy h' ↦ by addr_omega [hy, h', hb1])
        (by constructor <;> addr_omega [hb1])]
    exact hlm
  have x9₂ : u₂.getReg .x9 = logMem s := by rw [b80006dd8_x9 h₂, sp₁, lm₁]
  have x11₂ : u₂.getReg .x11 = logMem s := by rw [b80006dd8_x11 h₂, sp₁, lm₁]
  have x10₂ : u₂.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 608 := by
    rw [b80006dd8_x10 h₂, sp₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have rg₂ (r : Reg) (hr : r ∈ ([.x8, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27] :
      List Reg)) : u₂.getReg r = w.getReg r := by
    rw [k₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
  have st₁₂ := st₁.trans st₂
  have hp₂ := hp.keepR hpre st₁₂.toR (fun a ha ↦ by rcases ha with ha | ha <;> addr_omega [ha, hb1])
  obtain ⟨y, hry, hd | ⟨hpcy, Iy, sty, rgy, p88, p72, c2, c2Lo⟩⟩ := copy3 hT hM hpre I₂
    (b80006dd8_pc h₂) (b80006dd8_x1 h₂) x10₂ (b80006dd8_x13 h₂) (b80006dd8_x14 h₂) x9₂ x11₂
    ((rg₂ .x18 (by decide)).trans h18) ((rg₂ .x27 (by decide)).trans h27) hp₂ hn
  · exact ⟨y, hr₁.trans (hr₂.trans hry), Or.inl hd⟩
  have a0 := b80006dd8_m_x2_1096 h₂
  have a1 := b80006dd8_m_x2_1104 h₂
  have a2 := b80006dd8_m_x2_1112 h₂
  rw [sp₁, show s.getReg .x2 - 1344 + 488 = s.getReg .x2 - 856 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1], m856] at a0 a1 a2
  have mh (j : Nat) (hj : j ≤ 64) : u₁.getMem (vecPtr w (s.getReg .x2 - 864) + BitVec.ofNat 64 j) =
      w.getMem (vecPtr w (s.getReg .x2 - 864) + BitVec.ofNat 64 j) :=
    fr₁ _ fun i hi hw ↦ by addr_omega [hw, hi, hb1, j1, j2, hj]
  have c0 := b80006db4_m_x2_1216 h₁
  have c8 := b80006db4_m_x2_1224 h₁
  have c16 := b80006db4_m_x2_1232 h₁
  rw [sp] at c0 c8 c16
  refine ⟨y, hr₁.trans (hr₂.trans hry), Or.inr ⟨hpcy, {
    inv := Iy
    step := (st₁₂.trans sty).weaken fun a ha ↦ by
      rcases ha with (ha | ha) | ha
      · exact Or.inl ha
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr ha)
    regs := fun r hr ↦ by rw [rgy r (mem_of_mem hr _), rg₂ r (mem_of_mem hr _)]
    x9 := by rw [rgy .x9 (by decide), x9₂]
    c2 := c2
    c2Lo := c2Lo
    m1 := by
      rw [sty.eSlot hpre (fun y hy h' ↦ by rcases h' with h' | h' | h' <;> addr_omega [hy, h', hb1])
          (by constructor <;> addr_omega [hb1]),
        st₂.eSlot hpre (fun y hy h' ↦ by addr_omega [hy, h', hb1])
          (by constructor <;> addr_omega [hb1])]
      refine eAt_congr ?_ ?_ ?_
      · rw [show s.getReg .x2 - 128 = s.getReg .x2 - 1344 + 1216 by
          apply BitVec.eq_of_toNat_eq; addr_omega [hb1], c0]
        exact congrArg w.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
      · rw [show s.getReg .x2 - 128 + 8 = s.getReg .x2 - 1344 + 1224 by
          apply BitVec.eq_of_toNat_eq; addr_omega [hb1], c8]
        exact congrArg w.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
      · rw [show s.getReg .x2 - 128 + 16 = s.getReg .x2 - 1344 + 1232 by
          apply BitVec.eq_of_toNat_eq; addr_omega [hb1], c16]
        exact congrArg w.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
    m2 := by
      rw [sty.eSlot hpre (fun y hy h' ↦ by rcases h' with h' | h' | h' <;> addr_omega [hy, h', hb1])
          (by constructor <;> addr_omega [hb1])]
      refine eAt_congr ?_ ?_ ?_
      · rw [show s.getReg .x2 - 248 = s.getReg .x2 - 1344 + 1096 by
          apply BitVec.eq_of_toNat_eq; addr_omega [hb1], a0]
        exact mh 48 (by omega)
      · rw [show s.getReg .x2 - 248 + 8 = s.getReg .x2 - 1344 + 1104 by
          apply BitVec.eq_of_toNat_eq; addr_omega [hb1], a1,
          show vecPtr w (s.getReg .x2 - 864) + 48 + 8 =
            vecPtr w (s.getReg .x2 - 864) + BitVec.ofNat 64 56 by rw [BitVec.add_assoc]; rfl]
        exact mh 56 (by omega)
      · rw [show s.getReg .x2 - 248 + 16 = s.getReg .x2 - 1344 + 1112 by
          apply BitVec.eq_of_toNat_eq; addr_omega [hb1], a2,
          show vecPtr w (s.getReg .x2 - 864) + 48 + 16 =
            vecPtr w (s.getReg .x2 - 864) + BitVec.ofNat 64 64 by rw [BitVec.add_assoc]; rfl]
        exact mh 64 (by omega)
    pointPtr := p88
    pushPtr := by rw [p72, rg₂ .x24 (by decide)]
    len := hl }⟩⟩

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
