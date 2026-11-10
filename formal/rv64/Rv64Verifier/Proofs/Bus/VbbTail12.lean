import Rv64Verifier.Proofs.Bus.VbbTail11

/-!
# `verify_bus_balance` past the GKR loop: the points, to the claims' allocation

`0x80006e44` moves `memory[0..3]` to `S - 608`, `S - 248`, `S - 152` (`ptsD`) and calls
`alloc(168, 8)`. `pointsStage` composes `ptsA` to `ptsD`: at `alloc`'s entry (`Points`) the three
copies of `point[..log_memory]` are in registers, `memory`'s elements in the frame.
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem _root_.Rv64Verifier.Transcript.NewVecE.getD {s w : MachineState} {a : Word}
    {xs : List E} (h : NewVecE s w a xs) {i : Nat} (hi : i < (vecLen w a).toNat) :
    xs.getD i 0 = eAt w (vecPtr w a + BitVec.ofNat 64 (24 * i)) := by
  rw [← h.elems, vecEs, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by rw [eListAt_length]; exact hi), Option.getD_some,
    eListAt_getElem]

theorem _root_.Rv64Verifier.Transcript.NewVecE.length {s w : MachineState} {a : Word}
    {xs : List E} (h : NewVecE s w a xs) : xs.length = (vecLen w a).toNat := by
  rw [← h.elems, vecEs, eListAt_length]

/-- `0x80006e44`'s moves. -/
structure PtsD (s z v : MachineState) : Prop where
  inv : Inv s v
  step : StepS s z v fun a ↦ Within a (s.getReg .x2 - 608) 24 ∨
    Within a (s.getReg .x2 - 248) 24 ∨ Within a (s.getReg .x2 - 152) 24
  regs : ∀ r ∈ ([.x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27] : List Reg),
    v.getReg r = z.getReg r
  x1 : v.getReg .x1 = 0x80006e9c
  x10 : v.getReg .x10 = 8
  x11 : v.getReg .x11 = 168
  m0 : eAt v (s.getReg .x2 - 608) = eAt z (s.getReg .x2 - 720)
  m1 : eAt v (s.getReg .x2 - 248) = eAt z (s.getReg .x2 - 128)
  m2 : eAt v (s.getReg .x2 - 152) = eAt z (s.getReg .x2 - 248)

theorem ptsD {s z : MachineState} (hpre : BusBalancePre s) (h : Inv s z)
    (hpc : z.pc = 0x80006e44) :
    ∃ v, Reaches Image.code z v ∧ v.pc = 0x80000284 ∧ PtsD s z v := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have sp := h.sp
  obtain ⟨v, hr, h₁⟩ := Sym.BlockSpec.reaches b80006e44_spec hpc (by
    rv_eval [sp]
    and_intros <;> valid_access hval [hb1])
  have k₁ := b80006e44_keeps h₁
  have fr : DFrame z v fun a ↦ Within a (s.getReg .x2 - 608) 24 ∨
      Within a (s.getReg .x2 - 248) 24 ∨ Within a (s.getReg .x2 - 152) 24 := fun a ha ↦
    h₁.frame a (by
      rv_eval [sp]
      and_intros <;> intro he <;> exact ha 0 (by decide) (by
        rw [add_ofNat_zero, he]; addr_omega [hb1]))
  have st : StepS s z v fun a ↦ Within a (s.getReg .x2 - 608) 24 ∨
      Within a (s.getReg .x2 - 248) 24 ∨ Within a (s.getReg .x2 - 152) 24 :=
    StepS.ofDFrame h.heap fr (fun _ h ↦ h) (fun i hi hw ↦ by
      rcases hw with hw | hw | hw <;> addr_omega [hw, hi, hb1]) (k₁ .x2 (by decide))
  have mv (a b c : Nat) (hm : v.getMem (z.getReg .x2 + BitVec.ofNat 64 a) =
      z.getMem (z.getReg .x2 + BitVec.ofNat 64 b)) (ha : 1344 - a = c) (ha' : a ≤ 1344)
      (hb : b ≤ 1344) :
      v.getMem (s.getReg .x2 - BitVec.ofNat 64 c) =
        z.getMem (s.getReg .x2 - BitVec.ofNat 64 (1344 - b)) := by
    rw [sp] at hm
    rw [show s.getReg .x2 - BitVec.ofNat 64 c = s.getReg .x2 - 1344 + BitVec.ofNat 64 a by
      apply BitVec.eq_of_toNat_eq; addr_omega [hb1, ha, ha'], hm]
    exact congrArg z.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hb])
  have e3 (v' z' : MachineState) (c d : Nat)
      (h0 : v'.getMem (s.getReg .x2 - BitVec.ofNat 64 c) =
        z'.getMem (s.getReg .x2 - BitVec.ofNat 64 d))
      (h8 : v'.getMem (s.getReg .x2 - BitVec.ofNat 64 (c - 8)) =
        z'.getMem (s.getReg .x2 - BitVec.ofNat 64 (d - 8)))
      (h16 : v'.getMem (s.getReg .x2 - BitVec.ofNat 64 (c - 16)) =
        z'.getMem (s.getReg .x2 - BitVec.ofNat 64 (d - 16)))
      (hc : 24 ≤ c) (hc' : c ≤ 1344) (hd : 24 ≤ d) (hd' : d ≤ 1344) :
      eAt v' (s.getReg .x2 - BitVec.ofNat 64 c) = eAt z' (s.getReg .x2 - BitVec.ofNat 64 d) := by
    refine eAt_congr h0 ?_ ?_
    · rw [show s.getReg .x2 - BitVec.ofNat 64 c + 8 = s.getReg .x2 - BitVec.ofNat 64 (c - 8) by
          apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hc, hc'], h8,
        show s.getReg .x2 - BitVec.ofNat 64 (d - 8) = s.getReg .x2 - BitVec.ofNat 64 d + 8 by
          apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hd, hd']]
    · rw [show s.getReg .x2 - BitVec.ofNat 64 c + 16 = s.getReg .x2 - BitVec.ofNat 64 (c - 16) by
          apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hc, hc'], h16,
        show s.getReg .x2 - BitVec.ofNat 64 (d - 16) = s.getReg .x2 - BitVec.ofNat 64 d + 16 by
          apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hd, hd']]
  refine ⟨v, hr, b80006e44_pc h₁, {
    inv := h.afterR hpre (fun a ha ↦ by rcases ha with ha | ha | ha <;> addr_omega [ha, hb1])
      st.toR
    step := st
    regs := fun r hr ↦ k₁ r (mem_of_mem hr _)
    x1 := b80006e44_x1 h₁
    x10 := b80006e44_x10 h₁
    x11 := b80006e44_x11 h₁
    m0 := e3 v z 608 720 (mv 736 624 608 (b80006e44_m_x2_736 h₁) rfl (by omega) (by omega))
      (mv 744 632 600 (b80006e44_m_x2_744 h₁) rfl (by omega) (by omega))
      (mv 752 640 592 (b80006e44_m_x2_752 h₁) rfl (by omega) (by omega))
      (by omega) (by omega) (by omega) (by omega)
    m1 := e3 v z 248 128 (mv 1096 1216 248 (b80006e44_m_x2_1096 h₁) rfl (by omega) (by omega))
      (mv 1104 1224 240 (b80006e44_m_x2_1104 h₁) rfl (by omega) (by omega))
      (mv 1112 1232 232 (b80006e44_m_x2_1112 h₁) rfl (by omega) (by omega))
      (by omega) (by omega) (by omega) (by omega)
    m2 := e3 v z 152 248 (mv 1192 1096 152 (b80006e44_m_x2_1192 h₁) rfl (by omega) (by omega))
      (mv 1200 1104 144 (b80006e44_m_x2_1200 h₁) rfl (by omega) (by omega))
      (mv 1208 1112 136 (b80006e44_m_x2_1208 h₁) rfl (by omega) (by omega))
      (by omega) (by omega) (by omega) (by omega) }⟩

/-- What the steps from `0x80006ca0` to `alloc`'s entry write in the frame. -/
def PointsW (s : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 1280) 16 ∨ Within a (s.getReg .x2 - 1256) 8 ∨
    Within a (s.getReg .x2 - 1144) 8 ∨ Within a (s.getReg .x2 - 1128) 24 ∨
    Within a (s.getReg .x2 - 840) 664 ∨ Within a (s.getReg .x2 - 152) 48

theorem PointsW.frameW {s : MachineState} (hpre : BusBalancePre s) : FrameW s (PointsW s) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  intro a ha
  rcases ha with ha | ha | ha | ha | ha | ha <;> addr_omega [ha, hb1]

theorem PointsW.free {s : MachineState} (hpre : BusBalancePre s) {a : Word} (ha : PointsW s a) :
    Free s a := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  rcases ha with ha | ha | ha | ha | ha | ha
  · exact Or.inr (Or.inl (by addr_omega [ha, hb1]))
  · exact Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb1])))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb1])))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb1]))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by addr_omega [ha, hb1]))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by addr_omega [ha, hb1]))))))

/-- At `alloc`'s entry (`0x80000284`, for the claims' buffer): the copies of
`point[..log_memory]` in `s0`/`s5`, `s3`/`s7`, `s11`/`s8`, `memory`'s elements at `S - 608`,
`S - 248`, `S - 152`, the point's capacity, buffer and length at `S - 1320`, `S - 1256`,
`S - 1144`, `memory_final`'s limbs in `s9`, `s6` and at `S - 1112`, `bytecode_final`'s in `s10` and
at `S - 1120`, `S - 1128`. -/
structure Points (bev : MachineState → Word → List E → Option E) (s y : MachineState) (k : Start)
    (state : GkrState) (mem : List E) (mf bf : E) : Prop where
  inv : Inv s y
  kept : Kept s y k
  x1 : y.getReg .x1 = 0x80006e9c
  x10 : y.getReg .x10 = 8
  x11 : y.getReg .x11 = 168
  x18 : y.getReg .x18 = logMem s * 16 + logMem s * 8
  x20 : y.getReg .x20 = s.getReg .x12
  c0 : NewVecR s y (y.getReg .x8) (y.getReg .x21) (logMem s) (state.point.take (logMem s).toNat)
  c1 : NewVecR s y (y.getReg .x19) (y.getReg .x23) (logMem s) (state.point.take (logMem s).toNat)
  c2 : NewVecR s y (y.getReg .x27) (y.getReg .x24) (logMem s) (state.point.take (logMem s).toNat)
  m0 : eAt y (s.getReg .x2 - 608) = mem.getD 0 0
  m1 : eAt y (s.getReg .x2 - 248) = mem.getD 1 0
  m2 : eAt y (s.getReg .x2 - 152) = mem.getD 2 0
  memory : NewVecE s y (s.getReg .x2 - 864) mem
  memLen : 3 ≤ mem.length
  values : NewVecE s y (s.getReg .x2 - 176) state.values
  point : NewVecR s y (y.getMem (s.getReg .x2 - 1320)) (y.getMem (s.getReg .x2 - 1256))
    (y.getMem (s.getReg .x2 - 1144)) state.point
  valuesPtr : y.getMem (s.getReg .x2 - 1280) = vecPtr y (s.getReg .x2 - 176)
  pushPtr : y.getMem (s.getReg .x2 - 1272) = vecPtr s (s.getReg .x11 + 24)
  lm : (logMem s).toNat ≤ state.point.length
  lb : (logBc s).toNat ≤ state.point.length
  mfEq : mf = eOf3 (y.getReg .x25) (y.getReg .x22) (y.getMem (s.getReg .x2 - 1112))
  bfEq : bf = eOf3 (y.getReg .x26) (y.getMem (s.getReg .x2 - 1120))
    (y.getMem (s.getReg .x2 - 1128))
  tracks : Tracks (prog bev s) (s.getReg .x12) s y (rest bev s k state mem mf bf)

theorem pointsStage (hT : TryAllocZeroedSpec) (hM : MemcpySpec 0x800126e4)
    {bev : MachineState → Word → List E → Option E} {s q : MachineState} {k : Start}
    {state : GkrState} {mem : List E} {mf bf : E} (hpre : BusBalancePre s)
    (Sc : Scalars bev s q k state mem mf bf) (hpc : q.pc = 0x80006ca0) :
    ∃ v, Reaches Image.code q v ∧ (Dead Image.code v ∨
      (v.pc = 0x80000284 ∧ Points bev s v k state mem mf bf)) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  obtain ⟨w, hrw, hd | ⟨hpcw, A⟩⟩ := ptsA hT hM hpre Sc hpc
  · exact ⟨w, hrw, Or.inl hd⟩
  have fA : FrameW s (PtsAW s) := fun a ha ↦ by
    rcases ha with ha | ha | ha | ha | ha <;> addr_omega [ha, hb1]
  have memw : NewVecE s w (s.getReg .x2 - 864) mem := Sc.memory.keepR hpre A.step.toR fA
    (by addr_omega [hb1]) fun y hy h' ↦ by
      rcases h' with h' | h' | h' | h' | h' <;> addr_omega [hy, h', hb1]
  have lmw : w.getMem (s.getReg .x2 - 1136) = logMem s := by
    rw [A.step.slot hpre (fun y hy h' ↦ by
      rcases h' with h' | h' | h' | h' | h' <;> addr_omega [hy, h', hb1])
      (by constructor <;> addr_omega [hb1])]
    exact Sc.kept.lm
  have hlen : state.point.length = (q.getReg .x21).toNat := by
    rw [← Sc.point.elems, eListAt_length]
  have hn : (logMem s).toNat ≤ (q.getReg .x21).toNat := by rw [← hlen]; exact Sc.lm
  have pw := Sc.point.keepR hpre A.step.toR fA
  obtain ⟨y, hry, hd | ⟨hpcy, B⟩⟩ := ptsB hT hM hpre A.inv hpcw lmw memw A.x18
    (A.regs .x27 (by decide)) pw hn
  · exact ⟨y, hrw.trans hry, Or.inl hd⟩
  have fB : FrameW s fun a ↦ Within a (s.getReg .x2 - 720) 24 ∨
      Within a (s.getReg .x2 - 248) 24 ∨ Within a (s.getReg .x2 - 608) 24 := fun a ha ↦ by
    rcases ha with ha | ha | ha <;> addr_omega [ha, hb1]
  have memy := memw.keepR hpre B.step.toR fB (by addr_omega [hb1]) fun y hy h' ↦ by
    rcases h' with h' | h' | h' <;> addr_omega [hy, h', hb1]
  have lmy : y.getMem (s.getReg .x2 - 1136) = logMem s := by
    rw [B.step.slot hpre (fun y hy h' ↦ by rcases h' with h' | h' | h' <;> addr_omega [hy, h', hb1])
      (by constructor <;> addr_omega [hb1])]
    exact lmw
  have py := pw.keepR hpre B.step.toR fB
  obtain ⟨z, hrz, hd | ⟨hpcz, C⟩⟩ := ptsC hT hM hpre B.inv hpcy lmy memy
    ((B.regs .x18 (by decide)).trans A.x18)
    ((B.regs .x27 (by decide)).trans (A.regs .x27 (by decide))) py hn
  · exact ⟨z, hrw.trans (hry.trans hrz), Or.inl hd⟩
  obtain ⟨v, hrv, hpcv, D⟩ := ptsD hpre C.inv hpcz
  have stBCD : StepS s w v fun a ↦ Within a (s.getReg .x2 - 1272) 24 ∨
      Within a (s.getReg .x2 - 720) 616 :=
    ((B.step.trans C.step).trans D.step).weaken fun a ha ↦ by
      simp only [Copy3W] at ha
      rcases ha with ((ha | ha | ha) | ha | ha | ha | ha | ha) | ha | ha | ha
      · exact Or.inr (by addr_omega [ha, hb1])
      · exact Or.inr (by addr_omega [ha, hb1])
      · exact Or.inr (by addr_omega [ha, hb1])
      · exact Or.inr (by addr_omega [ha, hb1])
      · exact Or.inr (by addr_omega [ha, hb1])
      · exact Or.inr (by addr_omega [ha, hb1])
      · exact Or.inl (by addr_omega [ha, hb1])
      · exact Or.inl (by addr_omega [ha, hb1])
      · exact Or.inr (by addr_omega [ha, hb1])
      · exact Or.inr (by addr_omega [ha, hb1])
      · exact Or.inr (by addr_omega [ha, hb1])
  have st : StepS s q v (PointsW s) :=
    (A.step.trans ((B.step.trans C.step).trans D.step)).weaken fun a ha ↦ by
      simp only [Copy3W] at ha
      have i1280 (h : Within a (s.getReg .x2 - 1280) 16) : PointsW s a := Or.inl h
      have i1256 (h : Within a (s.getReg .x2 - 1256) 8) : PointsW s a := Or.inr (Or.inl h)
      have i1144 (h : Within a (s.getReg .x2 - 1144) 8) : PointsW s a := Or.inr (Or.inr (Or.inl h))
      have i1128 (h : Within a (s.getReg .x2 - 1128) 24) : PointsW s a :=
        Or.inr (Or.inr (Or.inr (Or.inl h)))
      have i840 (h : Within a (s.getReg .x2 - 840) 664) : PointsW s a :=
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      have i152 (h : Within a (s.getReg .x2 - 152) 48) : PointsW s a :=
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
      rcases ha with (ha | ha | ha | ha | ha) | ((ha | ha | ha) | ha | ha | ha | ha | ha) | ha | ha | ha
      · exact i1280 (by addr_omega [ha, hb1])
      · exact i1144 ha
      · exact i1128 ha
      · exact i840 (by addr_omega [ha, hb1])
      · exact i840 (by addr_omega [ha, hb1])
      · exact i840 (by addr_omega [ha, hb1])
      · exact i840 (by addr_omega [ha, hb1])
      · exact i840 (by addr_omega [ha, hb1])
      · exact i152 (by addr_omega [ha, hb1])
      · exact i840 (by addr_omega [ha, hb1])
      · exact i840 (by addr_omega [ha, hb1])
      · exact i1280 (by addr_omega [ha, hb1])
      · exact i1256 ha
      · exact i840 (by addr_omega [ha, hb1])
      · exact i840 (by addr_omega [ha, hb1])
      · exact i152 (by addr_omega [ha, hb1])
  have kv (x : Word) (hx : (s.getReg .x2 - 1344).toNat ≤ x.toNat ∧
      x.toNat + 8 ≤ (s.getReg .x2 - 1272).toNat ∨
      (s.getReg .x2 - 1248).toNat ≤ x.toNat ∧ x.toNat + 8 ≤ (s.getReg .x2 - 720).toNat) :
      v.getMem x = w.getMem x :=
    stBCD.slot hpre (fun y hy h' ↦ by
      rcases hx with hx | hx <;> rcases h' with h' | h' <;> addr_omega [hy, h', hx, hb1])
      (by rcases hx with hx | hx <;> constructor <;> addr_omega [hx, hb1])
  have rv (r : Reg) (hr : r ∈ ([.x8, .x18, .x20, .x21, .x22, .x25, .x26] : List Reg)) :
      v.getReg r = w.getReg r := by
    rw [D.regs r (mem_of_mem hr _), C.regs r (mem_of_mem hr _), B.regs r (mem_of_mem hr _)]
  have hS := st.toR.weaken fun _ ha ↦ PointsW.free hpre ha
  have fW := PointsW.frameW hpre
  have hpos : 0 < (vecLen q (s.getReg .x2 - 864)).toNat := by
    rw [← Sc.x9]
    rcases Nat.eq_zero_or_pos (q.getReg .x9).toNat with h0 | h0
    · exact absurd (BitVec.eq_of_toNat_eq h0) A.len
    · exact h0
  have hpm : vecPtr v (s.getReg .x2 - 176) = vecPtr q (s.getReg .x2 - 176) :=
    st.slot hpre (fun y hy h' ↦ by
      rcases h' with h' | h' | h' | h' | h' | h' <;> addr_omega [hy, h', hb1])
      (by constructor <;> addr_omega [hb1])
  have p1320 : v.getMem (s.getReg .x2 - 1320) = q.getMem (s.getReg .x2 - 1320) :=
    st.slot hpre (fun y hy h' ↦ by
      rcases h' with h' | h' | h' | h' | h' | h' <;> addr_omega [hy, h', hb1])
      (by constructor <;> addr_omega [hb1])
  have p1256 : v.getMem (s.getReg .x2 - 1256) = q.getReg .x27 := by
    rw [D.step.slot hpre (fun y hy h' ↦ by
      rcases h' with h' | h' | h' <;> addr_omega [hy, h', hb1])
      (by constructor <;> addr_omega [hb1])]
    exact C.pointPtr
  have p1144 : v.getMem (s.getReg .x2 - 1144) = q.getReg .x21 := by
    rw [kv _ (Or.inr (by constructor <;> addr_omega [hb1]))]; exact A.pointLen
  refine ⟨v, hrw.trans (hry.trans (hrz.trans hrv)), Or.inr ⟨hpcv, {
    inv := D.inv
    kept := Sc.kept.step hpre hS
    x1 := D.x1
    x10 := D.x10
    x11 := D.x11
    x18 := by rw [rv .x18 (by decide)]; exact A.x18
    x20 := by rw [rv .x20 (by decide), A.regs .x20 (by decide)]; exact Sc.x20
    c0 := by
      rw [rv .x8 (by decide), rv .x21 (by decide)]
      exact A.c0.keepR hpre stBCD.toR fun a ha ↦ by rcases ha with ha | ha <;> addr_omega [ha, hb1]
    c1 := by
      rw [D.regs .x19 (by decide), D.regs .x23 (by decide), C.regs .x19 (by decide),
        C.regs .x23 (by decide)]
      exact B.c1.keepR hpre (C.step.trans D.step).toR fun a ha ↦ by
        simp only [Copy3W] at ha
        rcases ha with (ha | ha | ha | ha | ha) | ha | ha | ha <;> addr_omega [ha, hb1]
    c2 := by
      rw [D.regs .x27 (by decide), D.regs .x24 (by decide)]
      exact C.c2.keepR hpre D.step.toR fun a ha ↦ by
        rcases ha with ha | ha | ha <;> addr_omega [ha, hb1]
    m0 := by
      rw [D.m0, C.step.eSlot hpre (fun y hy h' ↦ by
          simp only [Copy3W] at h'
          rcases h' with h' | h' | h' | h' | h' <;> addr_omega [hy, h', hb1])
          (by constructor <;> addr_omega [hb1]), B.m0, A.m0,
        Sc.memory.getD hpos, Nat.mul_zero, add_ofNat_zero, Sc.x8]
    m1 := by rw [D.m1, C.m1, B.m1, memw.getD (i := 1) (by have := B.len; omega)]; rfl
    m2 := by rw [D.m2, C.m2, memy.getD (i := 2) (by have := C.len; omega)]; rfl
    memory := Sc.memory.keepR hpre st.toR fW (by addr_omega [hb1]) fun y hy h' ↦ by
      rcases h' with h' | h' | h' | h' | h' | h' <;> addr_omega [hy, h', hb1]
    memLen := by rw [memy.length]; exact C.len
    values := Sc.values.keepR hpre st.toR fW (by addr_omega [hb1]) fun y hy h' ↦ by
      rcases h' with h' | h' | h' | h' | h' | h' <;> addr_omega [hy, h', hb1]
    point := by
      rw [p1320, p1256, p1144]
      exact Sc.point.keepR hpre st.toR fW
    valuesPtr := by
      rw [kv _ (Or.inl (by constructor <;> addr_omega [hb1])), A.valuesPtr, Sc.x19, hpm]
    pushPtr := by
      rw [D.step.slot hpre (fun y hy h' ↦ by
        rcases h' with h' | h' | h' <;> addr_omega [hy, h', hb1])
        (by constructor <;> addr_omega [hb1]), C.pushPtr, B.regs .x24 (by decide),
        A.regs .x24 (by decide)]
      exact Sc.x24
    lm := Sc.lm
    lb := Sc.lb
    mfEq := by
      rw [rv .x25 (by decide), rv .x22 (by decide), A.regs .x25 (by decide),
        A.regs .x22 (by decide), kv _ (Or.inr (by constructor <;> addr_omega [hb1])), A.mf2]
      exact Sc.mfEq
    bfEq := by
      rw [rv .x26 (by decide), A.regs .x26 (by decide),
        kv _ (Or.inr (by constructor <;> addr_omega [hb1])), A.bf1,
        kv _ (Or.inr (by constructor <;> addr_omega [hb1])), A.bf2]
      exact Sc.bfEq
    tracks := Sc.tracks.keep fun T hT ↦ st.transcript hpre Sc.inv fW hT }⟩⟩


end Rv64Verifier.Proofs.Bus.VerifyBusBalance
