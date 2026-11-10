import Rv64Verifier.Proofs.Bus.VbbTail17

/-!
# `verify_bus_balance` past the GKR loop: the claims, to `index_mle`

`claim5` writes `bytecode_final`'s claim at `0x8000702c` and calls
`index_mle(point[..log_memory])`. `claimsStage` composes the stages from `alloc`'s entry
(`Points`) to that call (`Claims`): the claims' `Vec` at `S - 840` holds the mirror's five claims.
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The five claims, as the mirror lists them. -/
def allClaims (s : MachineState) (state : GkrState) (mem : List E) (mf bf : E) :
    List ColumnClaim :=
  claims4 s state mem mf ++ [⟨bytecodeFinalCounters, state.point.take (logBc s).toNat, bf⟩]

theorem claim5 {s w z : MachineState} {state : GkrState} {mem : List E} {mf bf : E}
    (hpre : BusBalancePre s) (A : At702c s w z state mem mf) (hpc : z.pc = 0x8000702c)
    (hbf : bf = eOf3 (w.getReg .x26) (w.getMem (s.getReg .x2 - 1120))
      (w.getMem (s.getReg .x2 - 1128))) (hlb : w.getReg .x23 = logBc s) :
    ∃ t, Reaches Image.code z t ∧ t.pc = 0x80010cd4 ∧ Inv s t ∧
      StepS s w t (fun a ↦ Within a (s.getReg .x2 - 840) 24 ∨
        Within a (s.getReg .x2 - BitVec.ofNat 64 608) 24) ∧
      ClaimsOk s t (t.getMem (s.getReg .x2 - 840)) (t.getMem (s.getReg .x2 - 832))
        (t.getMem (s.getReg .x2 - 824)) (allClaims s state mem mf bf) ∧
      t.getMem (s.getReg .x2 - 824) = 5 ∧
      (∀ r ∈ ([.x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27] : List Reg),
        t.getReg r = w.getReg r) ∧
      t.getReg .x1 = 0x80007070 ∧ t.getReg .x10 = s.getReg .x2 - 816 ∧
      t.getReg .x11 = w.getReg .x27 ∧ t.getReg .x12 = w.getReg .x24 := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have sp := A.inv.sp
  have hb := A.claims.claims.buf
  have hlt := A.lt
  have hlo := hpre.heap.lo
  have hhi := A.inv.heap.hi
  have hfr := A.fresh
  have hmw := A.step.mono
  obtain ⟨q0, q1, q2⟩ : (z.getReg .x8).toNat % 8 = 0 ∧ heapNext s ≤ (z.getReg .x8).toNat ∧
      (z.getReg .x8).toNat + 56 * (z.getMem (s.getReg .x2 - 840)).toNat ≤ heapNext z := by
    simp only [NewBuf] at hb
    rcases hb.2 with h0 | h0
    · omega
    · exact ⟨hb.1, h0⟩
  simp only [heapNext, heapEnd, heapStart] at hlo hhi hfr hmw q1 q2
  have hheap : ValidMemRange (z.getReg .x8) 35 :=
    heapRange q0 (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega)
  obtain ⟨t, hr, h₁⟩ := Sym.BlockSpec.reaches b8000702c_spec hpc (by
    rv_eval [sp]
    and_intros <;> first
      | valid_access hval [hb1]
      | valid_access hheap [q0, q1, q2, hlo, hhi, hlt]
      | addr_omega [hb1, q1, q2, hlo, hhi, hlt])
  have k₁ := b8000702c_keeps h₁
  have fr : DFrame z t fun a ↦ Within a (s.getReg .x2 - 824) 8 ∨
      Within a (z.getReg .x8 + BitVec.ofNat 64 (56 * 4)) 56 := fun a ha ↦
    h₁.frame a (by
      rv_eval [sp]
      and_intros <;> intro he <;> exact ha 0 (by decide) (by
        rw [add_ofNat_zero, he]; addr_omega [hb1, q1, q2, hlo, hhi, hlt]))
  have hx := hpre.stack.next
  rw [stackLo_eq] at hx
  have hnz : t.getMem nextAddr = z.getMem nextAddr :=
    fr nextAddr fun i hi hw ↦ by
      rcases hw with hw | hw <;> addr_omega [hw, hi, hx, hb1, q1, q2, hlo, hhi, hlt]
  have hn : heapNext t = heapNext z := by simp only [heapNext, hnz]
  have st : StepS s w t fun a ↦ (Within a (s.getReg .x2 - 840) 24 ∨
      Within a (s.getReg .x2 - BitVec.ofNat 64 608) 24) ∨ Within a (s.getReg .x2 - 824) 8 :=
    A.step.extend (fr.mono fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inl ha
      · exact Or.inr ⟨by simp only [heapNext]; addr_omega [ha, q1, q2, hhi, hfr, hlt],
          by simp only [heapNext]; addr_omega [ha, q1, q2, hhi, hlt]⟩) hn (k₁ .x2 (by decide))
  have I := A.inv.step hpre fr (fun a ha ↦ by
      rcases ha with ha | ha
      · exact ⟨Or.inr (Or.inr (Or.inl (by rw [stackLo_eq]; addr_omega [ha, hb1]))),
          by addr_omega [ha, hb1]⟩
      · refine ⟨Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩))), by
          addr_omega [ha, hb1, q1, q2, hhi, hlt]⟩ <;> simp only [heapNext, hnz] <;>
          addr_omega [ha, q1, q2, hhi, hlt])
    ⟨by rw [hn]; exact A.inv.heap.lo, by rw [hn]; exact A.inv.heap.hi⟩ (by rw [hn])
    (k₁ .x2 (by decide))
  have sz (x : Word) (hx : (s.getReg .x2 - 1344).toNat ≤ x.toNat ∧
      x.toNat + 8 ≤ (s.getReg .x2 - 840).toNat ∨ (s.getReg .x2 - 816).toNat ≤ x.toNat ∧
      x.toNat + 8 ≤ (s.getReg .x2 - 608).toNat ∨ (s.getReg .x2 - 584).toNat ≤ x.toNat ∧
      x.toNat + 8 ≤ (s.getReg .x2).toNat) : z.getMem x = w.getMem x :=
    A.step.slot hpre (fun y hy h' ↦ by
      rcases hx with hx | hx | hx <;> rcases h' with h' | h' <;> addr_omega [hy, h', hx, hb1])
      (by rcases hx with hx | hx | hx <;> constructor <;> addr_omega [hb1, hx])
  have rz (r : Reg) (hr : r ∈ ([.x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27] :
      List Reg)) : t.getReg r = z.getReg r := k₁ r (mem_of_mem hr _)
  have c4 := A.c4.keepD fr (by rw [hn]) fun y hy hB ↦ by
    have ap := A.apart4
    simp only [Apart] at ap
    rcases hB with hB | hB
    · have hpb := A.c4.buf
      simp only [NewBuf, heapNext] at hpb
      rcases hpb.2 with h0 | ⟨b1, b2⟩
      · simp only [Within] at hy; omega
      · addr_omega [hB, hy, b2, hhi, hb1]
    · addr_omega [hB, hy, ap, q1, q2, hlt]
  have e0 : t.getMem (z.getReg .x8 + BitVec.ofNat 64 (56 * 4)) = z.getReg .x9 :=
    b8000702c_m_x8_224 h₁
  have e8 : t.getMem (z.getReg .x8 + BitVec.ofNat 64 (56 * 4 + 8)) = z.getReg .x18 :=
    b8000702c_m_x8_232 h₁
  have hc : ClaimAt s t (z.getReg .x8 + BitVec.ofNat 64 (56 * 4))
      ⟨bytecodeFinalCounters, state.point.take (logBc s).toNat, bf⟩ := by
    refine c4.claimAt' hpre.heap.lo e0 e8
      ((b8000702c_m_x8_240 h₁).trans ((A.regs .x23 (by decide)).trans hlb))
      ((congrArg BitVec.toNat ((b8000702c_m_x8_248 h₁).trans A.x19)).trans rfl) ?_
    rw [eAt_eOf3, hbf, ← A.regs .x26 (by decide)]
    congr 1
    · exact b8000702c_m_x8_256 h₁
    · rw [show z.getReg .x8 + BitVec.ofNat 64 (56 * 4 + 32) + 8 = z.getReg .x8 + 264 by
        rw [BitVec.add_assoc]; rfl, b8000702c_m_x8_264 h₁, sp,
        ← sz _ (Or.inl (by constructor <;> addr_omega [hb1]))]
      exact congrArg z.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
    · rw [show z.getReg .x8 + BitVec.ofNat 64 (56 * 4 + 32) + 16 = z.getReg .x8 + 272 by
        rw [BitVec.add_assoc]; rfl, b8000702c_m_x8_272 h₁, sp,
        ← sz _ (Or.inl (by constructor <;> addr_omega [hb1]))]
      exact congrArg z.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
  have hca : Apart (vecPtr t (z.getReg .x8 + BitVec.ofNat 64 (56 * 4)))
      ((vecCap t (z.getReg .x8 + BitVec.ofNat 64 (56 * 4))).toNat * 24) (z.getReg .x8)
      (56 * (z.getMem (s.getReg .x2 - 840)).toNat) := by
    simp only [vecPtr, vecCap]
    rw [e0, show z.getReg .x8 + BitVec.ofNat 64 (56 * 4) + 8 =
      z.getReg .x8 + BitVec.ofNat 64 (56 * 4 + 8) by rw [BitVec.add_assoc]; rfl, e8]
    exact A.apart4
  have l5 : t.getMem (s.getReg .x2 - 824) = 5 := by
    rw [show s.getReg .x2 - 824 = z.getReg .x2 + 520 by
      rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]]
    exact b8000702c_m_x2_520 h₁
  have CS := A.claims.push hpre A.inv.heap (by show 4 < _; exact hlt) fr
    (fun a ha ↦ by addr_omega [ha, hb1]) hn hc hca (len' := t.getMem (s.getReg .x2 - 824))
    (by rw [l5]; rfl)
  have t840 : t.getMem (s.getReg .x2 - 840) = z.getMem (s.getReg .x2 - 840) :=
    fr _ fun i hi hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hi, hb1, q1, q2, hhi, hlt]
  have t832 : t.getMem (s.getReg .x2 - 832) = z.getReg .x8 := by
    rw [fr _ fun i hi hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hi, hb1, q1, q2, hhi, hlt]]
    exact A.ptr
  refine ⟨t, hr, b8000702c_pc h₁, I, st.weaken fun a ha ↦ by
      rcases ha with ha | ha
      · exact ha
      · exact Or.inl (by addr_omega [ha, hb1]),
    by rw [t840, t832]; exact CS, l5,
    fun r hr ↦ by rw [rz r (mem_of_mem hr _)]; exact A.regs r hr, b8000702c_x1 h₁,
    by rw [b8000702c_x10 h₁, sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1],
    by rw [b8000702c_x11 h₁]; exact A.regs .x27 (by decide),
    by rw [b8000702c_x12 h₁]; exact A.regs .x24 (by decide)⟩

/-- At `index_mle(point[..log_memory])`'s entry (`0x80010cd4`, its result at `S - 816`): the
claims' `Vec` at `S - 840` holds the mirror's five claims; the result's address in `s5`,
`log_bytecode` in `s7`, `log_memory` in `s8`, the point's buffer in `s11`. -/
structure Claims (bev : MachineState → Word → List E → Option E) (s t : MachineState) (k : Start)
    (state : GkrState) (mem : List E) (mf bf : E) : Prop where
  inv : Inv s t
  kept : Kept s t k
  claims : ClaimsOk s t (t.getMem (s.getReg .x2 - 840)) (t.getMem (s.getReg .x2 - 832))
    (t.getMem (s.getReg .x2 - 824)) (allClaims s state mem mf bf)
  len : t.getMem (s.getReg .x2 - 824) = 5
  x1 : t.getReg .x1 = 0x80007070
  x10 : t.getReg .x10 = s.getReg .x2 - 816
  x11 : t.getReg .x11 = t.getMem (s.getReg .x2 - 1256)
  x12 : t.getReg .x12 = logMem s
  x20 : t.getReg .x20 = s.getReg .x12
  x21 : t.getReg .x21 = s.getReg .x10
  x23 : t.getReg .x23 = logBc s
  x24 : t.getReg .x24 = logMem s
  x27 : t.getReg .x27 = t.getMem (s.getReg .x2 - 1256)
  memory : NewVecE s t (s.getReg .x2 - 864) mem
  values : NewVecE s t (s.getReg .x2 - 176) state.values
  point : NewVecR s t (t.getMem (s.getReg .x2 - 1320)) (t.getMem (s.getReg .x2 - 1256))
    (t.getMem (s.getReg .x2 - 1144)) state.point
  valuesPtr : t.getMem (s.getReg .x2 - 1280) = vecPtr t (s.getReg .x2 - 176)
  pushPtr : t.getMem (s.getReg .x2 - 1272) = vecPtr s (s.getReg .x11 + 24)
  lm : (logMem s).toNat ≤ state.point.length
  lb : (logBc s).toNat ≤ state.point.length
  mfEq : mf = eOf3 (t.getReg .x25) (t.getReg .x22) (t.getMem (s.getReg .x2 - 1112))
  bfEq : bf = eOf3 (t.getReg .x26) (t.getMem (s.getReg .x2 - 1120))
    (t.getMem (s.getReg .x2 - 1128))
  tracks : Tracks (prog bev s) (s.getReg .x12) s t (rest bev s k state mem mf bf)

theorem claimsStage (hA : AllocSpec) (hT : TryAllocZeroedSpec) (hM : MemcpySpec 0x800126e4)
    (hG : GrowOneFreshSpec 0x8000c0a4 56 8) {bev : MachineState → Word → List E → Option E}
    {s y : MachineState} {k : Start} {state : GkrState} {mem : List E} {mf bf : E}
    (hpre : BusBalancePre s) (P : Points bev s y k state mem mf bf) (hpc : y.pc = 0x80000284) :
    ∃ t, Reaches Image.code y t ∧ (Dead Image.code t ∨
      (t.pc = 0x80010cd4 ∧ Claims bev s t k state mem mf bf)) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  obtain ⟨w, hrw, hd | ⟨hpcw, C⟩⟩ := claims3 hA hT hM hpre P hpc
  · exact ⟨w, hrw, Or.inl hd⟩
  obtain ⟨y', hry, hd | ⟨hpcy, D⟩⟩ := claim4 hG hT hM hpre C hpcw
  · exact ⟨y', hrw.trans hry, Or.inl hd⟩
  obtain ⟨z, hrz, hd | ⟨hpcz, Z⟩⟩ := to702c hG hpre D hpcy
  · exact ⟨z, hrw.trans (hry.trans hrz), Or.inl hd⟩
  obtain ⟨t, hrt, hpct, I, st, CS, l5, rg, x1, x10, x11, x12⟩ :=
    claim5 hpre Z hpcz C.bfEq C.x23
  have fT : FrameW s fun a ↦ Within a (s.getReg .x2 - 840) 24 ∨
      Within a (s.getReg .x2 - BitVec.ofNat 64 608) 24 := fun a ha ↦ by
    rcases ha with ha | ha <;> addr_omega [ha, hb1]
  have kT (x : Word) (hx : (s.getReg .x2 - 1344).toNat ≤ x.toNat ∧
      x.toNat + 8 ≤ (s.getReg .x2 - 840).toNat ∨ (s.getReg .x2 - 816).toNat ≤ x.toNat ∧
      x.toNat + 8 ≤ (s.getReg .x2 - 608).toNat ∨ (s.getReg .x2 - 584).toNat ≤ x.toNat ∧
      x.toNat + 8 ≤ (s.getReg .x2).toNat) : t.getMem x = w.getMem x :=
    st.slot hpre (fun z hz h' ↦ by
      rcases hx with hx | hx | hx <;> rcases h' with h' | h' <;> addr_omega [hz, h', hx, hb1])
      (by rcases hx with hx | hx | hx <;> constructor <;> addr_omega [hb1, hx])
  have K1 : ∀ x : Word, (s.getReg .x2 - 1344).toNat ≤ x.toNat ∧
      x.toNat + 8 ≤ (s.getReg .x2 - 840).toNat → t.getMem x = w.getMem x :=
    fun x hx ↦ kT x (Or.inl hx)
  have p1256 : t.getMem (s.getReg .x2 - 1256) = w.getMem (s.getReg .x2 - 1256) :=
    K1 _ (by constructor <;> addr_omega [hb1])
  refine ⟨t, hrw.trans (hry.trans (hrz.trans hrt)), Or.inr ⟨hpct, {
    inv := I
    kept := C.kept.step hpre (st.toR.weaken fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by addr_omega [ha, hb1]))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by addr_omega [ha, hb1])))))))
    claims := CS
    len := l5
    x1 := x1
    x10 := x10
    x11 := by rw [x11, p1256]; exact C.x27
    x12 := by rw [x12]; exact C.x24
    x20 := by rw [rg .x20 (by decide)]; exact C.x20
    x21 := by rw [rg .x21 (by decide)]; exact C.x21
    x23 := by rw [rg .x23 (by decide)]; exact C.x23
    x24 := by rw [rg .x24 (by decide)]; exact C.x24
    x27 := by rw [rg .x27 (by decide), p1256]; exact C.x27
    memory := C.memory.keepR hpre st.toR fT (by addr_omega [hb1]) fun z hz h' ↦ by
      rcases h' with h' | h' <;> addr_omega [hz, h', hb1]
    values := C.values.keepR hpre st.toR fT (by addr_omega [hb1]) fun z hz h' ↦ by
      rcases h' with h' | h' <;> addr_omega [hz, h', hb1]
    point := by
      rw [K1 _ (by constructor <;> addr_omega [hb1]), p1256,
        K1 _ (by constructor <;> addr_omega [hb1])]
      exact C.point.keepR hpre st.toR fT
    valuesPtr := by
      rw [K1 _ (by constructor <;> addr_omega [hb1]), C.valuesPtr, vecPtr, vecPtr,
        kT _ (Or.inr (Or.inr (by constructor <;> addr_omega [hb1])))]
    pushPtr := by rw [K1 _ (by constructor <;> addr_omega [hb1])]; exact C.pushPtr
    lm := C.lm
    lb := C.lb
    mfEq := by
      rw [rg .x25 (by decide), rg .x22 (by decide), K1 _ (by constructor <;> addr_omega [hb1])]
      exact C.mfEq
    bfEq := by
      rw [rg .x26 (by decide), K1 _ (by constructor <;> addr_omega [hb1]),
        K1 _ (by constructor <;> addr_omega [hb1])]
      exact C.bfEq
    tracks := C.tracks.keep fun T hT ↦ st.transcript hpre C.inv fT hT }⟩⟩

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
