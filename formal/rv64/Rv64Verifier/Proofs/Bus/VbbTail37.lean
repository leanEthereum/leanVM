import Rv64Verifier.Proofs.Bus.VbbTail36

/-!
# `verify_bus_balance`'s side loop: the point and the layout's buffers at the head

At the loop's head `h`, the point in `s11` and `S - 1144` (`pointAt`), and side `i`'s `BusLayout`'s
framework and tables buffers (`SideOk.fwBuf`, `SideOk.tbBuf`), lie in the heap below `z`'s `NEXT`.
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript

theorem pointAt {bev : MachineState → Word → List E → Option E} {s z w v h₀ h : MachineState}
    {k : Start} {state : GkrState} {mem : List E} {mf bf bv : E} {P : Word} {n : Nat}
    {acc : List (List Form) × List E} (hpre : BusBalancePre s)
    (C : SCtx bev s z w v h₀ k state mem mf bf bv) (Sd : Sides s z h₀ h P n acc) :
    PointAt z h (h.getReg .x27) (h.getMem (s.getReg .x2 - 1144)) state.point := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have F := C.fps
  have En := sideEnv hpre C Sd
  have stZH := (C.rows1.step.trans C.setup.step).trans Sd.step
  have hx27 : h.getReg .x27 = z.getMem (s.getReg .x2 - 1256) :=
    Sd.x27.trans ((C.setup.regs .x27 (by decide)).trans ((C.rows1.regs .x27 (by decide)).trans
      ((C.rows0.regs .x27 (by decide)).trans F.x27)))
  have h1144 : h.getMem (s.getReg .x2 - BitVec.ofNat 64 1144) =
      z.getMem (s.getReg .x2 - BitVec.ofNat 64 1144) :=
    stZH.slot' hpre (by omega) (by omega) fun y hy hy' ↦ by
      simp only [RowsW, SetupW, LoopW] at hy'
      rcases hy' with ((hy' | hy' | hy') | (hy' | hy')) | (hy' | hy' | hy' | hy' | hy' | hy' | hy' |
        hy') <;> addr_omega [hy, hy', hb1]
  have NR := F.point
  have pz := C.ptrs.point
  have hlo := hpre.heap.lo
  rw [hx27, show h.getMem (s.getReg .x2 - 1144) = z.getMem (s.getReg .x2 - 1144) from h1144]
  have hb := NR.buf
  have hl := NR.le
  simp only [NewBuf] at hb
  refine ⟨hb.1, ?_, pz, ?_⟩
  · rcases hb.2 with h0 | h0
    · exact Or.inl (by rw [Nat.mul_eq_zero] at h0; omega)
    · exact Or.inr (by omega)
  · rw [eListAt_heapKept En.hk F.inv.heap.hi (le_refl _) NR.buf (by omega)]
    exact NR.elems

/-- A layout's vector at `S - c`, kept at `h`: its buffer below `z`. -/
theorem layoutBuf {s z v h₀ h : MachineState} (hpre : BusBalancePre s) (En : SideEnv s z v h₀ h)
    {c : Nat} (hc : 936 ≤ c) (hc2 : c ≤ 1080)
    (hv : VecOk z (s.getReg .x2 - BitVec.ofNat 64 c) 16 8)
    (hn : NewBuf s z (vecPtr z (s.getReg .x2 - BitVec.ofNat 64 c))
      (16 * (vecCap z (s.getReg .x2 - BitVec.ofNat 64 c)).toNat) 8) :
    LowBuf (h.getMem (s.getReg .x2 - BitVec.ofNat 64 c + 8))
      (16 * (h.getMem (s.getReg .x2 - BitVec.ofNat 64 c + 16)).toNat) (heapNext z) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hlo := hpre.heap.lo
  have e8 : h.getMem (s.getReg .x2 - BitVec.ofNat 64 c + 8) =
      vecPtr z (s.getReg .x2 - BitVec.ofNat 64 c) := by
    rw [show (8 : Word) = BitVec.ofNat 64 8 from rfl, slot_add (by addr_omega [hb1, hc2]) (by omega)]
    exact (En.hz _ (by omega) (by omega)).trans (congrArg z.getMem
      (slot_add (S := s.getReg .x2) (j := c) (k := 8) (by addr_omega [hb1, hc2]) (by omega)).symm)
  have e16 : h.getMem (s.getReg .x2 - BitVec.ofNat 64 c + 16) =
      vecLen z (s.getReg .x2 - BitVec.ofNat 64 c) := by
    rw [show (16 : Word) = BitVec.ofNat 64 16 from rfl, slot_add (by addr_omega [hb1, hc2]) (by omega)]
    exact (En.hz _ (by omega) (by omega)).trans (congrArg z.getMem
      (slot_add (S := s.getReg .x2) (j := c) (k := 16) (by addr_omega [hb1, hc2]) (by omega)).symm)
  rw [e8, e16]
  have hl := hv.len
  simp only [NewBuf] at hn
  refine ⟨hn.1, ?_⟩
  rcases hn.2 with h0 | h0
  · exact Or.inl (by rw [Nat.mul_eq_zero] at h0; omega)
  · exact Or.inr ⟨by omega, by omega⟩

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
