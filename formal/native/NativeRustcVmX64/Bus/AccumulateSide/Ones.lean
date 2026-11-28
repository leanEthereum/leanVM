module

public import NativeRustcVmX64.Bus.AccumulateSide.LoopO
public import NativeRustcVmX64.Code.Vm.EqEvalFnOfEqAbove.Names

/-!
# `accumulate_side`: the framework ones, the whole loop (x86-64)

`ones`: from `b6` to `b12`, the ones over the framework in R14, R15.
-/

namespace NativeRustcVmX64.Bus.AccumulateSide

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeRustcVmX64.Vm.AccumulateSide
open NativeVm.Model NativeRustcVm.Bus NativeRustcVm.Layout

public section

variable [Host] {L : LayoutW} {rows : Array Nat} {bl : List NativeRustcVm.Data.Block}
  {Fm : Array (Array FormW)} {SL : BusLayoutW} {m0 : MachineData} {k : Nat}

/-- **The ones' loop** from turn `j`. -/
theorem onesLoop (hp : Placed code k) (h : Pre L rows bl Fm SL m0)
    (hee : Spec (Labels.label NativeRustcVmX64.Vm.EqEvalFnOfEqAbove.entryLabel) EqEvalFnOfEqAbovePre EqEvalFnOfEqAbovePost)
    {j : Nat} (hj : j < SL.framework.size) {st : MachineData}
    (hst : St m0 Z (Vt SL m0 (lpO SL m0 j)) DO 8 st) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b10Offset) ∧
      St m0 Z (Vt SL m0 (lpO SL m0 SL.framework.size)) DOf 8 st'.data ∧
      st'.data.regs.get64 .r14 = (sv SL m0 22).toBitVec ∧
      st'.data.regs.get64 .r15 = (sv SL m0 23).toBitVec)
      ⟨st, Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b8Offset)⟩ := by
  refine Sym.loop (fun n (s : MachineState) ↦ ∃ j, n = SL.framework.size - j ∧
      j < SL.framework.size ∧ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b8Offset) ∧
      St m0 Z (Vt SL m0 (lpO SL m0 j)) DO 8 s.data)
    (fun n s ⟨j, hn, hj, hpc, hst⟩ ↦ ?_) ⟨j, rfl, hj, rfl, hst⟩
  obtain ⟨d, pc⟩ := s
  simp only at hpc hst
  subst hpc
  refine (turnO hp h hee hj hst).mono fun s' ⟨hst', e12, e14, e15, hx⟩ ↦ ?_
  rcases hx with ⟨hpc', hlt⟩ | ⟨hpc', heq⟩
  · exact .inr ⟨SL.framework.size - (j + 1), by omega, j + 1, rfl, hlt, hpc',
      St.add hst' (fun _ _ ↦ rfl) (holds_reg e12 (holds_reg e14 (holds_reg e15 (holds_nil _ _ _))))⟩
  · refine .inl ⟨hpc', heq ▸ hst', ?_, ?_⟩
    · rw [e14, heq]; rfl
    · rw [e15, heq]; rfl

/-- **The ones** (`b6` to `b12`): from the ones' head, the ones over the framework. -/
theorem ones (hp : Placed code k) (h : Pre L rows bl Fm SL m0)
    (hee : Spec (Labels.label NativeRustcVmX64.Vm.EqEvalFnOfEqAbove.entryLabel) EqEvalFnOfEqAbovePre EqEvalFnOfEqAbovePost)
    {lp : Nat → UInt64} {st : MachineData} (hst : St m0 Z (Vt SL m0 lp) D6 8 st)
    (lp' : Nat → UInt64) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b12Offset) ∧
      St m0 Z (Vt SL m0 lp') D12 8 st'.data)
      ⟨st, Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b6Offset)⟩ := by
  have hfw := h.fw
  have hslnw := h.slIn.2.1
  unfold NativeRustcVm.NoWrap at hslnw
  have h13 := hst.hd.reg (r := .r13) (i := 17) (by decide)
  have h12 := hst.hd.reg (r := .r12) (i := 18) (by decide)
  obtain ⟨hmid, hw, htr⟩ := ok_b6
  refine St.run h (rest := []) (vs := fun _ ↦ 0) (ret := 0) rfl
    (infix_of b6_in_code (by simp [b6]) hp) exit_b6 nofun hst.fr hst.same
    (hst.hd.reg0 (by decide) rfl) (by decide) (wf0 h hst.fr.kept)
    (St.mt hst ⟨rfl, trivial⟩ trivial trivial trivial) hmid hw (by decide) htr
    fun st1 _ hpc1 hst1 _ ↦ ?_
  have hc6 : c6.eval (frameEnv m0 st F [] (fun _ ↦ 0) 0) = decide (SL.framework.size = 0) := by
    show CmpOp.apply .eq .W64 (BinOp.apply .and .W64 (st.regs.get64 .r13) (st.regs.get64 .r13))
      (BitVec.ofNat 64 0) = _
    rw [h13]
    simp only [BinOp.apply, low_W64, ext_W64, BitVec.and_self, eq64]
    show decide (BitVec.ofNat 64 SL.framework.size = BitVec.ofNat 64 0) = _
    rw [decide_eq_decide]
    constructor
    · intro he
      have := congrArg BitVec.toNat he
      rwa [toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)] at this
    · intro he; rw [he]
  simp only [PcOk] at hpc1
  rw [hc6] at hpc1
  by_cases hz : SL.framework.size = 0
  · -- `b11`: the ones `1`.
    simp only [hz, decide_true, ↓reduceIte] at hpc1
    rw [hp.label NativeRustcVmX64.Vm.AccumulateSide.label_5_at] at hpc1
    obtain ⟨d1, pc1⟩ := st1
    simp only at hpc1 hst1
    subst hpc1
    obtain ⟨-, -, -, hmid11, hw11, htr11, h14, h15, -⟩ := ok_b10
    refine St.run h (rest := []) (vs := fun _ ↦ 0) (ret := 0) rfl
      (infix_of b11_in_code (by simp [b11]) hp) exit_b11 nofun hst1.fr hst1.same
      (hst1.hd.reg0 (by decide) rfl) (by decide) (wf0 h hst1.fr.kept)
      (St.mt hst1 ⟨rfl, trivial⟩ trivial trivial trivial) hmid11 hw11 (by decide) htr11
      fun st2 hm2 hpc2 hst2 _ ↦ .done _ ⟨hpc2, ?_⟩
    have hon : onesF SL (ptA m0) SL.framework.size = 1 := by rw [hz]; rfl
    refine St.sub (St.add (V' := Vt SL m0 lp') hst2 (fun p hp ↦ Vt_lt (by revert p hp; decide))
      (holds_reg (r := .r14) (i := 22) ?_ (holds_reg (r := .r15) (i := 23) ?_ (holds_nil _ _ _))))
      (by decide)
    · rw [hm2.regs .r14 _ h14]
      show BitVec.ofNat 64 1 = (sv SL m0 22).toBitVec
      show _ = ((onesF SL (ptA m0) SL.framework.size).c0).toBitVec
      rw [hon]; rfl
    · rw [hm2.regs .r15 _ h15]
      show BitVec.ofNat 64 0 = (sv SL m0 23).toBitVec
      show _ = ((onesF SL (ptA m0) SL.framework.size).c1).toBitVec
      rw [hon]; rfl
  · -- `b7`: the loop's setup.
    simp only [hz, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc1
    have hpc1' : st1.pc = Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b7Offset) := hpc1
    obtain ⟨d1, pc1⟩ := st1
    simp only at hpc1' hst1
    subst hpc1'
    obtain ⟨hmid7, hw7, htr7, h13', h14, hbx, h15⟩ := ok_b7
    have g12 := hst1.hd.reg (r := .r12) (i := 18) (by decide)
    have g13 := hst1.hd.reg (r := .r13) (i := 17) (by decide)
    refine St.run h (rest := []) (vs := fun _ ↦ 0) (ret := 0) rfl
      (infix_of b7_in_code (by simp [b7]) hp) exit_b7 nofun hst1.fr hst1.same
      (hst1.hd.reg0 (by decide) rfl) (by decide) (wf0 h hst1.fr.kept)
      (St.mt hst1 ⟨rfl, trivial⟩ trivial trivial trivial) hmid7 hw7 (by decide) htr7
      fun st2 hm2 hpc2 hst2 _ ↦ ?_
    have hD : St m0 Z (Vt SL m0 (lpO SL m0 0)) DO 8 st2.data := by
      refine St.sub (St.add hst2 (fun p hp ↦ Vt_lt (by revert p hp; decide))
        (holds_reg (r := .rbx) (i := 27) ?_ (holds_reg (r := .r13) (i := 29) ?_
          (holds_reg (r := .r12) (i := 32) ?_ (holds_reg (r := .r14) (i := 33) ?_
            (holds_reg (r := .r15) (i := 34) ?_ (holds_nil _ _ _))))))) (by decide)
      · rw [hm2.regs .rbx _ hbx]; rfl
      · rw [hm2.regs .r13 _ h13']
        show BinOp.apply .add .W64 (d1.regs.get64 .r12)
          (BinOp.apply .shl .W64 (d1.regs.get64 .r13) (BitVec.ofNat 64 4)) = _
        rw [g12, g13, add64]
        show stackArg m0 0 + 16#64 + BinOp.apply .shl .W64 (BitVec.ofNat 64 SL.framework.size)
          (BitVec.ofNat 64 4) = _
        rw [shl4, toNat_ofNat_lt (by omega)]
        rfl
      · rw [hst2.hd.reg (r := .r12) (i := 18) (by decide)]
        show (UInt64.ofBitVec (stackArg m0 0 + 16#64)).toBitVec =
          (UInt64.ofBitVec (stackArg m0 0 + 16#64 + BitVec.ofNat 64 (16 * 0))).toBitVec
        rw [Nat.mul_zero, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
      · rw [hm2.regs .r14 _ h14]; rfl
      · rw [hm2.regs .r15 _ h15]; rfl
    have hpc2' : st2.pc = Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b8Offset) := by rw [hpc2]; rfl
    obtain ⟨d2, pc2⟩ := st2
    simp only at hpc2' hD
    subst hpc2'
    refine Eventually.bind (onesLoop hp h hee (by omega) hD) fun s ⟨hpc3, hst3, e14, e15⟩ ↦ ?_
    obtain ⟨d3, pc3⟩ := s
    simp only at hpc3 hst3 e14 e15
    subst hpc3
    -- `b10`: to `b12`.
    obtain ⟨hmid10, hw10, htr10, -⟩ := ok_b10
    have hst3' : St m0 Z (Vt SL m0 lp') D12 8 d3 :=
      St.sub (St.add (V' := Vt SL m0 lp') hst3 (fun p hp ↦ Vt_lt (by revert p hp; decide))
        (holds_reg (r := .r14) (i := 22) e14 (holds_reg (r := .r15) (i := 23) e15
          (holds_nil _ _ _)))) (by decide)
    refine St.run h (rest := []) (vs := fun _ ↦ 0) (ret := 0) rfl
      (infix_of b10_in_code (by simp [b10]) hp) exit_b10 nofun hst3'.fr hst3'.same
      (hst3'.hd.reg0 (by decide) rfl) (by decide) (wf0 h hst3'.fr.kept)
      (St.mt hst3' ⟨rfl, trivial⟩ trivial trivial trivial) hmid10 hw10 (by decide) htr10
      fun st4 _ hpc4 hst4 _ ↦ .done _ ⟨by rw [hpc4]; exact hp.label NativeRustcVmX64.Vm.AccumulateSide.label_8_at, hst4⟩

end

end NativeRustcVmX64.Bus.AccumulateSide
