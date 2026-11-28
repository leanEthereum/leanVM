module

public import NativeRustcVmX64.Bus.AccumulateSide.LoopKA
public import NativeRustcVmX64.Code.Vm.EWMul.Names

/-!
# `accumulate_side`: the known part's turn, from `eq_above` (x86-64)

`b3` multiplies the selector by `side_beta` plus the fingerprint (`EW::mul`), `b4` adds the
product to the sum (R15, R13) and goes to the next turn or out. `turnK`: a whole turn.
-/

namespace NativeRustcVmX64.Bus.AccumulateSide

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeRustcVmX64.Vm.AccumulateSide
open NativeVm.Model NativeRustcVm.Bus NativeRustcVm.Layout

public section

theorem ewRet_c0 {m : MachineData} {x : EW} (h : ewRet m = x) :
    m.regs.get64 .rax = x.c0.toBitVec := by
  rw [← h]; rfl

theorem ewRet_c1 {m : MachineData} {x : EW} (h : ewRet m = x) :
    m.regs.get64 .rdx = x.c1.toBitVec := by
  rw [← h]; rfl

variable [Host] {L : LayoutW} {rows : Array Nat} {bl : List NativeRustcVm.Data.Block}
  {Fm : Array (Array FormW)} {SL : BusLayoutW} {m0 : MachineData} {k : Nat}

/-- **The known part's turn `i`, from `eq_above`'s return.** -/
theorem turnKB (hp : Placed code k) (h : Pre L rows bl Fm SL m0)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {i : Nat} (hi : i < cA SL m0) {st : MachineData}
    (hst : St m0 Z (Vt SL m0 (lpK SL m0 i)) DKc 8 st) (hret : ewRet st = fsel SL (ptA m0) i) :
    Eventually (step1 Host.exe) (fun st' ↦
      St m0 Z (Vt SL m0 (lpK SL m0 (i + 1))) DK 8 st'.data ∧
      ((st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b2Offset) ∧ i + 1 < cA SL m0) ∨
        (st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b5Offset) ∧ i + 1 = cA SL m0)))
      ⟨st, Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b3Offset)⟩ := by
  let V := Vt SL m0 (lpK SL m0 i)
  have hcA : cA SL m0 ≤ 3 := Nat.le_trans (Nat.min_le_right _ _) h.fw.1
  obtain ⟨hmid, hw, htr⟩ := ok_b3
  refine St.run h (rest := []) (vs := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b3Offset + b3.length)).toBitVec)
    rfl (infix_of b3_in_code (by simp [b3]) hp) exit_b3 (fun _ _ ↦ rfl) hst.fr hst.same
    ((hst.hd.append (holds_reg (V := V) (i := 40) (ewRet_c0 hret)
      (holds_reg (i := 41) (ewRet_c1 hret) (holds_nil _ _ _)))).reg0 (by decide) rfl) (by decide)
    (wf0 h hst.fr.kept) (St.mt hst ⟨rfl, trivial⟩ trivial trivial trivial) hmid hw (by decide) htr
    fun st5 _ hpc5 hst5 _ ↦ ?_
  have r_di := hst5.hd.reg (r := .rdi) (i := 40) (by decide)
  have r_si := hst5.hd.reg (r := .rsi) (i := 41) (by decide)
  have r_dx := hst5.hd.reg (r := .rdx) (i := 38) (by decide)
  have r_cx := hst5.hd.reg (r := .rcx) (i := 39) (by decide)
  have hst5c : St m0 Z V DKc 0 st5.data := St.sub hst5 (by decide)
  refine St.call h hst5c le_mul (lo := 0) (n := 0) (by decide) (by decide) hmul hpc5
    (St.stackOk h hst5c le_mul) (W := Z) (fun _ h ↦ h.elim)
    (fun _ hq ↦ ⟨same_call hq.2.2.1, hq.2.2.2⟩) fun m6 hst6 hq6 ↦ ?_
  have e_ax : m6.regs.get64 .rax = (V 42).toBitVec := by
    rw [show m6.regs.get64 .rax = _ from hq6.1]
    show (EW.mul ⟨.ofBitVec (st5.data.regs.get64 .rdi), .ofBitVec (st5.data.regs.get64 .rsi)⟩
      ⟨.ofBitVec (st5.data.regs.get64 .rdx), .ofBitVec (st5.data.regs.get64 .rcx)⟩).c0.toBitVec = _
    rw [r_di, r_si, r_dx, r_cx]
    rfl
  have e_dx : m6.regs.get64 .rdx = (V 43).toBitVec := by
    rw [show m6.regs.get64 .rdx = _ from hq6.2.1]
    show (EW.mul ⟨.ofBitVec (st5.data.regs.get64 .rdi), .ofBitVec (st5.data.regs.get64 .rsi)⟩
      ⟨.ofBitVec (st5.data.regs.get64 .rdx), .ofBitVec (st5.data.regs.get64 .rcx)⟩).c1.toBitVec = _
    rw [r_di, r_si, r_dx, r_cx]
    rfl
  -- `b4`: the product added, the next turn.
  show Eventually _ _ (⟨m6, Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b4Offset)⟩ : MachineState)
  obtain ⟨hmid4, hw4, htr4, hbp4, h154, h134⟩ := ok_b4
  refine St.run h (rest := [(rspOf m0 + 8#64, 88)]) (vs := fun _ ↦ 0) (ret := 0) rfl
    (infix_of b4_in_code (by simp [b4]) hp) exit_b4 nofun hst6.fr hst6.same
    ((((hst6.hd.append (holds_reg (V := V) (i := 42) e_ax
      (holds_reg (i := 43) e_dx (holds_nil _ _ _)))).reg0
        (rs' := (fb m0, F + 8) :: [(rspOf m0 + 8#64, 88)]) (by decide) rfl)).append
      (St.holdsDA h hst6 Z_outs)) (by decide)
    (wf1 h hst6.fr.kept h.argsIn)
    (St.mt hst6 ⟨rfl, rfl, trivial⟩ trivial trivial argAliases_ok) hmid4 hw4 (by decide) htr4
    fun st7 hm7 hpc7 hst7 _ ↦ ?_
  have g_bp := hst6.hd.reg (r := .rbp) (i := 32) (by decide)
  have g_15 := hst6.hd.reg (r := .r15) (i := 33) (by decide)
  have g_13 := hst6.hd.reg (r := .r13) (i := 34) (by decide)
  have g24 : (Env.ofMachine m6 [(fb m0, F + 8)]).load 0 24 8 = (V 19).toBitVec :=
    hst6.hd.load (by decide)
  have e_bp : st7.data.regs.get64 .rbp = BitVec.ofNat 64 (16 * (i + 1)) := by
    rw [hm7.regs .rbp _ hbp4]
    show BinOp.apply .add .W64 (BitVec.ofNat 64 16) (m6.regs.get64 .rbp) = _
    rw [add64, g_bp]
    show BitVec.ofNat 64 16 + BitVec.ofNat 64 (16 * i) = _
    rw [← BitVec.ofNat_add]
    congr 1
    omega
  have hkn := knownN_succ SL (ptA m0) (fpsA m0) (betaA m0) i
  have e_15 : st7.data.regs.get64 .r15 = (Vt SL m0 (lpK SL m0 (i + 1)) 33).toBitVec := by
    rw [hm7.regs .r15 _ h154]
    show BinOp.apply .xor .W64 (m6.regs.get64 .r15) (m6.regs.get64 .rax) = _
    rw [xor64, g_15, e_ax]
    show _ = ((knownN SL (ptA m0) (fpsA m0) (betaA m0) (i + 1)).c0).toBitVec
    rw [hkn, add_c0, UInt64.toBitVec_xor]
    rfl
  have e_13 : st7.data.regs.get64 .r13 = (Vt SL m0 (lpK SL m0 (i + 1)) 34).toBitVec := by
    rw [hm7.regs .r13 _ h134]
    show BinOp.apply .xor .W64 (m6.regs.get64 .r13) (m6.regs.get64 .rdx) = _
    rw [xor64, g_13, e_dx]
    show _ = ((knownN SL (ptA m0) (fpsA m0) (betaA m0) (i + 1)).c1).toBitVec
    rw [hkn, add_c1, UInt64.toBitVec_xor]
    rfl
  have hnext : St m0 Z (Vt SL m0 (lpK SL m0 (i + 1))) DK 8 st7.data :=
    St.add hst7 (fun p hp ↦ Vt_lt (by revert p hp; decide))
      (holds_reg (by rw [e_bp]; rfl) (holds_reg e_15 (holds_reg e_13 (holds_nil _ _ _))))
  have hc4 : c4.eval (frameEnv m0 m6 F [(rspOf m0 + 8#64, 88)] (fun _ ↦ 0) 0) = decide (i + 1 ≠ cA SL m0) := by
    show (!(CmpOp.apply .eq .W64 ((frameEnv m0 m6 F [(rspOf m0 + 8#64, 88)] (fun _ ↦ 0) 0).load 0 24 8)
      (BinOp.apply .add .W64 (BitVec.ofNat 64 16) (m6.regs.get64 .rbp)))) = _
    rw [show (frameEnv m0 m6 F [(rspOf m0 + 8#64, 88)] (fun _ ↦ 0) 0).load 0 24 8 = _ from g24, add64, g_bp]
    show (!(CmpOp.apply .eq .W64 (BitVec.ofNat 64 (16 * cA SL m0))
      (BitVec.ofNat 64 16 + BitVec.ofNat 64 (16 * i)))) = _
    rw [← BitVec.ofNat_add, eq64]
    rw [Bool.eq_iff_iff, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_iff]
    constructor
    · intro hne heq; exact hne (by rw [← heq]; congr 1; omega)
    · intro hne heq
      have := congrArg BitVec.toNat heq
      rw [toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)] at this
      exact hne (by omega)
  simp only [PcOk] at hpc7
  rw [hc4] at hpc7
  by_cases hlast : i + 1 = cA SL m0
  · simp only [hlast, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
      at hpc7
    exact .done _ ⟨hnext, .inr ⟨by rw [hpc7]; rfl, hlast⟩⟩
  · simp only [hlast, ne_eq, not_false_eq_true, decide_true, ↓reduceIte] at hpc7
    exact .done _ ⟨hnext, .inl ⟨by rw [hpc7]; exact hp.label NativeRustcVmX64.Vm.AccumulateSide.label_2_at, by omega⟩⟩

end

end NativeRustcVmX64.Bus.AccumulateSide
