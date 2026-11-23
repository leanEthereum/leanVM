module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.Powers.Names
public import NativeRustcVmArm.Arrays.Powers.Exec

/-!
# `powers` on AArch64

**`powers_spec`**: rustc's `powers(base, out)`, placed anywhere in the program, meets
`PowersPre`/`PowersPost` given `EW::mul`'s contract: `out` holds `powers base |out|`. At
`|out| = 0` it returns at once (`b0`, `b5`); else the prologue (`b1`) saves X19-X22 and X30 in its
48-byte frame and the loop (`b2`, `EW::mul`, `b3`) stores the power (X0, X1) in `out[i]` and
multiplies it by the base (`Inv`: the model's fold after `i` steps, its array in `out`'s first `i`
slots), and the epilogue (`b4`, `b5`) returns.
-/

namespace NativeRustcVmArm.Arrays.Powers

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.Powers NativeVm.Model
open NativeRustcVm (ewsOf ewOf EWsAt EWAt WordAt)

public section

/-- `out`. -/
abbrev out (m : MachineData) : BitVec 64 := m.regs.X2.toBitVec
/-- `|out|`. -/
abbrev len (m : MachineData) : Nat := m.regs.X3.toNat
/-- The base. -/
abbrev base (m : MachineData) : EW := ⟨m.regs.X0, m.regs.X1⟩

/-- The model's fold after `n` steps. -/
@[expose] def P (b : EW) (n : Nat) : Array EW × EW :=
  (List.range n).foldl (fun (acc : Array EW × EW) _ ↦ (acc.1.push acc.2, acc.2 * b)) (#[], 1)

theorem P_succ (b : EW) (n : Nat) : P b (n + 1) = ((P b n).1.push (P b n).2, (P b n).2 * b) := by
  unfold P
  rw [List.range_succ, List.foldl_append]
  rfl

theorem length_P (b : EW) (n : Nat) : (P b n).1.toList.length = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [P_succ]; simp [ih]

theorem powers_eq (b : EW) (n : Nat) : powers b n = (P b n).1 := rfl

/-- **The loop head** `.LPowers_2`, `i` powers stored. -/
structure Inv (m0 : MachineData) (i : Nat) (s : MachineData) : Prop where
  body : Body m0 48 powersStack slots (out m0) (16 * len m0) s
  lt : i < len m0
  x19 : s.regs.X19.toBitVec = out m0 + BitVec.ofNat 64 (16 * i)
  x22 : s.regs.X22.toBitVec = out m0 + BitVec.ofNat 64 (16 * len m0)
  x21 : s.regs.X21 = m0.regs.X0
  x20 : s.regs.X20 = m0.regs.X1
  pw : (⟨s.regs.X0, s.regs.X1⟩ : EW) = (P (base m0) i).2
  written : EWsAt s.dmem (out m0) (P (base m0) i).1.toList

variable [Host] {k : Nat}

theorem hb0 (hp : Placed code k) : b0.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Powers.b0Offset) :=
  b0_in_code.trans hp.1 (by simp [b0])
theorem hb1 (hp : Placed code k) : b1.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Powers.b1Offset) :=
  b1_in_code.trans hp.1 (by simp [b1])
theorem hb2 (hp : Placed code k) : b2.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Powers.b2Offset) :=
  b2_in_code.trans hp.1 (by simp [b2])
theorem hb3 (hp : Placed code k) : b3.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Powers.b3Offset) :=
  b3_in_code.trans hp.1 (by simp [b3])
theorem hb4 (hp : Placed code k) : b4.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Powers.b4Offset) :=
  b4_in_code.trans hp.1 (by simp [b4])
theorem hb5 (hp : Placed code k) : b5.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Powers.b5Offset) :=
  b5_in_code.trans hp.1 (by simp [b5])

theorem lbl_entry (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.Powers.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.Powers.b0Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.Powers.entryOffset) NativeRustcVmArm.Vm.Powers.entry_at
theorem lbl_2 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.Powers.label_2 = Host.addrOf (k + NativeRustcVmArm.Vm.Powers.b2Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.Powers.b2Offset) NativeRustcVmArm.Vm.Powers.label_2_at
theorem lbl_4 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.Powers.label_4 = Host.addrOf (k + NativeRustcVmArm.Vm.Powers.b5Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.Powers.b5Offset) NativeRustcVmArm.Vm.Powers.label_4_at

/-- The postcondition, reached. -/
abbrev Post (m0 : MachineData) (s : MachineState) : Prop :=
  s.pc = retOf m0 ∧ PowersPost m0 s.data

/-- **The epilogue** `b4`, `b5`. -/
theorem finish (hp : Placed code k) {m0 : MachineData} (hpre : PowersPre m0) {s : MachineState}
    (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.Powers.b4Offset))
    (hb : Body m0 48 powersStack slots (out m0) (16 * len m0) s.data)
    (hw : EWsAt s.data.dmem (out m0) (P (base m0) (len m0)).1.toList) :
    Eventually (step1 Host.exe) (Post m0) s := by
  obtain ⟨hwf, hm⟩ := hb.exit_match hpre.1 (by decide) rfl
  refine exec_at (hb4 hp) run_b4 hwf hpc hm fun s' hm' hpc' ↦ ?_
  obtain ⟨hsaved, hx30, hdm⟩ := hb.saved hm' hwf (List.mem_map.mpr ⟨(0, .X30), by simp [slots], rfl⟩)
    (after_eq run_b4 ▸ b4_restores) rfl
  simp only [PcOk, NativeRustcVmArm.Vm.Powers.b4_length, NativeRustcVmArm.Vm.Powers.b4Length] at hpc'
  refine exec_at (hb5 hp) run_b5 (Env.wf_nil _) hpc' (match_nil _) fun s'' hm'' hpc'' ↦ .done _ ?_
  have hdm' : s''.data.dmem = s'.data.dmem := hm''.dmem_eq (Env.wf_nil _) rfl
  have hk := after_eq run_b5 ▸ b5_keeps
  simp only [keepsAll, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hk
  have hreg : ∀ r ∈ savedRegs, s''.data.regs.getXReg r = s'.data.regs.getXReg r := fun r hr ↦ by
    obtain ⟨hs, he⟩ := hk.1.1 r hr
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
    exact Match.reg_eq (match_nil _) hm'' hv (he.trans hv)
  refine ⟨?_, ?_, ?_, hsaved.trans ⟨fun r hr ↦ hreg r (mem_savedRegs hr),
    Match.sp_eq (match_nil _) hm'' hk.1.2, fun p hp ↦ by rw [hdm']; exact hp⟩⟩
  · simp only [PcOk] at hpc''
    rw [hpc'']
    simp only [retOf]
    rw [show s''.data.regs.X30 = s'.data.regs.X30 from hreg .X30 (by simp [savedRegs]), hx30]
  · rw [hdm', hdm, powers_eq]
    exact hw
  · intro p hp'
    rw [hdm', hdm]
    exact hb.same p hp'

/-- **A turn of the loop**: the power stored in `out[i]`, multiplied by the base, back at the head
or out of the loop and returned. -/
theorem step (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {m0 : MachineData} (hpre : PowersPre m0) {i : Nat} {s : MachineState}
    (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.Powers.b2Offset)) (hI : Inv m0 i s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ Post m0 s' ∨
      (s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.Powers.b2Offset) ∧ Inv m0 (i + 1) s'.data)) s := by
  obtain ⟨hS, ⟨hmO, hnO⟩, hoO⟩ := hpre
  have hlt := hI.lt
  have hL : len m0 = m0.regs.X3.toNat := rfl
  have hnw : (out m0).toNat + 16 * len m0 ≤ 2 ^ 64 := hnO
  have hnw' : m0.regs.X2.toBitVec.toNat + 16 * m0.regs.X3.toNat ≤ 2 ^ 64 := hnO
  have hlt' : i < m0.regs.X3.toNat := hlt
  have hco : (out m0).toNat = m0.regs.X2.toBitVec.toNat := rfl
  obtain ⟨s, pc⟩ := s
  simp only at hpc
  -- the slot `out[i]`
  have hnA : NoWrap (out m0 + BitVec.ofNat 64 (16 * i)) 16 := by
    unfold NoWrap; rw [toNat_add_ofNat' (by omega)]; omega
  have hmA : Mapped s.dmem (out m0 + BitVec.ofNat 64 (16 * i)) 16 := fun j hj ↦ by
    rw [NativeRustcVm.addr_add]; exact hI.body.kept _ (hmO _ (by omega))
  have hwf := wf_one hmA hnA (m := s)
  have hm : Match (Env.ofMachine s [(out m0 + BitVec.ofNat 64 (16 * i), 16)]) (ldS .X19 0) s :=
    match_ofMachine ⟨rfl, nofun, trivial⟩ rfl
      ⟨by show s.regs.X19.toBitVec = _; rw [hI.x19]; exact (BitVec.add_zero _).symm, trivial⟩
      trivial trivial trivial
  refine exec_at (hb2 hp) run_b2 hwf hpc hm fun s2 hm2 hpc2 ↦ ?_
  simp only [NativeRustcVmArm.Vm.Powers.b2_length, NativeRustcVmArm.Vm.Powers.b2Length] at hpc2
  obtain ⟨hk2, hw2, hw0, hw1⟩ := after_eq run_b2 ▸ b2_facts
  have hin : ∀ p, InRange (out m0 + BitVec.ofNat 64 (16 * i)) 16 p → InRange (out m0) (16 * len m0) p :=
    fun p h ↦ inRange_mono h (by omega)
  have hfr : Apart (out m0 + BitVec.ofNat 64 (16 * i)) 16 (stackBelow m0 powersStack) powersStack := by
    unfold OffStack at hoO
    unfold Apart at hoO ⊢
    rw [toNat_add_ofNat' (by omega)]
    omega
  have bd2 := hI.body.of_write hS hm hm2 hwf hin hk2 hw2 hfr (by decide) (by decide)
  have hsame2 := same_of_region0 hm2 hwf hw2
  have hslot : EWAt s2.data.dmem (out m0 + BitVec.ofNat 64 (16 * i)) (P (base m0) i).2 := by
    rw [← hI.pw, NativeRustcVm.ewAt_iff]
    have a0 := wordAt_of_write hm2 (o := 0) (by decide) hw0
    have a1 := wordAt_of_write hm2 (o := 8) (by decide) hw1
    rw [add_ofNat_zero] at a0
    exact ⟨a0, a1⟩
  have hpre2 : EWsAt s2.data.dmem (out m0) (P (base m0) i).1.toList := by
    refine bytesAt_congr hI.written fun j hj ↦ hsame2 _ fun h ↦ ?_
    rw [length_flatMap_ewBytes, length_P] at hj
    rw [inRange_iff hnA, toNat_add_ofNat' (by omega), toNat_add_ofNat' (by omega)] at h
    omega
  refine call_then hpc2 hmul (bd2.ewMulPre hS (by decide) (by decide)) fun s3 hpc3 hpost ↦ ?_
  have bd3 := bd2.call hS (by decide) (by decide) hpost
  have hkeep3 : ∀ p, InRange (out m0) (16 * len m0) p → s3.data.dmem.get? p = s2.data.dmem.get? p :=
    fun p hp' ↦ hpost.2.2.1 p fun h ↦ by
      unfold stackBelow at h
      rw [bd2.sp] at h
      have h' := inRange_stack (n := ewMulStack) (F := 48) (S := powersStack) (by decide) hS.2.1 h
      have hsnw : NoWrap (m0.regs.SP.toBitVec - BitVec.ofNat 64 powersStack) powersStack :=
        stack_noWrap hS
      have hSle : powersStack ≤ m0.regs.SP.toBitVec.toNat := hS.2.1
      rw [inRange_iff hnO] at hp'
      rw [inRange_iff hsnw, toNat_sub_ofNat hSle] at h'
      unfold OffStack Apart stackBelow at hoO
      rw [toNat_sub_ofNat hSle] at hoO
      omega
  have hw3 : EWsAt s3.data.dmem (out m0) (P (base m0) (i + 1)).1.toList := by
    rw [P_succ, Array.toList_push, NativeRustcVm.ewsAt_append, NativeRustcVm.ewsAt_singleton,
      length_P]
    refine ⟨bytesAt_keep hpre2 (by rw [length_flatMap_ewBytes, length_P]; omega) hnO hkeep3,
      bytesAt_keep hslot (by rw [NativeRustcVm.length_ewBytes]) hnA fun p h ↦ hkeep3 p (hin p h)⟩
  have hprod : (⟨s3.data.regs.X0, s3.data.regs.X1⟩ : EW) = (P (base m0) (i + 1)).2 := by
    rw [P_succ, hpost.1, hpost.2.1, ← hI.pw]
    show EW.mul ⟨s2.data.regs.getXReg .X0, s2.data.regs.getXReg .X1⟩
      ⟨s2.data.regs.getXReg .X2, s2.data.regs.getXReg .X3⟩ = _
    have h0 := hm2.regs .X0 _ rfl
    have h1 := hm2.regs .X1 _ rfl
    have h2 := hm2.regs .X2 _ rfl
    have h3 := hm2.regs .X3 _ rfl
    simp only [Sym.eval, Env.ofMachine_regs] at h0 h1 h2 h3
    rw [UInt64.toBitVec_inj.mp h0, UInt64.toBitVec_inj.mp h1, UInt64.toBitVec_inj.mp h2,
      UInt64.toBitVec_inj.mp h3]
    show EW.mul _ ⟨s.regs.X21, s.regs.X20⟩ = _
    rw [hI.x21, hI.x20]
    rfl
  have e3 : ∀ r ∈ [XReg.X20, .X21, .X22], s3.data.regs.getXReg r = s.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact (hpost.2.2.2.1 _ rfl).trans (Match.reg_eq hm hm2 rfl rfl)
  have hx19 : (s3.data.regs.getXReg .X19).toBitVec = out m0 + BitVec.ofNat 64 (16 * (i + 1)) := by
    rw [hpost.2.2.2.1 .X19 rfl]
    have h := hm2.regs .X19 _ rfl
    simp only [Sym.eval, base0] at h
    rw [h, show BitVec.ofInt 64 16 = BitVec.ofNat 64 16 from rfl, NativeRustcVm.addr_add]
    congr 2
  -- the loop test
  refine exec_at (hb3 hp) run_b3 (Env.wf_nil _) hpc3 (match_nil _) fun s4 hm4 hpc4 ↦ ?_
  have bd4 := bd3.of_block (match_nil _) hm4 (Env.wf_nil _) rfl (after_eq run_b3 ▸ b3_keeps)
  have hdm4 : s4.data.dmem = s3.data.dmem := hm4.dmem_eq (Env.wf_nil _) rfl
  have e4 : ∀ r, s4.data.regs.getXReg r = s3.data.regs.getXReg r := fun r ↦ by
    cases r <;> exact Match.reg_eq (match_nil _) hm4 rfl rfl
  simp only [PcOk] at hpc4
  sym_simp at hpc4
  have hpc4' := pc_ne hpc4
  have heq : (s3.data.regs.getXReg .X19).toBitVec = (s3.data.regs.getXReg .X22).toBitVec ↔
      i + 1 = len m0 := by
    rw [hx19, e3 .X22 (by simp), show (s.regs.getXReg .X22) = s.regs.X22 from rfl, hI.x22]
    constructor
    · intro h
      have h' := congrArg BitVec.toNat h
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h'
      omega
    · intro h; rw [h]
  by_cases hlast : i + 1 = len m0
  · have hpc4 := hpc4'.2 (heq.mpr hlast)
    simp only [NativeRustcVmArm.Vm.Powers.b3_length, NativeRustcVmArm.Vm.Powers.b3Length] at hpc4
    refine Eventually.mono (finish hp ⟨hS, ⟨hmO, hnO⟩, hoO⟩ hpc4 bd4 ?_) fun _ h ↦ Or.inl h
    rw [hdm4, ← hlast]
    exact hw3
  · have hpc4 := hpc4'.1 (fun h ↦ hlast (heq.mp h))
    refine .done _ (Or.inr ⟨hpc4.trans (lbl_2 hp), bd4, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    · show (s4.data.regs.getXReg .X19).toBitVec = _
      rw [e4, hx19]
    · show (s4.data.regs.getXReg .X22).toBitVec = _
      rw [e4, e3 .X22 (by simp)]; exact hI.x22
    · show s4.data.regs.getXReg .X21 = _
      rw [e4, e3 .X21 (by simp)]; exact hI.x21
    · show s4.data.regs.getXReg .X20 = _
      rw [e4, e3 .X20 (by simp)]; exact hI.x20
    · rw [← hprod]
      show (⟨s4.data.regs.getXReg .X0, s4.data.regs.getXReg .X1⟩ : EW) = _
      rw [e4, e4]
      rfl
    · rw [hdm4]; exact hw3

/-- **`powers` meets its contract.** -/
theorem powers_spec (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) :
    Spec (Labels.label NativeRustcVmArm.Vm.Powers.entryLabel) PowersPre PowersPost := by
  intro m0 hpre
  rw [lbl_entry hp]
  obtain ⟨hS, ⟨hmO, hnO⟩, hoO⟩ := hpre
  have h48 : 48 ≤ powersStack := by decide
  obtain ⟨hwf, hm⟩ := entry_match hS h48 rfl
  refine exec_then (hb0 hp) run_b0 hwf hm fun s1 hm1 hpc1 ↦ ?_
  simp only [PcOk, NativeRustcVmArm.Vm.Powers.b0_length, NativeRustcVmArm.Vm.Powers.b0Length] at hpc1
  sym_simp at hpc1
  have hpc1' := pc_cond hpc1
  by_cases hz : len m0 = 0
  · -- `|out| = 0`.
    have hpc1 := hpc1'.1 (by
      show ((m0.regs.getXReg .X3).toBitVec == 0#64) = true
      rw [beq_iff_eq]
      apply BitVec.eq_of_toNat_eq
      exact hz)
    obtain ⟨hk, hmem⟩ := after_eq run_b5e ▸ b5e_keeps
    refine exec_at (hb5 hp) (exec_after run_b0 run_b5e) hwf (hpc1.trans (lbl_4 hp)) hm1
      fun s2 hm2 hpc2 ↦ .done _ ⟨?_, ?_, ?_, ?_⟩
    · simp only [PcOk] at hpc2
      rw [hpc2]
      simp only [retOf]
      rw [show s2.data.regs.X30 = m0.regs.X30 from Match.reg_eq (r := .X30) hm hm2 rfl rfl]
    · show EWsAt _ _ (powers _ (len m0)).toList
      rw [hz]
      exact NativeRustcVm.ewsAt_nil _ _
    · intro p _
      rw [hm2.dmem_eq hwf hmem]
      rfl
    · exact Match.saved hm hm2 hwf rfl hk
  · have hpc1 := hpc1'.2 (by
      show ¬((m0.regs.getXReg .X3).toBitVec == 0#64) = true
      rw [beq_iff_eq]
      intro h
      exact hz (congrArg BitVec.toNat h))
    refine exec_at (hb1 hp) (exec_after run_b0 run_b1) hwf hpc1 hm1 fun s2 hm2 hpc2 ↦ ?_
    simp only [PcOk, NativeRustcVmArm.Vm.Powers.b1_length, NativeRustcVmArm.Vm.Powers.b1Length] at hpc2
    obtain ⟨hw, hmem, hregs⟩ := after_eq run_b1 ▸ b1_frame
    have hI : Inv m0 0 s2.data := by
      have h0 := reg_of hm2 (r := .X0) rfl
      have h1 := reg_of hm2 (r := .X1) rfl
      have h19 := hm2.regs .X19 _ rfl
      have h20 := reg_of hm2 (r := .X20) rfl
      have h21 := reg_of hm2 (r := .X21) rfl
      have h22 := hm2.regs .X22 _ rfl
      simp only [Sym.eval, UnOp.apply, shiftW, Sym.ext_W64, Sym.low_W64, shl4] at h22
      sym_simp at h0 h1 h19 h20 h21 h22
      simp only [Env.ofMachine_regs, UInt64.ofBitVec_toBitVec] at h19 h20 h21 h22
      refine ⟨Body.of_entry hS h48 hm2 rfl hw hregs hmem, Nat.pos_of_ne_zero hz, ?_, ?_, h21, h20,
        ?_, ?_⟩
      · show (s2.data.regs.getXReg .X19).toBitVec = _
        rw [h19, Nat.mul_zero, add_ofNat_zero]
        rfl
      · show (s2.data.regs.getXReg .X22).toBitVec = _
        rw [h22]
        rfl
      · show (⟨s2.data.regs.getXReg .X0, s2.data.regs.getXReg .X1⟩ : EW) = _
        rw [h0, h1]
        rfl
      · exact NativeRustcVm.ewsAt_nil _ _
    refine Sym.loop (fun n s ↦ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.Powers.b2Offset) ∧ ∃ i, len m0 - i = n ∧
      Inv m0 i s.data) (fun n s ⟨hpc, i, hn, hI⟩ ↦ ?_) ⟨hpc2, 0, rfl, hI⟩
    refine Eventually.mono (step hp hmul ⟨hS, ⟨hmO, hnO⟩, hoO⟩ hpc hI) fun s' h ↦ ?_
    rcases h with h | ⟨hpc', hI'⟩
    · exact Or.inl h
    · exact Or.inr ⟨len m0 - (i + 1), by have := hI'.lt; omega, hpc', i + 1, rfl, hI'⟩

end

end NativeRustcVmArm.Arrays.Powers
