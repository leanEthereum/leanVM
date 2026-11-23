module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Arrays.EqKernel.Basic

/-!
# `eq_kernel` on AArch64: the exits and the loops

The epilogue (`finish13`, after `b12`'s load of the size `finish12`), a round's set-up (`round`:
`b5`-`b7`), a pair (`pair`: `b8`, `EW::mul`, `b9`) and a round's pairs (`inner`).
-/

namespace NativeRustcVmArm.Arrays.EqKernel

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.EqKernel NativeVm.Model
open NativeRustcVm (ewsOf ewOf EWsAt EWAt WordAt half1)

public section

variable [Host] {k : Nat}

/-! ## The exits -/

/-- **The epilogue** `b13`: X0 `1`, X1 the size from X8. -/
theorem finish13 (hp : Placed code k) {m0 : MachineData} (hpre : EqKernelPre m0)
    (hle : 2 ^ np m0 ≤ len m0) {s : MachineState} (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.EqKernel.b13Offset))
    (hb : B m0 s.data) (hx8 : s.data.regs.X8.toNat = 2 ^ np m0) (hx0 : s.data.regs.X0 = 1)
    (hker : EWsAt s.data.dmem (out m0) (K m0 (np m0))) :
    Eventually (step1 Host.exe) (Post m0) s := by
  obtain ⟨hwf, hm⟩ := hb.exit_match hpre.1 (by decide) rfl
  refine exec_at (hb13 hp) run_b13 hwf hpc hm fun s' hm' hpc' ↦ .done _ ?_
  obtain ⟨hsaved, hx30, hdm⟩ := hb.saved hm' hwf
    (List.mem_map.mpr ⟨(24, .X30), by simp [slots], rfl⟩) (after_eq run_b13 ▸ b13_restores) rfl
  simp only [PcOk] at hpc'
  have e0 : s'.data.regs.X0 = s.data.regs.X0 := Match.reg_eq (r := .X0) hm hm' rfl rfl
  have e1 : s'.data.regs.X1 = s.data.regs.X8 := by
    have h := hm'.regs .X1 _ rfl
    simp only [Sym.eval, Env.ofMachine_regs] at h
    exact UInt64.toBitVec_inj.mp h
  refine ⟨?_, ?_, fun p hp' ↦ by rw [hdm]; exact hb.same p hp', hsaved⟩
  · rw [hpc']
    simp only [retOf, hx30]
  · simp only [hle, ↓reduceIte]
    refine ⟨e0.trans hx0, by rw [e1]; exact hx8, ?_⟩
    rw [hdm, ← K_np]
    exact hker

/-- **`.LEqKernel_10`** (`b12`): the size loaded, then the epilogue. -/
theorem finish12 (hp : Placed code k) {m0 : MachineData} (hpre : EqKernelPre m0)
    (hle : 2 ^ np m0 ≤ len m0) {s : MachineState} (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.EqKernel.b12Offset))
    (hb : B m0 s.data) (hf : Frame m0 s.data)
    (hker : EWsAt s.data.dmem (out m0) (K m0 (np m0))) :
    Eventually (step1 Host.exe) (Post m0) s := by
  obtain ⟨hwf, hm⟩ := hb.exit_match hpre.1 (by decide) rfl
  refine exec_at (hb12 hp) run_b12 hwf hpc hm fun s' hm' hpc' ↦ ?_
  simp only [PcOk, NativeRustcVmArm.Vm.EqKernel.b12_length, NativeRustcVmArm.Vm.EqKernel.b12Length] at hpc'
  have hdm : s'.data.dmem = s.data.dmem := hm'.dmem_eq hwf rfl
  have h64 : np m0 < 64 := hpre.2.1
  refine finish13 hp hpre hle hpc' (hb.of_block hm hm' hwf rfl (after_eq run_b12 ▸ b12_keeps))
    ?_ ?_ (by rw [hdm]; exact hker)
  · have h := hm'.regs .X8 _ rfl
    simp only [Sym.eval] at h
    rw [load_word (by rw [add_ofNat_zero]; exact hf.size)] at h
    show (s'.data.regs.getXReg .X8).toBitVec.toNat = _
    rw [h]
    show (UInt64.ofNat (2 ^ np m0)).toNat = _
    rw [UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) h64)
  · rw [show s'.data.regs.X0 = s'.data.regs.getXReg .X0 from rfl, reg_of hm' (r := .X0) rfl]
    rfl

/-! ## The loops -/

/-- **A round's set-up** (`b5`-`b7`): the tests, `point[i]` loaded. -/
theorem round (hp : Placed code k) {m0 : MachineData} (hpre : EqKernelPre m0)
    (hle : 2 ^ np m0 ≤ len m0) {i : Nat} {s : MachineState} (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.EqKernel.b5Offset))
    (hI : OInv m0 i s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.EqKernel.b8Offset) ∧ IInv m0 i 0 s'.data) s := by
  obtain ⟨hS, h64, ⟨⟨hmP, hnP⟩, hoP⟩, ⟨⟨hmO, hnO⟩, hoO⟩, hap⟩ := id hpre
  obtain ⟨hpos, hpow⟩ := pow_facts hle hI.lt
  have hnO' : (out m0).toNat + 16 * len m0 ≤ 2 ^ 64 := hnO
  have a20 : (s.data.regs.getXReg .X20).toBitVec.toNat = len m0 := by
    rw [show s.data.regs.getXReg .X20 = m0.regs.X3 from hI.x20]; rfl
  have a29 : (s.data.regs.getXReg .X29).toBitVec.toNat = 2 ^ i := hI.x29
  -- `b5`: `|out| - 2^i`, `|out| ≥ 2^i`
  refine exec_at (hb5 hp) run_b5 (Env.wf_nil _) hpc (match_nil _) fun s5 hm5 hpc5 ↦ ?_
  have bd5 := hI.body.of_block (match_nil _) hm5 (Env.wf_nil _) rfl (after_eq run_b5 ▸ b5_keeps)
  have hdm5 : s5.data.dmem = s.data.dmem := hm5.dmem_eq (Env.wf_nil _) rfl
  simp only [PcOk, NativeRustcVmArm.Vm.EqKernel.b5_length, NativeRustcVmArm.Vm.EqKernel.b5Length] at hpc5
  sym_simp at hpc5
  have hpc5 := (pc_cond hpc5).2 (by
    simp only [Env.ofMachine_regs, BitVec.ult_iff_lt, BitVec.lt_def, a20, a29]
    omega)
  have a8 : (s5.data.regs.getXReg .X8).toBitVec.toNat = len m0 - 2 ^ i := by
    have h := hm5.regs .X8 _ rfl
    sym_simp at h
    simp only [Env.ofMachine_regs] at h
    rw [h, BitVec.toNat_sub, a20, a29]
    omega
  have e5 : ∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
      s5.data.regs.getXReg r = s.data.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact Match.reg_eq (match_nil _) hm5 rfl rfl
  -- `b6`: `min(|out| - 2^i, 2^i) = 2^i` pairs, `|out| ≠ 2^i`
  refine exec_at (hb6 hp) run_b6 (Env.wf_nil _) hpc5 (match_nil _) fun s6 hm6 hpc6 ↦ ?_
  have bd6 := bd5.of_block (match_nil _) hm6 (Env.wf_nil _) rfl (after_eq run_b6 ▸ b6_keeps)
  have hdm6 : s6.data.dmem = s.data.dmem := (hm6.dmem_eq (Env.wf_nil _) rfl).trans hdm5
  simp only [PcOk, NativeRustcVmArm.Vm.EqKernel.b6_length, NativeRustcVmArm.Vm.EqKernel.b6Length] at hpc6
  sym_simp at hpc6
  have hpc6 := (pc_cond hpc6).2 (by
    simp only [Env.ofMachine_regs, beq_iff_eq]
    intro h
    have h' := congrArg BitVec.toNat h
    rw [e5 .X20 (by simp), e5 .X29 (by simp), a20, a29] at h'
    omega)
  have a19 : (s6.data.regs.getXReg .X19).toBitVec.toNat = 2 ^ i := by
    have h := hm6.regs .X19 _ rfl
    sym_simp at h
    simp only [Env.ofMachine_regs] at h
    have hc : (s5.data.regs.getXReg .X8).toBitVec.ult (s5.data.regs.getXReg .X29).toBitVec = false := by
      simp only [BitVec.ult, decide_eq_false_iff_not, a8, e5 .X29 (by simp), a29]
      omega
    rw [h]
    simp only [hc, Bool.false_eq_true, ↓reduceIte]
    rw [e5 .X29 (by simp), a29]
  have e6 : ∀ r ∈ [XReg.X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
      s6.data.regs.getXReg r = s.data.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (Match.reg_eq (match_nil _) hm6 rfl rfl).trans (e5 _ (by simp))
  -- `b7`: `r = point[i]`
  refine load_step (lo := .X23) (hi' := .X24) (hb7 hp) run_b7 rfl rfl
    (after_eq run_b7 ▸ b7_keeps.1) _ (after_eq run_b7 ▸ b7_keeps.2) bd6 hS ⟨hmP, hnP⟩ hoP hap hnO
    (show i < m0.regs.X1.toNat from hI.lt) hpc6
    (by
      rw [e6 .X22 (by simp)]
      show s.data.regs.X22.toBitVec = _
      rw [hI.x22]
      exact (BitVec.add_zero _).symm)
    fun s7 hm7 hpc7 bd7 hR e7 ↦ .done _ ⟨?_, ?_⟩
  · simp only [PcOk, NativeRustcVmArm.Vm.EqKernel.b7_length, NativeRustcVmArm.Vm.EqKernel.b7Length] at hpc7
    exact hpc7
  obtain ⟨hmA, hnA⟩ := elem_mapped (n := np m0) ⟨hmP, hnP⟩ bd6.kept hI.lt
  have hdm7 : s7.data.dmem = s.data.dmem :=
    (hm7.dmem_eq (wf_one hmA hnA) rfl).trans hdm6
  have q : ∀ r ∈ [XReg.X20, .X22, .X27, .X29],
      s7.data.regs.getXReg r = s.data.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact (e7 _ (by simp)).trans (e6 _ (by simp))
  have x27 : (s6.data.regs.getXReg .X27).toBitVec = out m0 + BitVec.ofNat 64 8 := by
    rw [e6 .X27 (by simp)]; exact hI.x27
  have x29 : (s6.data.regs.getXReg .X29).toBitVec.toNat = 2 ^ i := by
    rw [e6 .X29 (by simp)]; exact hI.x29
  refine ⟨bd7, hI.frame.of_dmem hdm7, hI.lt, hpos, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hR.trans (rr_eq m0 hI.lt).symm, ?_, ?_⟩
  · show (s7.data.regs.getXReg .X29).toNat = _
    rw [q .X29 (by simp)]; exact hI.x29
  · show (s7.data.regs.getXReg .X22).toBitVec = _
    rw [q .X22 (by simp)]; exact hI.x22
  · show s7.data.regs.getXReg .X20 = _
    rw [q .X20 (by simp)]; exact hI.x20
  · show (s7.data.regs.getXReg .X27).toBitVec = _
    rw [q .X27 (by simp)]; exact hI.x27
  · show (s7.data.regs.getXReg .X19).toNat = _
    rw [e7 .X19 (by simp)]
    exact a19
  · have h := hm7.regs .X28 _ rfl
    simp only [Sym.eval, Env.ofMachine_regs] at h
    show (s7.data.regs.getXReg .X28).toBitVec = _
    rw [h, x27]
  · have h := hm7.regs .X21 _ rfl
    simp only [Sym.eval, Env.ofMachine_regs, lsl4, BinOp.apply, Sym.low_W64, Sym.ext_W64] at h
    show (s7.data.regs.getXReg .X21).toBitVec = _
    rw [h, x27, x29, NativeRustcVm.addr_add]
    congr 2
    omega
  · rw [NativeRustcVm.half1_zero, hdm7]; exact hI.ker
  · simp only [List.take_zero, List.map_nil]
    exact NativeRustcVm.ewsAt_nil _ _

/-- **A pair** (`b8`, `EW::mul`, `b9`): `out[2^i + j] = K[j]·r`, `out[j] = K[j] + K[j]·r`; back
at `.LEqKernel_8` or the round done. -/
theorem pair (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {m0 : MachineData} (hpre : EqKernelPre m0) (hle : 2 ^ np m0 ≤ len m0) {i j : Nat}
    {s : MachineState} (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.EqKernel.b8Offset)) (hI : IInv m0 i j s.data) :
    Eventually (step1 Host.exe) (fun s' ↦
      (s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.EqKernel.b8Offset) ∧ IInv m0 i (j + 1) s'.data) ∨
      (s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.EqKernel.b10Offset) ∧ RInv m0 i s'.data)) s := by
  obtain ⟨hS, h64, ⟨⟨hmP, hnP⟩, hoP⟩, ⟨⟨hmO, hnO⟩, hoO⟩, hap⟩ := id hpre
  obtain ⟨hpos, hpow⟩ := pow_facts hle hI.lt
  have hjl := hI.jlt
  have hnO' : (out m0).toNat + 16 * len m0 ≤ 2 ^ 64 := hnO
  have hKlen : (K m0 i).length = 2 ^ i := length_K m0 (Nat.le_of_lt hI.lt)
  have hjK : j < (K m0 i).length := by omega
  have hjL : j < len m0 := by omega
  have hj2 : 2 ^ i + j < len m0 := by omega
  have lA : (((K m0 i).take j).map (· * (1 + rr m0 i))).length = j := by
    simp only [List.length_map, List.length_take]; omega
  have lB : (((K m0 i).take j).map (· * rr m0 i)).length = j := by
    simp only [List.length_map, List.length_take]; omega
  have hlo := hI.lo
  rw [NativeRustcVm.half1_split _ _ hjK, NativeRustcVm.ewsAt_append, NativeRustcVm.ewsAt_append,
    NativeRustcVm.ewsAt_singleton, lA, List.length_singleton, NativeRustcVm.addr_add] at hlo
  obtain ⟨hloA, hloB, hloC⟩ := hlo
  -- `b8`: `out[j]` loaded, `EW::mul`
  obtain ⟨hmA, hnA⟩ := elem_mapped (n := len m0) ⟨hmO, hnO⟩ hI.body.kept hjL
  have hwf8 := wf_one hmA hnA (m := s.data)
  have hm8 : Match (Env.ofMachine s.data [(out m0 + BitVec.ofNat 64 (16 * j), 16)]) loS s.data :=
    match_ofMachine ⟨rfl, nofun, trivial⟩ rfl
      ⟨by
        show s.data.regs.X28.toBitVec = out m0 + BitVec.ofNat 64 (16 * j) + BitVec.ofInt 64 8
        rw [hI.x28, show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, NativeRustcVm.addr_add],
        trivial⟩ trivial trivial trivial
  refine exec_at (hb8 hp) run_b8 hwf8 hpc hm8 fun s8 hm8' hpc8 ↦ ?_
  have bd8 := hI.body.of_block hm8 hm8' hwf8 rfl (after_eq run_b8 ▸ b8_keeps)
  have hdm8 : s8.data.dmem = s.data.dmem := hm8'.dmem_eq hwf8 rfl
  have hKj : ewOf s.data.dmem (out m0 + BitVec.ofNat 64 (16 * j)) = (K m0 i)[j] :=
    NativeRustcVm.ewOf_of_ewAt hloB
  have v01 : (⟨s8.data.regs.getXReg .X0, s8.data.regs.getXReg .X1⟩ : EW) = (K m0 i)[j] := by
    rw [ew_of_loads (lo := .X0) (hi := .X1) (off := 0) hm8' rfl rfl, add_ofNat_zero, hKj]
  have v25 : (⟨s8.data.regs.getXReg .X25, s8.data.regs.getXReg .X26⟩ : EW) = (K m0 i)[j] := by
    rw [ew_of_loads (lo := .X25) (hi := .X26) (off := 0) hm8' rfl rfl, add_ofNat_zero, hKj]
  have v23 : (⟨s8.data.regs.getXReg .X2, s8.data.regs.getXReg .X3⟩ : EW) = rr m0 i := by
    rw [reg_of hm8' (r := .X2) rfl, reg_of hm8' (r := .X3) rfl]
    simp only [Sym.eval, Env.ofMachine_regs, UInt64.ofBitVec_toBitVec]
    exact hI.r
  simp only [NativeRustcVmArm.Vm.EqKernel.b8_length, NativeRustcVmArm.Vm.EqKernel.b8Length] at hpc8
  refine call_then hpc8 hmul (bd8.ewMulPre hS (by decide) (by decide)) fun s9 hpc9 hpost ↦ ?_
  have bd9 := bd8.call hS (by decide) (by decide) hpost
  have hf9 : Frame m0 s9.data := Frame.call bd8 (hI.frame.of_dmem hdm8) hpost
  have hout9 := out_call hpre bd8 hpost
  have k9 : ∀ r, calleeSaved r = true → s9.data.regs.getXReg r = s8.data.regs.getXReg r :=
    hpost.2.2.2.1
  have e8 : ∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X27, .X28, .X29],
      s9.data.regs.getXReg r = s.data.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (k9 _ rfl).trans (Match.reg_eq hm8 hm8' rfl rfl)
  have prod : (⟨s9.data.regs.getXReg .X0, s9.data.regs.getXReg .X1⟩ : EW) =
      (K m0 i)[j] * rr m0 i := by
    show (⟨s9.data.regs.X0, s9.data.regs.X1⟩ : EW) = _
    rw [hpost.1, hpost.2.1]
    show EW.mul ⟨s8.data.regs.getXReg .X0, s8.data.regs.getXReg .X1⟩
      ⟨s8.data.regs.getXReg .X2, s8.data.regs.getXReg .X3⟩ = _
    rw [v01, v23]
    rfl
  have q0 : s9.data.regs.getXReg .X0 = ((K m0 i)[j] * rr m0 i).c0 := congrArg EW.c0 prod
  have q1 : s9.data.regs.getXReg .X1 = ((K m0 i)[j] * rr m0 i).c1 := congrArg EW.c1 prod
  have q25 : s9.data.regs.getXReg .X25 = ((K m0 i)[j]).c0 :=
    (k9 .X25 rfl).trans (congrArg EW.c0 v25)
  have q26 : s9.data.regs.getXReg .X26 = ((K m0 i)[j]).c1 :=
    (k9 .X26 rfl).trans (congrArg EW.c1 v25)
  -- `b9`: the stores
  obtain ⟨hmB, hnB⟩ := elem_mapped (n := len m0) ⟨hmO, hnO⟩ bd9.kept hj2
  obtain ⟨hmA9, -⟩ := elem_mapped (n := len m0) ⟨hmO, hnO⟩ bd9.kept hjL
  have hwf9 : (Env.ofMachine s9.data [(out m0 + BitVec.ofNat 64 (16 * j), 16),
      (out m0 + BitVec.ofNat 64 (16 * (2 ^ i + j)), 16)]).WF := by
    refine Env.wf_of ⟨⟨hmA9, hnA⟩, ⟨hmB, hnB⟩, trivial⟩ ?_
    refine List.Pairwise.cons ?_ (List.Pairwise.cons nofun .nil)
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    subst he
    show Apart _ 16 _ 16
    unfold Apart
    rw [toNat_add_ofNat' (by omega), toNat_add_ofNat' (by omega)]
    omega
  have hm9 : Match (Env.ofMachine s9.data [(out m0 + BitVec.ofNat 64 (16 * j), 16),
      (out m0 + BitVec.ofNat 64 (16 * (2 ^ i + j)), 16)]) pairS s9.data :=
    match_ofMachine ⟨rfl, nofun, rfl, nofun, trivial⟩ rfl
      ⟨by
        show (s9.data.regs.getXReg .X28).toBitVec =
          out m0 + BitVec.ofNat 64 (16 * j) + BitVec.ofInt 64 8
        rw [e8 .X28 (by simp), show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl,
          NativeRustcVm.addr_add]
        exact hI.x28,
      by
        show (s9.data.regs.getXReg .X21).toBitVec =
          out m0 + BitVec.ofNat 64 (16 * (2 ^ i + j)) + BitVec.ofInt 64 8
        rw [e8 .X21 (by simp), show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl,
          NativeRustcVm.addr_add]
        exact hI.x21,
      trivial⟩ trivial trivial trivial
  refine exec_at (hb9 hp) run_b9 hwf9 hpc9 hm9 fun s10 hm10 hpc10 ↦ ?_
  obtain ⟨hsp10, hw10, hw0a, hw0b, hw1a, hw1b⟩ := after_eq run_b9 ▸ b9_facts
  have hsame10 := BufEW.same_of_regions01 hm10 hwf9 hw10
  have keep : ∀ t, t < 16 * len m0 → (t < 16 * j ∨ 16 * j + 16 ≤ t) →
      (t < 16 * (2 ^ i + j) ∨ 16 * (2 ^ i + j) + 16 ≤ t) →
      s10.data.dmem.get? (out m0 + BitVec.ofNat 64 t) =
        s.data.dmem.get? (out m0 + BitVec.ofNat 64 t) := by
    intro t ht h0 h1
    rw [hsame10 _ (not_in_elem hnO' ht hjL h0) (not_in_elem hnO' ht hj2 h1),
      hout9 _ (inRange_add hnO ht), hdm8]
  have hsame : ∀ p, ¬InRange (out m0) (16 * len m0) p →
      s10.data.dmem.get? p = s9.data.dmem.get? p := fun p hp' ↦
    hsame10 p (fun h ↦ hp' (inRange_mono h (by omega))) (fun h ↦ hp' (inRange_mono h (by omega)))
  have bd10 : B m0 s10.data := B.of_out hpre bd9 (Match.sp_eq hm9 hm10 hsp10) hsame
    (hm10.kept hwf9)
  have hf10 : Frame m0 s10.data := hf9.of_out hpre hsame
  have nB : EWAt s10.data.dmem (out m0 + BitVec.ofNat 64 (16 * j))
      ((K m0 i)[j] + (K m0 i)[j] * rr m0 i) := by
    rw [NativeRustcVm.ewAt_iff]
    have a0 := BufEW.wordAt_of_writeSym hm10 (r := 0) (o := 0) rfl (by decide) hw0a
    have a1 := BufEW.wordAt_of_writeSym hm10 (r := 0) (o := 8) rfl (by decide) hw0b
    rw [add_ofNat_zero] at a0
    simp only [Sym.eval, Env.ofMachine_regs, BinOp.apply, Sym.low_W64, Sym.ext_W64, q0, q1, q25,
      q26] at a0 a1
    exact ⟨a0, a1⟩
  have nH : EWAt s10.data.dmem (out m0 + BitVec.ofNat 64 (16 * (2 ^ i + j)))
      ((K m0 i)[j] * rr m0 i) := by
    rw [NativeRustcVm.ewAt_iff]
    have a0 := BufEW.wordAt_of_writeSym hm10 (r := 1) (o := 0) rfl (by decide) hw1a
    have a1 := BufEW.wordAt_of_writeSym hm10 (r := 1) (o := 8) rfl (by decide) hw1b
    rw [add_ofNat_zero] at a0
    simp only [Sym.eval, Env.ofMachine_regs, UInt64.ofBitVec_toBitVec, q0, q1] at a0 a1
    exact ⟨a0, a1⟩
  have nlo : EWsAt s10.data.dmem (out m0) (half1 (K m0 i) (rr m0 i) (j + 1)) := by
    rw [NativeRustcVm.half1_succ_split _ _ hjK, NativeRustcVm.ewsAt_append,
      NativeRustcVm.ewsAt_append, NativeRustcVm.ewsAt_singleton, lA, List.length_singleton,
      NativeRustcVm.addr_add]
    refine ⟨?_, nB, ?_⟩
    · have h := ewsAt_keep (c := 0) (d' := s10.data.dmem) (by rw [add_ofNat_zero]; exact hloA)
        fun t _ ht ↦ by
          rw [lA] at ht
          exact keep t (by omega) (Or.inl (by omega)) (Or.inl (by omega))
      rwa [add_ofNat_zero] at h
    · refine ewsAt_keep hloC fun t h1 h2 ↦ ?_
      rw [List.length_drop, hKlen] at h2
      exact keep t (by omega) (Or.inr (by omega)) (Or.inl (by omega))
  have nhi : EWsAt s10.data.dmem (out m0 + BitVec.ofNat 64 (16 * 2 ^ i))
      (((K m0 i).take (j + 1)).map (· * rr m0 i)) := by
    rw [NativeRustcVm.half2_succ _ _ hjK, NativeRustcVm.ewsAt_append, NativeRustcVm.ewsAt_singleton,
      lB, NativeRustcVm.addr_add, show 16 * 2 ^ i + 16 * j = 16 * (2 ^ i + j) by omega]
    refine ⟨ewsAt_keep hI.hi fun t h1 h2 ↦ ?_, nH⟩
    rw [lB] at h2
    exact keep t (by omega) (Or.inr (by omega)) (Or.inl (by omega))
  have e10 : ∀ r ∈ [XReg.X20, .X22, .X23, .X24, .X27, .X29],
      s10.data.regs.getXReg r = s.data.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (Match.reg_eq hm9 hm10 rfl rfl).trans (e8 _ (by simp))
  have x19s : (s9.data.regs.getXReg .X19).toBitVec.toNat = 2 ^ i - j := by
    rw [e8 .X19 (by simp)]; exact hI.x19
  have a19 : (s10.data.regs.getXReg .X19).toBitVec.toNat = 2 ^ i - (j + 1) := by
    have h := hm10.regs .X19 _ rfl
    sym_simp at h
    simp only [Env.ofMachine_regs] at h
    rw [h, BitVec.toNat_sub, x19s, BitVec.toNat_ofNat]
    omega
  have x28 : (s10.data.regs.getXReg .X28).toBitVec = out m0 + BitVec.ofNat 64 (16 * (j + 1) + 8) := by
    have h := hm10.regs .X28 _ rfl
    simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
      Option.getD_some] at h
    rw [h, show BitVec.ofInt 64 24 = BitVec.ofNat 64 24 from rfl, NativeRustcVm.addr_add]
    congr 2
  have x21 : (s10.data.regs.getXReg .X21).toBitVec =
      out m0 + BitVec.ofNat 64 (16 * (2 ^ i + (j + 1)) + 8) := by
    have h := hm10.regs .X21 _ rfl
    simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.map_some, Option.getD_some] at h
    rw [h, show BitVec.ofInt 64 24 = BitVec.ofNat 64 24 from rfl, NativeRustcVm.addr_add]
    congr 2
  simp only [PcOk, NativeRustcVmArm.Vm.EqKernel.b9_length, NativeRustcVmArm.Vm.EqKernel.b9Length] at hpc10
  sym_simp at hpc10
  have hpc10' := pc_ne hpc10
  have r10 : (⟨s10.data.regs.X23, s10.data.regs.X24⟩ : EW) = rr m0 i := by
    show (⟨s10.data.regs.getXReg .X23, s10.data.regs.getXReg .X24⟩ : EW) = _
    rw [e10 .X23 (by simp), e10 .X24 (by simp)]
    exact hI.r
  have x29 : s10.data.regs.X29.toNat = 2 ^ i := by
    show (s10.data.regs.getXReg .X29).toNat = _
    rw [e10 .X29 (by simp)]; exact hI.x29
  have x22 : s10.data.regs.X22.toBitVec = pt m0 + BitVec.ofNat 64 (16 * i) := by
    show (s10.data.regs.getXReg .X22).toBitVec = _
    rw [e10 .X22 (by simp)]; exact hI.x22
  have x20 : s10.data.regs.X20 = m0.regs.X3 := by
    show s10.data.regs.getXReg .X20 = _
    rw [e10 .X20 (by simp)]; exact hI.x20
  have x27 : s10.data.regs.X27.toBitVec = out m0 + BitVec.ofNat 64 8 := by
    show (s10.data.regs.getXReg .X27).toBitVec = _
    rw [e10 .X27 (by simp)]; exact hI.x27
  by_cases hlast : j + 1 = 2 ^ i
  · have hpc := hpc10'.2 (by
      show (s9.data.regs.getXReg .X19).toBitVec = 1#64
      apply BitVec.eq_of_toNat_eq
      rw [x19s]
      simp only [BitVec.toNat_ofNat]
      omega)
    refine .done _ (Or.inr ⟨hpc, bd10, hf10, hI.lt, x29, x22, x20, x27, ?_⟩)
    have e1 : j + 1 = (K m0 i).length := by omega
    rw [e1, NativeRustcVm.half1_len] at nlo
    rw [e1, List.take_of_length_le (Nat.le_refl _)] at nhi
    rw [K_succ m0 hI.lt, NativeRustcVm.ewsAt_append, List.length_map, hKlen]
    exact ⟨nlo, nhi⟩
  · have hpc := hpc10'.1 (fun h ↦ by
      have h' := congrArg BitVec.toNat h
      change (s9.data.regs.getXReg .X19).toBitVec.toNat = _ at h'
      rw [x19s] at h'
      simp only [BitVec.toNat_ofNat] at h'
      omega)
    exact .done _ (Or.inl ⟨hpc.trans (lbl_8 hp), bd10, hf10, hI.lt, by omega, x29, x22, x20, x27,
      a19, x28, x21, r10, nlo, nhi⟩)

/-- **A round's pairs**: from `.LEqKernel_8` with no pair done to the round done. -/
theorem inner (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {m0 : MachineData} (hpre : EqKernelPre m0) (hle : 2 ^ np m0 ≤ len m0) {i : Nat}
    {s : MachineState} (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.EqKernel.b8Offset)) (hI : IInv m0 i 0 s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.EqKernel.b10Offset) ∧ RInv m0 i s'.data) s :=
  Sym.loop (fun n s ↦ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.EqKernel.b8Offset) ∧ ∃ j, 2 ^ i - j = n ∧ IInv m0 i j s.data)
    (fun _ _ ⟨hpc, j, hn, hI⟩ ↦ Eventually.mono (pair hp hmul hpre hle hpc hI) fun s' h ↦ by
      rcases h with ⟨hpc', hI'⟩ | h
      · exact Or.inr ⟨2 ^ i - (j + 1), by have := hI'.jlt; omega, hpc', j + 1, rfl, hI'⟩
      · exact Or.inl h)
    ⟨hpc, 0, rfl, hI⟩

end

end NativeRustcVmArm.Arrays.EqKernel
