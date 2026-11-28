module

public import NativeRustcVmX64.Arrays.EqKernel.Basic
public import NativeRustcVmX64.Code.Vm.EWMul.Names

/-!
# `eq_kernel` on x86-64: the loops

A round's set-up (`start`: `b6`-`b8`, `point[i]` into the frame), a pair (`pair`: `b9`,
`EW::mul`, `b10`), a round's pairs (`inner`), a round's end (`next`: `b11`, `b5`, then the next
round or the return `b13`, `b14`).
-/

namespace NativeRustcVmX64.Arrays.EqKernel

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.EqKernel NativeVm.Model
  NativeRustcVmX64.Field
open NativeRustcVm (ewsOf ewOf EWsAt EWAt WordAt half1)

public section

section
variable [Labels] {env : Env}

theorem eval_cmp_ult (a b : Sym) :
    (SBool.cmp .ult .W64 a b).eval env = decide ((a.eval env).toNat < (b.eval env).toNat) := by
  simp only [SBool.eval, CmpOp.apply, low_W64]
  rfl

theorem eval_sub (a b : Sym) : (Sym.bin .sub .W64 a b).eval env = a.eval env - b.eval env := by
  simp [Sym.eval, BinOp.apply]

end

theorem shl4_toNat (x : BitVec 64) (_h : x.toNat < 2 ^ 60) : x <<< 4 = BitVec.ofNat 64 (16 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

theorem ofNat_toNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-- `out`'s bytes where a block writes the frame below offset 64 only. -/
theorem out_kept [Labels] {m0 st m : MachineData} {rs : List (BitVec 64 × Nat)} {S : SState}
    {vars : Nat → BitVec 64} {ret : BitVec 64} (hpre : EqKernelPre m0)
    (hm : Match (Env.ofMachine st ((fb m0, 120) :: rs) vars ret) S m)
    (hwf : (Env.ofMachine st ((fb m0, 120) :: rs) vars ret).WF)
    (hw : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ 64) :
    ∀ t < 16 * len m0, m.dmem.get? (out m0 + BitVec.ofNat 64 t) =
      st.dmem.get? (out m0 + BitVec.ofNat 64 t) := by
  intro t ht
  refine hm.get?_mem0 hwf fun h ↦ ?_
  have h1 := written_region0 rfl hwf (show 64 ≤ 120 by decide) hw h
  obtain ⟨hS, -, -, ⟨⟨-, hnO⟩, hoO⟩, -⟩ := hpre
  have hS1 := hS.1
  have hS2 := hS.2.1
  have eO : (out m0).toNat = (reg m0 .rdx).toNat := rfl
  have eL : len m0 = (reg m0 .rcx).toNat := rfl
  rw [eqKernelStack_eq] at hS1
  have hfb := fb_toNat hS
  unfold OffStack Apart at hoO
  rw [stackBelow_toNat (by rw [eqKernelStack_eq]; omega), eqKernelStack_eq] at hoO
  unfold NoWrap at hnO
  rw [Sym.inRange_iff (by omega), hfb, toNat_add_ofNat _ _ (by omega)] at h1
  omega

/-- `EWsAt` in `out` kept where memory is unchanged. -/
theorem ewsAt_keep {d d' : DataMem} {O : BitVec 64} {c : Nat} {xs : List EW}
    (h : EWsAt d (O + BitVec.ofNat 64 c) xs)
    (he : ∀ t, c ≤ t → t < c + 16 * xs.length →
      d'.get? (O + BitVec.ofNat 64 t) = d.get? (O + BitVec.ofNat 64 t)) :
    EWsAt d' (O + BitVec.ofNat 64 c) xs :=
  ewsAt_congr h fun t ht ↦ by
    rw [addr_add]
    exact he _ (by omega) (by omega)

theorem ews_kept [Labels] {m0 st m : MachineData} {rs : List (BitVec 64 × Nat)} {S : SState}
    {vars : Nat → BitVec 64} {ret : BitVec 64} (hpre : EqKernelPre m0)
    (hm : Match (Env.ofMachine st ((fb m0, 120) :: rs) vars ret) S m)
    (hwf : (Env.ofMachine st ((fb m0, 120) :: rs) vars ret).WF)
    (hw : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ 64) {xs : List EW}
    (hl : 16 * xs.length ≤ 16 * len m0) (h : EWsAt st.dmem (out m0) xs) : EWsAt m.dmem (out m0) xs := by
  have h' : EWsAt st.dmem (out m0 + BitVec.ofNat 64 0) xs := by rw [add_ofNat_zero]; exact h
  have := ewsAt_keep h' fun t _ ht ↦ out_kept hpre hm hwf hw t (by omega)
  rwa [add_ofNat_zero] at this

variable [Host] {k : Nat}

/-- **A round's set-up** (`b6`-`b8`): the tests, `point[i]` into the frame. -/
theorem start (hp : Placed code k) {m0 : MachineData} (hpre : EqKernelPre m0)
    (hle : 2 ^ np m0 ≤ len m0) {i : Nat} {s : MachineState} (hpc : s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.EqKernel.b6Offset))
    (hI : OInv m0 i s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.EqKernel.b9Offset) ∧ IInv m0 i 0 s'.data) s := by
  have hpre' := hpre
  obtain ⟨hS, h64, hP, hO, hap⟩ := hpre
  obtain ⟨hpos, hpow⟩ := pow_facts hle hI.lt
  have hL : len m0 = (reg m0 .rcx).toNat := rfl
  have hN : np m0 = (reg m0 .rsi).toNat := rfl
  have hilt := hI.lt
  have hlen := lt_of_offStack hO.1.2 hO.2
  have hi64 : 2 ^ i < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (by omega)
  have h112 : 112 ≤ eqKernelStack := by decide
  -- `b6`: `|out| - 2^i`, `|out| ≥ 2^i`
  refine exec_at (hb6 hp) run_b6 (Env.wf_nil _) (by intro l h; cases h) hpc (match_nil _)
    fun s6 hm6 hpc6 ↦ ?_
  obtain ⟨bd6, hdm6, e6⟩ := B.of_regs hpre' hI.body hm6 b6_keeps
  have hr8 : reg s.data .r8 = reg m0 .rcx := hI.r8
  have hrdx : reg s.data .rdx = BitVec.ofNat 64 (2 ^ i) := hI.rdx
  simp only [PcOk, NativeRustcVmX64.Vm.EqKernel.b6_length] at hpc6
  rw [eval_cmp_ult, eval_reg, eval_reg] at hpc6
  rw [show (Env.ofMachine s.data []).regs .r8 = reg s.data .r8 from rfl,
    show (Env.ofMachine s.data []).regs .rdx = reg s.data .rdx from rfl, hr8, hrdx,
    ofNat_toNat_lt hi64] at hpc6
  have hpc6 := (pc_cond hpc6).2 (by simp; omega)
  have hbp6 : reg s6.data .rbp = BitVec.ofNat 64 (len m0 - 2 ^ i) := by
    rw [show reg s6.data .rbp = (Sym.bin .sub .W64 (.reg .r8) (.reg .rdx)).eval
      (Env.ofMachine s.data []) from hm6.regs .rbp _ rfl, eval_sub, eval_reg, eval_reg]
    show reg s.data .r8 - reg s.data .rdx = _
    rw [hr8, hrdx]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, ofNat_toNat_lt hi64, ofNat_toNat_lt (by omega)]
    omega
  -- `b7`: `min(|out| - 2^i, 2^i) = 2^i` pairs, the half into the frame, `|out| ≠ 2^i`
  have hwf7 := bd6.wf (vars := fun _ ↦ 0) (ret := 0) hS h112
  refine exec_at (hb7 hp) run_b7 hwf7 (by intro l h; cases h) hpc6 bd6.mid_match
    fun s7 hm7 hpc7 ↦ ?_
  obtain ⟨hk7, hw7, hbp7, hw24, o8, o16, o32, o40⟩ := after_eq run_b7 ▸ b7_facts
  have bd7 := bd6.of_frame (L := 64) hS h112 hwf7 bd6.mid_match hm7 (keepsRegs_rsp hk7) hw7
    (by decide) slots_ok
  have e7 := regs_eq_of bd6.mid_match hm7 hk7
  have hdx6 : reg s6.data .rdx = BitVec.ofNat 64 (2 ^ i) := (e6 .rdx (by simp)).trans hrdx
  have hr86 : reg s6.data .r8 = reg m0 .rcx := (e6 .r8 (by simp)).trans hr8
  have loc6 : Loc m0 s6.data.dmem i := by rw [hdm6]; exact hI.loc
  have loc7 : Loc m0 s7.data.dmem i :=
    ⟨fw_keep hm7 (by decide) o8 loc6.ptw, fw_keep hm7 (by decide) o16 loc6.size,
      fw_keep hm7 (by decide) o32 loc6.pend, fw_keep hm7 (by decide) o40 loc6.lenw⟩
  have half7 : WordAt s7.data.dmem (fb m0 + BitVec.ofNat 64 24)
      (UInt64.ofBitVec (BitVec.ofNat 64 (2 ^ i))) := by
    have a := fw_write hm7 (by decide) hw24
    rwa [eval_reg, show (frameEnv m0 s6.data 112).regs .rdx = reg s6.data .rdx from rfl,
      hdx6] at a
  have hbp7' : reg s7.data .rbp = BitVec.ofNat 64 (2 ^ i) := by
    rw [show reg s7.data .rbp = _ from hm7.regs .rbp _ hbp7]
    simp only [Sym.eval, SBool.eval, CmpOp.apply, low_W64]
    rw [show (frameEnv m0 s6.data 112).regs .rbp = reg s6.data .rbp from rfl,
      show (frameEnv m0 s6.data 112).regs .rdx = reg s6.data .rdx from rfl, hbp6, hdx6]
    have hc : (BitVec.ofNat 64 (len m0 - 2 ^ i)).ult (BitVec.ofNat 64 (2 ^ i)) = false := by
      rw [BitVec.ult, ofNat_toNat_lt (by omega), ofNat_toNat_lt hi64]
      simp; omega
    simp [hc]
  simp only [PcOk, NativeRustcVmX64.Vm.EqKernel.b7_length] at hpc7
  rw [eval_cmp_eq, eval_reg, eval_reg,
    show (frameEnv m0 s6.data 112).regs .r8 = reg s6.data .r8 from rfl,
    show (frameEnv m0 s6.data 112).regs .rdx = reg s6.data .rdx from rfl, hr86, hdx6] at hpc7
  have hpc7 := (pc_cond hpc7).2 (by
    rw [beq_iff_eq]
    intro h
    have h' := congrArg BitVec.toNat h
    rw [ofNat_toNat_lt hi64] at h'
    omega)
  -- `b8`: `point[i]` into the frame
  have hP' : SliceIn m0 eqKernelStack (out m0) (16 * len m0) (pt m0) (np m0) :=
    ⟨hP.1, hP.2, hap, hO.1.2⟩
  obtain ⟨hwf8, hm8, hval⟩ := bd7.elem (ret := 0) hS h112 hP' hI.lt (x := .load 0 8 8) (o := 0)
    ((eval_load _ _ _).trans ((load_fw loc7.ptw).trans (by rw [add_ofNat_zero])))
  refine exec_at (hb8 hp) run_b8 hwf8 (by intro l h; cases h) hpc7 hm8 fun s8 hm8' hpc8 ↦ ?_
  obtain ⟨hk8, hw8, hbp8, h128, hbx8, w48, w56, p8, p16, p24, p32, p40⟩ := after_eq run_b8 ▸ b8_facts
  have bd8 := bd7.of_frame (L := 64) hS h112 hwf8 hm8 hm8' (keepsRegs_rsp hk8) hw8 (by decide)
    slots_ok
  have e8 := regs_eq_of hm8 hm8' hk8
  simp only [PcOk, NativeRustcVmX64.Vm.EqKernel.b8_length] at hpc8
  have hr : ewArg ((elemEnv m0 s7.data 112 (pt m0) i).load 1 0 8)
      ((elemEnv m0 s7.data 112 (pt m0) i).load 1 8 8) = rr m0 i := hval.trans (rr_eq m0 hI.lt).symm
  have hr15 : reg s8.data .r15 = out m0 + BitVec.ofNat 64 8 :=
    (e8 .r15 (by simp)).trans ((e7 .r15 (by simp)).trans ((e6 .r15 (by simp)).trans hI.r15))
  refine .done _ ⟨hpc8, ?_⟩
  refine ⟨bd8, ⟨fw_keep hm8' (by decide) p8 loc7.ptw, fw_keep hm8' (by decide) p16 loc7.size,
      fw_keep hm8' (by decide) p32 loc7.pend, fw_keep hm8' (by decide) p40 loc7.lenw⟩,
    hI.lt, hpos, fw_keep hm8' (by decide) p24 half7, ?_, ?_, hm8'.regs .rbx _ hbx8, ?_, ?_, hr15,
    ?_, ?_⟩
  · have a := fw_write hm8' (by decide) w56
    rwa [eval_load, show UInt64.ofBitVec ((elemEnv m0 s7.data 112 (pt m0) i).load 1 0 8) =
      (rr m0 i).c0 from congrArg EW.c0 hr] at a
  · have a := fw_write hm8' (by decide) w48
    rwa [eval_load, show UInt64.ofBitVec ((elemEnv m0 s7.data 112 (pt m0) i).load 1 8 8) =
      (rr m0 i).c1 from congrArg EW.c1 hr] at a
  · rw [show reg s8.data .rbp = _ from hm8'.regs .rbp _ hbp8, eval_shl_lit _ (by decide), eval_reg,
      show (elemEnv m0 s7.data 112 (pt m0) i).regs .rbp = reg s7.data .rbp from rfl, hbp7',
      shl4_toNat _ (by rw [ofNat_toNat_lt hi64]; omega), ofNat_toNat_lt hi64]
  · rw [show reg s8.data .r12 = _ from hm8'.regs .r12 _ h128, eval_add,
      eval_shl_lit _ (by decide), eval_reg, eval_load, load_fw half7,
      show (elemEnv m0 s7.data 112 (pt m0) i).regs .r15 = reg s7.data .r15 from rfl,
      e7 .r15 (by simp), e6 .r15 (by simp), hI.r15, UInt64.toBitVec_ofBitVec,
      shl4_toNat _ (by rw [ofNat_toNat_lt hi64]; omega), ofNat_toNat_lt hi64, addr_add]
    exact congrArg _ (congrArg _ (by omega))
  · rw [NativeRustcVm.half1_zero]
    have hk : (K m0 i).length = 2 ^ i := length_K m0 (Nat.le_of_lt hI.lt)
    refine ews_kept hpre' hm8' hwf8 hw8 (by omega) (ews_kept hpre' hm7 hwf7 hw7 (by omega) ?_)
    rw [hdm6]; exact hI.ker
  · simp only [List.take_zero, List.map_nil]
    exact NativeRustcVm.ewsAt_nil _ _

/-- **A pair** (`b9`, `EW::mul`, `b10`): `out[2^i + j] = K[j]·r`, `out[j] = K[j] + K[j]·r`; back
at `NativeRustcVmX64.Vm.EqKernel.label_8` or the round done. -/
theorem pair (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {m0 : MachineData} (hpre : EqKernelPre m0) (hle : 2 ^ np m0 ≤ len m0) {i j : Nat}
    {s : MachineState} (hpc : s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.EqKernel.b9Offset)) (hI : IInv m0 i j s.data) :
    Eventually (step1 Host.exe) (fun s' ↦
      (s'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.EqKernel.b9Offset) ∧ IInv m0 i (j + 1) s'.data) ∨
      (s'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.EqKernel.b11Offset) ∧ RInv m0 i s'.data)) s := by
  have hpre' := hpre
  obtain ⟨hS, h64, hP, hO, hap⟩ := hpre
  obtain ⟨hpos, hpow⟩ := pow_facts hle hI.lt
  have hL : len m0 = (reg m0 .rcx).toNat := rfl
  have hN : np m0 = (reg m0 .rsi).toNat := rfl
  have hilt := hI.lt
  have hjl := hI.jlt
  have hnO : NoWrap (out m0) (16 * len m0) := hO.1.2
  have hnO' : (out m0).toNat + 16 * len m0 ≤ 2 ^ 64 := hnO
  have hlen := lt_of_offStack hO.1.2 hO.2
  have hi64 : 2 ^ i < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (by omega)
  have h112 : 112 ≤ eqKernelStack := by decide
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
  -- `b9`: `out[j]`, `r`, `EW::mul`
  obtain ⟨hwf9, hm9⟩ := hI.body.at_elem (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.EqKernel.b10Offset)).toBitVec) hS h112
    hO.1 hO.2 hjL (x := .bin .add .W64 (.reg .r15) (.reg .rbx)) (o := 8) (by
      rw [eval_add, eval_reg, eval_reg]
      show reg s.data .r15 + reg s.data .rbx = _
      rw [hI.r15, hI.rbx, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 8)])
  refine exec_at (hb9 hp) run_b9 hwf9 (fun _ _ ↦ rfl) hpc hm9 fun s9 hm9' hpc9 ↦ ?_
  obtain ⟨hsp9, hw9, hdi9, hsi9, hdx9, hcx9, h139, h149, hk9⟩ := after_eq run_b9 ▸ b9_facts
  have e9 := regs_eq_of hm9 hm9' hk9
  have hKj : ewOf s.data.dmem (out m0 + BitVec.ofNat 64 (16 * j)) = (K m0 i)[j] :=
    NativeRustcVm.ewOf_of_ewAt hloB
  have e01 : ewArg (reg s9.data .rdi) (reg s9.data .rsi) = (K m0 i)[j] := by
    rw [show reg s9.data .rdi = _ from hm9'.regs .rdi _ hdi9,
      show reg s9.data .rsi = _ from hm9'.regs .rsi _ hsi9, eval_load, eval_load]
    refine (ewOf_loads _ 1 0).symm.trans ?_
    rw [add_ofNat_zero]
    exact hKj
  have e1314 : ewArg (reg s9.data .r13) (reg s9.data .r14) = (K m0 i)[j] := by
    rw [show reg s9.data .r13 = _ from hm9'.regs .r13 _ h139,
      show reg s9.data .r14 = _ from hm9'.regs .r14 _ h149, eval_load, eval_load]
    refine (ewOf_loads _ 1 0).symm.trans ?_
    rw [add_ofNat_zero]
    exact hKj
  have e23 : ewArg (reg s9.data .rdx) (reg s9.data .rcx) = rr m0 i := by
    rw [show reg s9.data .rdx = (rr m0 i).c0.toBitVec from
        (hm9'.regs .rdx _ hdx9).trans (load_fw hI.rlo),
      show reg s9.data .rcx = (rr m0 i).c1.toBitVec from
        (hm9'.regs .rcx _ hcx9).trans (load_fw hI.rhi)]
    rfl
  refine Body.call_mul hmul hI.body hS (by decide) (by decide)
    (fun p hp ↦ ⟨by have := (slots_ok p hp).1; omega, (slots_ok p hp).2⟩) hwf9 hm9 hm9' hpc9
    (keepsRegs_free _ _) hsp9 hw9 fun s10 hpc10 bd10 hprod hsv hout hfr ↦ ?_
  rw [e01, e23] at hprod
  have q : ∀ r ∈ [Reg64.rbx, .rbp, .r12, .r15], reg s10.data r = reg s.data r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact (hsv _ rfl).trans (e9 _ (by simp))
  have e1314' : ewArg (reg s10.data .r13) (reg s10.data .r14) = (K m0 i)[j] := by
    rw [hsv .r13 rfl, hsv .r14 rfl]; exact e1314
  -- `b10`: the stores
  have hfm : Mapped s10.data.dmem (fb m0) 120 := fun t ht ↦
    bd10.kept _ ((stackOk_mono hS h112).2.2 t ht)
  have hfn : NoWrap (fb m0) 120 := frame_noWrap (stackOk_mono hS h112)
  obtain ⟨hmA, hnA⟩ := elem_mapped hO.1 bd10.kept hjL
  obtain ⟨hmB, hnB⟩ := elem_mapped hO.1 bd10.kept hj2
  have aA := elem_apart_frame hS h112 hO.1 hO.2 hjL
  have aB := elem_apart_frame hS h112 hO.1 hO.2 hj2
  have hwf10 : (Env.ofMachine s10.data [(fb m0, 120), (out m0 + BitVec.ofNat 64 (16 * j), 16),
      (out m0 + BitVec.ofNat 64 (16 * (2 ^ i + j)), 16)]).WF := by
    refine Env.wf_of ⟨⟨hfm, hfn⟩, ⟨hmA, hnA⟩, ⟨hmB, hnB⟩, trivial⟩ ?_
    refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.Pairwise.cons nofun .nil))
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · exact aA
      · exact aB
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      subst he
      show Apart _ 16 _ 16
      unfold Apart
      rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)]
      omega
  have hm10 : Match (Env.ofMachine s10.data [(fb m0, 120), (out m0 + BitVec.ofNat 64 (16 * j), 16),
      (out m0 + BitVec.ofNat 64 (16 * (2 ^ i + j)), 16)]) storeS s10.data := by
    refine match_ofMachine ⟨rfl, rfl, rfl, trivial⟩ ⟨bd10.rsp, trivial⟩ trivial trivial ⟨?_, ?_, trivial⟩
    · show reg s10.data .r15 + reg s10.data .rbx =
        out m0 + BitVec.ofNat 64 (16 * j) + BitVec.ofInt 64 8
      rw [q .r15 (by simp), q .rbx (by simp), hI.r15, hI.rbx,
        show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, addr_add, addr_add]
      exact congrArg _ (congrArg _ (by omega))
    · show reg s10.data .r12 + reg s10.data .rbx =
        out m0 + BitVec.ofNat 64 (16 * (2 ^ i + j)) + BitVec.ofInt 64 8
      rw [q .r12 (by simp), q .rbx (by simp), hI.r12, hI.rbx,
        show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, addr_add, addr_add]
      exact congrArg _ (congrArg _ (by omega))
  refine exec_at (hb10 hp) run_b10 hwf10 (by intro l h; cases h) hpc10 hm10 fun s11 hm11 hpc11 ↦ ?_
  obtain ⟨hk10, hbx10, hw10, hw1a, hw1b, hw2a, hw2b⟩ := after_eq run_b10 ▸ b10_facts
  have e10 := regs_eq_of hm10 hm11 hk10
  have hsame10 := same12 hm11 hwf10 hw10
  have hsame : ∀ p, ¬InRange (out m0) (16 * len m0) p → s11.data.dmem.get? p = s10.data.dmem.get? p :=
    fun p hp' ↦ hsame10 p (fun h ↦ hp' (in_out hnO hjL h)) (fun h ↦ hp' (in_out hnO hj2 h))
  have bd11 : B m0 s11.data := B.of_out hpre' bd10 (e10 .rsp (by simp)) hsame (hm11.kept hwf10)
  -- the frame's bytes
  have hframe : ∀ t, 8 ≤ t → t < 64 → s11.data.dmem.get? (fb m0 + BitVec.ofNat 64 t) =
      s.data.dmem.get? (fb m0 + BitVec.ofNat 64 t) := fun t h1 h2 ↦ by
    rw [hsame _ (frame_not_out hpre' (by omega)), hfr t (by omega),
      frame_above hm9' hwf9 hw9 t h1 (by omega)]
  -- `out`'s bytes but the two elements
  have hnS : NoWrap (stackBelow m0 eqKernelStack) eqKernelStack := by
    have := hS.1; have := (rspOf m0).isLt
    unfold NoWrap; rw [stackBelow_toNat hS.1]; omega
  have keep : ∀ t, t < 16 * len m0 → (t < 16 * j ∨ 16 * j + 16 ≤ t) →
      (t < 16 * (2 ^ i + j) ∨ 16 * (2 ^ i + j) + 16 ≤ t) →
      s11.data.dmem.get? (out m0 + BitVec.ofNat 64 t) =
        s.data.dmem.get? (out m0 + BitVec.ofNat 64 t) := by
    intro t ht h0 h1
    rw [hsame10 _ (not_in_elem hnO' ht hjL h0) (not_in_elem hnO' ht hj2 h1)]
    exact hout _ (not_inRange_of_apart (apart_mono hO.2 (Nat.le_add_right _ 8)) hnO hnS ht)
  have hprod' : ewArg (reg s10.data .rax) (reg s10.data .rdx) = (K m0 i)[j] * rr m0 i := hprod
  have nB : EWAt s11.data.dmem (out m0 + BitVec.ofNat 64 (16 * j))
      ((K m0 i)[j] + (K m0 i)[j] * rr m0 i) := by
    have a := ewAt_of_writes hm11 (r := 1) (o := 0) rfl (by decide) hw1a hw1b
    rw [add_ofNat_zero, eval_xor, eval_xor, eval_reg, eval_reg, eval_reg, eval_reg] at a
    rw [← hprod', ← e1314']
    exact a
  have nH : EWAt s11.data.dmem (out m0 + BitVec.ofNat 64 (16 * (2 ^ i + j)))
      ((K m0 i)[j] * rr m0 i) := by
    have a := ewAt_of_writes hm11 (r := 2) (o := 0) rfl (by decide) hw2a hw2b
    rw [add_ofNat_zero, eval_reg, eval_reg] at a
    rw [← hprod']
    exact a
  have nlo : EWsAt s11.data.dmem (out m0) (half1 (K m0 i) (rr m0 i) (j + 1)) := by
    rw [NativeRustcVm.half1_succ_split _ _ hjK, NativeRustcVm.ewsAt_append,
      NativeRustcVm.ewsAt_append, NativeRustcVm.ewsAt_singleton, lA, List.length_singleton,
      NativeRustcVm.addr_add]
    refine ⟨?_, nB, ?_⟩
    · have h := ewsAt_keep (c := 0) (d' := s11.data.dmem) (by rw [add_ofNat_zero]; exact hloA)
        fun t _ ht ↦ by
          rw [lA] at ht
          exact keep t (by omega) (Or.inl (by omega)) (Or.inl (by omega))
      rwa [add_ofNat_zero] at h
    · refine ewsAt_keep hloC fun t h1 h2 ↦ ?_
      rw [List.length_drop, hKlen] at h2
      exact keep t (by omega) (Or.inr (by omega)) (Or.inl (by omega))
  have nhi : EWsAt s11.data.dmem (out m0 + BitVec.ofNat 64 (16 * 2 ^ i))
      (((K m0 i).take (j + 1)).map (· * rr m0 i)) := by
    rw [NativeRustcVm.half2_succ _ _ hjK, NativeRustcVm.ewsAt_append, NativeRustcVm.ewsAt_singleton,
      lB, NativeRustcVm.addr_add, show 16 * 2 ^ i + 16 * j = 16 * (2 ^ i + j) by omega]
    refine ⟨ewsAt_keep hI.hi fun t h1 h2 ↦ ?_, nH⟩
    rw [lB] at h2
    exact keep t (by omega) (Or.inr (by omega)) (Or.inl (by omega))
  have r11 : ∀ r ∈ [Reg64.rbp, .r12, .r15], reg s11.data r = reg s.data r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact (e10 _ (by simp)).trans (q _ (by simp))
  have hbx11 : reg s11.data .rbx = BitVec.ofNat 64 (16 * (j + 1)) := by
    rw [show reg s11.data .rbx = _ from hm11.regs .rbx _ hbx10, eval_add, eval_lit, eval_reg]
    show _ + reg s10.data .rbx = _
    rw [q .rbx (by simp), hI.rbx, ← BitVec.ofNat_add]
    exact congrArg _ (by omega)
  simp only [PcOk, NativeRustcVmX64.Vm.EqKernel.b10_length] at hpc11
  rw [eval_not, eval_cmp_eq, eval_add, eval_lit, eval_reg, eval_reg,
    show (Env.ofMachine s10.data [(fb m0, 120), (out m0 + BitVec.ofNat 64 (16 * j), 16),
      (out m0 + BitVec.ofNat 64 (16 * (2 ^ i + j)), 16)]).regs .rbp = reg s10.data .rbp from rfl,
    show (Env.ofMachine s10.data [(fb m0, 120), (out m0 + BitVec.ofNat 64 (16 * j), 16),
      (out m0 + BitVec.ofNat 64 (16 * (2 ^ i + j)), 16)]).regs .rbx = reg s10.data .rbx from rfl,
    q .rbp (by simp), q .rbx (by simp), hI.rbp, hI.rbx, ← BitVec.ofNat_add,
    ofNat_beq (by omega) (by omega)] at hpc11
  obtain ⟨hT, hFl⟩ := pc_cond hpc11
  have loc11 : Loc m0 s11.data.dmem i := hI.loc.congr hframe
  have half11 := fw_congr hI.half fun t h1 h2 ↦ hframe t (by omega) (by omega)
  by_cases hlast : j + 1 = 2 ^ i
  · have hpc := hFl (by simp; omega)
    refine .done _ (Or.inr ⟨hpc, bd11, loc11, hI.lt, half11, (r11 .r15 (by simp)).trans hI.r15, ?_⟩)
    have e1 : j + 1 = (K m0 i).length := by omega
    rw [e1, NativeRustcVm.half1_len] at nlo
    rw [e1, List.take_of_length_le (Nat.le_refl _)] at nhi
    rw [K_succ m0 hI.lt, NativeRustcVm.ewsAt_append, List.length_map, hKlen]
    exact ⟨nlo, nhi⟩
  · have hpc := hT (by simp; omega)
    exact .done _ (Or.inl ⟨hpc.trans (lbl_8 hp), bd11, loc11, hI.lt, by omega, half11,
      fw_congr hI.rlo fun t h1 h2 ↦ hframe t (by omega) (by omega),
      fw_congr hI.rhi fun t h1 h2 ↦ hframe t (by omega) (by omega), hbx11,
      (r11 .rbp (by simp)).trans hI.rbp, (r11 .r12 (by simp)).trans hI.r12,
      (r11 .r15 (by simp)).trans hI.r15, nlo, nhi⟩)

/-- **A round's pairs**: from `NativeRustcVmX64.Vm.EqKernel.label_8` with no pair done to the round done. -/
theorem inner (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {m0 : MachineData} (hpre : EqKernelPre m0) (hle : 2 ^ np m0 ≤ len m0) {i : Nat}
    {s : MachineState} (hpc : s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.EqKernel.b9Offset)) (hI : IInv m0 i 0 s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.EqKernel.b11Offset) ∧ RInv m0 i s'.data) s :=
  Sym.loop (fun n s ↦ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.EqKernel.b9Offset) ∧ ∃ j, 2 ^ i - j = n ∧ IInv m0 i j s.data)
    (fun _ _ ⟨hpc, j, hn, hI⟩ ↦ Eventually.mono (pair hp hmul hpre hle hpc hI) fun s' h ↦ by
      rcases h with ⟨hpc', hI'⟩ | h
      · exact Or.inr ⟨2 ^ i - (j + 1), by have := hI'.jlt; omega, hpc', j + 1, rfl, hI'⟩
      · exact Or.inl h)
    ⟨hpc, 0, rfl, hI⟩

/-- **The return with the size** (`b13`, `b14`): from the body, `out` the kernel, the size in the
frame. -/
theorem finish (hp : Placed code k) {m0 : MachineData} (hpre : EqKernelPre m0)
    (hle : 2 ^ np m0 ≤ len m0) {s : MachineState} (hpc : s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.EqKernel.b13Offset))
    (hb : B m0 s.data) (hl : Loc m0 s.data.dmem (np m0))
    (hker : EWsAt s.data.dmem (out m0) (K m0 (np m0))) :
    Eventually (step1 Host.exe) (Post m0) s := by
  have hS := hpre.1
  have h64 : np m0 < 64 := hpre.2.1
  have h112 : 112 ≤ eqKernelStack := by decide
  refine exec_at (hb1314 hp) run_b1314 (hb.wf (vars := fun _ ↦ 0) (ret := 0) hS h112)
    (by intro l h; cases h) hpc hb.mid_match fun s' hm' hpc' ↦ .done _ ?_
  obtain ⟨hres, hmem, hax, hdx⟩ := after_eq run_b1314 ▸ b1314_facts
  obtain ⟨hpc'', hrsp, hdm, hsaved⟩ := hb.done hS h112 hm' hpc' hres hmem
    (ret_not_in hS hpre.2.2.2.1.1.2 hpre.2.2.2.1.2)
  refine ⟨hpc'', hrsp, ?_, fun p hp' ↦ by rw [hdm]; exact hb.same p hp', hsaved⟩
  split
  rotate_left
  · rename_i hn; exact absurd hle hn
  refine ⟨hm'.regs .rax _ hax, ?_, ?_⟩
  · rw [show reg s'.data .rdx = _ from (hm'.regs .rdx _ hdx).trans (load_fw hl.size),
      UInt64.toBitVec_ofBitVec, ofNat_toNat_lt (Nat.pow_lt_pow_right (by decide) h64)]
  · rw [hdm, ← K_np]; exact hker

/-- **A round's end** (`b11`, `b5`): the next round, or out of the loop and returned. -/
theorem next (hp : Placed code k) {m0 : MachineData} (hpre : EqKernelPre m0)
    (hle : 2 ^ np m0 ≤ len m0) {i : Nat} {s : MachineState}
    (hpc : s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.EqKernel.b11Offset)) (hR : RInv m0 i s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ Post m0 s' ∨
      (s'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.EqKernel.b6Offset) ∧ OInv m0 (i + 1) s'.data)) s := by
  have hpre' := hpre
  obtain ⟨hS, h64, hP, hO, hap⟩ := hpre
  have hL : len m0 = (reg m0 .rcx).toNat := rfl
  have hN : np m0 = (reg m0 .rsi).toNat := rfl
  have hilt := hR.lt
  have hnP : (pt m0).toNat + 16 * np m0 ≤ 2 ^ 64 := hP.1.2
  have hi64 : 2 ^ i < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (by omega)
  have hi64' : 2 ^ (i + 1) < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (by omega)
  have h112 : 112 ≤ eqKernelStack := by decide
  have hpow : 2 ^ (i + 1) ≤ len m0 :=
    le_trans (Nat.pow_le_pow_right (by decide) (by omega)) hle
  -- `b11`
  refine exec_at (hb11 hp) run_b11 (Env.wf_nil _) (by intro l h; cases h) hpc (match_nil _)
    fun s11 hm11 hpc11 ↦ ?_
  obtain ⟨bd11, hdm11, e11⟩ := B.of_regs hpre' hR.body hm11 b11_keeps
  simp only [PcOk] at hpc11
  have loc11 : Loc m0 s11.data.dmem i := by rw [hdm11]; exact hR.loc
  have half11 : WordAt s11.data.dmem (fb m0 + BitVec.ofNat 64 24)
      (UInt64.ofBitVec (BitVec.ofNat 64 (2 ^ i))) := by rw [hdm11]; exact hR.half
  -- `b5`
  have hwf5 := bd11.wf (vars := fun _ ↦ 0) (ret := 0) hS h112
  refine exec_at (hb5 hp) run_b5 hwf5 (by intro l h; cases h) (hpc11.trans (lbl_9 hp))
    bd11.mid_match fun s5 hm5 hpc5 ↦ ?_
  obtain ⟨hk5, hw5, hdx5, hr85, w8, o16, o32, o40⟩ := after_eq run_b5 ▸ b5_facts
  have bd5 := bd11.of_frame (L := 64) hS h112 hwf5 bd11.mid_match hm5 (keepsRegs_rsp hk5) hw5
    (by decide) slots_ok
  have e5 := regs_eq_of bd11.mid_match hm5 hk5
  have hpt' : (Sym.bin .add .W64 (.lit 16) (.load 0 8 8)).eval (frameEnv m0 s11.data 112) =
      pt m0 + BitVec.ofNat 64 (16 * (i + 1)) := by
    rw [eval_add, eval_lit, eval_load, load_fw loc11.ptw, UInt64.toBitVec_ofBitVec, add16]
  have loc5 : Loc m0 s5.data.dmem (i + 1) := by
    refine ⟨?_, fw_keep hm5 (by decide) o16 loc11.size, fw_keep hm5 (by decide) o32 loc11.pend,
      fw_keep hm5 (by decide) o40 loc11.lenw⟩
    have a := fw_write hm5 (by decide) w8
    rwa [hpt'] at a
  have ker5 : EWsAt s5.data.dmem (out m0) (K m0 (i + 1)) := by
    refine ews_kept hpre' hm5 hwf5 hw5 ?_ (by rw [hdm11]; exact hR.ker)
    rw [length_K m0 (by omega)]; omega
  simp only [PcOk, NativeRustcVmX64.Vm.EqKernel.b5_length] at hpc5
  rw [eval_cmp_eq, hpt', eval_load, load_fw loc11.pend, UInt64.toBitVec_ofBitVec, beq_add_left,
    ofNat_beq (by omega) (by omega)] at hpc5
  obtain ⟨hT, hFl⟩ := pc_cond hpc5
  by_cases hlast : i + 1 = np m0
  · refine Eventually.mono (finish hp hpre' hle ((hT (by simp; omega)).trans (lbl_10 hp)) bd5
      (hlast ▸ loc5) (hlast ▸ ker5)) fun _ h ↦ Or.inl h
  · refine .done _ (Or.inr ⟨hFl (by simp; omega), bd5, loc5, by omega, ?_, ?_, ?_, ker5⟩)
    · rw [show reg s5.data .rdx = _ from hm5.regs .rdx _ hdx5, eval_add, eval_load,
        load_fw half11, UInt64.toBitVec_ofBitVec, ← BitVec.ofNat_add, Nat.pow_succ]
      exact congrArg _ (by omega)
    · rw [show reg s5.data .r8 = _ from hm5.regs .r8 _ hr85, eval_load, load_fw loc11.lenw,
        UInt64.toBitVec_ofBitVec]
    · exact (e5 .r15 (by simp)).trans ((e11 .r15 (by simp)).trans hR.r15)

end

end NativeRustcVmX64.Arrays.EqKernel
