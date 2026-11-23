module

public import NativeRustcVmX64.Whir.VerifyStackedOpening.Ladder
public import NativeRustcVmX64.Code.Vm.Memcpy.Names

/-!
# `verify_stacked_opening`: the levels copied (x86-64)

`copy_b44`: from `b44` (`AtB44`), `memcpy` copies the ladder's levels from the frame's `168` to
`320`; `b45` reads their count (at most `6`, never `7`); `b46` reads the `WhirW`'s address (the
stack argument `2`) and adds the out-of-domain term (R12, R13: the batched target); with levels
`b47` reads the first one's fold: at `b48` (`AtB48`).
-/

namespace NativeRustcVmX64.Whir.VerifyStackedOpening

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmX64.Transcript NativeRustcVm.Whir NativeRustcVmX64.Vm.VerifyStackedOpening
open LeanVM.Parameters

@[expose] public section

/-- **At `b48`**: the levels at the frame's `320`, the `WhirW` in RAX, the batched target in R12,
R13, the stack's log-size in R14, the levels' count in R9, the first fold in RDX. -/
structure AtB48 [Labels] (a : DecArea) (s : TState) (layout : LayoutW) (target : EW)
    (cs : Array ColumnClaimW) (value : EW) (ls : List Whir.Level) (m0 st : MachineData) :
    Prop where
  ok : Ok m0 st 8
  out : Outs a s layout cs m0 st.dmem
  fw : FW st.dmem m0 (fwL m0 ++ basisW m0 layout cs)
  lad : Whir.ladder layout.stackLog (reg m0 .rdx).toNat = some ls
  len : ls.length ≤ 6
  lv : LevelsAt st.dmem (win m0 320) ls
  rax : reg st .rax = pA m0
  r12 : reg st .r12 = (claimOf s layout target cs value).c0.toBitVec
  r13 : reg st .r13 = (claimOf s layout target cs value).c1.toBitVec
  r14 : reg st .r14 = layout.stackLog.toUInt64.toBitVec
  r9 : (reg st .r9).toNat = ls.length
  rdx : (reg st .rdx).toNat = (ls.head?.map (·.fold)).getD 0

end

public section

theorem eval_not_ult [Labels] {env : Env} (X : Sym) {c : Nat} (hc : c < 2 ^ 64) :
    (SBool.not (.cmp .ult .W64 X (.lit c))).eval env = !decide ((X.eval env).toNat < c) := by
  simp only [SBool.eval, CmpOp.apply, low_W64, Sym.eval, BitVec.ult, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hc]

theorem xor_c0 {x y : EW} {lo hi : BitVec 64} (h : x + ewArg lo hi = y) :
    lo ^^^ x.c0.toBitVec = y.c0.toBitVec ∧ hi ^^^ x.c1.toBitVec = y.c1.toBitVec := by
  subst h
  refine ⟨?_, ?_⟩
  · show _ = (x.c0 ^^^ UInt64.ofBitVec lo).toBitVec
    rw [UInt64.toBitVec_xor, BitVec.xor_comm]
  · show _ = (x.c1 ^^^ UInt64.ofBitVec hi).toBitVec
    rw [UInt64.toBitVec_xor, BitVec.xor_comm]

variable [Host] {k : Nat} {a : DecArea} {s : TState} {layout : LayoutW} {target : EW}
  {coefficients point slices : Array EW} {cs : Array ColumnClaimW} {z : Array EW} {value : EW}
  {m0 : MachineData} {ls : List Whir.Level}

/-- **The levels copied**: `b44` to `b48`. -/
theorem copy_b44 (h : Parts a s layout target coefficients point slices cs z value m0)
    (hp : Placed code k) (hmemcpy : Spec (Labels.label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b44Offset))
    (hA : AtB44 a s layout target cs value ls m0 st.data) {R : MachineState → Prop}
    (cont : ∀ st', st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b48Offset) →
      AtB48 a s layout target cs value ls m0 st'.data → Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hok := hA.ok
  obtain ⟨-, hlen', hcnt, hlv⟩ := hA.lat
  have hlen : ls.length ≤ 6 := hlen'
  rw [off_off] at hlv
  -- `b44`, `memcpy`
  refine h.run hp b44_in_code (List.cons_ne_nil _ _) hpc hok (vars := fun _ ↦ 0) (hok.got_wf h)
    (hok.m_copy h) run_b44 (o := 0) (by decide +kernel) (by decide) fun st1 hok1 hs1 hm1 hpc1 ↦ ?_
  have hout1 := Outs.keep h hA.out (hm1.kept (hok.got_wf h)) (h.blk_stack hs1)
  have hfw1 := FW.block_os (hok.got_wf h) hm1 rfl hA.fw
    [24, 40, 48, 56, 64, 104, 112, 120, 128, 136, 144, 152] rfl (by decide +kernel)
  have h72_1 := (FW.block_os (L := [(72, _)]) (hok.got_wf h) hm1 rfl (FW.one hA.hi72) [72] rfl
    (by decide +kernel)).get List.mem_cons_self
  have hcnt0 : NativeRustcVm.WordAt st.data.dmem (off (stackBelow m0 512) 312)
      ls.length.toUInt64 := by
    rw [off_off] at hcnt
    exact hcnt
  have hcnt1 := (FW.block_os (L := [(312, ls.length.toUInt64)]) (hok.got_wf h) hm1 rfl
    (FW.one hcnt0) [312] rfl (by decide +kernel)).get List.mem_cons_self
  have hlow := sameOutside_low (hok.got_wf h) hm1 (r := 0) rfl (hi := 8) (by omega) (by decide +kernel)
  have hlv1 : LevelsAt st1.data.dmem (win m0 168) ls := by
    have hfb : (stackBelow m0 512).toNat = (rspOf m0).toNat - 512 := h.fbn
    have hR := h.rsp
    intro i hi
    obtain ⟨h1, h2, h3, h4⟩ := hlv i hi
    refine ⟨h1, h2, h3, NativeRustcVm.BytesAt.of_sameOutside h4 hlow fun j hj hq ↦ ?_⟩
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append,
      NativeRustcVm.length_wordBytes] at hj
    have hi6 : i < 6 := by omega
    rw [off_off, off_add] at hq
    rw [inR (by unfold NativeRustcVm.NoWrap; omega), toNat_off (by simp only [levelBytes]; omega)]
      at hq
    simp only [levelBytes] at hq
    omega
  have e_di : reg st1.data .rdi = win m0 320 := (hm1.regs .rdi _ rfl).trans (eval_ptr0 320)
  have e_si : reg st1.data .rsi = win m0 168 := (hm1.regs .rsi _ rfl).trans (eval_ptr0 168)
  have e_dx : (reg st1.data .rdx).toNat = 144 := by
    rw [show reg st1.data .rdx = BitVec.ofNat 64 144 from hm1.regs .rdx (.lit 144) rfl]; rfl
  have hN : 512 + 0 ≤ verifyStackedOpeningStack := by rw [stack_eq]; decide
  have hR := h.rsp
  have hw320 := hok1.win_in h (lo := 320) (n := 144) (by omega) (by omega) hN
  have hw168 := hok1.win_in h (lo := 168) (n := 144) (by omega) (by omega) hN
  have t320 := h.win_toNat (lo := 320) (by omega)
  have t168 := h.win_toNat (lo := 168) (by omega)
  have hpre : MemcpyPre st1.data := by
    unfold MemcpyPre
    rw [e_di, e_si, e_dx]
    refine ⟨hok1.stackOk h hN, hw320.1.1, hw168.1.1, hw320.1.2, hw168.1.2, ?_, ?_⟩
    · unfold Apart; rw [t320, t168]; omega
    · have e1 : (rspOf st1.data).toNat = (rspOf m0).toNat - 512 := by
        rw [Ok.sp hok1]; exact h.fbn
      unfold Apart
      rw [t320, e1]
      omega
  refine call_then (P := MemcpyPre) (Q := MemcpyPost) hpc1 hmemcpy hpre
    fun st2 hpc2 hrsp2 ⟨_, hcp, hch, hsv⟩ ↦ ?_
  rw [e_di, e_si, e_dx] at hcp
  rw [e_di, e_dx] at hch
  have hch' : NativeRustcVm.SameOutside st1.data.dmem st2.data.dmem
      (fun q ↦ NativeRustcVm.InRange (win m0 320) 144 q ∨
        NativeRustcVm.InRange (stackBelow st1.data 0) 0 q) :=
    NativeRustcVm.SameOutside.mono hch fun _ hq ↦ .inl hq
  obtain ⟨hok2, hs2⟩ := hok1.callWin h hsv hrsp2 hN (lo := 320) (n := 144) (by omega) hch'
  have hout2 := Outs.keep h hout1 hsv.2 hs2
  have hfw2 := FW.callWin h hok1 hN (by omega) hch' hfw1
    (by
      intro p hp
      simp only [fwL, basisW, List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp)
    (le_of_map [24, 40, 48, 56, 64, 104, 112, 120, 128, 136, 144, 152] rfl (by decide))
  have hc312 := (FW.callWin h hok1 hN (by omega) hch' (L := [(312, ls.length.toUInt64)])
    (FW.one hcnt1)
    (fun p hp ↦ by simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; subst hp; simp)
    (le_of_map [312] rfl (by decide))).get List.mem_cons_self
  have hlv2 : LevelsAt st2.data.dmem (win m0 320) ls := by
    exact levelsAt_copy hcp hlv1 hlen
  have k2 : ∀ r, calleeSaved r = true → reg st2.data r = reg st.data r := fun r hr ↦
    (hsv.1 r hr).trans (regKeep hm1 r (by cases r <;> first | rfl | exact absurd hr (by decide)))
  -- `b45`
  refine h.run hp b45_in_code (List.cons_ne_nil _ _)
    (hpc2.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.VerifyStackedOpening.b44_next)) hok2 (vars := fun _ ↦ 0) (hok2.wf0 h)
    hok2.m_reg run_b45 (o := 8) (by decide +kernel) (by decide) fun st3 hok3 hs3 hm3 hpc3 ↦ ?_
  have hd3 : st3.data.dmem = st2.data.dmem := hm3.dmem_eq (hok2.wf0 h) rfl
  have hl312 : (frameEnv m0 st2.data 512 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b45Offset + b45.length)).toBitVec).load 0 312 8 = ls.length.toUInt64.toBitVec :=
    load_ofMachine (r := 0) rfl hc312
  have e3_r9 : (reg st3.data .r9).toNat = ls.length := by
    rw [show reg st3.data .r9 = _ from hm3.regs .r9 _ rfl]
    show ((frameEnv m0 st2.data 512 [] (fun _ ↦ 0) _).load 0 312 8).toNat = _
    rw [hl312]
    exact u64n (by omega)
  simp only [PcOk] at hpc3
  rw [eval_not_ult _ (by decide)] at hpc3
  rw [show ((Sym.load 0 312 8).eval (frameEnv m0 st2.data 512 [] (fun _ ↦ 0)
    (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b45Offset + b45.length)).toBitVec)).toNat = ls.length from by
      show ((frameEnv m0 st2.data 512 [] (fun _ ↦ 0) _).load 0 312 8).toNat = _
      rw [hl312]; exact u64n (by omega)] at hpc3
  simp only [show ls.length < 7 by omega, decide_true, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte] at hpc3
  have k3 : ∀ r, calleeSaved r = true → reg st3.data r = reg st.data r := fun r hr ↦
    (regKeep hm3 r (by cases r <;> first | rfl | exact absurd hr (by decide))).trans (k2 r hr)
  -- `b46`
  obtain ⟨ham, hanw, haap⟩ := h.arg_ok
  have hwf4 : ∀ ret, (frameEnv m0 st3.data 512 [(rspOf m0 + 8#64, 24)] (fun _ ↦ 0) ret).WF :=
    fun _ ↦ hok3.wf1 h ham hanw haap
  have hm4 : ∀ ret, Match (frameEnv m0 st3.data 512 [(rspOf m0 + 8#64, 24)] (fun _ ↦ 0) ret) argS
      st3.data := fun _ ↦
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hok3.fr.rsp_eval, trivial⟩ trivial trivial argAl_ok
  have hfw3 : FW st3.data.dmem m0 (fwL m0 ++ basisW m0 layout cs) := by rw [hd3]; exact hfw2
  have h72 : NativeRustcVm.WordAt st3.data.dmem (win m0 72) (accP s layout target cs value).c1 := by
    rw [hd3]
    refine (FW.callWin h hok1 hN (by omega) hch' (L := [(72, _)]) (FW.one h72_1)
      (fun p hp ↦ by simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; subst hp; simp)
      (le_of_map [72] rfl (by decide))).get List.mem_cons_self
  obtain ⟨hx0, hx1⟩ := xor_c0 hA.sum
  refine h.run hp b46_in_code (List.cons_ne_nil _ _)
    (hpc3.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.VerifyStackedOpening.b45_next)) hok3 (hwf4 _) (hm4 _) run_b46 (o := 8)
    (by decide +kernel) (by decide) fun st4 hok4 hs4 hm4' hpc4 ↦ ?_
  have hd4 : st4.data.dmem = st3.data.dmem := hm4'.dmem_eq (hwf4 _) rfl
  have e4_rax : reg st4.data .rax = pA m0 := by
    rw [show reg st4.data .rax = _ from hm4'.regs .rax _ rfl]
    exact hok3.argLoad h (i := 2) (by omega)
  have e4_r12 : reg st4.data .r12 = (claimOf s layout target cs value).c0.toBitVec := by
    rw [show reg st4.data .r12 = _ from hm4'.regs .r12 _ rfl, eval_xor64]
    show reg st3.data .r12 ^^^ reg st3.data .rbx = _
    rw [k3 .r12 rfl, k3 .rbx rfl, hA.rbx, hx0]
  have e4_r13 : reg st4.data .r13 = (claimOf s layout target cs value).c1.toBitVec := by
    rw [show reg st4.data .r13 = _ from hm4'.regs .r13 _ rfl, eval_xor64]
    show reg st3.data .r13 ^^^ (frameEnv m0 st3.data 512 _ (fun _ ↦ 0) _).load 0 72 8 = _
    rw [k3 .r13 rfl, load_ofMachine (r := 0) rfl h72, hx1]
  have e4_r14 : reg st4.data .r14 = layout.stackLog.toUInt64.toBitVec := by
    rw [regKeep hm4' .r14 rfl, k3 .r14 rfl]; exact hA.r14
  have e4_r9 : (reg st4.data .r9).toNat = ls.length := by rw [regKeep hm4' .r9 rfl]; exact e3_r9
  have e4_rdx : (reg st4.data .rdx).toNat = ls.length := by
    rw [show reg st4.data .rdx = reg st3.data .r9 from hm4'.regs .rdx _ rfl]; exact e3_r9
  have hout4 : Outs a s layout cs m0 st4.data.dmem := by rw [hd4, hd3]; exact hout2
  have hfw4 : FW st4.data.dmem m0 (fwL m0 ++ basisW m0 layout cs) := by rw [hd4]; exact hfw3
  have hlv4 : LevelsAt st4.data.dmem (win m0 320) ls := by rw [hd4, hd3]; exact hlv2
  simp only [PcOk] at hpc4
  rw [eval_test0] at hpc4
  rw [show ((Sym.reg .r9).eval (frameEnv m0 st3.data 512 [(rspOf m0 + 8#64, 24)] (fun _ ↦ 0)
    (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b46Offset + b46.length)).toBitVec)).toNat = ls.length from e3_r9] at hpc4
  cases hls : ls with
  | nil =>
    simp only [hls, List.length_nil, decide_true, ↓reduceIte] at hpc4
    rw [hp.label NativeRustcVmX64.Vm.VerifyStackedOpening.label_38_at] at hpc4
    refine cont st4 hpc4 ⟨hok4, hout4, hfw4, hA.lad, hlen, hlv4, e4_rax, e4_r12, e4_r13, e4_r14,
      e4_r9, ?_⟩
    rw [e4_rdx, hls]
    rfl
  | cons l0 ls' =>
    simp only [hls, List.length_cons, show ls'.length + 1 ≠ 0 by omega, decide_false,
      Bool.false_eq_true, ↓reduceIte] at hpc4
    -- `b47`: the first fold
    refine h.run hp b47_in_code (List.cons_ne_nil _ _)
      (hpc4.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.VerifyStackedOpening.b46_next)) hok4 (vars := fun _ ↦ 0) (hok4.wf0 h)
      hok4.m_reg run_b47 (o := 8) (by decide +kernel) (by decide) fun st5 hok5 hs5 hm5 hpc5 ↦ ?_
    have hd5 : st5.data.dmem = st4.data.dmem := hm5.dmem_eq (hok4.wf0 h) rfl
    simp only [PcOk] at hpc5
    have k5 : ∀ r : Reg64, r ∈ [Reg64.rax, .r12, .r13, .r14, .r9] →
        reg st5.data r = reg st4.data r := fun r hr ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact regKeep hm5 _ rfl
    have hl0 := hlv4 0 (by rw [hls]; simp)
    obtain ⟨hf, -, -, hws⟩ := hl0
    have hw0 := (NativeRustcVm.wordsAt_cons_iff.mp hws).1
    rw [Nat.mul_zero, off_zero] at hw0
    refine cont st5 (hpc5.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.VerifyStackedOpening.b47_next))
      ⟨hok5, by rw [hd5]; exact hout4, by rw [hd5]; exact hfw4, hA.lad, hlen,
        by rw [hd5]; exact hlv4, by rw [k5 .rax (by simp)]; exact e4_rax,
        by rw [k5 .r12 (by simp)]; exact e4_r12, by rw [k5 .r13 (by simp)]; exact e4_r13,
        by rw [k5 .r14 (by simp)]; exact e4_r14, by rw [k5 .r9 (by simp)]; exact e4_r9, ?_⟩
    rw [show reg st5.data .rdx = _ from hm5.regs .rdx _ rfl]
    show ((frameEnv m0 st4.data 512 [] (fun _ ↦ 0) _).load 0 320 8).toNat = _
    rw [load_ofMachine (r := 0) rfl hw0, u64n hf]
    simp [hls]

end

end NativeRustcVmX64.Whir.VerifyStackedOpening
