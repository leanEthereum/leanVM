module

public import NativeRustcVmX64.Bus.VerifyBusBalance.HeadCalls
public import NativeRustcVmX64.Code.Vm.BusLayout.Names
public import NativeRustcVmX64.Code.Vm.Memcpy.Names

/-!
# `verify_bus_balance`'s three layouts (x86-64)

From the entry: `b0` saves the registers, writes the bytecode at `128`, the framework sizes at
`328` and calls `bus_layout` on the push side; `b1` checks it; `b2` keeps the bus at `112` and
copies the layout to `2816`; `b3` stores its depth at `2808` and calls `bus_layout` on the pull
side; `b4`, `b5` copy it to `3696`; `b6` calls `bus_layout` on the count side; `b7`, `b8` copy it
to `4584` (`head_spec`, then `AtGrind`).
-/

namespace NativeRustcVmX64.Bus.VerifyBusBalance

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.VerifyBusBalance
open NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck NativeRustcVmX64.Bus.Gkr
open NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Bus NativeRustcVm.Layout

public section
variable [Host] {a : DecArea} {s0 : TState} {L : LayoutW} {m0 : MachineData} {k : Nat}

/-- **The three layouts** (`b0` to `b8`): the state at `b9`. -/
theorem head_spec (hp : Placed code k) (h : VerifyBusBalancePre a s0 L m0)
    (hbl : ∀ L bl, Spec (Labels.label NativeRustcVmX64.Vm.BusLayout.entryLabel) (BusLayoutPre L bl) (BusLayoutPost L bl))
    (hmc : Spec (Labels.label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hg : ∀ d, AtGrind a s0 L m0 d →
      Eventually (step1 Host.exe) (Goal a s0 L m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b9Offset)⟩) :
    Eventually (step1 Host.exe) (Goal a s0 L m0) ⟨m0, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b0Offset)⟩ := by
  have hS := pre_stack h
  have hlo := pre_layOk h
  have hlay := pre_lay h
  have hlm := hlay.log_memory_le
  have hlb := hlay.log_bytecode_le
  obtain ⟨rows, -, -, -, hrows⟩ := hlay.rows
  have hob : optBusLayoutBytes = 896 := rfl
  have hlb' : layoutBytes = 3912 := rfl
  have notX : ∀ {o n : Nat}, o + n ≤ 5520 → ∀ {ivs : List (Nat × Nat)},
      ivs.all (fun p ↦ decide (p.2 ≤ 5472)) = true →
      ivs.all (fun p ↦ decide (p.2 ≤ o) || decide (o + n ≤ p.1)) = true → ∀ j, InIv ivs j →
      ¬ NativeRustcVm.InRange (loc m0 o) n (loc m0 j) := fun {_ _} hon {_} hlt hap j hj hq ↦ by
    have hj5 := inIv_lt hlt hj
    exact loc_notIn hS (j := j) (by omega) (by omega) (inIv_apart hap hj) hq
  -- `b0`: the prologue, the framework sizes; `bus_layout` of the push side.
  have hwf0 : (frameEnv m0 m0 5520 [(reg m0 .rsi, 16)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b0Offset + b0.length)).toBitVec).WF :=
    Bus.wf1 hS N_ge (fun _ h ↦ h) ⟨fun i hi ↦ hlo.1.1 i (by omega),
      by have := hlo.1.2; unfold NativeRustcX64.NoWrap at this ⊢; omega⟩
      (NativeRustcVm.Apart.mono hlo.2 le_rfl (by omega) le_rfl le_rfl)
  have hm0 : Match (frameEnv m0 m0 5520 [(reg m0 .rsi, 16)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b0Offset + b0.length)).toBitVec) eS m0 :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨match_rsp, by
      show reg m0 .rsi = reg m0 .rsi + BitVec.ofInt 64 0
      rw [ofInt_zero64, BitVec.add_zero], trivial⟩ trivial trivial trivial
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) exit_b0 hwf0 (fun _ _ ↦ rfl) hm0
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hpro, hw0, wr0', hrbx1, hrcx1, hrdx1, hrsi1, hrdi1, hrbp1, hr81, hr91, hr121, hr131,
    hr141, hr151⟩ := ok_b0
  have fr1 : St m0 96 st1.data :=
    Fr.of_prologue hS N_ge hwf0 hm1 hpro slots_le slots_cs fun w hw ↦ (hw0 w hw).1
  have hs1 := blk_same hS hwf0 hm1 hw0 (by omega)
  have ts1 := ts_keep h (hm1.kept hwf0) hs1 (fun q hq ↦ .inl (frame_stack hS hq)) (pre_ts h)
  have hsp1 : rspOf st1.data = loc m0 96 := fr1.frame.sp
  have lm0 : NativeRustcVm.WordAt m0.dmem (off (reg m0 .rsi) 0) L.logMemory.toUInt64 := by
    rw [off_zero]; exact hlay.log_memory
  have e0 : (Sym.load 1 0 8).eval (frameEnv m0 m0 5520 [(reg m0 .rsi, 16)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b0Offset + b0.length)).toBitVec) = L.logMemory.toUInt64.toBitVec :=
    load_ofMachine (r := 1) rfl lm0
  have e8 : (Sym.load 1 8 8).eval (frameEnv m0 m0 5520 [(reg m0 .rsi, 16)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b0Offset + b0.length)).toBitVec) = L.logBytecode.toUInt64.toBitVec :=
    load_ofMachine (r := 1) rfl hlay.log_bytecode
  have wW1 : ∀ {o : Nat} {v : Sym}, o + 8 ≤ 5520 →
      (∀ t < 8, findWrite 0 (o + t) (after b0 eS).mem = some (v, t)) →
      NativeRustcVm.WordAt st1.data.dmem (loc m0 o) (UInt64.ofBitVec (v.eval
        (frameEnv m0 m0 5520 [(reg m0 .rsi, 16)] (fun _ ↦ 0)
          (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b0Offset + b0.length)).toBitVec))) :=
    fun ho hw ↦ wordAt_write hm1 (r := 0) (b := fb m0) (sz := 5520 + 8) rfl (by omega) hw
  have w128 : NativeRustcVm.WordAt st1.data.dmem (loc m0 128) (UInt64.ofBitVec (reg m0 .rdx)) :=
    wW1 (o := 128) (v := .reg .rdx) (by omega) (wr0'.find (List.Mem.head _))
  have w136 : NativeRustcVm.WordAt st1.data.dmem (loc m0 136) (UInt64.ofBitVec (reg m0 .rcx)) :=
    wW1 (o := 136) (v := .reg .rcx) (by omega) (wr0'.find (List.Mem.tail _ (List.Mem.head _)))
  have w328 : NativeRustcVm.WordAt st1.data.dmem (loc m0 328) 0 :=
    wW1 (o := 328) (v := .lit 0) (by omega) (wr0'.find (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  have w336 : NativeRustcVm.WordAt st1.data.dmem (loc m0 336) L.logMemory.toUInt64 := by
    have := wW1 (o := 336) (v := .load 1 0 8) (by omega)
      (wr0'.find (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
    rwa [e0, UInt64.ofBitVec_toBitVec] at this
  have w344 : NativeRustcVm.WordAt st1.data.dmem (loc m0 344) L.logBytecode.toUInt64 := by
    have := wW1 (o := 344) (v := .load 1 8 8) (by omega) (wr0'.find
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
    rwa [e8, UInt64.ofBitVec_toBitVec] at this
  have x1bx : reg st1.data .rbx = reg m0 .rdi := hm1.regs .rbx _ hrbx1
  have x1bp : reg st1.data .rbp = L.logMemory.toUInt64.toBitVec := (hm1.regs .rbp _ hrbp1).trans e0
  have x112 : reg st1.data .r12 = reg m0 .r8 := hm1.regs .r12 _ hr121
  have x113 : reg st1.data .r13 = L.logBytecode.toUInt64.toBitVec :=
    (hm1.regs .r13 _ hr131).trans e8
  have x114 : reg st1.data .r14 = reg m0 .rsi := by
    rw [show reg st1.data .r14 = _ from hm1.regs .r14 _ hr141]
    show reg m0 .rsi + BitVec.ofInt 64 0 = _
    rw [ofInt_zero64, BitVec.add_zero]
  have x115 : reg st1.data .r15 = reg m0 .r9 := hm1.regs .r15 _ hr151
  have x1si : reg st1.data .rsi = loc m0 328 := (hm1.regs .rsi _ hrsi1).trans (eval_ptr0 328)
  have x1dx : (reg st1.data .rdx).toNat = 3 := by
    rw [show reg st1.data .rdx = _ from hm1.regs .rdx _ hrdx1]; rfl
  have hle : 5520 - 96 + busLayoutStack ≤ NN := le_bl
  simp only [PcOk] at hpc1
  refine bl_call h hbl fr1 hpc1 (side := 0) (it := .pushBlocks) side0_bytes (by simp)
    (by rw [side0_len]; omega) (by rw [side0_len, maxBlocks_eq]) side0_own hrows
    (fw := fwRows L) (fw_nats x1si x1dx w328 w336 w344 hlm hlb)
    (by omega) (fun s hs ↦ by simp [fwRows] at hs; rcases hs with rfl | rfl | rfl <;> omega)
    (by rw [x1si, x1dx]; exact cal_localIn h fr1 (by omega) hle (by omega) (by omega))
    (by rw [x1si, x1dx]; exact loc_apart hS (by omega) (by omega) (by omega))
    (by
      intro l hl _
      rw [x1si, x1dx]
      exact got_apart_frame (pre_got h) hS hl N_ge (by omega))
    ((hm1.regs .rdi _ hrdi1).trans (eval_ptr0 672)) (hm1.regs .rcx _ hrcx1)
    (by rw [show reg st1.data .r8 = _ from hm1.regs .r8 _ hr81, side0_len]; rfl)
    (by
      rw [show reg st1.data .r9 = _ from hm1.regs .r9 _ hr91]
      show reg m0 .rsi + BitVec.ofInt 64 0 = _
      rw [ofInt_zero64, BitVec.add_zero])
    fun m2 fr2 ho2 hk2 hcs2 hs2 ↦ ?_
  have hle0 : 5520 - 96 + 0 ≤ NN := le_mem
  have e672 : off (loc m0 672) 8 = loc m0 680 := by
    show off (off (fb m0) 672) 8 = off (fb m0) 680; rw [off_off]
  have tsC : ∀ {st m : MachineData} {s : TState}, rspOf st = loc m0 96 →
      Kept st.dmem m.dmem → NativeRustcVm.SameOutside st.dmem m.dmem (fun q ↦
        NativeRustcVm.InRange (stackBelow st busLayoutStack) busLayoutStack q ∨
          NativeRustcVm.InRange (loc m0 672) optBusLayoutBytes q) →
      TStateAt st.dmem (reg m0 .rdi) a s → TStateAt m.dmem (reg m0 .rdi) a s :=
    fun hsp hk hs ht ↦ ts_keep h hk hs (fun q hq ↦ hq.elim
      (fun h' ↦ .inl (callee_stack hS hsp (by omega) hle h'))
      (fun h' ↦ .inl (loc_stack hS (by decide) h'))) ht
  have tsM : ∀ {st m : MachineData} {s : TState} {o n : Nat}, o + n ≤ 5520 →
      rspOf st = loc m0 96 → Kept st.dmem m.dmem →
      NativeRustcVm.SameOutside st.dmem m.dmem (fun q ↦
        NativeRustcVm.InRange (stackBelow st 0) 0 q ∨ NativeRustcVm.InRange (loc m0 o) n q) →
      TStateAt st.dmem (reg m0 .rdi) a s → TStateAt m.dmem (reg m0 .rdi) a s :=
    fun hon hsp hk hs ht ↦ ts_keep h hk hs (fun q hq ↦ hq.elim
      (fun h' ↦ .inl (callee_stack hS hsp (by omega) hle0 h'))
      (fun h' ↦ .inl (loc_stack hS hon h'))) ht
  have hP2 : BusLayoutWAt m2.dmem (loc m0 680) (pushL L) := by
    have := ho2.2; rw [e672] at this; exact this
  have k2 : KeepIv [(128, 144), (328, 352)] m0 st1.data.dmem m2.dmem :=
    keepIv_call hS hsp1 (by omega) hle hs2 (by decide) (by decide)
      (notX (by decide) (by decide) (by decide))
  have ts2 := tsC hsp1 hk2 hs2 ts1
  have c2 : ∀ r ∈ clRegs, reg m2 r = reg st1.data r := fun r hr' ↦ hcs2 r (clRegs_cs r hr').1
  -- `b1`: the push side's tag.
  rw [show k + NativeRustcVmX64.Vm.VerifyBusBalance.b0Offset + b0.length = k + NativeRustcVmX64.Vm.VerifyBusBalance.b1Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyBusBalance.b0_next]]
  refine test_spec hp h (j := NativeRustcVmX64.Vm.VerifyBusBalance.b1Offset) (n := b1.length) (infix_of b1_in_code (by simp [b1]) hp) rfl exit_b1
    ok_b1 fr2 (fun hc ↦ by rw [tag32_false ho2.1] at hc; cases hc) fun d3 fr3 hd3 hk3 _ ↦ ?_
  have c3 : ∀ r ∈ clRegs, reg d3 r = reg st1.data r := fun r hr' ↦
    (hk3 r (clRegs_cs r hr').2.2).trans (c2 r hr')
  -- `b2`: the bus at `112`; `memcpy(2816, 688, 880)`.
  rw [show k + NativeRustcVmX64.Vm.VerifyBusBalance.b1Offset + b1.length = k + NativeRustcVmX64.Vm.VerifyBusBalance.b2Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyBusBalance.b1_next]]
  have hwf4 := wf_copy h fr3.frame.kept (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b2Offset + b2.length)).toBitVec)
  refine exec_then (infix_of b2_in_code (by simp [b2]) hp) exit_b2 hwf4 (fun _ _ ↦ rfl)
    (match_copy h fr3) fun st4 hm4 hpc4 ↦ ?_
  obtain ⟨hmid4, hw4, wr4, hrdi4, hrsi4, hrdx4, hr124, hk4⟩ := ok_b2
  have fr4 : St m0 96 st4.data := St.blk fr3 hS hwf4 hm4 hmid4 fun q hq ↦ wr0 hS hw4 (by omega) hq
  have hin4 := writesIn_of_mid hmid4
  have hs4 := blk_same hS hwf4 hm4 hw4 (by omega)
  have hsp4 : rspOf st4.data = loc m0 96 := fr4.frame.sp
  have k4 : KeepIv [(128, 144), (328, 352)] m0 d3.dmem st4.data.dmem :=
    keepIv_block hwf4 hm4 hin4 (W0.reg0 hw4) (by decide) (by decide)
  have kS4 : KeepIv [(672, 1568)] m0 d3.dmem st4.data.dmem :=
    keepIv_block hwf4 hm4 hin4 (W0.reg0 hw4) (by decide) (by decide)
  have ts4 := ts_keep h (hm4.kept hwf4) hs4 (fun q hq ↦ .inl (frame_stack hS hq))
    (show TStateAt d3.dmem (reg m0 .rdi) a s0 by rw [hd3]; exact ts2)
  have hP4 : BusLayoutWAt st4.data.dmem (loc m0 680) (pushL L) :=
    BusLayoutWAt.of_same (show BusLayoutWAt d3.dmem (loc m0 680) (pushL L) by rw [hd3]; exact hP2)
      (kS4.sameIn (lo := 672) (hi := 1568) (by simp) (by omega) (by rw [busLayoutBytes_eq]))
  have w112 : NativeRustcVm.WordAt st4.data.dmem (loc m0 112) (UInt64.ofBitVec (reg m0 .r8)) := by
    have := wordAt_write hm4 (r := 0) (b := fb m0) (sz := 5520 + 8) (o := 112) (v := .reg .r12) rfl
      (by omega) (wr4.find (List.Mem.head _))
    rwa [show (Sym.reg .r12).eval (frameEnv m0 d3 5520 [(gotAddr "memcpy", 8)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b2Offset + b2.length)).toBitVec) = reg m0 .r8 from
        (c3 .r12 (by simp)).trans x112] at this
  have x412 : reg st4.data .r12 = (pushL L).depth.toUInt64.toBitVec :=
    (hm4.regs .r12 _ hr124).trans (load_loc (show NativeRustcVm.WordAt d3.dmem (loc m0 680) _ by
      rw [hd3]; exact hP2.depth))
  have c4 : ∀ r ∈ [Reg64.rbx, .rbp, .r13, .r14, .r15], reg st4.data r = reg st1.data r :=
    fun r hr' ↦ (hk4.reg hm4 hr').trans (c3 r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr' ⊢
      rcases hr' with h' | h' | h' | h' | h' <;> simp [h']))
  simp only [PcOk] at hpc4
  refine mc_call h hmc fr4 hpc4 (dst := 2816) (src := 688) (n := 880) (by omega) (by omega)
    (by omega) (by omega) (by omega) ((hm4.regs .rdi _ hrdi4).trans (eval_ptr0 2816))
    ((hm4.regs .rsi _ hrsi4).trans (eval_ptr0 688))
    (by rw [show reg st4.data .rdx = _ from hm4.regs .rdx _ hrdx4]; rfl)
    fun m5 fr5 hb5 hk5 hcs5 hs5 ↦ ?_
  have k5 : KeepIv [(112, 120), (128, 144), (328, 352)] m0 st4.data.dmem m5.dmem :=
    keepIv_call hS hsp4 (by omega) hle0 hs5 (by decide) (by decide)
      (notX (by omega) (by decide) (by decide))
  have ts5 := tsM (by omega) hsp4 hk5 hs5 ts4
  have c5 : ∀ r ∈ clRegs, reg m5 r = reg st4.data r := fun r hr' ↦ hcs5 r (clRegs_cs r hr').1
  -- `b3`: the push side's depth at `2808`; `bus_layout` of the pull side.
  rw [show k + NativeRustcVmX64.Vm.VerifyBusBalance.b2Offset + b2.length = k + NativeRustcVmX64.Vm.VerifyBusBalance.b3Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyBusBalance.b2_next]]
  have hwf6 := wf0 h fr5.frame.kept (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b3Offset + b3.length)).toBitVec)
  refine exec_then (infix_of b3_in_code (by simp [b3]) hp) exit_b3 hwf6 (fun _ _ ↦ rfl)
    (match_fS fr5) fun st6 hm6 hpc6 ↦ ?_
  obtain ⟨hmid6, hw6, wr6, hrcx6, hrdx6, hrsi6, hrdi6, hr86, hr96, hk6⟩ := ok_b3
  have fr6 : St m0 96 st6.data := St.blk fr5 hS hwf6 hm6 hmid6 fun q hq ↦ wr0 hS hw6 (by omega) hq
  have hin6 := writesIn_of_mid hmid6
  have hs6 := blk_same hS hwf6 hm6 hw6 (by omega)
  have hsp6 : rspOf st6.data = loc m0 96 := fr6.frame.sp
  have k6 : KeepIv [(112, 120), (128, 144), (328, 352)] m0 m5.dmem st6.data.dmem :=
    keepIv_block' hwf6 hm6 hin6 (by decide) (by decide +kernel)
  have ts6 := ts_keep h (hm6.kept hwf6) hs6 (fun q hq ↦ .inl (frame_stack hS hq)) ts5
  have c6 : ∀ r ∈ clRegs, reg st6.data r = reg st4.data r := fun r hr' ↦
    (hk6.reg hm6 (clRegs_cs r hr').2.1).trans (c5 r hr')
  have w2808 : NativeRustcVm.WordAt st6.data.dmem (loc m0 2808) (pushL L).depth.toUInt64 := by
    have := wordAt_write hm6 (r := 0) (b := fb m0) (sz := 5520 + 8) (o := 2808) (v := .reg .r12)
      rfl (by omega) (wr6.find (List.Mem.head _))
    rwa [show (Sym.reg .r12).eval (frameEnv m0 m5 5520 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b3Offset + b3.length)).toBitVec) = _ from (c5 .r12 (by simp)).trans x412,
      UInt64.ofBitVec_toBitVec] at this
  have hP6 : BusLayoutWAt st6.data.dmem (loc m0 2808) (pushL L) :=
    blw_copy hP4 w2808 (by
      have e1 : off (loc m0 680) 8 = loc m0 688 := by
        show off (off (fb m0) 680) 8 = off (fb m0) 688; rw [off_off]
      have e2 : off (loc m0 2808) 8 = loc m0 2816 := by
        show off (off (fb m0) 2808) 8 = off (fb m0) 2816; rw [off_off]
      rw [e1, e2]
      exact copy_keep hb5 (keepB hwf6 hm6 hin6 (j := 2816) (n := 880) (by omega)
        (miss0 hw6 (by omega))))
  have k5' : KeepIv [(128, 144), (328, 352)] m0 st4.data.dmem m5.dmem :=
    keepIv_call hS hsp4 (by omega) hle0 hs5 (by decide) (by decide)
      (notX (by omega) (by decide) (by decide))
  have k6' : KeepIv [(128, 144), (328, 352)] m0 m5.dmem st6.data.dmem :=
    keepIv_block' hwf6 hm6 hin6 (by decide) (by decide +kernel)
  have kF6 : KeepIv [(128, 144), (328, 352)] m0 st1.data.dmem st6.data.dmem :=
    k2.trans ((KeepIv.rfl' hd3).trans (k4.trans (k5'.trans k6')))
  have fw6 : ∀ {o : Nat} {x : UInt64}, 328 ≤ o → o + 8 ≤ 352 →
      NativeRustcVm.WordAt st1.data.dmem (loc m0 o) x →
      NativeRustcVm.WordAt st6.data.dmem (loc m0 o) x := fun h1 h2 hw ↦
    NativeRustcVm.Layout.WordAt.of_same hw (kF6.sameIn (lo := 328) (hi := 352) (by simp) h1 h2)
      le_rfl
  have x6si : reg st6.data .rsi = loc m0 328 := (hm6.regs .rsi _ hrsi6).trans (eval_ptr0 328)
  have x6dx : (reg st6.data .rdx).toNat = 3 := by
    rw [show reg st6.data .rdx = _ from hm6.regs .rdx _ hrdx6]; rfl
  simp only [PcOk] at hpc6
  refine bl_call h hbl fr6 hpc6 (side := 1) (it := .pullBlocks) side1_bytes (by simp)
    (by rw [side1_len]; omega) (by rw [side1_len, maxBlocks_eq]) side1_own hrows
    (fw := fwRows L) (fw_nats x6si x6dx (fw6 (by omega) (by omega) w328)
      (fw6 (by omega) (by omega) w336) (fw6 (by omega) (by omega) w344) hlm hlb)
    (by omega) (fun s hs ↦ by simp [fwRows] at hs; rcases hs with rfl | rfl | rfl <;> omega)
    (by rw [x6si, x6dx]; exact cal_localIn h fr6 (by omega) hle (by omega) (by omega))
    (by rw [x6si, x6dx]; exact loc_apart hS (by omega) (by omega) (by omega))
    (by
      intro l hl _
      rw [x6si, x6dx]
      exact got_apart_frame (pre_got h) hS hl N_ge (by omega))
    ((hm6.regs .rdi _ hrdi6).trans (eval_ptr0 672)) (hm6.regs .rcx _ hrcx6)
    (by rw [show reg st6.data .r8 = _ from hm6.regs .r8 _ hr86, side1_len]; rfl)
    ((hm6.regs .r9 _ hr96).trans ((c5 .r14 (by simp)).trans ((c4 .r14 (by simp)).trans x114)))
    fun m7 fr7 ho7 hk7 hcs7 hs7 ↦ ?_
  have hQ7 : BusLayoutWAt m7.dmem (loc m0 680) (pullL L) := by
    have := ho7.2; rw [e672] at this; exact this
  have kE7 : KeepIv [(112, 120), (128, 144), (2808, 3696)] m0 st6.data.dmem m7.dmem :=
    keepIv_call hS hsp6 (by omega) hle hs7 (by decide) (by decide)
      (notX (by decide) (by decide) (by decide))
  have ts7 := tsC hsp6 hk7 hs7 ts6
  have c7 : ∀ r ∈ clRegs, reg m7 r = reg st4.data r := fun r hr' ↦
    (hcs7 r (clRegs_cs r hr').1).trans (c6 r hr')
  -- `b4`: the pull side's tag.
  rw [show k + NativeRustcVmX64.Vm.VerifyBusBalance.b3Offset + b3.length = k + NativeRustcVmX64.Vm.VerifyBusBalance.b4Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyBusBalance.b3_next]]
  refine test_spec hp h (j := NativeRustcVmX64.Vm.VerifyBusBalance.b4Offset) (n := b4.length) (infix_of b4_in_code (by simp [b4]) hp) rfl exit_b4
    ok_b4 fr7 (fun hc ↦ by rw [tag8_false ho7.1] at hc; cases hc) fun d8 fr8 hd8 hk8 _ ↦ ?_
  have c8 : ∀ r ∈ clRegs, reg d8 r = reg st4.data r := fun r hr' ↦
    (hk8 r (clRegs_cs r hr').2.2).trans (c7 r hr')
  -- `b5`: `memcpy(3696, 680, 888)`.
  rw [show k + NativeRustcVmX64.Vm.VerifyBusBalance.b4Offset + b4.length = k + NativeRustcVmX64.Vm.VerifyBusBalance.b5Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyBusBalance.b4_next]]
  have hwf9 := wf_copy h fr8.frame.kept (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b5Offset + b5.length)).toBitVec)
  refine exec_then (infix_of b5_in_code (by simp [b5]) hp) exit_b5 hwf9 (fun _ _ ↦ rfl)
    (match_copy h fr8) fun st9 hm9 hpc9 ↦ ?_
  obtain ⟨hmid9, hw9, hrdi9, hrsi9, hrdx9, hk9⟩ := ok_b5
  have fr9 : St m0 96 st9.data := St.blk fr8 hS hwf9 hm9 hmid9 fun q hq ↦ wr0 hS hw9 (by omega) hq
  have hin9 := writesIn_of_mid hmid9
  have hs9 := blk_same hS hwf9 hm9 hw9 (by omega)
  have hsp9 : rspOf st9.data = loc m0 96 := fr9.frame.sp
  have kE9 : KeepIv [(112, 120), (128, 144), (2808, 3696)] m0 d8.dmem st9.data.dmem :=
    keepIv_block hwf9 hm9 hin9 (W0.reg0 hw9) (by decide) (by decide)
  have kS9 : KeepIv [(672, 1568)] m0 d8.dmem st9.data.dmem :=
    keepIv_block hwf9 hm9 hin9 (W0.reg0 hw9) (by decide) (by decide)
  have ts9 := ts_keep h (hm9.kept hwf9) hs9 (fun q hq ↦ .inl (frame_stack hS hq))
    (show TStateAt d8.dmem (reg m0 .rdi) a s0 by rw [hd8]; exact ts7)
  have hQ9 : BusLayoutWAt st9.data.dmem (loc m0 680) (pullL L) :=
    BusLayoutWAt.of_same (show BusLayoutWAt d8.dmem (loc m0 680) (pullL L) by rw [hd8]; exact hQ7)
      (kS9.sameIn (lo := 672) (hi := 1568) (by simp) (by omega) (by rw [busLayoutBytes_eq]))
  have c9 : ∀ r ∈ clRegs, reg st9.data r = reg st4.data r := fun r hr' ↦
    (hk9.reg hm9 (clRegs_cs r hr').2.1).trans (c8 r hr')
  simp only [PcOk] at hpc9
  refine mc_call h hmc fr9 hpc9 (dst := 3696) (src := 680) (n := 888) (by omega) (by omega)
    (by omega) (by omega) (by omega) ((hm9.regs .rdi _ hrdi9).trans (eval_ptr0 3696))
    ((hm9.regs .rsi _ hrsi9).trans (eval_ptr0 680))
    (by rw [show reg st9.data .rdx = _ from hm9.regs .rdx _ hrdx9]; rfl)
    fun m10 fr10 hb10 hk10 hcs10 hs10 ↦ ?_
  have hQ10 : BusLayoutWAt m10.dmem (loc m0 3696) (pullL L) := busLayoutWAt_transfer
    (fun i hi x hx ↦ get_of_copy hb10 i hi x hx) hQ9
  have kE10 : KeepIv [(112, 120), (128, 144), (2808, 3696)] m0 st9.data.dmem m10.dmem :=
    keepIv_call hS hsp9 (by omega) hle0 hs10 (by decide) (by decide)
      (notX (by omega) (by decide) (by decide))
  have ts10 := tsM (by omega) hsp9 hk10 hs10 ts9
  have c10 : ∀ r ∈ clRegs, reg m10 r = reg st4.data r := fun r hr' ↦
    (hcs10 r (clRegs_cs r hr').1).trans (c9 r hr')
  -- `b6`: `bus_layout` of the count side.
  rw [show k + NativeRustcVmX64.Vm.VerifyBusBalance.b5Offset + b5.length = k + NativeRustcVmX64.Vm.VerifyBusBalance.b6Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyBusBalance.b5_next]]
  have hwf11 := wf0 h fr10.frame.kept (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b6Offset + b6.length)).toBitVec)
  refine exec_then (infix_of b6_in_code (by simp [b6]) hp) exit_b6 hwf11 (fun _ _ ↦ rfl)
    (match_fS fr10) fun st11 hm11 hpc11 ↦ ?_
  obtain ⟨hmid11, hw11, hrcx11, hrdx11, hrsi11, hrdi11, hr811, hr911, hk11⟩ := ok_b6
  have fr11 : St m0 96 st11.data :=
    St.blk fr10 hS hwf11 hm11 hmid11 fun q hq ↦ wr0 hS hw11 (by omega) hq
  have hin11 := writesIn_of_mid hmid11
  have hs11 := blk_same hS hwf11 hm11 hw11 (by omega)
  have hsp11 : rspOf st11.data = loc m0 96 := fr11.frame.sp
  have kE11 : KeepIv [(112, 120), (128, 144), (2808, 3696)] m0 m10.dmem st11.data.dmem :=
    keepIv_block hwf11 hm11 hin11 (W0.reg0 hw11) (by decide) (by decide)
  have kP11 : KeepIv [(3696, 4584)] m0 m10.dmem st11.data.dmem :=
    keepIv_block hwf11 hm11 hin11 (W0.reg0 hw11) (by decide) (by decide)
  have ts11 := ts_keep h (hm11.kept hwf11) hs11 (fun q hq ↦ .inl (frame_stack hS hq)) ts10
  have c11 : ∀ r ∈ clRegs, reg st11.data r = reg st4.data r := fun r hr' ↦
    (hk11.reg hm11 (clRegs_cs r hr').2.1).trans (c10 r hr')
  have x11si : reg st11.data .rsi = BitVec.ofNat 64 8 := hm11.regs .rsi _ hrsi11
  have x11dx : (reg st11.data .rdx).toNat = 0 := by
    rw [show reg st11.data .rdx = _ from hm11.regs .rdx _ hrdx11]; rfl
  have hb8 : 5424 + busLayoutStack + 8 ≤ NN := by decide
  simp only [PcOk] at hpc11
  refine bl_call h hbl fr11 hpc11 (side := 2) (it := .countBlocks) side2_bytes (by simp)
    (by rw [side2_len]; omega) (by rw [side2_len, maxBlocks_eq]; omega) side2_own hrows
    (fw := #[]) (by rw [x11dx]; rfl) (by omega) (by simp)
    (by
      rw [x11si, x11dx]
      refine ⟨⟨fun i hi ↦ absurd hi (by omega), by
        show (BitVec.ofNat 64 8).toNat + 8 * 0 ≤ 2 ^ 64; simp⟩, ?_⟩
      show (BitVec.ofNat 64 8).toNat + 8 * 0 ≤ (stackBelow st11.data busLayoutStack).toNat ∨ _
      left
      have := rsp_ge hS
      have hl := loc_toNat hS (j := 96) (by omega)
      rw [stackBelow_toNat (by rw [hsp11, hl]; omega), hsp11, hl]
      simp only [BitVec.toNat_ofNat]
      omega)
    (by
      rw [x11si, x11dx]
      show _ ∨ (BitVec.ofNat 64 8).toNat + 8 * 0 ≤ (loc m0 672).toNat
      right
      have := rsp_ge hS
      rw [loc_toNat hS (by omega)]
      simp only [BitVec.toNat_ofNat]
      omega)
    (by intro _ _ hn; rw [x11dx] at hn; omega)
    ((hm11.regs .rdi _ hrdi11).trans (eval_ptr0 672)) (hm11.regs .rcx _ hrcx11)
    (by rw [show reg st11.data .r8 = _ from hm11.regs .r8 _ hr811, side2_len]; rfl)
    ((hm11.regs .r9 _ hr911).trans ((c10 .r14 (by simp)).trans ((c4 .r14 (by simp)).trans x114)))
    fun m12 fr12 ho12 hk12 hcs12 hs12 ↦ ?_
  have hC12 : BusLayoutWAt m12.dmem (loc m0 680) (countL L) := by
    have := ho12.2; rw [e672] at this; exact this
  have kE12 : KeepIv [(112, 120), (128, 144), (2808, 3696)] m0 st11.data.dmem m12.dmem :=
    keepIv_call hS hsp11 (by omega) hle hs12 (by decide) (by decide)
      (notX (by decide) (by decide) (by decide))
  have kP12 : KeepIv [(3696, 4584)] m0 st11.data.dmem m12.dmem :=
    keepIv_call hS hsp11 (by omega) hle hs12 (by decide) (by decide)
      (notX (by decide) (by decide) (by decide))
  have ts12 := tsC hsp11 hk12 hs12 ts11
  have c12 : ∀ r ∈ clRegs, reg m12 r = reg st4.data r := fun r hr' ↦
    (hcs12 r (clRegs_cs r hr').1).trans (c11 r hr')
  -- `b7`: the count side's tag.
  rw [show k + NativeRustcVmX64.Vm.VerifyBusBalance.b6Offset + b6.length = k + NativeRustcVmX64.Vm.VerifyBusBalance.b7Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyBusBalance.b6_next]]
  refine test_spec hp h (j := NativeRustcVmX64.Vm.VerifyBusBalance.b7Offset) (n := b7.length) (infix_of b7_in_code (by simp [b7]) hp) rfl exit_b7
    ok_b7 fr12 (fun hc ↦ by rw [tag8_false ho12.1] at hc; cases hc) fun d13 fr13 hd13 hk13 _ ↦ ?_
  have c13 : ∀ r ∈ clRegs, reg d13 r = reg st4.data r := fun r hr' ↦
    (hk13 r (clRegs_cs r hr').2.2).trans (c12 r hr')
  -- `b8`: `memcpy(4584, 680, 888)`.
  rw [show k + NativeRustcVmX64.Vm.VerifyBusBalance.b7Offset + b7.length = k + NativeRustcVmX64.Vm.VerifyBusBalance.b8Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyBusBalance.b7_next]]
  have hwf14 := wf_copy h fr13.frame.kept (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b8Offset + b8.length)).toBitVec)
  refine exec_then (infix_of b8_in_code (by simp [b8]) hp) exit_b8 hwf14 (fun _ _ ↦ rfl)
    (match_copy h fr13) fun st14 hm14 hpc14 ↦ ?_
  obtain ⟨hmid14, hw14, hrdi14, hrsi14, hrdx14, hk14⟩ := ok_b8
  have fr14 : St m0 96 st14.data :=
    St.blk fr13 hS hwf14 hm14 hmid14 fun q hq ↦ wr0 hS hw14 (by omega) hq
  have hin14 := writesIn_of_mid hmid14
  have hs14 := blk_same hS hwf14 hm14 hw14 (by omega)
  have hsp14 : rspOf st14.data = loc m0 96 := fr14.frame.sp
  have kE14 : KeepIv [(112, 120), (128, 144), (2808, 3696)] m0 d13.dmem st14.data.dmem :=
    keepIv_block hwf14 hm14 hin14 (W0.reg0 hw14) (by decide) (by decide)
  have kP14 : KeepIv [(3696, 4584)] m0 d13.dmem st14.data.dmem :=
    keepIv_block hwf14 hm14 hin14 (W0.reg0 hw14) (by decide) (by decide)
  have kS14 : KeepIv [(672, 1568)] m0 d13.dmem st14.data.dmem :=
    keepIv_block hwf14 hm14 hin14 (W0.reg0 hw14) (by decide) (by decide)
  have ts14 := ts_keep h (hm14.kept hwf14) hs14 (fun q hq ↦ .inl (frame_stack hS hq))
    (show TStateAt d13.dmem (reg m0 .rdi) a s0 by rw [hd13]; exact ts12)
  have hC14 : BusLayoutWAt st14.data.dmem (loc m0 680) (countL L) :=
    BusLayoutWAt.of_same (show BusLayoutWAt d13.dmem (loc m0 680) (countL L) by
      rw [hd13]; exact hC12)
      (kS14.sameIn (lo := 672) (hi := 1568) (by simp) (by omega) (by rw [busLayoutBytes_eq]))
  have c14 : ∀ r ∈ clRegs, reg st14.data r = reg st4.data r := fun r hr' ↦
    (hk14.reg hm14 (clRegs_cs r hr').2.1).trans (c13 r hr')
  simp only [PcOk] at hpc14
  refine mc_call h hmc fr14 hpc14 (dst := 4584) (src := 680) (n := 888) (by omega) (by omega)
    (by omega) (by omega) (by omega) ((hm14.regs .rdi _ hrdi14).trans (eval_ptr0 4584))
    ((hm14.regs .rsi _ hrsi14).trans (eval_ptr0 680))
    (by rw [show reg st14.data .rdx = _ from hm14.regs .rdx _ hrdx14]; rfl)
    fun m15 fr15 hb15 hk15 hcs15 hs15 ↦ ?_
  have hC15 : BusLayoutWAt m15.dmem (loc m0 4584) (countL L) := busLayoutWAt_transfer
    (fun i hi x hx ↦ get_of_copy hb15 i hi x hx) hC14
  have kE15 : KeepIv [(112, 120), (128, 144), (2808, 3696)] m0 st14.data.dmem m15.dmem :=
    keepIv_call hS hsp14 (by omega) hle0 hs15 (by decide) (by decide)
      (notX (by omega) (by decide) (by decide))
  have kP15 : KeepIv [(3696, 4584)] m0 st14.data.dmem m15.dmem :=
    keepIv_call hS hsp14 (by omega) hle0 hs15 (by decide) (by decide)
      (notX (by omega) (by decide) (by decide))
  have ts15 := tsM (by omega) hsp14 hk15 hs15 ts14
  have c15 : ∀ r ∈ clRegs, reg m15 r = reg st4.data r := fun r hr' ↦
    (hcs15 r (clRegs_cs r hr').1).trans (c14 r hr')
  -- The state at `b9`.
  rw [show k + NativeRustcVmX64.Vm.VerifyBusBalance.b8Offset + b8.length = k + NativeRustcVmX64.Vm.VerifyBusBalance.b9Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyBusBalance.b8_next]]
  have kE : KeepIv [(112, 120), (128, 144), (2808, 3696)] m0 st6.data.dmem m15.dmem :=
    kE7.trans ((KeepIv.rfl' hd8).trans (kE9.trans (kE10.trans (kE11.trans (kE12.trans
      ((KeepIv.rfl' hd13).trans (kE14.trans kE15)))))))
  have kP : KeepIv [(3696, 4584)] m0 m10.dmem m15.dmem :=
    kP11.trans (kP12.trans ((KeepIv.rfl' hd13).trans (kP14.trans kP15)))
  have wE : ∀ {lo hi o : Nat} {x : UInt64}, (lo, hi) ∈ [(112, 120), (128, 144), (2808, 3696)] →
      lo ≤ o → o + 8 ≤ hi → NativeRustcVm.WordAt st6.data.dmem (loc m0 o) x →
      NativeRustcVm.WordAt m15.dmem (loc m0 o) x := fun hm h1 h2 hw ↦
    NativeRustcVm.Layout.WordAt.of_same hw (kE.sameIn hm h1 h2) le_rfl
  have w112' : NativeRustcVm.WordAt st6.data.dmem (loc m0 112) (UInt64.ofBitVec (reg m0 .r8)) :=
    NativeRustcVm.Layout.WordAt.of_same w112 ((k5.sameIn (lo := 112) (hi := 120) (by simp)
      (by omega) (by omega)).trans (k6.sameIn (lo := 112) (hi := 120) (by simp) (by omega)
      (by omega))) le_rfl
  have w6 : ∀ {o : Nat} {x : UInt64}, 128 ≤ o → o + 8 ≤ 144 →
      NativeRustcVm.WordAt st1.data.dmem (loc m0 o) x →
      NativeRustcVm.WordAt st6.data.dmem (loc m0 o) x := fun h1 h2 hw ↦
    NativeRustcVm.Layout.WordAt.of_same hw (kF6.sameIn (lo := 128) (hi := 144) (by simp) h1 h2)
      le_rfl
  have hb : busLayoutBytes = 888 := busLayoutBytes_eq
  exact hg m15 ⟨fr15, wE (lo := 112) (hi := 120) (by simp) (by omega) (by omega) w112',
    BusLayoutWAt.of_same hP6 (kE.sameIn (lo := 2808) (hi := 3696) (by simp) (by omega) (by omega)),
    BusLayoutWAt.of_same hQ10 (kP.sameIn (lo := 3696) (hi := 4584) (by simp) (by omega)
      (by omega)), hC15,
    wE (lo := 128) (hi := 144) (by simp) (by omega) (by omega) (w6 (by omega) (by omega) w128),
    wE (lo := 128) (hi := 144) (by simp) (by omega) (by omega) (w6 (by omega) (by omega) w136),
    (c15 .rbx (by simp)).trans ((c4 .rbx (by simp)).trans x1bx),
    (c15 .r12 (by simp)).trans x412,
    (c15 .r13 (by simp)).trans ((c4 .r13 (by simp)).trans x113),
    (c15 .r14 (by simp)).trans ((c4 .r14 (by simp)).trans x114),
    (c15 .r15 (by simp)).trans ((c4 .r15 (by simp)).trans x115),
    (c15 .rbp (by simp)).trans ((c4 .rbp (by simp)).trans x1bp), ts15⟩

end

end NativeRustcVmX64.Bus.VerifyBusBalance
