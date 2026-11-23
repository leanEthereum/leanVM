module

public import NativeRustcVmX64.Bus.VerifyBusBalance.Fp
public import NativeRustcVmX64.Code.Vm.AccumulateSide.Names
public import NativeRustcVmX64.Code.Vm.BufEW63Extend.Names
public import NativeRustcVmX64.Code.Vm.VerifyBusBalanceClosure0.Names

/-!
# `verify_bus_balance`'s pull side (x86-64)

From `b47` (`k + NativeRustcVmX64.Vm.VerifyBusBalance.b47Offset`, RSP at the frame's offset `8` after the push side's `accumulate_side`):
`b47` checks the push side's tag; `b48` keeps its total in R13, RBP and calls the closure for the
pull side's fingerprints (`pc_final`, the final counters); `b49` calls `accumulate_side` on the
pull side; then the count side (`pull_spec`).

`Chg m0 d d'`: memory kept, changed only in the stack and the bus (`Chg.trans`, `Chg.tc`).
-/

namespace NativeRustcVmX64.Bus.VerifyBusBalance

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.VerifyBusBalance
open NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck NativeRustcVmX64.Bus.Gkr
open NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Bus NativeRustcVm.Layout

public section

/-- Memory kept, changed only in the stack and the bus. -/
@[expose] def Chg (m0 : MachineData) (d d' : Mem 64) : Prop :=
  Kept d d' ∧ NativeRustcVm.SameOutside d d' (fun q ↦
    NativeRustcVm.InRange (stackBelow m0 NN) NN q ∨ NativeRustcVm.InRange (reg m0 .r8) busBytes q)

theorem Chg.trans {m0 : MachineData} {d d' d'' : Mem 64} (h : Chg m0 d d') (h' : Chg m0 d' d'') :
    Chg m0 d d'' :=
  ⟨kept_trans h.1 h'.1, (h.2.trans h'.2).mono fun _ hq ↦ hq.elim id id⟩

theorem Chg.rfl' {m0 : MachineData} {d d' : Mem 64} (h : d' = d) : Chg m0 d d' :=
  ⟨fun _ hp ↦ h ▸ hp, fun _ _ ↦ by rw [h]⟩

theorem Chg.of {m0 : MachineData} {d d' : Mem 64} {X : BitVec 64 → Prop} (hk : Kept d d')
    (hs : NativeRustcVm.SameOutside d d' X)
    (hX : ∀ q, X q → NativeRustcVm.InRange (stackBelow m0 NN) NN q ∨
      NativeRustcVm.InRange (reg m0 .r8) busBytes q) : Chg m0 d d' :=
  ⟨hk, hs.mono hX⟩

/-- A stack argument the frame holds, RSP at its offset `c`. -/
theorem stackArg_at {m0 d : MachineData} {c : Nat} (hsp : rspOf d = loc m0 c) {i : Nat}
    {w : UInt64} (h : NativeRustcVm.WordAt d.dmem (loc m0 (c + (8 + 8 * i))) w) :
    stackArg d i = w.toBitVec := by
  unfold stackArg
  rw [hsp, off_add]
  exact congrArg UInt64.toBitVec (NativeRustcVm.wordOf_of_wordAt h)

end

public section
variable [Labels] {a : DecArea} {s0 : TState} {L : LayoutW} {m0 : MachineData}

theorem Chg.tc (h : VerifyBusBalancePre a s0 L m0) {d d' : Mem 64} (hc : Chg m0 d d') {s : TState}
    {cs : Array ColumnClaimW} (hts : TStateAt d (reg m0 .rdi) a s)
    (hcl : ClaimsWAt d (reg m0 .r9) cs) :
    TStateAt d' (reg m0 .rdi) a s ∧ ClaimsWAt d' (reg m0 .r9) cs :=
  tc_keep h hc.1 hc.2 (fun _ hq ↦ hq) hts hcl

end

public section
variable [Labels] {a : DecArea} {s0 : TState} {L : LayoutW} {m0 : MachineData}

/-- **The bus's bytes kept** by a change in the stack. -/
theorem bus_same (h : VerifyBusBalancePre a s0 L m0) {d d' : Mem 64} {X : BitVec 64 → Prop}
    (hs : NativeRustcVm.SameOutside d d' X)
    (hX : ∀ q, X q → NativeRustcVm.InRange (stackBelow m0 NN) NN q) {n : Nat} (hn : n ≤ busBytes) :
    Same d d' (reg m0 .r8) n := Same.of_sameOutside hs fun j hj hq ↦
  NativeRustcVm.Apart.not_inRange_add (pre_bus h).2.2.2.2.1 (pre_bus h).2.1
    (noWrap_stackBelow (pre_stack h)) (by omega) (inRange_mono (hX _ hq) (by omega))

end

public section
variable [Host] {a : DecArea} {s0 : TState} {L : LayoutW} {m0 : MachineData} {k : Nat}

/-- **The pull side** (`b47`, `k + NativeRustcVmX64.Vm.VerifyBusBalance.b47Offset`). -/
theorem pull_spec (hp : Placed code k) (h : VerifyBusBalancePre a s0 L m0)
    (hfc : Spec (Labels.label NativeRustcVmX64.Vm.VerifyBusBalanceClosure0.entryLabel) FpClosurePre FpClosurePost)
    (hacc : ∀ L rows bl F SL, Spec (Labels.label NativeRustcVmX64.Vm.AccumulateSide.entryLabel)
      (AccumulateSidePre L rows bl F SL) (AccumulateSidePost L rows bl F SL))
    (hext : Spec (Labels.label NativeRustcVmX64.Vm.BufEW63Extend.entryLabel) (BufEWExtendPre 63) (BufEWExtendPost 63))
    {d : MachineData} {w pt tv mem : Array EW} {beta mf bf share : EW} {bp : Array EW}
    {s' : TState} (fr : St m0 8 d)
    (hrun : (verifyBusBalance L).run s0 = some (resultOf L w beta pt tv mem mf bf share bp, s'))
    (hl : SideMem m0 L w pt tv mem beta mf bf share d.dmem)
    (hopt : OptEWAt d.dmem (loc m0 192) (some (acc0 L w beta pt tv mem share).2))
    (hF : FormsAt d.dmem (reg m0 .r8) (acc0 L w beta pt tv mem share).1)
    (hfits : FitsUpTo (acc0 L w beta pt tv mem share).1 1)
    (x14 : reg d .r14 = reg m0 .rsi) (x15 : reg d .r15 = loc m0 368)
    (xbx : reg d .rbx = loc m0 624)
    (hts : TStateAt d.dmem (reg m0 .rdi) a s')
    (hcl : ClaimsWAt d.dmem (reg m0 .r9) (claimsOf L pt mem mf bf)) :
    Eventually (step1 Host.exe) (Goal a s0 L m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b47Offset)⟩ := by
  have hS := pre_stack h
  have psz := hl.tail.psz
  -- `b47`: the push side's tag.
  have hwf0 := wf0 h fr.frame.kept (vars := fun _ ↦ 0) (ret := 0)
  refine exec_then (infix_of b47_in_code (by simp [b47]) hp) exit_b47 hwf0 nofun (match_fS fr)
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid1, hmem1, hk1⟩ := ok_b47
  have fr1 := (fr.block0 hS N_ge hwf0 hm1 hmid1 slots_le (by simp [hmem1])).1
  have hd1 : st1.data.dmem = d.dmem := hm1.dmem_eq hwf0 hmem1
  simp only [PcOk, tag32_false hopt.1, Bool.false_eq_true, ↓reduceIte] at hpc1
  rw [NativeRustcVmX64.Vm.VerifyBusBalance.b47_length] at hpc1
  have k1 : ∀ r ∈ cs, reg st1.data r = reg d r := fun r hr ↦ hk1.reg hm1 hr
  -- `b48`: the closure for the pull side's fingerprints.
  have hwf2 := wf0 h fr1.frame.kept (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b48Offset + b48.length)).toBitVec)
  refine exec_at (infix_of b48_in_code (by simp [b48]) hp) exit_b48 hwf2 (fun _ _ ↦ rfl) hpc1
    (match_fS fr1) fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨hmid2, hw2, wr2, hrdi, hrsi, hrdx, hrcx, hr8, hr9, hr13, hrbp, hk2⟩ := ok_b48
  have fr2 : St m0 80 st2.data := St.blk fr1 hS hwf2 hm2 hmid2 fun q hq ↦ wr0 hS hw2 (by omega) hq
  have hin2 := writesIn_of_mid hmid2
  have hs2 := blk_same hS hwf2 hm2 hw2 (by omega)
  have ld : ∀ {o : Nat} {x : UInt64}, NativeRustcVm.WordAt d.dmem (loc m0 o) x →
      (frameEnv m0 st1.data 5520 [] (fun _ ↦ 0)
        (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b48Offset + b48.length)).toBitVec).load 0 o 8 = x.toBitVec :=
    fun hw ↦ load_loc (hd1 ▸ hw)
  have hl2 : SideMem m0 L w pt tv mem beta mf bf share st2.data.dmem :=
    hl.of_keep (hd1 ▸ keepIv_block hwf2 hm2 hin2 (W0.reg0 hw2) (by decide) (by decide))
  have x2bx : reg st2.data .rbx = loc m0 624 :=
    (hk2.reg hm2 (by simp)).trans ((k1 .rbx (by simp [cs])).trans xbx)
  obtain ⟨-, ht0⟩ := hopt
  rw [ewAt_iff, off_off] at ht0
  have x2_13 : reg st2.data .r13 = (acc0 L w beta pt tv mem share).2.c0.toBitVec :=
    (hm2.regs .r13 _ hr13).trans (ld ht0.1)
  have x2bp : reg st2.data .rbp = (acc0 L w beta pt tv mem share).2.c1.toBitVec := by
    rw [off_off] at ht0
    exact (hm2.regs .rbp _ hrbp).trans (ld ht0.2)
  have hsp2 : rspOf st2.data = loc m0 80 := fr2.frame.sp
  have sa0 : stackArg st2.data 0 = bf.c1.toBitVec := by
    have w88 := wordAt_write hm2 (r := 0) (o := 88) (b := fb m0) (sz := 5520 + 8) rfl
      (by omega) (v := .load 0 144 8) (wr2.find (List.Mem.head _))
    rw [show (Sym.load 0 144 8).eval (frameEnv m0 st1.data 5520 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b48Offset + b48.length)).toBitVec) = bf.c1.toBitVec from ld hl.w144,
      UInt64.ofBitVec_toBitVec] at w88
    exact stackArg_at hsp2 (i := 0) w88
  simp only [PcOk] at hpc2
  refine fpCall h hfc fr2 hpc2 hl2 ((hm2.regs .rdi _ hrdi).trans ((k1 .rbx (by simp [cs])).trans xbx))
    ((hm2.regs .rsi _ hrsi).trans (eval_ptr0 248)) fun m3 fr3 hfp3 hs3 hk3 hcs3 ↦ ?_
  rw [show reg st2.data .rdx = _ from hm2.regs .rdx _ hrdx,
    show reg st2.data .rcx = _ from hm2.regs .rcx _ hrcx,
    show reg st2.data .r8 = _ from hm2.regs .r8 _ hr8,
    show reg st2.data .r9 = _ from hm2.regs .r9 _ hr9, sa0] at hfp3
  simp only [Sym.eval, ld hl.w128, ld hl.w168, ld hl.w160, ld hl.w152, ewArg,
    UInt64.ofBitVec_toBitVec] at hfp3
  have hfp3' : NativeRustcVm.EWsAt m3.dmem (loc m0 624) (fingerprints w mem
      (pt.extract 0 L.logMemory) (pt.extract 0 L.logBytecode) share
      (gpow (2 ^ L.logBytecode - 1)) mf bf).toList := hfp3
  have hle3 : 5520 - 80 + fpClosureStack ≤ NN := le_fp
  have hX3 : ∀ q, (NativeRustcVm.InRange (stackBelow st2.data fpClosureStack) fpClosureStack q ∨
      NativeRustcVm.InRange (loc m0 624) 48 q) → NativeRustcVm.InRange (stackBelow m0 NN) NN q :=
    fun q hq ↦ hq.elim (callee_stack hS hsp2 (by omega) hle3) (loc_stack hS (by omega))
  have hl3 : SideMem m0 L w pt tv mem beta mf bf share m3.dmem :=
    hl2.of_keep (keepIv_call hS hsp2 (by omega) hle3 hs3 (by decide) (by decide) fun j hj hq ↦
      loc_notIn hS (j := j) (by have := inIv_lt (B := 5472) (by decide) hj; omega) (by omega)
        (inIv_apart (o := 624) (n := 48) (by decide) hj) hq)
  have k3 : ∀ r ∈ [Reg64.rbx, .r12, .r14, .r15], reg m3 r = reg st1.data r := fun r hr ↦ by
    have hcs : calleeSaved r = true := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> rfl
    exact (hcs3 r hcs).trans (hk2.reg hm2 hr)
  have x3_13 : reg m3 .r13 = (acc0 L w beta pt tv mem share).2.c0.toBitVec :=
    (hcs3 .r13 rfl).trans x2_13
  have x3bp : reg m3 .rbp = (acc0 L w beta pt tv mem share).2.c1.toBitVec :=
    (hcs3 .rbp rfl).trans x2bp
  have x3bx : reg m3 .rbx = loc m0 624 := (k3 .rbx (by simp)).trans ((k1 .rbx (by simp [cs])).trans xbx)
  have x3_15 : reg m3 .r15 = loc m0 368 :=
    (k3 .r15 (by simp)).trans ((k1 .r15 (by simp [cs])).trans x15)
  have x3_14 : reg m3 .r14 = reg m0 .rsi :=
    (k3 .r14 (by simp)).trans ((k1 .r14 (by simp [cs])).trans x14)
  -- `b49`: the pull side's `accumulate_side`.
  rw [show k + NativeRustcVmX64.Vm.VerifyBusBalance.b48Offset + b48.length = k + NativeRustcVmX64.Vm.VerifyBusBalance.b49Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyBusBalance.b48_next]]
  have hwf4 := wf0 h fr3.frame.kept (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b49Offset + b49.length)).toBitVec)
  refine exec_then (infix_of b49_in_code (by simp [b49]) hp) exit_b49 hwf4 (fun _ _ ↦ rfl)
    (match_fS fr3) fun st4 hm4 hpc4 ↦ ?_
  obtain ⟨hmid4, hw4, wr4, hrdi4, hrsi4, hrdx4, hrcx4, hr84, hr94, hk4⟩ := ok_b49
  have fr4 : St m0 0 st4.data := St.blk fr3 hS hwf4 hm4 hmid4 fun q hq ↦ wr0 hS hw4 (by omega) hq
  have hin4 := writesIn_of_mid hmid4
  have hs4 := blk_same hS hwf4 hm4 hw4 (by omega)
  have hsp4 : rspOf st4.data = loc m0 0 := fr4.frame.sp
  have hl4 : SideMem m0 L w pt tv mem beta mf bf share st4.data.dmem :=
    hl3.of_keep (keepIv_block hwf4 hm4 hin4 (W0.reg0 hw4) (by decide) (by decide))
  have ld4 : ∀ {o : Nat} {x : UInt64}, NativeRustcVm.WordAt m3.dmem (loc m0 o) x →
      (frameEnv m0 m3 5520 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b49Offset + b49.length)).toBitVec).load 0 o 8 =
        x.toBitVec := fun hw ↦ load_loc hw
  have sa : ∀ {i : Nat} {v : Sym}, 8 + 8 * i + 8 ≤ 5520 →
      (∀ t < 8, findWrite 0 (8 + 8 * i + t) (after b49 (fS 88)).mem = some (v, t)) →
      stackArg st4.data i = v.eval (frameEnv m0 m3 5520 [] (fun _ ↦ 0)
        (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b49Offset + b49.length)).toBitVec) := fun hle hw ↦
    (stackArg_loc hsp4 (wordAt_write hm4 (r := 0) (b := fb m0) (sz := 5520 + 8) rfl (by omega) hw)).trans
      rfl
  have e0 : stackArg st4.data 0 = loc m0 3696 :=
    (sa (i := 0) (by omega) (wr4.find (List.Mem.head _))).trans (eval_ptr0 3696)
  have e1 : stackArg st4.data 1 = loc m0 624 :=
    (sa (i := 1) (by omega) (wr4.find (List.Mem.tail _ (List.Mem.head _)))).trans x3bx
  have e2 : stackArg st4.data 2 = 3#64 :=
    sa (i := 2) (by omega) (wr4.find (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  have e3 : stackArg st4.data 3 = loc m0 368 :=
    (sa (i := 3) (by omega) (wr4.find (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.head _)))))).trans x3_15
  have e4 : stackArg st4.data 4 = 16#64 :=
    sa (i := 4) (by omega) (wr4.find (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.head _))))))
  have e5 : stackArg st4.data 5 = beta.c0.toBitVec :=
    (sa (i := 5) (by omega) (wr4.find (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))).trans (ld4 hl3.w184)
  have e6 : stackArg st4.data 6 = beta.c1.toBitVec :=
    (sa (i := 6) (by omega) (wr4.find (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))).trans
      (ld4 hl3.w176)
  have e7 : stackArg st4.data 7 = loc m0 1800 :=
    (sa (i := 7) (by omega) (wr4.find (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.head _)))))))))).trans (ld4 hl3.tail.w104)
  have e8 : stackArg st4.data 8 = pt.size.toUInt64.toBitVec :=
    (sa (i := 8) (by omega) (wr4.find (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.head _))))))))))).trans (ld4 hl3.tail.w120)
  have e9 : stackArg st4.data 9 = (tv.getD 1 0).c0.toBitVec :=
    (sa (i := 9) (by omega) (wr4.find (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.head _)))))))))))).trans (ld4 hl3.w136)
  have e10 : stackArg st4.data 10 = (tv.getD 1 0).c1.toBitVec :=
    (sa (i := 10) (by omega) (wr4.find (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))).trans (ld4 hl3.w320)
  have hnsz : pt.size.toUInt64.toBitVec.toNat = pt.size := by
    rw [UInt64.toNat_toBitVec]
    exact UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)
  have hle : 5520 - 0 + accumulateSideStack ≤ NN := le_acc
  have hfb : formsBytes ≤ busBytes := formsBytes_le
  -- The memory from `d` to `st4`, in the frame and the closure's stack.
  have e01 : NativeRustcVm.SameOutside d.dmem st1.data.dmem (NativeRustcVm.InRange (fb m0) 5520) :=
    fun _ _ ↦ by rw [hd1]
  have hs04 := (e01.trans (hs2.trans hs3)).trans hs4
  have hX4 : ∀ q, ((NativeRustcVm.InRange (fb m0) 5520 q ∨
      (NativeRustcVm.InRange (fb m0) 5520 q ∨
        (NativeRustcVm.InRange (stackBelow st2.data fpClosureStack) fpClosureStack q ∨
          NativeRustcVm.InRange (loc m0 624) 48 q))) ∨ NativeRustcVm.InRange (fb m0) 5520 q) →
      NativeRustcVm.InRange (stackBelow m0 NN) NN q := by
    rintro q ((hq | hq | hq | hq) | hq)
    · exact frame_stack hS hq
    · exact frame_stack hS hq
    · exact hX3 q (.inl hq)
    · exact hX3 q (.inr hq)
    · exact frame_stack hS hq
  have hF4 : FormsAt st4.data.dmem (reg m0 .r8) (acc0 L w beta pt tv mem share).1 :=
    FormsAt.of_same hF (bus_same h hs04 hX4 hfb)
  have hfp4 : NativeRustcVm.EWsAt st4.data.dmem (loc m0 624) (fingerprints w mem
      (pt.extract 0 L.logMemory) (pt.extract 0 L.logBytecode) share
      (gpow (2 ^ L.logBytecode - 1)) mf bf).toList :=
    NativeRustcVm.Tables.EWsAt.of_same hfp3' (keepB hwf4 hm4 hin4 (j := 624) (n := 48) (by omega)
      (miss0 hw4 (by omega))) (by rfl)
  obtain ⟨rows, -, -, -, hbb⟩ := (pre_lay h).rows
  have hpull4 : BusLayoutWAt st4.data.dmem (loc m0 3696) (pullL L) := hl4.pull
  have hcs4 : (pullL L).tables.size = (sideBlocks 1).length := by
    have e := sideOf_eq hbb 1
    rw [show sideOf L 1 = L.pull from rfl] at e
    rw [busLayout_tables_size, ← e]
    simp
  have hlen : (sideBlocks 1).length = 51 := by decide +kernel
  have hap : ∀ {j n : Nat}, j + n ≤ 5520 → NativeRustcVm.Apart (reg m0 .r8) formsBytes (loc m0 j) n :=
    fun hjn ↦ bus_loc h hfb hjn
  simp only [PcOk] at hpc4
  refine accCall h hacc fr4 hpc4 (side := 1) (by omega) (it := .pullBlocks) rfl (by simp)
    (fps := fingerprints w mem (pt.extract 0 L.logMemory) (pt.extract 0 L.logBytecode) share
      (gpow (2 ^ L.logBytecode - 1)) mf bf) (w := w) (pt := pt) (beta := beta)
    (tree := tv.getD 1 0) (o := 192) (ol := 3696) (by omega) (by omega) (by omega) (by omega) hpull4 hcs4 hF4 hfits
    ((hm4.regs .rdi _ hrdi4).trans (eval_ptr0 192))
    ((hm4.regs .rsi _ hrsi4).trans (ld4 hl3.tail.w112))
    (by rw [show reg st4.data .rdx = _ from hm4.regs .rdx _ hrdx4]; rfl)
    (by rw [show reg st4.data .rcx = _ from hm4.regs .rcx _ hrcx4]; rfl)
    (by rw [show reg st4.data .r8 = _ from hm4.regs .r8 _ hr84, hlen]; rfl)
    ((hm4.regs .r9 _ hr94).trans x3_14) e0
    (fun _ ↦ by
      rw [e1, e2]
      exact ⟨cal_localIn h fr4 (j := 624) (n := 48) (by omega) hle (by omega) (by omega),
        hap (n := 48) (by omega),
        loc_apart hS (n' := 48) (by rw [busLayoutBytes_eq]; omega) (by omega) (.inr (by omega))⟩)
    (by
      rw [e3, e4]
      exact ⟨cal_localIn h fr4 (j := 368) (n := 256) (by omega) hle (by omega) (by omega),
        hap (n := 256) (by omega)⟩)
    e7 (by rw [e8, hnsz]; exact psz)
    (by rw [e1, e2]; exact congrArg List.toArray (NativeRustcVm.ewsOf_of_ewsAt hfp4))
    (by rw [e3, e4]; exact (Bus.slice_of_ewsAt hl4.hw (by rw [Array.length_toList, hl4.wsz]; rfl)))
    (by rw [e5, e6]; rfl)
    (by rw [e7, e8]; exact Bus.slice_of_ewsAt hl4.tail.hpt (by rw [Array.length_toList, hnsz]))
    (by rw [e9, e10]; rfl) (by
      intro l hl
      constructor
      · intro _
        rw [e1, e2]
        exact got_apart_frame (pre_got h) hS hl N_ge (by simp only [BitVec.toNat_ofNat]; omega)
      · rw [e3, e4]
        exact got_apart_frame (pre_got h) hS hl N_ge (by simp only [BitVec.toNat_ofNat]; omega))
    fun m5 fr5 hopt5 hF5 hfits5 hs5 hk5 hcs5 ↦ ?_
  have hle5 : 5520 - 0 + accumulateSideStack ≤ NN := le_acc
  have hl5 : SideMem m0 L w pt tv mem beta mf bf share m5.dmem :=
    hl4.of_keep (keepIv_call hS hsp4 (by omega) hle5 hs5 (by decide) (by decide) fun j hj hq ↦ by
      have hj5 := inIv_lt (B := 5472) (by decide) hj
      rcases hq with hq | hq
      · exact loc_notIn hS (j := j) (by omega) (by omega)
          (inIv_apart (o := 192) (n := 24) (by decide) hj) hq
      · exact bus_notLoc h (o := 0) (n := formsBytes) (by decide) (j := j) (l := 1) (by omega)
          (by rw [off_zero]; exact hq) (loc_inR hS (by omega) (by omega) (by omega)))
  have hcs : ∀ r, r ∈ [Reg64.r13, .rbp, .r14] → reg m5 r = reg m3 r := fun r hr ↦ by
    have hc : calleeSaved r = true := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> rfl
    exact (hcs5 r hc).trans (hk4.reg hm4 (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [cs, List.mem_cons, List.not_mem_nil, or_false]
      rcases hr with rfl | rfl | rfl <;> simp))
  have hc5 : Chg m0 d.dmem m5.dmem := by
    refine Chg.of (kept_trans (kept_trans (by rw [← hd1]; exact hm2.kept hwf2) hk3)
      (kept_trans (hm4.kept hwf4) hk5)) (hs04.trans hs5) fun q hq ↦ ?_
    rcases hq with hq | hq | hq | hq
    · exact .inl (hX4 q hq)
    · exact .inl (callee_stack hS hsp4 (by omega) hle5 hq)
    · exact .inl (loc_stack hS (by omega) hq)
    · exact .inr (inRange_mono hq hfb)
  obtain ⟨hts5, hcl5⟩ := hc5.tc h hts hcl
  rw [show k + NativeRustcVmX64.Vm.VerifyBusBalance.b49Offset + b49.length = k + NativeRustcVmX64.Vm.VerifyBusBalance.b50Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyBusBalance.b49_next]]
  exact count_spec hp h hacc hext fr5 hrun hopt5 hF5 hfits5 hl5.count hl5.tail hl5.w312 hl5.w304
    ((hcs .r14 (by simp)).trans x3_14) ((hcs .r13 (by simp)).trans x3_13)
    ((hcs .rbp (by simp)).trans x3bp) hts5 hcl5

end

end NativeRustcVmX64.Bus.VerifyBusBalance
