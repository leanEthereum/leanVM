module

public import NativeRustcVmX64.Bus.VerifyBusBalance.PushPre
public import NativeRustcVmX64.Code.Vm.AccumulateSide.Names
public import NativeRustcVmX64.Code.Vm.BufEW63Extend.Names
public import NativeRustcVmX64.Code.Vm.Kpow.Names
public import NativeRustcVmX64.Code.Vm.VerifyBusBalanceClosure0.Names

/-!
# `verify_bus_balance`'s push side (x86-64)

From `b43` (`k + NativeRustcVmX64.Vm.VerifyBusBalance.b43Offset`), after `computed_bytecode_value`: `b43` writes the closure's environment
and calls `kpow` for `pc_final`; `b44` empties the bus's forms, keeps `pc_final` and the trees'
values, and calls `kpow` for `gpow(0)`; `b45` calls the closure for the push side's
fingerprints; `b46` calls `accumulate_side` on the push side; then the pull side (`push_spec`).
-/

namespace NativeRustcVmX64.Bus.VerifyBusBalance

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.VerifyBusBalance
open NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck NativeRustcVmX64.Bus.Gkr
open NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Bus NativeRustcVm.Layout

public section
variable [Labels] {a : DecArea} {s0 : TState} {L : LayoutW} {m0 : MachineData}

omit [Labels] in
/-- An element of the trees' values by its words. -/
theorem tv_words {d : Mem 64} {tv : Array EW} (h : NativeRustcVm.EWsAt d (loc m0 1744) tv.toList)
    (hs : tv.size = 3) {i : Nat} (hi : i < 3) :
    NativeRustcVm.WordAt d (loc m0 (1744 + 16 * i)) (tv.getD i 0).c0 ∧
      NativeRustcVm.WordAt d (loc m0 (1744 + 16 * i + 8)) (tv.getD i 0).c1 := by
  have := NativeRustcVm.ewsAt_getElem h (i := i) (by rw [Array.length_toList, hs]; exact hi)
  rw [NativeRustcVm.ewAt_iff] at this
  have e : tv.toList[i]'(by rw [Array.length_toList, hs]; exact hi) = tv.getD i 0 := by
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega : i < tv.size)]
  rw [e] at this
  have e1 : loc m0 1744 + BitVec.ofNat 64 (16 * i) = loc m0 (1744 + 16 * i) := by
    show off (off (fb m0) 1744) (16 * i) = _
    rw [off_off]
  have e2 : loc m0 (1744 + 16 * i) + 8#64 = loc m0 (1744 + 16 * i + 8) := by
    show off (off (fb m0) (1744 + 16 * i)) 8 = _
    rw [off_off]
  rw [e1] at this
  rw [e2] at this
  exact this

end

public section
variable [Host] {a : DecArea} {s0 : TState} {L : LayoutW} {m0 : MachineData} {k : Nat}

/-- **The push side** (`b43`, `k + NativeRustcVmX64.Vm.VerifyBusBalance.b43Offset`). -/
theorem push_spec (hp : Placed code k) (h : VerifyBusBalancePre a s0 L m0)
    (hkp : Spec (Labels.label NativeRustcVmX64.Vm.Kpow.entryLabel) KpowPre KpowPost)
    (hfc : Spec (Labels.label NativeRustcVmX64.Vm.VerifyBusBalanceClosure0.entryLabel) FpClosurePre FpClosurePost)
    (hacc : ∀ L rows bl F SL, Spec (Labels.label NativeRustcVmX64.Vm.AccumulateSide.entryLabel)
      (AccumulateSidePre L rows bl F SL) (AccumulateSidePost L rows bl F SL))
    (hext : Spec (Labels.label NativeRustcVmX64.Vm.BufEW63Extend.entryLabel) (BufEWExtendPre 63) (BufEWExtendPost 63))
    {d : MachineData} {w pt tv mem : Array EW} {beta mf bf share : EW} {bp : Array EW}
    {s' : TState} (fr : St m0 104 d)
    (hrun : (verifyBusBalance L).run s0 = some (resultOf L w beta pt tv mem mf bf share bp, s'))
    (pm : PushMem m0 L w pt tv mem beta mf bf share d.dmem)
    (x13 : reg d .r13 = L.logBytecode.toUInt64.toBitVec) (x14 : reg d .r14 = reg m0 .rsi)
    (x15 : reg d .r15 = loc m0 368) (xbp : reg d .rbp = (min L.logMemory pt.size).toUInt64.toBitVec)
    (x12 : reg d .r12 = (min L.logBytecode pt.size).toUInt64.toBitVec)
    (hts : TStateAt d.dmem (reg m0 .rdi) a s')
    (hcl : ClaimsWAt d.dmem (reg m0 .r9) (claimsOf L pt mem mf bf)) :
    Eventually (step1 Host.exe) (Goal a s0 L m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b43Offset)⟩ := by
  have hS := pre_stack h
  have psz := pm.tail.psz
  have lb := (pre_lay h).log_bytecode_le
  have hbus := pre_bus h
  -- `b43`: the closure's environment, `kpow(2^log_bytecode - 1)`.
  have hwf1 := wf0 h fr.frame.kept (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b43Offset + b43.length)).toBitVec)
  refine exec_then (infix_of b43_in_code (by simp [b43]) hp) exit_b43 hwf1 (fun _ _ ↦ rfl)
    (match_fS fr) fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid1, hw1, wr1', hrdi1, hrbx1, hk1⟩ := ok_b43
  have fr1 : St m0 96 st1.data := St.blk fr hS hwf1 hm1 hmid1 fun q hq ↦ wr0 hS hw1 (by omega) hq
  have hin1 := writesIn_of_mid hmid1
  have hs1 := blk_same hS hwf1 hm1 hw1 (by omega)
  have ld1 : ∀ {o : Nat} {x : UInt64}, NativeRustcVm.WordAt d.dmem (loc m0 o) x →
      (frameEnv m0 d 5520 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b43Offset + b43.length)).toBitVec).load 0 o 8 =
        x.toBitVec := fun hw ↦ load_loc hw
  have wW1 : ∀ {o : Nat} {v : Sym}, o + 8 ≤ 5520 →
      (∀ t < 8, findWrite 0 (o + t) (after b43 (fS 104)).mem = some (v, t)) →
      NativeRustcVm.WordAt st1.data.dmem (loc m0 o) (UInt64.ofBitVec (v.eval
        (frameEnv m0 d 5520 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b43Offset + b43.length)).toBitVec))) :=
    fun ho hw ↦ wordAt_write hm1 (r := 0) (b := fb m0) (sz := 5520 + 8) rfl (by omega) hw
  have hpm1 : PushMem m0 L w pt tv mem beta mf bf share st1.data.dmem :=
    pm.of_keep (keepIv_block' hwf1 hm1 hin1 (by decide) (by decide +kernel))
  have x1bx : reg st1.data .rbx = loc m0 1800 :=
    (hm1.regs .rbx _ hrbx1).trans (ld1 pm.tail.w104)
  have k1 : ∀ r ∈ [Reg64.rbp, .r12, .r13, .r14, .r15], reg st1.data r = reg d r :=
    fun r hr ↦ hk1.reg hm1 hr
  have mask : (reg st1.data .rdi).toNat = 2 ^ L.logBytecode - 1 := by
    rw [show reg st1.data .rdi = _ from hm1.regs .rdi _ hrdi1]
    show (UnOp.apply .not .W64 (BinOp.apply .shl .W64 (BitVec.ofNat 64 18446744073709551615)
      (UnOp.apply .trunc .W32 (reg d .r13)))).toNat = _
    have hn : (reg d .r13).toNat = L.logBytecode := by
      rw [x13, UInt64.toNat_toBitVec]
      exact UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)
    rw [mask_toNat (by omega), hn]
  simp only [PcOk] at hpc1
  have hleK : 5520 - 96 + kpowStack ≤ NN := le_kpow
  refine callF h (c := 96) (Nc := kpowStack) (lo := 0) (len := 0) (X := fun _ ↦ False)
    (by omega) hleK (by omega) (fun _ h ↦ h.elim) hkp fr1 hpc1 (cal_stack h fr1 (by omega) hleK)
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun _ h ↦ .inl h, hq.2.2⟩) fun m2 fr2 hq2 hs2 hcs2 ↦ ?_
  obtain ⟨hrax2, -, hsv2⟩ := hq2
  rw [mask] at hrax2
  have hsp1 : rspOf st1.data = loc m0 96 := fr1.frame.sp
  have hX2 : ∀ q, (NativeRustcVm.InRange (stackBelow st1.data kpowStack) kpowStack q ∨ False) →
      NativeRustcVm.InRange (stackBelow m0 NN) NN q :=
    fun q hq ↦ hq.elim (callee_stack hS hsp1 (by omega) hleK) False.elim
  have kc2 : KeepIv pushIv m0 st1.data.dmem m2.dmem :=
    keepIv_call hS hsp1 (by omega) hleK hs2 (by decide) (by decide) fun _ _ h ↦ h
  have hsv2' := hsv2
  have hpm2 : PushMem m0 L w pt tv mem beta mf bf share m2.dmem := hpm1.of_keep kc2
  have rax2 : reg m2 .rax = (gpowK (2 ^ L.logBytecode - 1)).toBitVec := hrax2
  have kE : ∀ {j n : Nat}, 96 ≤ j → j + n ≤ 5528 → Same st1.data.dmem m2.dmem (loc m0 j) n :=
    fun h1 h2 ↦ keepC hS hsp1 (by omega) hleK hs2 h1 h2 fun _ _ h ↦ h
  have x2 : ∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15], reg m2 r = reg st1.data r :=
    fun r hr ↦ hcs2 r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
  -- `b44`: the forms emptied, `kpow(0)`.
  have hwf3 := wfBus h fr2.frame.kept (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b44Offset + b44.length)).toBitVec)
  rw [show k + NativeRustcVmX64.Vm.VerifyBusBalance.b43Offset + b43.length = k + NativeRustcVmX64.Vm.VerifyBusBalance.b44Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyBusBalance.b43_next]]
  refine exec_then (infix_of b44_in_code (by simp [b44]) hp) exit_b44 hwf3 (fun _ _ ↦ rfl)
    (match_bS fr2 hpm2.tail.w112) fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨hmid3, hw3, wr3, wb3, hrdi3, hrbp3, hr12, hr13, hk3⟩ := ok_b44
  have hbusO : ∀ q, NativeRustcVm.InRange (reg m0 .r8) busBytes q → outs m0 q :=
    fun q hq ↦ .inr (.inl hq)
  have fr3 : St m0 96 st3.data := St.blk fr2 hS hwf3 hm3 hmid3
    (fun q hq ↦ wr1 hS hw3 (by omega) (by rw [busBytes_eq]; omega) hbus.2.1 hbusO hq)
  have hin3 := writesIn_of_mid hmid3
  have ld3 : ∀ {o : Nat} {x : UInt64}, NativeRustcVm.WordAt m2.dmem (loc m0 o) x →
      (frameEnv m0 m2 5520 [(reg m0 .r8, busBytes)] (fun _ ↦ 0)
        (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b44Offset + b44.length)).toBitVec).load 0 o 8 = x.toBitVec :=
    fun hw ↦ load_loc hw
  have wW3 : ∀ {o : Nat} {v : Sym}, o + 8 ≤ 5520 →
      (∀ t < 8, findWrite 0 (o + t) (after b44 bS).mem = some (v, t)) →
      NativeRustcVm.WordAt st3.data.dmem (loc m0 o) (UInt64.ofBitVec (v.eval
        (frameEnv m0 m2 5520 [(reg m0 .r8, busBytes)] (fun _ ↦ 0)
          (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b44Offset + b44.length)).toBitVec))) :=
    fun ho hw ↦ wordAt_write hm3 (r := 0) (b := fb m0) (sz := 5520 + 8) rfl (by omega) hw
  have hpm3 : PushMem m0 L w pt tv mem beta mf bf share st3.data.dmem :=
    hpm2.of_keep (keepIv_block' hwf3 hm3 hin3 (by decide) (by decide +kernel))
  have tw0 := tv_words pm.htv pm.tsz (i := 0) (by omega)
  have tw1 := tv_words pm.htv pm.tsz (i := 1) (by omega)
  have tw2 := tv_words pm.htv pm.tsz (i := 2) (by omega)
  have tvk : ∀ {o : Nat} {x : UInt64}, 1744 ≤ o → o + 8 ≤ 1792 →
      NativeRustcVm.WordAt d.dmem (loc m0 o) x → NativeRustcVm.WordAt m2.dmem (loc m0 o) x :=
    fun h1 h2 hw ↦ NativeRustcVm.Layout.WordAt.of_same hw ((keepB hwf1 hm1 hin1 (j := _) (n := 8)
      (by omega) (miss0 hw1 (by omega))).trans (kE (by omega) (by omega))) le_rfl
  have ev3 : ∀ {v : Sym} {x : UInt64}, v.eval (frameEnv m0 m2 5520 [(reg m0 .r8, busBytes)]
      (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b44Offset + b44.length)).toBitVec) = x.toBitVec →
      UInt64.ofBitVec (v.eval (frameEnv m0 m2 5520 [(reg m0 .r8, busBytes)]
      (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b44Offset + b44.length)).toBitVec)) = x :=
    fun hv ↦ by rw [hv, UInt64.ofBitVec_toBitVec]
  have w128 : NativeRustcVm.WordAt st3.data.dmem (loc m0 128) (gpowK (2 ^ L.logBytecode - 1)) :=
    ev3 (v := .reg .rax) rax2 ▸ wW3 (o := 128) (by omega) (wr3.find (List.Mem.head _))
  have w136 : NativeRustcVm.WordAt st3.data.dmem (loc m0 136) (tv.getD 1 0).c0 :=
    ev3 (v := .load 0 1760 8) (ld3 (tvk (by omega) (by omega) tw1.1)) ▸
      wW3 (o := 136) (by omega) (wr3.find (List.Mem.tail _ (List.Mem.head _)))
  have w304 : NativeRustcVm.WordAt st3.data.dmem (loc m0 304) (tv.getD 2 0).c1 :=
    ev3 (v := .load 0 1784 8) (ld3 (tvk (by omega) (by omega) tw2.2)) ▸
      wW3 (o := 304) (by omega) (wr3.find (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  have w312 : NativeRustcVm.WordAt st3.data.dmem (loc m0 312) (tv.getD 2 0).c0 :=
    ev3 (v := .load 0 1776 8) (ld3 (tvk (by omega) (by omega) tw2.1)) ▸
      wW3 (o := 312) (by omega) (wr3.find (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.head _)))))
  have w320 : NativeRustcVm.WordAt st3.data.dmem (loc m0 320) (tv.getD 1 0).c1 :=
    ev3 (v := .load 0 1768 8) (ld3 (tvk (by omega) (by omega) tw1.2)) ▸
      wW3 (o := 320) (by omega) (wr3.find (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.head _))))))
  have x3_13 : reg st3.data .r13 = (tv.getD 0 0).c0.toBitVec :=
    (hm3.regs .r13 _ hr13).trans (ld3 (tvk (by omega) (by omega) tw0.1))
  have x3_12 : reg st3.data .r12 = (tv.getD 0 0).c1.toBitVec :=
    (hm3.regs .r12 _ hr12).trans (ld3 (tvk (by omega) (by omega) tw0.2))
  have x3bp : reg st3.data .rbp = reg m0 .r8 := (hm3.regs .rbp _ hrbp3).trans (ld3 hpm2.tail.w112)
  have k3 : ∀ r ∈ [Reg64.rbx, .r14, .r15], reg st3.data r = reg m2 r := fun r hr ↦ hk3.reg hm3 hr
  have zw : ∀ j < 18, NativeRustcVm.WordAt st3.data.dmem (off (reg m0 .r8) (5928 * j)) 0 :=
    fun j hj ↦ wordAt_write hm3 (r := 1) (b := reg m0 .r8) (sz := busBytes) rfl
      (by rw [busBytes_eq]; omega) (v := .lit 0)
      (wb3.find (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))
  -- `kpow(0)`.
  simp only [PcOk] at hpc3
  have hsp3 : rspOf st3.data = loc m0 96 := fr3.frame.sp
  refine callF h (c := 96) (Nc := kpowStack) (lo := 0) (len := 0) (X := fun _ ↦ False)
    (by omega) hleK (by omega) (fun _ h ↦ h.elim) hkp fr3 hpc3 (cal_stack h fr3 (by omega) hleK)
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun _ h ↦ .inl h, hq.2.2⟩)
    fun m4 fr4 hq4 hs4 hcs4 ↦ ?_
  obtain ⟨hrax4, -, hsv4⟩ := hq4
  have rax4 : reg m4 .rax = (gpowK 0).toBitVec := by
    rw [hrax4, show reg st3.data .rdi = _ from hm3.regs .rdi _ hrdi3]; rfl
  have kE4 : ∀ {j n : Nat}, 96 ≤ j → j + n ≤ 5528 → Same st3.data.dmem m4.dmem (loc m0 j) n :=
    fun h1 h2 ↦ keepC hS hsp3 (by omega) hleK hs4 h1 h2 fun _ _ h ↦ h
  have hpm4 : PushMem m0 L w pt tv mem beta mf bf share m4.dmem :=
    hpm3.of_keep (keepIv_call hS hsp3 (by omega) hleK hs4 (by decide) (by decide) fun _ _ h ↦ h)
  have k4 : ∀ {o : Nat} {x : UInt64}, 96 ≤ o → o + 8 ≤ 5520 →
      NativeRustcVm.WordAt st3.data.dmem (loc m0 o) x → NativeRustcVm.WordAt m4.dmem (loc m0 o) x :=
    fun h1 h2 hw ↦ NativeRustcVm.Layout.WordAt.of_same hw (kE4 h1 (by omega)) le_rfl
  have hm44 : ∀ w ∈ (after b44 bS).mem, w.r = 0 → w.off + w.n ≤ 248 ∨ 304 ≤ w.off := by
    have hd : ((after b44 bS).mem.all fun w ↦ w.r != 0 || decide (w.off + w.n ≤ 248) ||
        decide (304 ≤ w.off)) = true := by decide +kernel
    intro w hw hr
    have := List.all_eq_true.mp hd w hw
    simp only [hr, bne_self_eq_false, Bool.false_or, Bool.or_eq_true, decide_eq_true_eq] at this
    exact this
  have kenv : ∀ {o : Nat} {x : UInt64}, 248 ≤ o → o + 8 ≤ 304 →
      NativeRustcVm.WordAt st1.data.dmem (loc m0 o) x → NativeRustcVm.WordAt m4.dmem (loc m0 o) x :=
    fun h1 h2 hw ↦ NativeRustcVm.Layout.WordAt.of_same hw ((kE (by omega) (by omega)).trans
      ((keepB hwf3 hm3 hin3 (j := _) (n := 8) (by omega) fun w hw hr ↦ by
        have := hm44 w hw hr; omega).trans (kE4 (by omega) (by omega)))) le_rfl
  have ev1 : ∀ {v : Sym} {x : BitVec 64}, v.eval (frameEnv m0 d 5520 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b43Offset + b43.length)).toBitVec) = x →
      UInt64.ofBitVec (v.eval (frameEnv m0 d 5520 [] (fun _ ↦ 0)
        (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b43Offset + b43.length)).toBitVec)) = UInt64.ofBitVec x :=
    fun hv ↦ by rw [hv]
  have hl4 : SideMem m0 L w pt tv mem beta mf bf share m4.dmem := by
    refine ⟨hpm4.tail, hpm4.pull, hpm4.count, hpm4.hw, hpm4.wsz, hpm4.hmem, hpm4.msz,
      k4 (by omega) (by omega) w128, k4 (by omega) (by omega) w136,
      k4 (by omega) (by omega) w320, k4 (by omega) (by omega) w312,
      k4 (by omega) (by omega) w304, hpm4.w168, hpm4.w160, hpm4.w152, hpm4.w144, hpm4.w184,
      hpm4.w176, hpm4.share, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact kenv (by omega) (by omega)
        (ev1 (v := .reg .r15) x15 ▸ wW1 (o := 248) (by omega) (wr1'.find (List.Mem.head _)))
    · exact kenv (by omega) (by omega)
        (ev1 (v := .ptr 0 216) (eval_ptr0 216) ▸ wW1 (o := 256) (by omega)
          (wr1'.find (List.Mem.tail _ (List.Mem.head _))))
    · exact kenv (by omega) (by omega)
        (ev1 (v := .load 0 104 8) (ld1 pm.tail.w104) ▸ wW1 (o := 264) (by omega)
          (wr1'.find (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
    · have := ev1 (v := .reg .rbp) xbp ▸ wW1 (o := 272) (by omega)
        (wr1'.find (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
      rw [UInt64.ofBitVec_toBitVec] at this
      exact kenv (by omega) (by omega) this
    · exact kenv (by omega) (by omega)
        (ev1 (v := .load 0 104 8) (ld1 pm.tail.w104) ▸ wW1 (o := 280) (by omega)
          (wr1'.find (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
            (List.Mem.head _)))))))
    · have := ev1 (v := .reg .r12) x12 ▸ wW1 (o := 288) (by omega)
        (wr1'.find (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
          (List.Mem.tail _ (List.Mem.head _)))))))
      rw [UInt64.ofBitVec_toBitVec] at this
      exact kenv (by omega) (by omega) this
    · exact kenv (by omega) (by omega)
        (ev1 (v := .ptr 0 352) (eval_ptr0 352) ▸ wW1 (o := 296) (by omega)
          (wr1'.find (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
            (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))
  have x4 : ∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15], reg m4 r = reg st3.data r :=
    fun r hr ↦ hcs4 r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
  have x4bx : reg m4 .rbx = loc m0 1800 :=
    (x4 .rbx (by simp)).trans ((k3 .rbx (by simp)).trans ((x2 .rbx (by simp)).trans x1bx))
  have x4_14 : reg m4 .r14 = reg m0 .rsi := (x4 .r14 (by simp)).trans ((k3 .r14 (by simp)).trans
    ((x2 .r14 (by simp)).trans ((k1 .r14 (by simp)).trans x14)))
  have x4_15 : reg m4 .r15 = loc m0 368 := (x4 .r15 (by simp)).trans ((k3 .r15 (by simp)).trans
    ((x2 .r15 (by simp)).trans ((k1 .r15 (by simp)).trans x15)))
  have x4bp : reg m4 .rbp = reg m0 .r8 := (x4 .rbp (by simp)).trans x3bp
  have x4_13 : reg m4 .r13 = (tv.getD 0 0).c0.toBitVec := (x4 .r13 (by simp)).trans x3_13
  have x4_12 : reg m4 .r12 = (tv.getD 0 0).c1.toBitVec := (x4 .r12 (by simp)).trans x3_12
  -- `b45`: the closure for the push side's fingerprints.
  rw [show k + NativeRustcVmX64.Vm.VerifyBusBalance.b44Offset + b44.length = k + NativeRustcVmX64.Vm.VerifyBusBalance.b45Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyBusBalance.b44_next]]
  have hwf5 := wf0 h fr4.frame.kept (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b45Offset + b45.length)).toBitVec)
  refine exec_then (infix_of b45_in_code (by simp [b45]) hp) exit_b45 hwf5 (fun _ _ ↦ rfl)
    (match_fS fr4) fun st5 hm5 hpc5 ↦ ?_
  obtain ⟨hmid5, hw5, wr5, hrdi5, hrsi5, hrdx5, hrcx5, hr85, hr95, hk5⟩ := ok_b45
  have fr5 : St m0 80 st5.data := St.blk fr4 hS hwf5 hm5 hmid5 fun q hq ↦ wr0 hS hw5 (by omega) hq
  have hin5 := writesIn_of_mid hmid5
  have hs5 := blk_same hS hwf5 hm5 hw5 (by omega)
  have hsp5 : rspOf st5.data = loc m0 80 := fr5.frame.sp
  have hl5 : SideMem m0 L w pt tv mem beta mf bf share st5.data.dmem :=
    hl4.of_keep (keepIv_block hwf5 hm5 hin5 (W0.reg0 hw5) (by decide) (by decide))
  have hpm5 : PushMem m0 L w pt tv mem beta mf bf share st5.data.dmem :=
    hpm4.of_keep (keepIv_block hwf5 hm5 hin5 (W0.reg0 hw5) (by decide) (by decide))
  have k5 : ∀ r ∈ cs, reg st5.data r = reg m4 r := fun r hr ↦ hk5.reg hm5 hr
  have sa0 : stackArg st5.data 0 = 0#64 := by
    have w88 := wordAt_write hm5 (r := 0) (o := 88) (b := fb m0) (sz := 5520 + 8) rfl
      (by omega) (v := .lit 0) (wr5.find (List.Mem.head _))
    exact stackArg_at hsp5 (i := 0) w88
  simp only [PcOk] at hpc5
  refine fpCall h hfc fr5 hpc5 hl5 ((hm5.regs .rdi _ hrdi5).trans (eval_ptr0 624))
    ((hm5.regs .rsi _ hrsi5).trans (eval_ptr0 248)) fun m6 fr6 hfp6 hs6 hk6 hcs6 ↦ ?_
  rw [show reg st5.data .rdx = _ from hm5.regs .rdx _ hrdx5,
    show reg st5.data .rcx = _ from hm5.regs .rcx _ hrcx5,
    show reg st5.data .r8 = _ from hm5.regs .r8 _ hr85,
    show reg st5.data .r9 = _ from hm5.regs .r9 _ hr95, sa0] at hfp6
  have hfp6' : NativeRustcVm.EWsAt m6.dmem (loc m0 624) (fingerprints w mem
      (pt.extract 0 L.logMemory) (pt.extract 0 L.logBytecode) share (gpow 0) 1 1).toList := by
    have e : (Sym.reg .rax).eval (frameEnv m0 m4 5520 [] (fun _ ↦ 0)
        (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b45Offset + b45.length)).toBitVec) = (gpowK 0).toBitVec := rax4
    rw [e] at hfp6
    exact hfp6
  have hle6 : 5520 - 80 + fpClosureStack ≤ NN := le_fp
  have kc6 : ∀ {ivs : List (Nat × Nat)}, ivs.all (fun p ↦ decide (p.2 ≤ 5520)) = true →
      ivs.all (fun p ↦ decide (80 ≤ p.1)) = true →
      ivs.all (fun p ↦ decide (p.2 ≤ 624) || decide (672 ≤ p.1)) = true →
      KeepIv ivs m0 st5.data.dmem m6.dmem := fun h1 h2 h3 ↦
    keepIv_call hS hsp5 (by omega) hle6 hs6 h1 h2 fun j hj hq ↦
      loc_notIn hS (j := j) (by have := inIv_lt h1 hj; omega) (by omega)
        (inIv_apart (o := 624) (n := 48) h3 hj) hq
  have hl6 : SideMem m0 L w pt tv mem beta mf bf share m6.dmem :=
    hl5.of_keep (kc6 (by decide) (by decide) (by decide))
  have hpm6 : PushMem m0 L w pt tv mem beta mf bf share m6.dmem :=
    hpm5.of_keep (kc6 (by decide) (by decide) (by decide))
  have x6 : ∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15], reg m6 r = reg m4 r := fun r hr ↦ by
    have hc : calleeSaved r = true ∧ r ∈ cs := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl, by simp [cs]⟩
    exact (hcs6 r hc.1).trans (k5 r hc.2)
  -- `b46`: the push side's `accumulate_side`.
  rw [show k + NativeRustcVmX64.Vm.VerifyBusBalance.b45Offset + b45.length = k + NativeRustcVmX64.Vm.VerifyBusBalance.b46Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyBusBalance.b45_next]]
  have hwf7 := wf0 h fr6.frame.kept (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b46Offset + b46.length)).toBitVec)
  refine exec_then (infix_of b46_in_code (by simp [b46]) hp) exit_b46 hwf7 (fun _ _ ↦ rfl)
    (match_fS fr6) fun st7 hm7 hpc7 ↦ ?_
  obtain ⟨hmid7, hw7, wr7, hrdi7, hrsi7, hrdx7, hrcx7, hr87, hr97, hrbx7, hk7⟩ := ok_b46
  have fr7 : St m0 0 st7.data := St.blk fr6 hS hwf7 hm7 hmid7 fun q hq ↦ wr0 hS hw7 (by omega) hq
  have hin7 := writesIn_of_mid hmid7
  have hs7 := blk_same hS hwf7 hm7 hw7 (by omega)
  have hsp7 : rspOf st7.data = loc m0 0 := fr7.frame.sp
  have hl7 : SideMem m0 L w pt tv mem beta mf bf share st7.data.dmem :=
    hl6.of_keep (keepIv_block hwf7 hm7 hin7 (W0.reg0 hw7) (by decide) (by decide))
  have hpm7 : PushMem m0 L w pt tv mem beta mf bf share st7.data.dmem :=
    hpm6.of_keep (keepIv_block hwf7 hm7 hin7 (W0.reg0 hw7) (by decide) (by decide))
  have ld7 : ∀ {o : Nat} {x : UInt64}, NativeRustcVm.WordAt m6.dmem (loc m0 o) x →
      (frameEnv m0 m6 5520 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b46Offset + b46.length)).toBitVec).load 0 o 8 =
        x.toBitVec := fun hw ↦ load_loc hw
  have sa : ∀ {i : Nat} {v : Sym}, 8 + 8 * i + 8 ≤ 5520 →
      (∀ t < 8, findWrite 0 (8 + 8 * i + t) (after b46 (fS 88)).mem = some (v, t)) →
      stackArg st7.data i = v.eval (frameEnv m0 m6 5520 [] (fun _ ↦ 0)
        (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b46Offset + b46.length)).toBitVec) := fun hle hw ↦
    (stackArg_loc hsp7 (wordAt_write hm7 (r := 0) (b := fb m0) (sz := 5520 + 8) rfl (by omega)
      hw)).trans rfl
  have rg : ∀ {r : Reg64}, (Sym.reg r).eval (frameEnv m0 m6 5520 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b46Offset + b46.length)).toBitVec) = reg m6 r := rfl
  have e0 : stackArg st7.data 0 = loc m0 2808 :=
    (sa (i := 0) (by omega) (wr7.find (List.Mem.head _))).trans (eval_ptr0 2808)
  have e1 : stackArg st7.data 1 = loc m0 624 :=
    (sa (i := 1) (by omega) (wr7.find (List.Mem.tail _ (List.Mem.head _)))).trans (eval_ptr0 624)
  have e2 : stackArg st7.data 2 = 3#64 :=
    sa (i := 2) (by omega) (wr7.find (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  have e3 : stackArg st7.data 3 = loc m0 368 :=
    (sa (i := 3) (by omega) (wr7.find (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.head _)))))).trans (rg.trans ((x6 .r15 (by simp)).trans x4_15))
  have e4 : stackArg st7.data 4 = 16#64 :=
    sa (i := 4) (by omega) (wr7.find (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.head _))))))
  have e5 : stackArg st7.data 5 = beta.c0.toBitVec :=
    (sa (i := 5) (by omega) (wr7.find (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))).trans (ld7 hl6.w184)
  have e6 : stackArg st7.data 6 = beta.c1.toBitVec :=
    (sa (i := 6) (by omega) (wr7.find (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))).trans
      (ld7 hl6.w176)
  have e7 : stackArg st7.data 7 = loc m0 1800 :=
    (sa (i := 7) (by omega) (wr7.find (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.head _)))))))))).trans (rg.trans ((x6 .rbx (by simp)).trans x4bx))
  have e8 : stackArg st7.data 8 = pt.size.toUInt64.toBitVec :=
    (sa (i := 8) (by omega) (wr7.find (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.head _))))))))))).trans (ld7 hl6.tail.w120)
  have e9 : stackArg st7.data 9 = (tv.getD 0 0).c0.toBitVec :=
    (sa (i := 9) (by omega) (wr7.find (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.head _)))))))))))).trans
      (rg.trans ((x6 .r13 (by simp)).trans x4_13))
  have e10 : stackArg st7.data 10 = (tv.getD 0 0).c1.toBitVec :=
    (sa (i := 10) (by omega) (wr7.find (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))).trans
      (rg.trans ((x6 .r12 (by simp)).trans x4_12))
  have hnsz : pt.size.toUInt64.toBitVec.toNat = pt.size := by
    rw [UInt64.toNat_toBitVec]
    exact UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)
  have hle : 5520 - 0 + accumulateSideStack ≤ NN := le_acc
  have hfb : formsBytes ≤ busBytes := formsBytes_le
  have hfp7 : NativeRustcVm.EWsAt st7.data.dmem (loc m0 624) (fingerprints w mem
      (pt.extract 0 L.logMemory) (pt.extract 0 L.logBytecode) share (gpow 0) 1 1).toList :=
    NativeRustcVm.Tables.EWsAt.of_same hfp6' (keepB hwf7 hm7 hin7 (j := 624) (n := 48) (by omega)
      (miss0 hw7 (by omega))) (by rfl)
  -- The forms emptied, from `st3` to `st7`.
  have hsp4 : rspOf st3.data = loc m0 96 := hsp3
  have hF7 : FormsAt st7.data.dmem (reg m0 .r8) forms0 := by
    refine FormsAt.of_same (forms0_at zw) ?_
    refine ((bus_same h hs4 (fun q hq ↦ hq.elim (callee_stack hS hsp3 (by omega) hleK) False.elim)
      hfb).trans (bus_same h hs5 (fun q ↦ frame_stack hS) hfb)).trans ?_
    exact (bus_same h hs6 (fun q hq ↦ hq.elim (callee_stack hS hsp5 (by omega) hle6)
      (loc_stack hS (by omega))) hfb).trans (bus_same h hs7 (fun q ↦ frame_stack hS) hfb)
  obtain ⟨rows, -, -, -, hbb⟩ := (pre_lay h).rows
  have hcs7 : (pushL L).tables.size = (sideBlocks 0).length := by
    have e := sideOf_eq hbb 0
    rw [show sideOf L 0 = L.push from rfl] at e
    rw [busLayout_tables_size, ← e]
    simp
  have hlen : (sideBlocks 0).length = 51 := by decide +kernel
  have hap : ∀ {j n : Nat}, j + n ≤ 5520 → NativeRustcVm.Apart (reg m0 .r8) formsBytes (loc m0 j) n :=
    fun hjn ↦ bus_loc h hfb hjn
  simp only [PcOk] at hpc7
  refine accCall h hacc fr7 hpc7 (side := 0) (by omega) (it := .pushBlocks) rfl (by simp)
    (fps := fingerprints w mem (pt.extract 0 L.logMemory) (pt.extract 0 L.logBytecode) share
      (gpow 0) 1 1) (w := w) (pt := pt) (beta := beta) (tree := tv.getD 0 0) (o := 192)
    (ol := 2808) (by omega) (by omega) (by omega) (by omega) hpm7.push hcs7 hF7 fits_forms0
    ((hm7.regs .rdi _ hrdi7).trans (eval_ptr0 192))
    ((hm7.regs .rsi _ hrsi7).trans ((x6 .rbp (by simp)).trans x4bp))
    (by rw [show reg st7.data .rdx = _ from hm7.regs .rdx _ hrdx7]; rfl)
    (by rw [show reg st7.data .rcx = _ from hm7.regs .rcx _ hrcx7]; rfl)
    (by rw [show reg st7.data .r8 = _ from hm7.regs .r8 _ hr87, hlen]; rfl)
    ((hm7.regs .r9 _ hr97).trans ((x6 .r14 (by simp)).trans x4_14)) e0
    (fun _ ↦ by
      rw [e1, e2]
      exact ⟨cal_localIn h fr7 (j := 624) (n := 48) (by omega) hle (by omega) (by omega),
        hap (n := 48) (by omega),
        loc_apart hS (n' := 48) (by rw [busLayoutBytes_eq]; omega) (by omega) (.inr (by omega))⟩)
    (by
      rw [e3, e4]
      exact ⟨cal_localIn h fr7 (j := 368) (n := 256) (by omega) hle (by omega) (by omega),
        hap (n := 256) (by omega)⟩)
    e7 (by rw [e8, hnsz]; exact psz)
    (by rw [e1, e2]; exact congrArg List.toArray (NativeRustcVm.ewsOf_of_ewsAt hfp7))
    (by rw [e3, e4]; exact (Bus.slice_of_ewsAt hl7.hw (by rw [Array.length_toList, hl7.wsz]; rfl)))
    (by rw [e5, e6]; rfl)
    (by rw [e7, e8]; exact Bus.slice_of_ewsAt hl7.tail.hpt (by rw [Array.length_toList, hnsz]))
    (by rw [e9, e10]; rfl) (by
      intro l hl
      constructor
      · intro _
        rw [e1, e2]
        exact got_apart_frame (pre_got h) hS hl N_ge (by simp only [BitVec.toNat_ofNat]; omega)
      · rw [e3, e4]
        exact got_apart_frame (pre_got h) hS hl N_ge (by simp only [BitVec.toNat_ofNat]; omega))
    fun m8 fr8 hopt8 hF8 hfits8 hs8 hk8 hcs8 ↦ ?_
  have hl8 : SideMem m0 L w pt tv mem beta mf bf share m8.dmem :=
    hl7.of_keep (keepIv_call hS hsp7 (by omega) hle hs8 (by decide) (by decide) fun j hj hq ↦ by
      have hj5 := inIv_lt (B := 5472) (by decide) hj
      rcases hq with hq | hq
      · exact loc_notIn hS (j := j) (by omega) (by omega)
          (inIv_apart (o := 192) (n := 24) (by decide) hj) hq
      · exact bus_notLoc h (o := 0) (n := formsBytes) (by decide) (j := j) (l := 1) (by omega)
          (by rw [off_zero]; exact hq) (loc_inR hS (by omega) (by omega) (by omega)))
  have x8 : ∀ r ∈ [Reg64.rbx, .r14, .r15], reg m8 r = reg st7.data r := fun r hr ↦ hcs8 r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> rfl)
  have hs3' : NativeRustcVm.SameOutside m2.dmem st3.data.dmem (fun q ↦
      NativeRustcVm.InRange (fb m0) 5520 q ∨ NativeRustcVm.InRange (reg m0 .r8) busBytes q) :=
    fun q hq ↦ hm3.get?_mem0 hwf3 fun hW ↦ hq (written_fb1 hS N_ge (fun w hw ↦
      (hw3 w hw).elim (fun h ↦ .inl ⟨h.1, by omega⟩) fun h ↦ .inr ⟨h.1, by rw [busBytes_eq]; omega⟩)
      hbus.2.1 hW)
  have c1 : Chg m0 d.dmem st1.data.dmem :=
    Chg.of (hm1.kept hwf1) hs1 fun q hq ↦ .inl (frame_stack hS hq)
  have c2 : Chg m0 st1.data.dmem m2.dmem := Chg.of hsv2.2 hs2 fun q hq ↦
    hq.elim (fun h ↦ .inl (callee_stack hS hsp1 (by omega) hleK h)) False.elim
  have c3 : Chg m0 m2.dmem st3.data.dmem := Chg.of (hm3.kept hwf3) hs3' fun q hq ↦
    hq.elim (fun h ↦ .inl (frame_stack hS h)) .inr
  have c4 : Chg m0 st3.data.dmem m4.dmem := Chg.of hsv4.2 hs4 fun q hq ↦
    hq.elim (fun h ↦ .inl (callee_stack hS hsp3 (by omega) hleK h)) False.elim
  have c5 : Chg m0 m4.dmem st5.data.dmem :=
    Chg.of (hm5.kept hwf5) hs5 fun q hq ↦ .inl (frame_stack hS hq)
  have c6 : Chg m0 st5.data.dmem m6.dmem := Chg.of hk6 hs6 fun q hq ↦
    hq.elim (fun h ↦ .inl (callee_stack hS hsp5 (by omega) hle6 h))
      fun h ↦ .inl (loc_stack hS (by omega) h)
  have c7 : Chg m0 m6.dmem st7.data.dmem :=
    Chg.of (hm7.kept hwf7) hs7 fun q hq ↦ .inl (frame_stack hS hq)
  have c8 : Chg m0 st7.data.dmem m8.dmem := Chg.of hk8 hs8 fun q hq ↦ by
    rcases hq with hq | hq | hq
    · exact .inl (callee_stack hS hsp7 (by omega) hle hq)
    · exact .inl (loc_stack hS (by omega) hq)
    · exact .inr (inRange_mono hq hfb)
  have hc8 := ((((((c1.trans c2).trans c3).trans c4).trans c5).trans c6).trans c7).trans c8
  obtain ⟨hts8, hcl8⟩ := hc8.tc h hts hcl
  rw [show k + NativeRustcVmX64.Vm.VerifyBusBalance.b46Offset + b46.length = k + NativeRustcVmX64.Vm.VerifyBusBalance.b47Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyBusBalance.b46_next]]
  exact pull_spec hp h hfc hacc hext fr8 hrun hl8 hopt8 hF8 hfits8
    ((x8 .r14 (by simp)).trans ((hk7.reg hm7 (by simp)).trans ((x6 .r14 (by simp)).trans x4_14)))
    ((x8 .r15 (by simp)).trans ((hk7.reg hm7 (by simp)).trans ((x6 .r15 (by simp)).trans x4_15)))
    ((x8 .rbx (by simp)).trans ((hm7.regs .rbx _ hrbx7).trans (eval_ptr0 624))) hts8 hcl8

end

end NativeRustcVmX64.Bus.VerifyBusBalance
