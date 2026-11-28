module

public import NativeRustcVmX64.Bus.VerifyBusBalance.Push
public import NativeRustcVmX64.Code.Vm.AccumulateSide.Names
public import NativeRustcVmX64.Code.Vm.BufEW63Extend.Names
public import NativeRustcVmX64.Code.Vm.BytecodeShare.Names
public import NativeRustcVmX64.Code.Vm.ComputedBytecodeValue.Names
public import NativeRustcVmX64.Code.Vm.Kpow.Names
public import NativeRustcVmX64.Code.Vm.VerifyBusBalanceClosure0.Names

/-!
# `verify_bus_balance`'s bytecode share (x86-64)

From `b38` (`k + NativeRustcVmX64.Vm.VerifyBusBalance.b38Offset`), after the claims and the bytecode point's zeroing: `b38` calls
`bytecode_share`; `b39` checks its tag; `b40` keeps the share at `352` and checks the point's
length (`< 68`); `b41` calls `computed_bytecode_value`; `b42` checks it; then the push side
(`share_spec`).
-/

namespace NativeRustcVmX64.Bus.VerifyBusBalance

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.VerifyBusBalance
open NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck NativeRustcVmX64.Bus.Gkr
open NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Bus NativeRustcVm.Layout

public section

/-- **The locals at `b38`**: `PushMem` but the share. -/
structure ShareMem (m0 : MachineData) (L : LayoutW) (w pt tv mem : Array EW)
    (beta mf bf : EW) (d : Mem 64) : Prop where
  tail : TailMem m0 pt d
  push : BusLayoutWAt d (loc m0 2808) (pushL L)
  pull : BusLayoutWAt d (loc m0 3696) (pullL L)
  count : BusLayoutWAt d (loc m0 4584) (countL L)
  hw : NativeRustcVm.EWsAt d (loc m0 368) w.toList
  wsz : w.size = 16
  hmem : NativeRustcVm.EWsAt d (loc m0 216) mem.toList
  msz : mem.size = 2
  htv : NativeRustcVm.EWsAt d (loc m0 1744) tv.toList
  tsz : tv.size = 3
  w168 : NativeRustcVm.WordAt d (loc m0 168) mf.c0
  w160 : NativeRustcVm.WordAt d (loc m0 160) mf.c1
  w152 : NativeRustcVm.WordAt d (loc m0 152) bf.c0
  w144 : NativeRustcVm.WordAt d (loc m0 144) bf.c1
  w184 : NativeRustcVm.WordAt d (loc m0 184) beta.c0
  w176 : NativeRustcVm.WordAt d (loc m0 176) beta.c1
  w128 : NativeRustcVm.WordAt d (loc m0 128) (UInt64.ofBitVec (reg m0 .rdx))
  w136 : NativeRustcVm.WordAt d (loc m0 136) (UInt64.ofBitVec (reg m0 .rcx))

/-- The locals' intervals at `b38`. -/
abbrev shareIv : List (Nat × Nat) := [(104, 192), (216, 248), (368, 624), (1744, 5472)]

theorem ShareMem.of_keep {m0 : MachineData} {L : LayoutW} {w pt tv mem : Array EW}
    {beta mf bf : EW} {d d' : Mem 64} (h : ShareMem m0 L w pt tv mem beta mf bf d)
    (hk : KeepIv shareIv m0 d d') : ShareMem m0 L w pt tv mem beta mf bf d' := by
  have psz := h.tail.psz
  have i1 : (104, 192) ∈ shareIv := by simp
  have i3 : (216, 248) ∈ shareIv := by simp
  have i4 : (368, 624) ∈ shareIv := by simp
  have i5 : (1744, 5472) ∈ shareIv := by simp
  have w2 : ∀ {o : Nat} {x : UInt64}, 104 ≤ o → o + 8 ≤ 192 →
      NativeRustcVm.WordAt d (loc m0 o) x → NativeRustcVm.WordAt d' (loc m0 o) x :=
    fun h1 h2 hw ↦ NativeRustcVm.Layout.WordAt.of_same hw (hk.sameIn i1 h1 h2) le_rfl
  have hk4 : KeepIv tailIv m0 d d' := fun j ⟨p, hp, h1, h2⟩ ↦ hk j (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact ⟨_, i1, by simp only at h1 h2 ⊢; omega, by simp only at h1 h2 ⊢; omega⟩
    · exact ⟨_, i5, by simp only at h1 h2 ⊢; omega, by simp only at h1 h2 ⊢; omega⟩)
  have hb : busLayoutBytes = 888 := busLayoutBytes_eq
  exact ⟨h.tail.of_keep hk4,
    BusLayoutWAt.of_same h.push (hk.sameIn i5 (by omega) (by omega)),
    BusLayoutWAt.of_same h.pull (hk.sameIn i5 (by omega) (by omega)),
    BusLayoutWAt.of_same h.count (hk.sameIn i5 (by omega) (by omega)),
    NativeRustcVm.Tables.EWsAt.of_same h.hw (hk.sameIn i4 (n := 256) (by omega) (by omega))
      (by rw [Array.length_toList, h.wsz]), h.wsz,
    NativeRustcVm.Tables.EWsAt.of_same h.hmem (hk.sameIn i3 (n := 32) (by omega) (by omega))
      (by rw [Array.length_toList, h.msz]), h.msz,
    NativeRustcVm.Tables.EWsAt.of_same h.htv (hk.sameIn i5 (n := 48) (by omega) (by omega))
      (by rw [Array.length_toList, h.tsz]), h.tsz,
    w2 (by omega) (by omega) h.w168, w2 (by omega) (by omega) h.w160,
    w2 (by omega) (by omega) h.w152, w2 (by omega) (by omega) h.w144,
    w2 (by omega) (by omega) h.w184, w2 (by omega) (by omega) h.w176,
    w2 (by omega) (by omega) h.w128, w2 (by omega) (by omega) h.w136⟩

end

public section
variable [Labels] {a : DecArea} {s0 : TState} {L : LayoutW} {m0 : MachineData}

/-- A `None` tag's low half is not `1`. -/
theorem tag32_true {d : MachineData} {rest : List (BitVec 64 × Nat)} {ret : BitVec 64} {o : Nat}
    (hw : NativeRustcVm.WordAt d.dmem (loc m0 o) 0) :
    (tag32 o).eval (frameEnv m0 d 5520 rest (fun _ ↦ 0) ret) = true := by
  have hl : (frameEnv m0 d 5520 rest (fun _ ↦ 0) ret).load 0 o 4 = BitVec.ofNat 64 0 :=
    load4_of_tag (w := 0) (.inl rfl) hw
  show (!CmpOp.apply .eq .W32 ((frameEnv m0 d 5520 rest (fun _ ↦ 0) ret).load 0 o 4)
    (BitVec.ofNat 64 1)) = true
  rw [hl]
  rfl

omit [Labels] in
theorem ult_toNat (x y : BitVec 64) : x.ult y = decide (x.toNat < y.toNat) := rfl

omit [Labels] in
/-- A range of the frame within another. -/
theorem loc_sub (hS : StackOk m0 NN) {j n lo len : Nat} (h1 : lo ≤ j) (h2 : j + n ≤ lo + len)
    (h3 : lo + len ≤ 5520) {q : BitVec 64} (hq : NativeRustcVm.InRange (loc m0 j) n q) :
    NativeRustcVm.InRange (loc m0 lo) len q := by
  have := inR_loc hS (by omega) hq
  have := rsp_ge hS
  have := rsp_top hS
  have := N_ge
  rw [inRange_toNat (by rw [loc_toNat hS (by omega)]; omega), loc_toNat hS (by omega)]
  omega

/-- **The bytecode's words** in a state of the body. -/
theorem bc_words (h : VerifyBusBalancePre a s0 L m0) {d : Mem 64}
    (hs : NativeRustcVm.SameOutside m0.dmem d
      (fun q ↦ NativeRustcVm.InRange (stackBelow m0 NN) NN q ∨ outs m0 q)) :
    NativeRustcVm.wordsOf d (reg m0 .rdx) (reg m0 .rcx).toNat = L.bytecode.toList := by
  have e := NativeRustcVm.wordsOf_of_wordsAt (pre_bc h)
  rw [Array.length_toList, pre_n h] at e
  rcases Nat.eq_zero_or_pos (reg m0 .rcx).toNat with h0 | h0
  · rw [h0] at e ⊢
    rw [← e]
    simp only [NativeRustcVm.wordsOf, List.range_zero, List.map_nil]
  rw [← e]
  have hnw := (pre_bcR h).2
  refine NativeRustcVm.wordsOf_congr fun j hj ↦ hs _ ?_
  rintro (hq | hq | hq | hq)
  · exact NativeRustcVm.Apart.not_inRange_add (pre_bcS h h0) hnw
      (noWrap_stackBelow (pre_stack h)) hj (inRange_mono hq (by omega))
  · exact NativeRustcVm.Apart.not_inRange_add (pre_bcT h h0) hnw (pre_ts h).footprint.1.2 hj hq
  · exact NativeRustcVm.Apart.not_inRange_add (pre_busB h h0).symm hnw (pre_bus h).2.1 hj hq
  · exact NativeRustcVm.Apart.not_inRange_add (pre_clB h h0).symm hnw (pre_cl h).2.1 hj hq

end

public section
variable [Host] {a : DecArea} {s0 : TState} {L : LayoutW} {m0 : MachineData} {k : Nat}

/-- **The bytecode share** (`b38`, `k + NativeRustcVmX64.Vm.VerifyBusBalance.b38Offset`). -/
theorem share_spec (hp : Placed code k) (h : VerifyBusBalancePre a s0 L m0)
    (hbs : ∀ s, Spec (Labels.label NativeRustcVmX64.Vm.BytecodeShare.entryLabel) (BytecodeSharePre a s) (BytecodeSharePost a s))
    (hcbv : Spec (Labels.label NativeRustcVmX64.Vm.ComputedBytecodeValue.entryLabel) ComputedBytecodeValuePre
      ComputedBytecodeValuePost)
    (hkp : Spec (Labels.label NativeRustcVmX64.Vm.Kpow.entryLabel) KpowPre KpowPost)
    (hfc : Spec (Labels.label NativeRustcVmX64.Vm.VerifyBusBalanceClosure0.entryLabel) FpClosurePre FpClosurePost)
    (hacc : ∀ L rows bl F SL, Spec (Labels.label NativeRustcVmX64.Vm.AccumulateSide.entryLabel)
      (AccumulateSidePre L rows bl F SL) (AccumulateSidePost L rows bl F SL))
    (hext : Spec (Labels.label NativeRustcVmX64.Vm.BufEW63Extend.entryLabel) (BufEWExtendPre 63) (BufEWExtendPost 63))
    {d : MachineData} {w pt tv mem : Array EW} {beta mf bf : EW} {s3 : TState}
    (fr : St m0 104 d)
    (hrun : (verifyBusBalance L).run s0 =
      ((bytecodeShare w (pt.extract 0 L.logBytecode)).run s3).bind fun y4 ↦
        ((computedBytecodeValue L.bytecode y4.1.2.1 y4.1.2.2).run y4.2).bind fun y5 ↦
          some (resultOf L w beta pt tv mem mf bf y4.1.1 y4.1.2.1, y5.2))
    (sm : ShareMem m0 L w pt tv mem beta mf bf d.dmem)
    (xbx : reg d .rbx = reg m0 .rdi)
    (x13 : reg d .r13 = L.logBytecode.toUInt64.toBitVec) (x14 : reg d .r14 = reg m0 .rsi)
    (xbp : reg d .rbp = (min L.logMemory pt.size).toUInt64.toBitVec)
    (x12 : reg d .r12 = (min L.logBytecode pt.size).toUInt64.toBitVec)
    (hts : TStateAt d.dmem (reg m0 .rdi) a s3)
    (hcl : ClaimsWAt d.dmem (reg m0 .r9) (claimsOf L pt mem mf bf)) :
    Eventually (step1 Host.exe) (Goal a s0 L m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b38Offset)⟩ := by
  have hS := pre_stack h
  have psz := sm.tail.psz
  have lb := (pre_lay h).log_bytecode_le
  -- `b38`: `bytecode_share(248, t, 368, point, n, 672)`.
  have hwf1 := wf0 h fr.frame.kept (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b38Offset + b38.length)).toBitVec)
  refine exec_then (infix_of b38_in_code (by simp [b38]) hp) exit_b38 hwf1 (fun _ _ ↦ rfl)
    (match_fS fr) fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid1, hw1, hrdi1, hrsi1, hrdx1, hrcx1, hr81, hr91, hr151, hk1⟩ := ok_b38
  have fr1 : St m0 96 st1.data := St.blk fr hS hwf1 hm1 hmid1 fun q hq ↦ wr0 hS hw1 (by omega) hq
  have hin1 := writesIn_of_mid hmid1
  have hs1 := blk_same hS hwf1 hm1 hw1 (by omega)
  have hsm1 : ShareMem m0 L w pt tv mem beta mf bf st1.data.dmem :=
    sm.of_keep (keepIv_block hwf1 hm1 hin1 (W0.reg0 hw1) (by decide) (by decide))
  have hsp1 : rspOf st1.data = loc m0 96 := fr1.frame.sp
  have hle : 5520 - 96 + bytecodeShareStack ≤ NN := le_share
  have x1si : reg st1.data .rsi = reg m0 .rdi := (hm1.regs .rsi _ hrsi1).trans xbx
  have x1cx : reg st1.data .rcx = loc m0 1800 := (hm1.regs .rcx _ hrcx1).trans (load_loc sm.tail.w104)
  have x18 : reg st1.data .r8 = (min L.logBytecode pt.size).toUInt64.toBitVec :=
    (hm1.regs .r8 _ hr81).trans x12
  have n8 : (min L.logBytecode pt.size).toUInt64.toBitVec.toNat = min L.logBytecode pt.size := by
    rw [UInt64.toNat_toBitVec]
    exact UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)
  have hts1 : TStateAt st1.data.dmem (reg m0 .rdi) a s3 :=
    ts_keep h (hm1.kept hwf1) hs1 (fun q hq ↦ .inl (frame_stack hS hq)) hts
  have hT := cal_tok h fr1 (by omega) hle
  have hTo : ∀ {j n : Nat}, j + n ≤ 5520 →
      NativeRustcVm.Apart (loc m0 j) n (reg m0 .rdi) tstateBytes := fun hjn ↦
    (apart_loc hS (pre_tok h).1 hjn).symm
  simp only [PcOk] at hpc1
  refine callF h (c := 96) (Nc := bytecodeShareStack) (lo := 248) (len := 1496)
    (X := fun q ↦ NativeRustcVm.InRange (loc m0 248) 48 q ∨ NativeRustcVm.InRange (loc m0 672) 1072 q ∨
      NativeRustcVm.InRange (reg m0 .rdi) tstateBytes q) (by omega) hle (by omega)
    (fun q hq ↦ by
      rcases hq with hq | hq | hq
      · exact .inr (loc_sub hS (by omega) (by omega) (by omega) hq)
      · exact .inr (loc_sub hS (by omega) (by omega) (by omega) hq)
      · exact .inl (.inl hq)) (hbs s3) fr1 hpc1 ?_ ?_ fun m2 fr2 hq2 hs2 hcs2 ↦ ?_
  · unfold BytecodeSharePre
    rw [show reg st1.data .rdi = _ from (hm1.regs .rdi _ hrdi1).trans (eval_ptr0 248), x1si,
      show reg st1.data .rdx = _ from (hm1.regs .rdx _ hrdx1).trans (eval_ptr0 368), x1cx, x18,
      show reg st1.data .r9 = _ from (hm1.regs .r9 _ hr91).trans (eval_ptr0 672), n8]
    have hsh : sharePointSlots = 67 := rfl
    rw [hsh]
    refine ⟨cal_stack h fr1 (by omega) hle, cal_rc h fr1 (by omega) hle, hts1, hT,
      cal_localIn h fr1 (by omega) hle (by omega) (by omega), by unfold busPointCap; omega,
      cal_localIn h fr1 (by omega) hle (by omega) (by omega),
      cal_local h fr1 (by omega) hle (by omega) (by omega),
      cal_local h fr1 (by omega) hle (by omega) (by omega),
      loc_apart hS (by omega) (by omega) (.inl (by omega)),
      loc_apart hS (by omega) (by omega) (.inl (by omega)),
      hTo (by omega), hTo (by omega), cal_got h fr1 (by omega) hle (by decide) ?_⟩
    intro l hl b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ((pre_got h).1 l hl).2.2.2 _ (by simp)
    · exact ((pre_got h).1 l hl).2.2.2 _ (by simp)
    · exact got_apart_frame (pre_got h) hS hl N_ge (by omega)
    · exact got_apart_frame (pre_got h) hS hl N_ge (by omega)
    · exact got_apart_frame (pre_got h) hS hl N_ge (by omega)
    · exact got_apart_frame (pre_got h) hS hl N_ge (by omega)
    · exact ((pre_got h).1 l hl).2.2.2 _ (by simp)
  · intro m' hq
    simp only [BytecodeSharePost] at hq
    refine ⟨NativeRustcVm.SameOutside.mono hq.2.2.1 fun q hq' ↦ ?_, hq.2.2.2⟩
    rw [show reg st1.data .rdi = _ from (hm1.regs .rdi _ hrdi1).trans (eval_ptr0 248), x1si,
      show reg st1.data .r9 = _ from (hm1.regs .r9 _ hr91).trans (eval_ptr0 672)] at hq'
    rcases hq' with hq' | hq' | hq' | hq'
    · exact .inr (.inl hq')
    · exact .inr (.inr (.inl hq'))
    · exact .inr (.inr (.inr hq'))
    · exact .inl hq'
  · obtain ⟨h2o, h2r, -, hsv2⟩ := hq2
    have r1 : reg st1.data .rdi = loc m0 248 := (hm1.regs .rdi _ hrdi1).trans (eval_ptr0 248)
    have r2 : reg st1.data .rdx = loc m0 368 := (hm1.regs .rdx _ hrdx1).trans (eval_ptr0 368)
    have r3 : reg st1.data .r9 = loc m0 672 := (hm1.regs .r9 _ hr91).trans (eval_ptr0 672)
    rw [r1, r2, x1cx, x18] at h2o
    rw [x1si, r2, x1cx, x18, r3] at h2r
    have ew : (NativeRustcVm.ewsOf st1.data.dmem (loc m0 368) 16).toArray = w := by
      have := NativeRustcVm.ewsOf_of_ewsAt hsm1.hw
      rw [Array.length_toList, hsm1.wsz] at this
      rw [this]
    rw [ew, slice_prefix hsm1.tail.hpt psz] at h2o h2r
    have hsp2 : rspOf st1.data = loc m0 96 := hsp1
    have hX2 : ∀ j, InIv shareIv j → ¬ (NativeRustcVm.InRange (loc m0 248) 48 (loc m0 j) ∨
        NativeRustcVm.InRange (loc m0 672) 1072 (loc m0 j) ∨
        NativeRustcVm.InRange (reg m0 .rdi) tstateBytes (loc m0 j)) := fun j hj hq ↦ by
      have hj5 := inIv_lt (B := 5472) (by decide) hj
      rcases hq with hq | hq | hq
      · exact loc_notIn hS (j := j) (by omega) (by omega)
          (inIv_apart (o := 248) (n := 48) (by decide) hj) hq
      · exact loc_notIn hS (j := j) (by omega) (by omega)
          (inIv_apart (o := 672) (n := 1072) (by decide) hj) hq
      · exact not_loc hS (pre_tok h).1 (pre_ts h).footprint.1.2 (j := j) (l := 1) (by omega) hq
          (loc_inR hS (by omega) (by omega) (by omega))
    have hsm2 : ShareMem m0 L w pt tv mem beta mf bf m2.dmem :=
      hsm1.of_keep (keepIv_call hS hsp2 (by omega) hle hs2 (by decide) (by decide) hX2)
    have x2 : ∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15], reg m2 r = reg st1.data r :=
      fun r hr ↦ hcs2 r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
    have kd : ∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14], reg m2 r = reg d r := fun r hr ↦ by
      have hr' : r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with h | h | h | h | h <;> simp [h]
      exact (x2 r hr').trans (hk1.reg hm1 hr)
    have x2_15 : reg m2 .r15 = loc m0 368 :=
      (x2 .r15 (by simp)).trans ((hm1.regs .r15 _ hr151).trans (eval_ptr0 368))
    have hcl2 : ClaimsWAt m2.dmem (reg m0 .r9) (claimsOf L pt mem mf bf) := by
      have hc := pre_cl h
      refine NativeRustcVm.Tables.ClaimsWAt.of_same hcl (Same.of_sameOutside (hs1.trans hs2)
        fun j hj hq ↦ ?_)
      have hst : ∀ {q : BitVec 64}, NativeRustcVm.InRange (stackBelow m0 NN) NN q →
          ¬ NativeRustcVm.InRange (stackBelow m0 NN) NN (reg m0 .r9 + BitVec.ofNat 64 j) →
          q = reg m0 .r9 + BitVec.ofNat 64 j → False := fun h1 h2 h3 ↦ h2 (h3 ▸ h1)
      have hnot : ¬ NativeRustcVm.InRange (stackBelow m0 NN) NN (reg m0 .r9 + BitVec.ofNat 64 j) :=
        fun h' ↦ NativeRustcVm.Apart.not_inRange_add hc.2.2.2.2.1 hc.2.1
          (noWrap_stackBelow hS) hj (inRange_mono h' (by omega))
      rcases hq with hq | hq | hq | hq | hq
      · exact hnot (frame_stack hS hq)
      · exact hnot (callee_stack hS hsp2 (by omega) hle hq)
      · exact hnot (loc_stack hS (by omega) hq)
      · exact hnot (loc_stack hS (by omega) hq)
      · exact NativeRustcVm.Apart.not_inRange_add hc.2.2.1 hc.2.1 (pre_ts h).footprint.1.2 hj hq
    have hS2 : NativeRustcVm.SameOutside d.dmem m2.dmem (fun q ↦
        NativeRustcVm.InRange (stackBelow m0 NN) NN q ∨ NativeRustcVm.InRange (reg m0 .rdi) tstateBytes q) :=
      (hs1.trans hs2).mono fun q hq ↦ by
        rcases hq with hq | hq | hq | hq | hq
        · exact .inl (frame_stack hS hq)
        · exact .inl (callee_stack hS hsp2 (by omega) hle hq)
        · exact .inl (loc_stack hS (by omega) hq)
        · exact .inl (loc_stack hS (by omega) hq)
        · exact .inr hq
    have hk2 : Kept d.dmem m2.dmem := kept_trans (hm1.kept hwf1) hsv2.2
    -- `b39`: the share's tag.
    rw [show k + NativeRustcVmX64.Vm.VerifyBusBalance.b38Offset + b38.length = k + NativeRustcVmX64.Vm.VerifyBusBalance.b39Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyBusBalance.b38_next]]
    cases hr : (bytecodeShare w (pt.extract 0 L.logBytecode)).run s3 with
    | none =>
      rw [hr] at h2o
      have hnone : (verifyBusBalance L).run s0 = none := by rw [hrun, hr]; rfl
      refine test_spec hp h (j := NativeRustcVmX64.Vm.VerifyBusBalance.b39Offset) (n := b39.length) (infix_of b39_in_code (by simp [b39]) hp) rfl
        exit_b39 ok_b39 fr2 (fun _ ↦ hnone) fun _ _ _ _ hc ↦ ?_
      rw [tag32_true h2o] at hc
      cases hc
    | some y =>
    obtain ⟨⟨share, bp, value⟩, s4⟩ := y
    rw [hr] at h2o
    obtain ⟨h2bp, hts2⟩ := h2r _ _ hr
    obtain ⟨ht1, hsh, hbpz, hval⟩ := h2o
    have hbsz : bp.size = min L.logBytecode pt.size + 4 := by
      have := bytecodeShare_size hr
      simpa using this
    refine test_spec hp h (j := NativeRustcVmX64.Vm.VerifyBusBalance.b39Offset) (n := b39.length) (infix_of b39_in_code (by simp [b39]) hp) rfl
      exit_b39 ok_b39 fr2 (fun hc ↦ by rw [tag32_false ht1] at hc; cases hc)
      fun d3 fr3 hd3 hk3 _ ↦ ?_
    -- `b40`: the share kept, the point's length checked.
    show Eventually (step1 Host.exe) (Goal a s0 L m0) { data := d3, pc := Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b40Offset) }
    have hwf4 := wf0 h fr3.frame.kept (vars := fun _ ↦ 0) (ret := 0)
    refine exec_then (infix_of b40_in_code (by simp [b40]) hp) exit_b40 hwf4 nofun (match_fS fr3)
      fun st4 hm4 hpc4 ↦ ?_
    obtain ⟨hmid4, hw4, wr4, hrcx4, hr84, hr94, hk4⟩ := ok_b40
    have fr4 : St m0 104 st4.data := St.blk fr3 hS hwf4 hm4 hmid4 fun q hq ↦ wr0 hS hw4 (by omega) hq
    have hin4 := writesIn_of_mid hmid4
    have hs4 := blk_same hS hwf4 hm4 hw4 (by omega)
    have ld4 : ∀ {o : Nat} {x : UInt64}, NativeRustcVm.WordAt m2.dmem (loc m0 o) x →
        (frameEnv m0 d3 5520 [] (fun _ ↦ 0) 0).load 0 o 8 = x.toBitVec :=
      fun hw ↦ load_loc (hd3 ▸ hw)
    have hb272 : NativeRustcVm.WordAt m2.dmem (loc m0 272) bp.size.toUInt64 := by
      have := hbpz; rwa [off_off] at this
    obtain ⟨hv0, hv1⟩ := ewAt_iff.mp hval
    rw [off_off] at hv0
    rw [off_off, off_off] at hv1
    obtain ⟨hs0, hs1'⟩ := ewAt_iff.mp hsh
    rw [off_off] at hs0
    rw [off_off, off_off] at hs1'
    have nbp : bp.size.toUInt64.toBitVec.toNat = bp.size := by
      rw [UInt64.toNat_toBitVec]
      exact UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)
    have hc4 : SBool.eval (frameEnv m0 d3 5520 [] (fun _ ↦ 0) 0)
        (.not (.cmp .ult .W64 (.load 0 272 8) (.lit 68))) = false := by
      show (!CmpOp.apply .ult .W64 ((frameEnv m0 d3 5520 [] (fun _ ↦ 0) 0).load 0 272 8)
        (BitVec.ofNat 64 68)) = false
      rw [ld4 hb272]
      simp only [CmpOp.apply, low_W64, ult_toNat, nbp, BitVec.toNat_ofNat]
      simp only [Bool.not_eq_false', decide_eq_true_eq]
      omega
    simp only [PcOk, hc4, Bool.false_eq_true, ↓reduceIte] at hpc4
    rw [show k + NativeRustcVmX64.Vm.VerifyBusBalance.b40Offset + b40.length = k + NativeRustcVmX64.Vm.VerifyBusBalance.b41Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyBusBalance.b40_next]] at hpc4
    have wW4 : ∀ {o : Nat} {v : Sym}, o + 8 ≤ 5520 →
        (∀ t < 8, findWrite 0 (o + t) (after b40 (fS 104)).mem = some (v, t)) →
        NativeRustcVm.WordAt st4.data.dmem (loc m0 o) (UInt64.ofBitVec (v.eval
          (frameEnv m0 d3 5520 [] (fun _ ↦ 0) 0))) :=
      fun ho hw ↦ wordAt_write hm4 (r := 0) (b := fb m0) (sz := 5520 + 8) rfl (by omega) hw
    have hsh4 : NativeRustcVm.EWAt st4.data.dmem (loc m0 352) share := by
      refine ewAt_iff.mpr ⟨?_, ?_⟩
      · have := wW4 (o := 352) (by omega) (wr4.find (List.Mem.head _))
        rwa [show (Sym.load 0 256 8).eval (frameEnv m0 d3 5520 [] (fun _ ↦ 0) 0) = _ from ld4 hs0,
          UInt64.ofBitVec_toBitVec] at this
      · have := wW4 (o := 360) (by omega) (wr4.find (List.Mem.tail _ (List.Mem.head _)))
        rw [show (Sym.load 0 264 8).eval (frameEnv m0 d3 5520 [] (fun _ ↦ 0) 0) = _ from ld4 hs1',
          UInt64.ofBitVec_toBitVec] at this
        rw [off_off]
        exact this
    have hsm4 : ShareMem m0 L w pt tv mem beta mf bf st4.data.dmem :=
      hsm2.of_keep (hd3 ▸ keepIv_block hwf4 hm4 hin4 (W0.reg0 hw4) (by decide) (by decide))
    have hbp4 : NativeRustcVm.EWsAt st4.data.dmem (loc m0 672) bp.toList :=
      NativeRustcVm.Tables.EWsAt.of_same (hd3 ▸ h2bp) (keepB hwf4 hm4 hin4 (j := 672)
        (n := 16 * bp.size) (by omega) (miss0 hw4 (by omega))) (by simp)
    have k4 : ∀ r ∈ cs, reg st4.data r = reg d3 r := fun r hr ↦ hk4.reg hm4 hr
    -- `b41`: `computed_bytecode_value`.
    have hwf5 := wf0 h fr4.frame.kept (vars := fun _ ↦ 0)
      (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b41Offset + b41.length)).toBitVec)
    refine exec_at (infix_of b41_in_code (by simp [b41]) hp) exit_b41 hwf5 (fun _ _ ↦ rfl) hpc4
      (match_fS fr4) fun st5 hm5 hpc5 ↦ ?_
    obtain ⟨hmid5, hw5, hrdi5, hrsi5, hrdx5, hk5⟩ := ok_b41
    have fr5 : St m0 96 st5.data := St.blk fr4 hS hwf5 hm5 hmid5 fun q hq ↦ wr0 hS hw5 (by omega) hq
    have hin5 := writesIn_of_mid hmid5
    have hs5 := blk_same hS hwf5 hm5 hw5 (by omega)
    have hsp5 : rspOf st5.data = loc m0 96 := fr5.frame.sp
    have hle5 : 5520 - 96 + computedBytecodeValueStack ≤ NN := le_cbv
    have x5di : reg st5.data .rdi = reg m0 .rdx := by
      rw [show reg st5.data .rdi = _ from hm5.regs .rdi _ hrdi5, Sym.eval, load_loc hsm4.w128]
    have x5si : reg st5.data .rsi = reg m0 .rcx := by
      rw [show reg st5.data .rsi = _ from hm5.regs .rsi _ hrsi5, Sym.eval, load_loc hsm4.w136]
    have x5dx : reg st5.data .rdx = loc m0 672 := (hm5.regs .rdx _ hrdx5).trans (eval_ptr0 672)
    have x5cx : reg st5.data .rcx = bp.size.toUInt64.toBitVec :=
      (hk5.reg hm5 (by simp)).trans ((hm4.regs .rcx _ hrcx4).trans (ld4 hb272))
    have x58 : reg st5.data .r8 = value.c0.toBitVec :=
      (hk5.reg hm5 (by simp)).trans ((hm4.regs .r8 _ hr84).trans (ld4 hv0))
    have x59 : reg st5.data .r9 = value.c1.toBitVec :=
      (hk5.reg hm5 (by simp)).trans ((hm4.regs .r9 _ hr94).trans (ld4 hv1))
    have hbp5 : NativeRustcVm.EWsAt st5.data.dmem (loc m0 672) bp.toList :=
      NativeRustcVm.Tables.EWsAt.of_same hbp4 (keepB hwf5 hm5 hin5 (j := 672)
        (n := 16 * bp.size) (by omega) (miss0 hw5 (by omega))) (by simp)
    have hbc := pre_bcR h
    simp only [PcOk] at hpc5
    refine callF h (c := 96) (Nc := computedBytecodeValueStack) (lo := 0) (len := 0)
      (X := fun _ ↦ False) (by omega) hle5 (by omega) (fun _ h ↦ h.elim) hcbv fr5 hpc5 ?_
      (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun q hq' ↦ ?_, hq.2.2⟩)
      fun m6 fr6 hq6 hs6 hcs6 ↦ ?_
    · unfold ComputedBytecodeValuePre
      rw [x5di, x5si, x5dx, x5cx]
      refine ⟨cal_stack h fr5 (by omega) hle5,
        ⟨Mapped.keeps hbc.1 fr5.frame.kept, hbc.2⟩,
        fun h0 ↦ apart_callee (pre_bcS h h0) (cal_at h fr5 (by omega)).sp (rsp_ge hS) hle5, ?_⟩
      unfold SliceOk
      rw [nbp]
      exact cal_localIn h fr5 (by omega) hle5 (by omega) (by omega)
    · rcases hq' with hq' | hq'
      · exact absurd hq' (by unfold NativeRustcX64.InRange; simp)
      · exact .inl hq'
    · obtain ⟨hal6, -, hsv6⟩ := hq6
      rw [x5di, x5si, x5dx, x5cx, x58, x59] at hal6
      have e1 : wordSliceE st5.data (reg m0 .rdx) (reg m0 .rcx) = L.bytecode.map EW.ofK := by
        unfold wordSliceE
        rw [bc_words h fr5.same]
        apply Array.ext'
        simp
      have e2 : slice st5.data (loc m0 672) bp.size.toUInt64.toBitVec = bp := by
        unfold slice
        rw [nbp]
        have := NativeRustcVm.ewsOf_of_ewsAt hbp5
        rw [Array.length_toList] at this
        rw [this]
      have e3 : ewArg value.c0.toBitVec value.c1.toBitVec = value := by simp [ewArg]
      rw [e1, e2, e3] at hal6
      have hrun' : (verifyBusBalance L).run s0 =
          if (multilinearEval (L.bytecode.map EW.ofK) bp == value) = true then
            some (resultOf L w beta pt tv mem mf bf share bp, s4) else none := by
        rw [hrun, hr, Option.bind_some, cbv_run]
        split <;> rfl
      have hle6 := hle5
      have hsm6 : ShareMem m0 L w pt tv mem beta mf bf m6.dmem :=
        hsm4.of_keep ((keepIv_block hwf5 hm5 hin5 (W0.reg0 hw5) (by decide) (by decide)).trans
          (keepIv_call hS hsp5 (by omega) hle5 hs6 (by decide) (by decide) fun _ _ h ↦ h))
      have hsh6 : NativeRustcVm.EWAt m6.dmem (loc m0 352) share :=
        NativeRustcVm.Layout.EWAt.of_same hsh4 ((keepB hwf5 hm5 hin5 (j := 352) (n := 16)
          (by omega) (miss0 hw5 (by omega))).trans (keepC hS hsp5 (by omega) hle5 hs6
          (j := 352) (n := 16) (by omega) (by omega) fun _ _ h ↦ h)) le_rfl
      have hc6 : Chg m0 m2.dmem m6.dmem := by
        refine Chg.of (kept_trans (hd3 ▸ hm4.kept hwf4) (kept_trans (hm5.kept hwf5) hsv6.2))
          ((hd3 ▸ hs4).trans (hs5.trans hs6)) fun q hq ↦ ?_
        rcases hq with hq | hq | hq | hq
        · exact .inl (frame_stack hS hq)
        · exact .inl (frame_stack hS hq)
        · exact .inl (callee_stack hS hsp5 (by omega) hle5 hq)
        · exact hq.elim
      have hts6 : TStateAt m6.dmem (reg m0 .rdi) a s4 :=
        ts_keep h hc6.1 hc6.2 (fun q hq ↦ hq.elim .inl fun h' ↦ .inr (.inl h')) hts2
      have hcl6 : ClaimsWAt m6.dmem (reg m0 .r9) (claimsOf L pt mem mf bf) := (hc6.tc h hts2 hcl2).2
      have x6 : ∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15], reg m6 r = reg m2 r := fun r hr ↦ by
        have hc : calleeSaved r = true ∧ r ∈ cs ∧ r ∈ [Reg64.rcx, .r8, .r9, .rbx, .rbp, .r12, .r13,
            .r14, .r15] := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl, by simp [cs], by simp⟩
        exact (hcs6 r hc.1).trans ((hk5.reg hm5 hc.2.2).trans ((k4 r hc.2.1).trans
          (by rw [show reg d3 r = reg m2 r from by
            have := hk3 r (by simp only [nsp, cs, List.mem_cons] at hc ⊢; rcases hc.2.1 with h' | h' | h' | h' | h' | h' | h' <;> simp_all)
            exact this])))
      -- `b42`: the bytecode's value.
      rw [show k + NativeRustcVmX64.Vm.VerifyBusBalance.b41Offset + b41.length = k + NativeRustcVmX64.Vm.VerifyBusBalance.b42Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyBusBalance.b41_next]]
      refine test_spec hp h (j := NativeRustcVmX64.Vm.VerifyBusBalance.b42Offset) (n := b42.length) (infix_of b42_in_code (by simp [b42]) hp) rfl
        exit_b42 ok_b42 fr6 (fun hc ↦ ?_) fun d7 fr7 hd7 hk7 hc ↦ ?_
      · rw [hrun']
        cases hb : (multilinearEval (L.bytecode.map EW.ofK) bp == value)
        · rfl
        · rw [hb] at hal6
          rw [alZ_false (show boolRet m6 = 1 from hal6)] at hc
          cases hc
      · cases hb : (multilinearEval (L.bytecode.map EW.ofK) bp == value)
        · rw [hb] at hal6
          rw [alZ_true (show boolRet m6 = 0 from hal6)] at hc
          cases hc
        rw [hb] at hrun'
        simp only [↓reduceIte] at hrun'
        have k7 : ∀ r ∈ [Reg64.rbp, .r12, .r13, .r14], reg d7 r = reg d r := fun r hr ↦ by
          have hn : r ∈ nsp := by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl | rfl <;> simp [nsp]
          have h6 : r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15] := by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
            rcases hr with h' | h' | h' | h' <;> simp [h']
          have h5 : r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14] := by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
            rcases hr with h' | h' | h' | h' <;> simp [h']
          rw [hk7 r hn, x6 r h6]
          exact kd r h5
        have pm : PushMem m0 L w pt tv mem beta mf bf share d7.dmem := by
          rw [hd7]
          exact ⟨hsm6.tail, hsm6.push, hsm6.pull, hsm6.count, hsm6.hw, hsm6.wsz, hsm6.hmem,
            hsm6.msz, hsm6.htv, hsm6.tsz, hsm6.w168, hsm6.w160, hsm6.w152, hsm6.w144, hsm6.w184,
            hsm6.w176, hsh6⟩
        exact push_spec hp h hkp hfc hacc hext fr7 hrun' pm
          ((k7 .r13 (by simp)).trans x13) ((k7 .r14 (by simp)).trans x14)
          ((hk7 .r15 (by simp [nsp])).trans ((x6 .r15 (by simp)).trans x2_15))
          ((k7 .rbp (by simp)).trans xbp) ((k7 .r12 (by simp)).trans x12)
          (hd7 ▸ hts6) (hd7 ▸ hcl6)
