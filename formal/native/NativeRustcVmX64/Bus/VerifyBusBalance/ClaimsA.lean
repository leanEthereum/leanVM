module

public import NativeRustcVmX64.Bus.VerifyBusBalance.ClaimsC
public import NativeRustcVmX64.Code.Vm.AccumulateSide.Names
public import NativeRustcVmX64.Code.Vm.BufEW63Extend.Names
public import NativeRustcVmX64.Code.Vm.BytecodeShare.Names
public import NativeRustcVmX64.Code.Vm.ComputedBytecodeValue.Names
public import NativeRustcVmX64.Code.Vm.Kpow.Names
public import NativeRustcVmX64.Code.Vm.PushClaim.Names
public import NativeRustcVmX64.Code.Vm.TStateReadScalar.Names
public import NativeRustcVmX64.Code.Vm.VerifyBusBalanceClosure0.Names

/-!
# `verify_bus_balance`'s final counters and first claim (x86-64)

`AtRs`: the state at `b25` (`k + NativeRustcVmX64.Vm.VerifyBusBalance.b25Offset`), the memory's scalars at `216`, the final memory counter
at `672`. `b25` keeps that counter at `160`, `168` and calls `read_scalar` for the final bytecode
counter; `b26` checks its tag; `b27` keeps it at `144`, `152`, empties the claims and pushes the
first; then the other three (`claimsA_spec`).
-/

namespace NativeRustcVmX64.Bus.VerifyBusBalance

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.VerifyBusBalance
open NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck NativeRustcVmX64.Bus.Gkr
open NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Bus NativeRustcVm.Layout

public section

/-- The locals kept from the bus layouts to the bytecode share, but the final counters. -/
structure BaseMem (m0 : MachineData) (L : LayoutW) (w pt tv mem : Array EW) (beta : EW)
    (d : Mem 64) : Prop where
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
  w184 : NativeRustcVm.WordAt d (loc m0 184) beta.c0
  w176 : NativeRustcVm.WordAt d (loc m0 176) beta.c1
  w128 : NativeRustcVm.WordAt d (loc m0 128) (UInt64.ofBitVec (reg m0 .rdx))
  w136 : NativeRustcVm.WordAt d (loc m0 136) (UInt64.ofBitVec (reg m0 .rcx))

/-- `BaseMem`'s intervals. -/
abbrev baseIv : List (Nat × Nat) := [(104, 144), (176, 192), (216, 248), (368, 624), (1744, 5472)]

theorem BaseMem.of_keep {m0 : MachineData} {L : LayoutW} {w pt tv mem : Array EW} {beta : EW}
    {d d' : Mem 64} (h : BaseMem m0 L w pt tv mem beta d) (hk : KeepIv baseIv m0 d d') :
    BaseMem m0 L w pt tv mem beta d' := by
  have psz := h.tail.psz
  have i1 : (104, 144) ∈ baseIv := by simp
  have i2 : (176, 192) ∈ baseIv := by simp
  have i3 : (216, 248) ∈ baseIv := by simp
  have i4 : (368, 624) ∈ baseIv := by simp
  have i5 : (1744, 5472) ∈ baseIv := by simp
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
    NativeRustcVm.Layout.WordAt.of_same h.w184 (hk.sameIn i2 (by omega) (by omega)) le_rfl,
    NativeRustcVm.Layout.WordAt.of_same h.w176 (hk.sameIn i2 (by omega) (by omega)) le_rfl,
    NativeRustcVm.Layout.WordAt.of_same h.w128 (hk.sameIn i1 (by omega) (by omega)) le_rfl,
    NativeRustcVm.Layout.WordAt.of_same h.w136 (hk.sameIn i1 (by omega) (by omega)) le_rfl⟩

theorem ShareMem.of_base {m0 : MachineData} {L : LayoutW} {w pt tv mem : Array EW}
    {beta mf bf : EW} {d : Mem 64} (h : BaseMem m0 L w pt tv mem beta d)
    (w168 : NativeRustcVm.WordAt d (loc m0 168) mf.c0)
    (w160 : NativeRustcVm.WordAt d (loc m0 160) mf.c1)
    (w152 : NativeRustcVm.WordAt d (loc m0 152) bf.c0)
    (w144 : NativeRustcVm.WordAt d (loc m0 144) bf.c1) : ShareMem m0 L w pt tv mem beta mf bf d :=
  ⟨h.tail, h.push, h.pull, h.count, h.hw, h.wsz, h.hmem, h.msz, h.htv, h.tsz, w168, w160, w152,
    w144, h.w184, h.w176, h.w128, h.w136⟩

/-- **The state at `b25`.** -/
structure AtRs (a : DecArea) (L : LayoutW) (m0 : MachineData) (w pt tv mem : Array EW)
    (beta mf : EW) (s : TState) (d : MachineData) : Prop where
  fr : St m0 104 d
  base : BaseMem m0 L w pt tv mem beta d.dmem
  hmf : OptEWAt d.dmem (loc m0 672) (some mf)
  xbx : reg d .rbx = reg m0 .rdi
  x13 : reg d .r13 = L.logBytecode.toUInt64.toBitVec
  x14 : reg d .r14 = reg m0 .rsi
  x15 : reg d .r15 = reg m0 .r9
  xbp : reg d .rbp = (min L.logMemory pt.size).toUInt64.toBitVec
  x12 : reg d .r12 = (min L.logBytecode pt.size).toUInt64.toBitVec
  ts : TStateAt d.dmem (reg m0 .rdi) a s

end

public section
variable [Labels] {m0 : MachineData}

/-- A `None` tag's low byte is `0`. -/
theorem tag8_true {d : MachineData} {rest : List (BitVec 64 × Nat)} {ret : BitVec 64} {o : Nat}
    (hw : NativeRustcVm.WordAt d.dmem (loc m0 o) 0) :
    (tag8 o).eval (frameEnv m0 d 5520 rest (fun _ ↦ 0) ret) = true := by
  have hl : (frameEnv m0 d 5520 rest (fun _ ↦ 0) ret).load 0 o 1 = BitVec.ofNat 64 0 :=
    load1_of_tag (w := 0) (.inl rfl) hw
  show CmpOp.apply .eq .W8 ((frameEnv m0 d 5520 rest (fun _ ↦ 0) ret).load 0 o 1)
    (BitVec.ofNat 64 0) = true
  rw [hl]
  rfl

end

public section
variable [Host] {a : DecArea} {s0 : TState} {L : LayoutW} {m0 : MachineData} {k : Nat}

/-- **The final bytecode counter and the first claim** (`b25`, `k + NativeRustcVmX64.Vm.VerifyBusBalance.b25Offset`). -/
theorem claimsA_spec (hp : Placed code k) (h : VerifyBusBalancePre a s0 L m0)
    (hrs : ∀ s, Spec (Labels.label NativeRustcVmX64.Vm.TStateReadScalar.entryLabel) (ReadScalarPre a s) (ReadScalarPost a s))
    (hpc : ∀ cs, Spec (Labels.label NativeRustcVmX64.Vm.PushClaim.entryLabel) (PushClaimPre cs) (PushClaimPost cs))
    (hbs : ∀ s, Spec (Labels.label NativeRustcVmX64.Vm.BytecodeShare.entryLabel) (BytecodeSharePre a s) (BytecodeSharePost a s))
    (hcbv : Spec (Labels.label NativeRustcVmX64.Vm.ComputedBytecodeValue.entryLabel) ComputedBytecodeValuePre
      ComputedBytecodeValuePost)
    (hkp : Spec (Labels.label NativeRustcVmX64.Vm.Kpow.entryLabel) KpowPre KpowPost)
    (hfc : Spec (Labels.label NativeRustcVmX64.Vm.VerifyBusBalanceClosure0.entryLabel) FpClosurePre FpClosurePost)
    (hacc : ∀ L rows bl F SL, Spec (Labels.label NativeRustcVmX64.Vm.AccumulateSide.entryLabel)
      (AccumulateSidePre L rows bl F SL) (AccumulateSidePost L rows bl F SL))
    (hext : Spec (Labels.label NativeRustcVmX64.Vm.BufEW63Extend.entryLabel) (BufEWExtendPre 63) (BufEWExtendPost 63))
    {w pt tv mem : Array EW} {beta mf : EW} {s : TState} {d : MachineData}
    (A : AtRs a L m0 w pt tv mem beta mf s d)
    (hrun : (verifyBusBalance L).run s0 = (readScalar.run s).bind fun y3 ↦
      ((bytecodeShare w (pt.extract 0 L.logBytecode)).run y3.2).bind fun y4 ↦
        ((computedBytecodeValue L.bytecode y4.1.2.1 y4.1.2.2).run y4.2).bind fun y5 ↦
          some (resultOf L w beta pt tv mem mf y3.1 y4.1.1 y4.1.2.1, y5.2)) :
    Eventually (step1 Host.exe) (Goal a s0 L m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b25Offset)⟩ := by
  have hS := pre_stack h
  have psz := A.base.tail.psz
  have lm := (pre_lay h).log_memory_le
  -- `b25`: the final memory counter kept, `read_scalar(672, t)`.
  have hwf1 := wf0 h A.fr.frame.kept (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b25Offset + b25.length)).toBitVec)
  refine exec_then (infix_of b25_in_code (by simp [b25]) hp) exit_b25 hwf1 (fun _ _ ↦ rfl)
    (match_fS A.fr) fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid1, hw1, wr25, hrdi1, hrsi1, hk1⟩ := ok_b25
  have fr1 : St m0 96 st1.data := St.blk A.fr hS hwf1 hm1 hmid1 fun q hq ↦ wr0 hS hw1 (by omega) hq
  have hin1 := writesIn_of_mid hmid1
  have hs1 := blk_same hS hwf1 hm1 hw1 (by omega)
  have hsp1 : rspOf st1.data = loc m0 96 := fr1.frame.sp
  have ld1 : ∀ {o : Nat} {x : UInt64}, NativeRustcVm.WordAt d.dmem (loc m0 o) x →
      (frameEnv m0 d 5520 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b25Offset + b25.length)).toBitVec).load 0 o 8 =
        x.toBitVec := fun hw ↦ load_loc hw
  have wW1 : ∀ {o : Nat} {v : Sym}, o + 8 ≤ 5520 →
      (∀ t < 8, findWrite 0 (o + t) (after b25 (fS 104)).mem = some (v, t)) →
      NativeRustcVm.WordAt st1.data.dmem (loc m0 o) (UInt64.ofBitVec (v.eval
        (frameEnv m0 d 5520 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b25Offset + b25.length)).toBitVec))) :=
    fun ho hw ↦ wordAt_write hm1 (r := 0) (b := fb m0) (sz := 5520 + 8) rfl (by omega) hw
  obtain ⟨-, hmfE⟩ := A.hmf
  obtain ⟨hmf0, hmf1⟩ := ewAt_iff.mp hmfE
  rw [off_off] at hmf0
  rw [off_off, off_off] at hmf1
  have w168 : NativeRustcVm.WordAt st1.data.dmem (loc m0 168) mf.c0 := by
    have := wW1 (o := 168) (by omega) (wr25.find (List.Mem.tail _ (List.Mem.head _)))
    rwa [show (Sym.load 0 680 8).eval (frameEnv m0 d 5520 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b25Offset + b25.length)).toBitVec) = _ from ld1 hmf0,
      UInt64.ofBitVec_toBitVec] at this
  have w160 : NativeRustcVm.WordAt st1.data.dmem (loc m0 160) mf.c1 := by
    have := wW1 (o := 160) (by omega) (wr25.find (List.Mem.head _))
    rwa [show (Sym.load 0 688 8).eval (frameEnv m0 d 5520 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b25Offset + b25.length)).toBitVec) = _ from ld1 hmf1,
      UInt64.ofBitVec_toBitVec] at this
  have hts1 := ts_keep h (hm1.kept hwf1) hs1 (fun q hq ↦ .inl (frame_stack hS hq)) A.ts
  have hle : 5520 - 96 + readScalarStack ≤ NN := le_rs
  simp only [PcOk] at hpc1
  refine callF h (c := 96) (Nc := readScalarStack) (lo := 672) (len := 24)
    (X := fun q ↦ NativeRustcVm.InRange (loc m0 672) 24 q ∨
      NativeRustcVm.InRange (reg m0 .rdi) tstateBytes q) (by omega) hle (by omega)
    (fun q hq ↦ hq.elim .inr fun h' ↦ .inl (.inl h')) (hrs s) fr1 hpc1 ?_
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.1 fun q hq' ↦ ?_, hq.2.2.2⟩)
    fun m2 fr2 hq2 hs2 hcs2 ↦ ?_
  · unfold ReadScalarPre
    rw [show reg st1.data .rsi = _ from (hm1.regs .rsi _ hrsi1).trans A.xbx,
      show reg st1.data .rdi = _ from (hm1.regs .rdi _ hrdi1).trans (eval_ptr0 672)]
    refine ⟨cal_stack h fr1 (by omega) hle, cal_rc h fr1 (by omega) hle, hts1,
      cal_tok h fr1 (by omega) hle, cal_local h fr1 (by omega) hle (by omega) (by omega),
      cal_got h fr1 (by omega) hle (by decide) ?_⟩
    intro l hl b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact ((pre_got h).1 l hl).2.2.2 _ (by simp)
    · exact ((pre_got h).1 l hl).2.2.2 _ (by simp)
    · exact got_apart_frame (pre_got h) hS hl N_ge (by omega)
    · exact ((pre_got h).1 l hl).2.2.2 _ (by simp)
  · rw [show reg st1.data .rsi = _ from (hm1.regs .rsi _ hrsi1).trans A.xbx,
      show reg st1.data .rdi = _ from (hm1.regs .rdi _ hrdi1).trans (eval_ptr0 672)] at hq'
    rcases hq' with hq' | hq' | hq'
    · exact .inr (.inl hq')
    · exact .inr (.inr hq')
    · exact .inl hq'
  · obtain ⟨hout2, hnext2, -, hsv2⟩ := hq2
    rw [show reg st1.data .rdi = _ from (hm1.regs .rdi _ hrdi1).trans (eval_ptr0 672)] at hout2
    rw [show reg st1.data .rsi = _ from (hm1.regs .rsi _ hrsi1).trans A.xbx] at hnext2
    have hX : ∀ {ivs : List (Nat × Nat)}, ivs.all (fun p ↦ decide (p.2 ≤ 5472)) = true →
        ivs.all (fun p ↦ decide (p.2 ≤ 672) || decide (672 + 24 ≤ p.1)) = true → ∀ j, InIv ivs j →
        ¬ (NativeRustcVm.InRange (loc m0 672) 24 (loc m0 j) ∨
          NativeRustcVm.InRange (reg m0 .rdi) tstateBytes (loc m0 j)) := fun hlt hap j hj hq ↦ by
      have hj5 := inIv_lt hlt hj
      rcases hq with hq | hq
      · exact loc_notIn hS (j := j) (by omega) (by omega) (inIv_apart hap hj) hq
      · exact not_loc hS (pre_tok h).1 (pre_ts h).footprint.1.2 (j := j) (l := 1) (by omega) hq
          (loc_inR hS (by omega) (by omega) (by omega))
    have kv0 : KeepIv baseIv m0 d.dmem st1.data.dmem :=
      keepIv_block' hwf1 hm1 hin1 (by decide) (by decide +kernel)
    have kv2 : KeepIv baseIv m0 st1.data.dmem m2.dmem :=
      keepIv_call hS hsp1 (by omega) hle hs2 (by decide) (by decide) (hX (by decide) (by decide))
    have kf2 : KeepIv [(160, 176)] m0 st1.data.dmem m2.dmem :=
      keepIv_call hS hsp1 (by omega) hle hs2 (by decide) (by decide) (hX (by decide) (by decide))
    have hk2 : Kept d.dmem m2.dmem := kept_trans (hm1.kept hwf1) hsv2.2
    have hc := pre_cl h
    -- `b26`: the final bytecode counter's tag.
    rw [show k + NativeRustcVmX64.Vm.VerifyBusBalance.b25Offset + b25.length = k + NativeRustcVmX64.Vm.VerifyBusBalance.b26Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyBusBalance.b25_next]]
    cases hr : readScalar.run s with
    | none =>
      rw [hr] at hout2
      refine test_spec hp h (j := NativeRustcVmX64.Vm.VerifyBusBalance.b26Offset) (n := b26.length) (infix_of b26_in_code (by simp [b26]) hp) rfl
        exit_b26 ok_b26 fr2 (fun _ ↦ by rw [hrun, hr]; rfl) fun _ _ _ _ hc' ↦ ?_
      rw [tag8_true (show NativeRustcVm.WordAt m2.dmem (loc m0 672) 0 from hout2)] at hc'
      cases hc'
    | some y =>
    obtain ⟨bf, s3⟩ := y
    rw [hr] at hout2
    have hts2 := hnext2 _ _ hr
    obtain ⟨ht2, hbf2⟩ := hout2
    obtain ⟨hb0, hb1⟩ := ewAt_iff.mp hbf2
    rw [off_off] at hb0
    rw [off_off, off_off] at hb1
    refine test_spec hp h (j := NativeRustcVmX64.Vm.VerifyBusBalance.b26Offset) (n := b26.length) (infix_of b26_in_code (by simp [b26]) hp) rfl
      exit_b26 ok_b26 fr2 (fun hc' ↦ by rw [tag8_false ht2] at hc'; cases hc')
      fun d3 fr3 hd3 hk3 _ ↦ ?_
    -- `b27`: the final bytecode counter kept, the claims emptied, `push_claim` of the first.
    rw [show k + NativeRustcVmX64.Vm.VerifyBusBalance.b26Offset + b26.length = k + NativeRustcVmX64.Vm.VerifyBusBalance.b27Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyBusBalance.b26_next]]
    have hx9 : (reg m0 .r9).toNat + 8 ≤ 2 ^ 64 := by
      have := hc.2.1
      unfold NativeRustcX64.NoWrap at this
      rw [claimsBytes_eq] at this
      omega
    have hwf4 : (frameEnv m0 d3 5520 [(reg m0 .r9, 8)] (fun _ ↦ 0)
        (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b27Offset + b27.length)).toBitVec).WF :=
      Bus.wf1 hS N_ge fr3.frame.kept
        ⟨NativeRustcVm.Mapped.mono hc.1 (by rw [claimsBytes_eq]; omega), hx9⟩
        (NativeRustcVm.Apart.mono hc.2.2.2.2.1 le_rfl (by rw [claimsBytes_eq]; omega) le_rfl le_rfl)
    have g3 : ∀ r ∈ clRegs, reg d3 r = reg d r := fun r hr' ↦
      (hk3 r (clRegs_cs r hr').2.2).trans ((hcs2 r (clRegs_cs r hr').1).trans
        (hk1.reg hm1 (clRegs_cs r hr').2.1))
    have hm4 : Match (frameEnv m0 d3 5520 [(reg m0 .r9, 8)] (fun _ ↦ 0)
        (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b27Offset + b27.length)).toBitVec) cS d3 :=
      match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨fr3.frame.rsp_eval, by
        show reg d3 .r15 = reg m0 .r9 + BitVec.ofInt 64 0
        rw [ofInt_zero64, BitVec.add_zero, g3 .r15 (by simp), A.x15], trivial⟩ trivial trivial
        trivial
    refine exec_then (infix_of b27_in_code (by simp [b27]) hp) exit_b27 hwf4 (fun _ _ ↦ rfl) hm4
      fun st4 hm4' hpc4 ↦ ?_
    obtain ⟨hmid4, hw4, wr4, wr4', hrdi4, hrsi4, hrdx4, hrcx4, hr84, hr94, hr154, hk4⟩ := ok_b27
    have hclO : ∀ q, NativeRustcVm.InRange (reg m0 .r9) 8 q → outs m0 q :=
      fun q hq ↦ .inr (.inr (inRange_mono hq (by rw [claimsBytes_eq]; omega)))
    have fr4 : St m0 96 st4.data := St.blk fr3 hS hwf4 hm4' hmid4
      (fun q hq ↦ wr1 hS hw4 (by omega) le_rfl hx9 hclO hq)
    have hin4 := writesIn_of_mid hmid4
    have hs4 : NativeRustcVm.SameOutside d3.dmem st4.data.dmem (fun q ↦
        NativeRustcVm.InRange (fb m0) 5520 q ∨ NativeRustcVm.InRange (reg m0 .r9) 8 q) :=
      fun q hq ↦ hm4'.get?_mem0 hwf4 fun hW ↦ hq (written_fb1 hS N_ge (fun w hw ↦
        (hw4 w hw).elim (fun h' ↦ .inl ⟨h'.1, by omega⟩) fun h' ↦ .inr ⟨h'.1, by omega⟩) hx9 hW)
    have kv4 : KeepIv baseIv m0 d3.dmem st4.data.dmem :=
      keepIv_block' hwf4 hm4' hin4 (by decide) (by decide +kernel)
    have kf4 : KeepIv [(160, 176)] m0 d3.dmem st4.data.dmem :=
      keepIv_block' hwf4 hm4' hin4 (by decide) (by decide +kernel)
    have ld4 : ∀ {o : Nat} {x : UInt64}, NativeRustcVm.WordAt m2.dmem (loc m0 o) x →
        (frameEnv m0 d3 5520 [(reg m0 .r9, 8)] (fun _ ↦ 0)
          (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b27Offset + b27.length)).toBitVec).load 0 o 8 = x.toBitVec :=
      fun hw ↦ load_loc (hd3 ▸ hw)
    have wW4 : ∀ {o : Nat} {v : Sym}, o + 8 ≤ 5520 →
        (∀ t < 8, findWrite 0 (o + t) (after b27 cS).mem = some (v, t)) →
        NativeRustcVm.WordAt st4.data.dmem (loc m0 o) (UInt64.ofBitVec (v.eval
          (frameEnv m0 d3 5520 [(reg m0 .r9, 8)] (fun _ ↦ 0)
            (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b27Offset + b27.length)).toBitVec))) :=
      fun ho hw ↦ wordAt_write hm4' (r := 0) (b := fb m0) (sz := 5520 + 8) rfl (by omega) hw
    have w144 : NativeRustcVm.WordAt st4.data.dmem (loc m0 144) bf.c1 := by
      have := wW4 (o := 144) (by omega) (wr4.find (List.Mem.head _))
      rwa [show (Sym.load 0 688 8).eval (frameEnv m0 d3 5520 [(reg m0 .r9, 8)] (fun _ ↦ 0)
        (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b27Offset + b27.length)).toBitVec) = _ from ld4 hb1,
        UInt64.ofBitVec_toBitVec] at this
    have w152 : NativeRustcVm.WordAt st4.data.dmem (loc m0 152) bf.c0 := by
      have := wW4 (o := 152) (by omega) (wr4.find (List.Mem.tail _ (List.Mem.head _)))
      rwa [show (Sym.load 0 680 8).eval (frameEnv m0 d3 5520 [(reg m0 .r9, 8)] (fun _ ↦ 0)
        (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b27Offset + b27.length)).toBitVec) = _ from ld4 hb0,
        UInt64.ofBitVec_toBitVec] at this
    have cl4 : ClaimsWAt st4.data.dmem (reg m0 .r9) #[] := by
      have := wordAt_write hm4' (r := 1) (o := 0) (b := reg m0 .r9) (sz := 8) rfl (by omega)
        (v := .lit 0) (wr4'.find (List.mem_singleton.mpr rfl))
      rw [off_zero] at this
      exact ⟨by simp [claimCap], this, fun i h' ↦ absurd h' (by simp)⟩
    have hts4 : TStateAt st4.data.dmem (reg m0 .rdi) a s3 :=
      ts_keep h (hm4'.kept hwf4) hs4 (fun q hq ↦ hq.elim (fun h' ↦ .inl (frame_stack hS h'))
        fun h' ↦ .inr (.inr (inRange_mono h' (by rw [claimsBytes_eq]; omega))))
        (show TStateAt d3.dmem (reg m0 .rdi) a s3 by rw [hd3]; exact hts2)
    have kb : KeepIv baseIv m0 d.dmem st4.data.dmem :=
      kv0.trans (kv2.trans ((KeepIv.rfl' hd3).trans kv4))
    have kf : KeepIv [(160, 176)] m0 st1.data.dmem st4.data.dmem :=
      kf2.trans ((KeepIv.rfl' hd3).trans kf4)
    have base4 := A.base.of_keep kb
    have base3 := A.base.of_keep (kv0.trans (kv2.trans (KeepIv.rfl' hd3)))
    have sm4 : ShareMem m0 L w pt tv mem beta mf bf st4.data.dmem :=
      ShareMem.of_base base4
        (NativeRustcVm.Layout.WordAt.of_same w168
          (kf.sameIn (lo := 160) (hi := 176) (by simp) (by omega) (by omega)) le_rfl)
        (NativeRustcVm.Layout.WordAt.of_same w160
          (kf.sameIn (lo := 160) (hi := 176) (by simp) (by omega) (by omega)) le_rfl)
        w152 w144
    have mw0 := mem_words base3.hmem base3.msz (i := 0) (by omega)
    have w216 : NativeRustcVm.WordAt d3.dmem (loc m0 216) (mem.getD 0 0).c0 := mw0.1
    have w224 : NativeRustcVm.WordAt d3.dmem (loc m0 224) (mem.getD 0 0).c1 := mw0.2
    have g4 : ∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14], reg st4.data r = reg d r := fun r hr' ↦
      (hk4.reg hm4' hr').trans (g3 r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr' ⊢
        rcases hr' with h' | h' | h' | h' | h' <;> simp [h']))
    have x15 : reg st4.data .r15 = reg m0 .r9 := by
      rw [show reg st4.data .r15 = _ from hm4'.regs .r15 _ hr154]
      show reg m0 .r9 + BitVec.ofInt 64 0 = _
      rw [ofInt_zero64, BitVec.add_zero]
    simp only [PcOk] at hpc4
    refine pcCall h hpc fr4 hpc4 sm4 hts4 cl4 (by simp [claimCap])
      (by
        rw [show reg st4.data .rdi = _ from hm4'.regs .rdi _ hrdi4]
        show reg m0 .r9 + BitVec.ofInt 64 0 = _
        rw [ofInt_zero64, BitVec.add_zero])
      ((hm4'.regs .rdx _ hrdx4).trans (load_loc (hd3 ▸ (A.base.of_keep (kv0.trans kv2)).tail.w104)))
      lm ((hm4'.regs .rcx _ hrcx4).trans ((g3 .rbp (by simp)).trans A.xbp)) (id := 0)
      (v := mem.getD 0 0)
      (by rw [show reg st4.data .rsi = _ from hm4'.regs .rsi _ hrsi4]; rfl)
      (by
        rw [show reg st4.data .r8 = _ from hm4'.regs .r8 _ hr84,
          show reg st4.data .r9 = _ from hm4'.regs .r9 _ hr94]
        show ewArg ((frameEnv m0 d3 5520 [(reg m0 .r9, 8)] (fun _ ↦ 0)
            (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b27Offset + b27.length)).toBitVec).load 0 216 8)
          ((frameEnv m0 d3 5520 [(reg m0 .r9, 8)] (fun _ ↦ 0)
            (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b27Offset + b27.length)).toBitVec).load 0 224 8) = _
        rw [load_loc w216, load_loc w224]
        rfl)
      fun m5 fr5 sm5 hts5 hal5 hcl5 hcs5 ↦ ?_
    have r5 : ∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14], reg m5 r = reg d r := fun r hr' ↦
      (hcs5 r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
        rcases hr' with rfl | rfl | rfl | rfl | rfl <;> rfl)).trans (g4 r hr')
    have A5 : ClSt a L m0 w pt tv mem beta mf bf s3
        #[⟨LeanVM.Protocol.Verifier.memory0, pt.extract 0 L.logMemory, mem.getD 0 0⟩] m5 :=
      ⟨fr5, sm5, (r5 .rbx (by simp)).trans A.xbx, (r5 .r13 (by simp)).trans A.x13,
        (r5 .r14 (by simp)).trans A.x14, ((hcs5 .r15 rfl).trans x15),
        (r5 .rbp (by simp)).trans A.xbp, (r5 .r12 (by simp)).trans A.x12, hts5, hcl5⟩
    rw [show k + NativeRustcVmX64.Vm.VerifyBusBalance.b27Offset + b27.length = k + NativeRustcVmX64.Vm.VerifyBusBalance.b28Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyBusBalance.b27_next]]
    exact claimsB_spec hp h hpc hbs hcbv hkp hfc hacc hext (by rw [hrun, hr]; rfl) A5 hal5

end

end NativeRustcVmX64.Bus.VerifyBusBalance
