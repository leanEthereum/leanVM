module

public import NativeRustcVmX64.Bus.VerifyBusBalance.ClaimsPre
public import NativeRustcVmX64.Code.Vm.BitLength.Names
public import NativeRustcVmX64.Code.Vm.Memcpy.Names
public import NativeRustcVmX64.Code.Vm.SpongeWSqueeze.Names
public import NativeRustcVmX64.Code.Vm.TStateGrind.Names
public import NativeRustcVmX64.Code.Vm.TStateSampleChallenges.Names
public import NativeRustcVmX64.Code.Vm.VerifyGkrGrandProducts.Names

/-!
# `verify_bus_balance`'s grind, challenges and GKR walk (x86-64)

`AtGrind`: the state at `b9` (`k + NativeRustcVmX64.Vm.VerifyBusBalance.b9Offset`), the three layouts built. `b9` checks the push side's
depth; `b10` calls `bit_length` of its mask; `b11` grinds; `b12` checks it; `b13` samples the `16`
weights; `b14` squeezes `β`; `b15` keeps `β`; `b16` zeroes the point's buffer (`21` rounds); `b17`
copies it into the `GkrStateW`; `b18` calls `verify_gkr_grand_products`; `b19`, `b20` check its
count root (`grind_spec`, then `scal_spec`).
-/

namespace NativeRustcVmX64.Bus.VerifyBusBalance

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.VerifyBusBalance
open NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck NativeRustcVmX64.Bus.Gkr
open NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Bus NativeRustcVm.Layout

public section

/-- **The state at `b9`.** -/
structure AtGrind (a : DecArea) (s0 : TState) (L : LayoutW) (m0 : MachineData) (d : MachineData) :
    Prop where
  fr : St m0 104 d
  w112 : NativeRustcVm.WordAt d.dmem (loc m0 112) (UInt64.ofBitVec (reg m0 .r8))
  push : BusLayoutWAt d.dmem (loc m0 2808) (pushL L)
  pull : BusLayoutWAt d.dmem (loc m0 3696) (pullL L)
  count : BusLayoutWAt d.dmem (loc m0 4584) (countL L)
  w128 : NativeRustcVm.WordAt d.dmem (loc m0 128) (UInt64.ofBitVec (reg m0 .rdx))
  w136 : NativeRustcVm.WordAt d.dmem (loc m0 136) (UInt64.ofBitVec (reg m0 .rcx))
  xbx : reg d .rbx = reg m0 .rdi
  x12 : reg d .r12 = (pushL L).depth.toUInt64.toBitVec
  x13 : reg d .r13 = L.logBytecode.toUInt64.toBitVec
  x14 : reg d .r14 = reg m0 .rsi
  x15 : reg d .r15 = reg m0 .r9
  xbp : reg d .rbp = L.logMemory.toUInt64.toBitVec
  ts : TStateAt d.dmem (reg m0 .rdi) a s0

/-- The grind's bit count as `b11` computes it from the bit length `d`. -/
theorem grind_bits {x : BitVec 64} {d : Nat} (hx : x.toNat = d) (hd : d < 64) :
    (if (!CmpOp.apply .ult .W32 x (BitVec.ofNat 64 3)) = true then
      BinOp.apply .sub .W32 x (BitVec.ofNat 64 3) else BitVec.ofNat 64 0).toNat % 2 ^ 32 =
        d - 3 := by
  have hl : (low .W32 x).toNat = d := by
    simp only [low, Width.bits, BitVec.toNat_setWidth, hx, Nat.reducePow]
    omega
  have h3 : (low .W32 (BitVec.ofNat 64 3)).toNat = 3 := rfl
  have hc : CmpOp.apply .ult .W32 x (BitVec.ofNat 64 3) = decide (d < 3) := by
    show decide ((low .W32 x).toNat < (low .W32 (BitVec.ofNat 64 3)).toNat) = _
    rw [hl, h3]
  rw [hc]
  by_cases h : d < 3
  · simp only [h, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte, BitVec.toNat_ofNat]
    omega
  · simp only [h, decide_false, Bool.not_false, ↓reduceIte]
    show ((low .W32 x - low .W32 (BitVec.ofNat 64 3)).setWidth 64).toNat % 2 ^ 32 = d - 3
    rw [BitVec.toNat_setWidth, BitVec.toNat_sub, hl, h3]
    simp only [Width.bits, Nat.reducePow]
    omega

/-- The count root's test (`b20`): its limbs' `or` is `0` when it is `0`. -/
theorem or_eq0 (c : EW) :
    CmpOp.apply .eq .W64 (BinOp.apply .or .W64 c.c1.toBitVec c.c0.toBitVec)
      (BitVec.ofNat 64 0) = (c == 0) := by
  obtain ⟨x, y⟩ := c
  simp only [CmpOp.apply, BinOp.apply, low_W64, ext_W64]
  rw [show ((⟨x, y⟩ : EW) == 0) = (x == 0 && y == 0) from rfl]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, Bool.and_eq_true]
  rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.or_eq_zero_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨UInt64.toBitVec_inj.mp h2, UInt64.toBitVec_inj.mp h1⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩

end

public section
variable [Host] {a : DecArea} {s0 : TState} {L : LayoutW} {m0 : MachineData} {k : Nat}

/-- The locals the GKR walk's head keeps. -/
abbrev gIv : List (Nat × Nat) := [(112, 120), (128, 144), (176, 192), (368, 624), (2808, 5472)]

/-- A state of the point buffer's zeroing loop. -/
theorem match_l1 {d : MachineData} (fr : St m0 104 d) {i : Nat}
    (hrax : reg d .rax = BitVec.ofNat 64 (40 + 48 * i)) {ret : BitVec 64} :
    Match (frameEnv m0 d 5520 [] (fun _ ↦ 0) ret) (l1S i) d :=
  match_ofMachine ⟨rfl, trivial⟩ ⟨fr.frame.rsp_eval, hrax, trivial⟩ trivial trivial trivial

/-- **The point buffer's zeroing**, from round `i` (`NativeRustcVmX64.Vm.VerifyBusBalance.label_6`, `k + NativeRustcVmX64.Vm.VerifyBusBalance.b16Offset`). -/
theorem loop16_spec (hp : Placed code k) (h : VerifyBusBalancePre a s0 L m0) {d0 : Mem 64}
    {R0 : MachineData} {s : TState}
    (cont : ∀ d, St m0 104 d → KeepIv gIv m0 d0 d.dmem → (∀ r ∈ clRegs, reg d r = reg R0 r) →
      TStateAt d.dmem (reg m0 .rdi) a s →
      Eventually (step1 Host.exe) (Goal a s0 L m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b17Offset)⟩) :
    ∀ n i, i + n = 20 → ∀ d, St m0 104 d → KeepIv gIv m0 d0 d.dmem →
      (∀ r ∈ clRegs, reg d r = reg R0 r) → TStateAt d.dmem (reg m0 .rdi) a s →
      reg d .rax = BitVec.ofNat 64 (40 + 48 * i) →
      Eventually (step1 Host.exe) (Goal a s0 L m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b16Offset)⟩ := by
  have hS := pre_stack h
  intro n
  induction n with
  | zero =>
    intro i hi d fr hk hr hts hrax
    obtain ⟨S, hx, hmid, hw, -, hks, -⟩ := of_ok16 (ok16_all i (by omega))
    have hwf := wf0 h fr.frame.kept (vars := fun _ ↦ 0) (ret := 0)
    refine exec_then (infix_of b16_in_code (by simp [b16]) hp) hx hwf nofun (match_l1 fr hrax)
      fun st1 hm1 hpc1 ↦ ?_
    have fr1 : St m0 104 st1.data := St.blk fr hS hwf hm1 hmid fun q hq ↦ wr0 hS hw (by omega) hq
    have hs1 := blk_same hS hwf hm1 hw (by omega)
    have k1 : KeepIv gIv m0 d.dmem st1.data.dmem := keepIv_block hwf hm1 (writesIn_of_mid hmid)
      (lo := 672) (hi := 1728) (fun w hw' hr ↦ by have := hw w hw'; omega) (by decide) (by decide)
    simp only [PcOk, SBool.eval, show i = 20 by omega, decide_true, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte] at hpc1
    exact at_pc (hpc1.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.VerifyBusBalance.b16_next)) (cont st1.data fr1
      (hk.trans k1) (fun r hr' ↦ (hks.reg hm1 (clRegs_cs r hr').2.1).trans (hr r hr'))
      (ts_keep h (hm1.kept hwf) hs1 (fun q hq ↦ .inl (frame_stack hS hq)) hts))
  | succ n ih =>
    intro i hi d fr hk hr hts hrax
    obtain ⟨S, hx, hmid, hw, -, hks, hra⟩ := of_ok16 (ok16_all i (by omega))
    have hwf := wf0 h fr.frame.kept (vars := fun _ ↦ 0) (ret := 0)
    refine exec_then (infix_of b16_in_code (by simp [b16]) hp) hx hwf nofun (match_l1 fr hrax)
      fun st1 hm1 hpc1 ↦ ?_
    have fr1 : St m0 104 st1.data := St.blk fr hS hwf hm1 hmid fun q hq ↦ wr0 hS hw (by omega) hq
    have hs1 := blk_same hS hwf hm1 hw (by omega)
    have k1 : KeepIv gIv m0 d.dmem st1.data.dmem := keepIv_block hwf hm1 (writesIn_of_mid hmid)
      (lo := 672) (hi := 1728) (fun w hw' hr ↦ by have := hw w hw'; omega) (by decide) (by decide)
    have hne : decide (i = 20) = false := by simp only [decide_eq_false_iff_not]; omega
    simp only [PcOk, SBool.eval, hne, Bool.not_false, ↓reduceIte] at hpc1
    refine at_pc (hpc1.trans (hp.label (label_of_infix b16_in_code rfl)))
      (ih (i + 1) (by omega) st1.data fr1 (hk.trans k1)
        (fun r hr' ↦ (hks.reg hm1 (clRegs_cs r hr').2.1).trans (hr r hr'))
        (ts_keep h (hm1.kept hwf) hs1 (fun q hq ↦ .inl (frame_stack hS hq)) hts) ?_)
    rw [show reg st1.data .rax = _ from hm1.regs .rax _ hra]
    show BitVec.ofNat 64 (88 + 48 * i) = _
    congr 1
    omega

/-- **The grind, the challenges, the GKR walk** (`b9`, `k + NativeRustcVmX64.Vm.VerifyBusBalance.b9Offset`). -/
theorem grind_spec (hp : Placed code k) (h : VerifyBusBalancePre a s0 L m0)
    (hmc : Spec (Labels.label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hbit : Spec (Labels.label NativeRustcVmX64.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost)
    (hgr : ∀ s, Spec (Labels.label NativeRustcVmX64.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    (hsc : ∀ s, Spec (Labels.label NativeRustcVmX64.Vm.TStateSampleChallenges.entryLabel) (SampleChallengesPre a s)
      (SampleChallengesPost a s))
    (hsq : ∀ sp, Spec (Labels.label NativeRustcVmX64.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp))
    (hgkr : ∀ s, Spec (Labels.label NativeRustcVmX64.Vm.VerifyGkrGrandProducts.entryLabel) (VerifyGkrPre a s) (VerifyGkrPost a s))
    (hsc' : ∀ w pt tv beta s d, AtScal a s0 L m0 w pt tv beta s d →
      Eventually (step1 Host.exe) (Goal a s0 L m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b21Offset)⟩)
    {d : MachineData} (A : AtGrind a s0 L m0 d) :
    Eventually (step1 Host.exe) (Goal a s0 L m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b9Offset)⟩ := by
  have hS := pre_stack h
  have hrun := vbb_run L s0
  have hdl : (pushL L).depth < 2 ^ 64 := A.push.depth_lt
  have ndep : (pushL L).depth.toUInt64.toBitVec.toNat = (pushL L).depth := by
    rw [UInt64.toNat_toBitVec]
    exact UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)
  -- `b9`: the push side's depth below `64`.
  have hc9 : SBool.eval (frameEnv m0 d 5520 [] (fun _ ↦ 0) 0)
      (.not (.cmp .ult .W64 (.reg .r12) (.lit 64))) = !decide ((pushL L).depth < 64) := by
    show (!CmpOp.apply .ult .W64 (reg d .r12) (BitVec.ofNat 64 64)) = _
    rw [A.x12]
    simp only [CmpOp.apply, low_W64, ult_toNat, ndep, BitVec.toNat_ofNat, Nat.reducePow,
      Nat.reduceMod]
  refine test_spec hp h (j := NativeRustcVmX64.Vm.VerifyBusBalance.b9Offset) (n := b9.length) (infix_of b9_in_code (by simp [b9]) hp) rfl exit_b9
    ok_b9 A.fr (fun hc ↦ ?_) fun d1 fr1 hd1 hk1 hc ↦ ?_
  · rw [hc9] at hc
    have : ¬ (pushL L).depth < 64 := by simpa using hc
    rw [hrun]
    simp [this]
  rw [hc9] at hc
  have hdep : (pushL L).depth < 64 := by simpa using hc
  simp only [hdep, ↓reduceIte, busGrindingBits_eq] at hrun
  have g1 : ∀ r ∈ clRegs, reg d1 r = reg d r := fun r hr' ↦ hk1 r (clRegs_cs r hr').2.2
  have x12 : reg d1 .r12 = (pushL L).depth.toUInt64.toBitVec := (g1 .r12 (by simp)).trans A.x12
  have hd12 : (reg d1 .r12).toNat < 64 := by rw [x12, ndep]; exact hdep
  -- the frame's ranges apart from the kept intervals
  have notX : ∀ {o n : Nat}, o + n ≤ 5520 → ∀ {ivs : List (Nat × Nat)},
      ivs.all (fun p ↦ decide (p.2 ≤ 5472)) = true →
      ivs.all (fun p ↦ decide (p.2 ≤ o) || decide (o + n ≤ p.1)) = true → ∀ j, InIv ivs j →
      ¬ NativeRustcVm.InRange (loc m0 o) n (loc m0 j) := fun {_ _} hon {_} hlt hap j hj hq ↦ by
    have hj5 := inIv_lt hlt hj
    exact loc_notIn hS (j := j) (by omega) (by omega) (inIv_apart hap hj) hq
  have notT : ∀ {ivs : List (Nat × Nat)}, ivs.all (fun p ↦ decide (p.2 ≤ 5472)) = true →
      ∀ j, InIv ivs j → ¬ NativeRustcVm.InRange (reg m0 .rdi) tstateBytes (loc m0 j) :=
    fun {_} hlt j hj hq ↦ by
      have hj5 := inIv_lt hlt hj
      exact not_loc hS (pre_tok h).1 (pre_ts h).footprint.1.2 (j := j) (l := 1) (by omega) hq
        (loc_inR hS (by omega) (by omega) (by omega))
  -- `b10`: `bit_length` of the push side's mask.
  rw [show k + NativeRustcVmX64.Vm.VerifyBusBalance.b9Offset + b9.length = k + NativeRustcVmX64.Vm.VerifyBusBalance.b10Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyBusBalance.b9_next]]
  have hwf2 := wf0 h fr1.frame.kept (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b10Offset + b10.length)).toBitVec)
  refine exec_then (infix_of b10_in_code (by simp [b10]) hp) exit_b10 hwf2 (fun _ _ ↦ rfl)
    (match_fS fr1) fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨hmid2, hw2, hrdi2, hk2⟩ := ok_b10
  have fr2 : St m0 96 st2.data := St.blk fr1 hS hwf2 hm2 hmid2 fun q hq ↦ wr0 hS hw2 (by omega) hq
  have hs2 := blk_same hS hwf2 hm2 hw2 (by omega)
  have hsp2 : rspOf st2.data = loc m0 96 := fr2.frame.sp
  have kA2 : KeepIv [(112, 120), (128, 144), (2808, 5472)] m0 d1.dmem st2.data.dmem :=
    keepIv_block' hwf2 hm2 (writesIn_of_mid hmid2) (by decide) (by decide +kernel)
  have ts2 := ts_keep h (hm2.kept hwf2) hs2 (fun q hq ↦ .inl (frame_stack hS hq))
    (show TStateAt d1.dmem (reg m0 .rdi) a s0 by rw [hd1]; exact A.ts)
  have r2 : ∀ r ∈ clRegs, reg st2.data r = reg d r := fun r hr' ↦
    (hk2.reg hm2 (clRegs_cs r hr').2.1).trans (g1 r hr')
  have x2di : (reg st2.data .rdi).toNat = 2 ^ (pushL L).depth - 1 := by
    rw [show reg st2.data .rdi = _ from hm2.regs .rdi _ hrdi2]
    have := mask_toNat hd12
    rw [x12, ndep] at this
    rw [← this, ← x12]
    rfl
  have hle2 : 5520 - 96 + bitLengthStack ≤ NN := le_len
  simp only [PcOk] at hpc2
  refine callF h (c := 96) (Nc := bitLengthStack) (lo := 0) (len := 0) (X := fun _ ↦ False)
    (by omega) hle2 (by omega) (fun _ hq ↦ hq.elim) hbit fr2 hpc2 (cal_stack h fr2 (by omega) hle2)
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun _ h' ↦ .inl h', hq.2.2⟩)
    fun m3 fr3 hq3 hs3 hcs3 ↦ ?_
  have x3ax : (reg m3 .rax).toNat = (pushL L).depth := by
    rw [hq3.1, x2di, bitLength_mask]
  have kA3 : KeepIv [(112, 120), (128, 144), (2808, 5472)] m0 st2.data.dmem m3.dmem :=
    keepIv_call hS hsp2 (by omega) hle2 hs3 (by decide) (by decide) fun _ _ h' ↦ h'
  have ts3 := ts_keep h hq3.2.2.2 hs3 (fun q hq ↦ hq.elim
    (fun h' ↦ .inl (callee_stack hS hsp2 (by omega) hle2 h')) False.elim) ts2
  have r3 : ∀ r ∈ clRegs, reg m3 r = reg d r := fun r hr' ↦
    (hcs3 r (clRegs_cs r hr').1).trans (r2 r hr')
  -- `b11`: the grind of `depth - 3` bits.
  rw [show k + NativeRustcVmX64.Vm.VerifyBusBalance.b10Offset + b10.length = k + NativeRustcVmX64.Vm.VerifyBusBalance.b11Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyBusBalance.b10_next]]
  have hwf4 := wf0 h fr3.frame.kept (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b11Offset + b11.length)).toBitVec)
  refine exec_then (infix_of b11_in_code (by simp [b11]) hp) exit_b11 hwf4 (fun _ _ ↦ rfl)
    (match_fS fr3) fun st4 hm4 hpc4 ↦ ?_
  obtain ⟨hmid4, hw4, hrsi4, hrdi4, hk4⟩ := ok_b11
  have fr4 : St m0 96 st4.data := St.blk fr3 hS hwf4 hm4 hmid4 fun q hq ↦ wr0 hS hw4 (by omega) hq
  have hs4 := blk_same hS hwf4 hm4 hw4 (by omega)
  have hsp4 : rspOf st4.data = loc m0 96 := fr4.frame.sp
  have kA4 : KeepIv [(112, 120), (128, 144), (2808, 5472)] m0 m3.dmem st4.data.dmem :=
    keepIv_block' hwf4 hm4 (writesIn_of_mid hmid4) (by decide) (by decide +kernel)
  have ts4 := ts_keep h (hm4.kept hwf4) hs4 (fun q hq ↦ .inl (frame_stack hS hq)) ts3
  have r4 : ∀ r ∈ clRegs, reg st4.data r = reg d r := fun r hr' ↦
    (hk4.reg hm4 (clRegs_cs r hr').2.1).trans (r3 r hr')
  have x4di : reg st4.data .rdi = reg m0 .rdi :=
    (hm4.regs .rdi _ hrdi4).trans ((r3 .rbx (by simp)).trans A.xbx)
  have g4 : grindBits st4.data = (pushL L).depth - 3 := by
    unfold grindBits
    rw [show reg st4.data .rsi = _ from hm4.regs .rsi _ hrsi4]
    exact grind_bits (x := reg m3 .rax) x3ax hdep
  have hle4 : 5520 - 96 + grindStack ≤ NN := le_grind
  simp only [PcOk] at hpc4
  refine callF h (c := 96) (Nc := grindStack) (lo := 0) (len := 0)
    (X := NativeRustcVm.InRange (reg m0 .rdi) tstateBytes) (by omega) hle4 (by omega)
    (fun q hq ↦ .inl (.inl hq)) (hgr s0) fr4 hpc4 ?_
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.1 fun q hq' ↦ by
      rw [x4di] at hq'; exact hq'.elim .inr .inl, hq.2.2.2⟩)
    fun m5 fr5 hq5 hs5 hcs5 ↦ ?_
  · unfold GrindPre
    rw [x4di, g4]
    refine ⟨cal_stack h fr4 (by omega) hle4, cal_rc h fr4 (by omega) hle4, ts4,
      cal_tok h fr4 (by omega) hle4, by omega, cal_got h fr4 (by omega) hle4 (by decide) ?_⟩
    intro l hl b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;>
      exact ((pre_got h).1 l hl).2.2.2 _ (by simp)
  obtain ⟨hal5, hnx5, -, hsv5⟩ := hq5
  rw [g4] at hal5 hnx5
  rw [x4di] at hnx5
  have kA5 : KeepIv [(112, 120), (128, 144), (2808, 5472)] m0 st4.data.dmem m5.dmem :=
    keepIv_call hS hsp4 (by omega) hle4 hs5 (by decide) (by decide) (notT (by decide))
  have r5 : ∀ r ∈ clRegs, reg m5 r = reg d r := fun r hr' ↦
    (hcs5 r (clRegs_cs r hr').1).trans (r4 r hr')
  -- `b12`: the grind's result.
  rw [show k + NativeRustcVmX64.Vm.VerifyBusBalance.b11Offset + b11.length = k + NativeRustcVmX64.Vm.VerifyBusBalance.b12Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyBusBalance.b11_next]]
  cases hr1 : (grind ((pushL L).depth - 3)).run s0 with
  | none =>
    rw [hr1] at hal5
    refine test_spec hp h (j := NativeRustcVmX64.Vm.VerifyBusBalance.b12Offset) (n := b12.length) (infix_of b12_in_code (by simp [b12]) hp) rfl
      exit_b12 ok_b12 fr5 (fun _ ↦ by rw [hrun, hr1]; rfl) fun _ _ _ _ hc ↦ ?_
    rw [alZ_true (show boolRet m5 = 0 from hal5)] at hc
    cases hc
  | some y1 =>
  obtain ⟨u1, s1⟩ := y1
  rw [hr1] at hal5
  rw [hr1, Option.bind_some] at hrun
  have ts5 := hnx5 _ _ hr1
  refine test_spec hp h (j := NativeRustcVmX64.Vm.VerifyBusBalance.b12Offset) (n := b12.length) (infix_of b12_in_code (by simp [b12]) hp) rfl
    exit_b12 ok_b12 fr5 (fun hc ↦ by rw [alZ_false (show boolRet m5 = 1 from hal5)] at hc; cases hc)
    fun d6 fr6 hd6 hk6 _ ↦ ?_
  have r6 : ∀ r ∈ clRegs, reg d6 r = reg d r := fun r hr' ↦
    (hk6 r (clRegs_cs r hr').2.2).trans (r5 r hr')
  -- `b13`: `sample_challenges(t, 368, 16)`.
  rw [show k + NativeRustcVmX64.Vm.VerifyBusBalance.b12Offset + b12.length = k + NativeRustcVmX64.Vm.VerifyBusBalance.b13Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyBusBalance.b12_next]]
  have hwf7 := wf0 h fr6.frame.kept (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b13Offset + b13.length)).toBitVec)
  refine exec_then (infix_of b13_in_code (by simp [b13]) hp) exit_b13 hwf7 (fun _ _ ↦ rfl)
    (match_fS fr6) fun st7 hm7 hpc7 ↦ ?_
  obtain ⟨hmid7, hw7, hrdi7, hrsi7, hrdx7, hk7⟩ := ok_b13
  have fr7 : St m0 96 st7.data := St.blk fr6 hS hwf7 hm7 hmid7 fun q hq ↦ wr0 hS hw7 (by omega) hq
  have hs7 := blk_same hS hwf7 hm7 hw7 (by omega)
  have hsp7 : rspOf st7.data = loc m0 96 := fr7.frame.sp
  have kA7 : KeepIv [(112, 120), (128, 144), (2808, 5472)] m0 d6.dmem st7.data.dmem :=
    keepIv_block' hwf7 hm7 (writesIn_of_mid hmid7) (by decide) (by decide +kernel)
  have ts7 := ts_keep h (hm7.kept hwf7) hs7 (fun q hq ↦ .inl (frame_stack hS hq))
    (show TStateAt d6.dmem (reg m0 .rdi) a s1 by rw [hd6]; exact ts5)
  have r7 : ∀ r ∈ clRegs, reg st7.data r = reg d r := fun r hr' ↦
    (hk7.reg hm7 (clRegs_cs r hr').2.1).trans (r6 r hr')
  have x7di : reg st7.data .rdi = reg m0 .rdi :=
    (hm7.regs .rdi _ hrdi7).trans ((r6 .rbx (by simp)).trans A.xbx)
  have x7si : reg st7.data .rsi = loc m0 368 := (hm7.regs .rsi _ hrsi7).trans (eval_ptr0 368)
  have x7dx : (reg st7.data .rdx).toNat = 16 := by
    rw [show reg st7.data .rdx = _ from hm7.regs .rdx _ hrdx7]; rfl
  have hle7 : 5520 - 96 + sampleChallengesStack ≤ NN := le_samp
  simp only [PcOk] at hpc7
  refine callF h (c := 96) (Nc := sampleChallengesStack) (lo := 368) (len := 256)
    (X := fun q ↦ NativeRustcVm.InRange (loc m0 368) 256 q ∨
      NativeRustcVm.InRange (reg m0 .rdi) tstateBytes q) (by omega) hle7 (by omega)
    (fun q hq ↦ hq.elim .inr fun h' ↦ .inl (.inl h')) (hsc s1) fr7 hpc7 ?_
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun q hq' ↦ by
      rw [x7di, x7si, x7dx] at hq'
      rcases hq' with hq' | hq' | hq'
      · exact .inr (.inl hq')
      · exact .inr (.inr hq')
      · exact .inl hq', hq.2.2⟩)
    fun m8 fr8 hq8 hs8 hcs8 ↦ ?_
  · unfold SampleChallengesPre
    rw [x7di, x7si, x7dx]
    refine ⟨cal_stack h fr7 (by omega) hle7, cal_rc h fr7 (by omega) hle7, ts7,
      cal_tok h fr7 (by omega) hle7, cal_local h fr7 (by omega) hle7 (by omega) (by omega),
      cal_got h fr7 (by omega) hle7 (by decide) ?_⟩
    intro l hl b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact ((pre_got h).1 l hl).2.2.2 _ (by simp)
    · exact ((pre_got h).1 l hl).2.2.2 _ (by simp)
    · exact got_apart_frame (pre_got h) hS hl N_ge (by omega)
    · exact ((pre_got h).1 l hl).2.2.2 _ (by simp)
  obtain ⟨⟨w, s2, hr2, hw8, ts8⟩, -, hsv8⟩ := hq8
  rw [x7si] at hw8
  rw [x7di] at ts8
  rw [x7dx] at hr2
  rw [hr2, Option.bind_some] at hrun
  rw [show sampleChallenge.run s2 =
    some (s2.sponge.squeeze.1, { s2 with sponge := s2.sponge.squeeze.2 }) from rfl,
    Option.bind_some] at hrun
  have hwsz : w.size = 16 := NativeRustcVm.Transcript.pushes_size
    (show (pushes sampleChallenge 16).run s1 = some (w, s2) from hr2)
  have kA8 : KeepIv [(112, 120), (128, 144), (2808, 5472)] m0 st7.data.dmem m8.dmem :=
    keepIv_call hS hsp7 (by omega) hle7 hs8 (by decide) (by decide) fun j hj hq ↦
      hq.elim (notX (by omega) (by decide) (by decide) j hj) (notT (by decide) j hj)
  have r8 : ∀ r ∈ clRegs, reg m8 r = reg d r := fun r hr' ↦
    (hcs8 r (clRegs_cs r hr').1).trans (r7 r hr')
  -- `b14`: `β`, squeezed.
  rw [show k + NativeRustcVmX64.Vm.VerifyBusBalance.b13Offset + b13.length = k + NativeRustcVmX64.Vm.VerifyBusBalance.b14Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyBusBalance.b13_next]]
  have hwf9 := wf0 h fr8.frame.kept (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b14Offset + b14.length)).toBitVec)
  refine exec_then (infix_of b14_in_code (by simp [b14]) hp) exit_b14 hwf9 (fun _ _ ↦ rfl)
    (match_fS fr8) fun st9 hm9 hpc9 ↦ ?_
  obtain ⟨hmid9, hw9, hrdi9, hk9⟩ := ok_b14
  have fr9 : St m0 96 st9.data := St.blk fr8 hS hwf9 hm9 hmid9 fun q hq ↦ wr0 hS hw9 (by omega) hq
  have hs9 := blk_same hS hwf9 hm9 hw9 (by omega)
  have hsp9 : rspOf st9.data = loc m0 96 := fr9.frame.sp
  have kA9 : KeepIv [(112, 120), (128, 144), (2808, 5472)] m0 m8.dmem st9.data.dmem :=
    keepIv_block hwf9 hm9 (writesIn_of_mid hmid9) (W0.reg0 hw9) (by decide) (by decide)
  have kW9 : KeepIv [(368, 624)] m0 m8.dmem st9.data.dmem :=
    keepIv_block hwf9 hm9 (writesIn_of_mid hmid9) (W0.reg0 hw9) (by decide) (by decide)
  have ts9 := ts_keep h (hm9.kept hwf9) hs9 (fun q hq ↦ .inl (frame_stack hS hq)) ts8
  have r9 : ∀ r ∈ clRegs, reg st9.data r = reg d r := fun r hr' ↦
    (hk9.reg hm9 (clRegs_cs r hr').2.1).trans (r8 r hr')
  have x9di : reg st9.data .rdi = reg m0 .rdi :=
    (hm9.regs .rdi _ hrdi9).trans ((r8 .rbx (by simp)).trans A.xbx)
  have hle9 : 5520 - 96 + squeezeStack ≤ NN := le_sq
  have htok9 := cal_tok h fr9 (by omega) hle9
  have hfp := ts9.footprint
  have hpre9 : SqueezePre s2.sponge st9.data := by
    unfold SqueezePre
    rw [x9di]
    have h1 : (reg m0 .rdi).toNat + 760 ≤ (stackBelow st9.data squeezeStack).toNat ∨
        (stackBelow st9.data squeezeStack).toNat + (squeezeStack + 8) ≤ (reg m0 .rdi).toNat :=
      htok9.1
    have h2 : (reg m0 .rdi).toNat + 760 ≤ rcAddr.toNat ∨ rcAddr.toNat + 192 ≤ (reg m0 .rdi).toNat :=
      htok9.2.2
    have hnw : (reg m0 .rdi).toNat + 760 ≤ 2 ^ 64 := hfp.1.2
    refine ⟨cal_stack h fr9 (by omega) hle9, cal_rc h fr9 (by omega) hle9,
      ⟨fun j hj ↦ hfp.1.1 j (by simp only [spongeBytes] at hj; show j < 760; omega), ?_, ?_, ?_⟩,
      ts9.sponge, ?_⟩
    · show (reg m0 .rdi).toNat + 328 ≤ 2 ^ 64; omega
    · show (reg m0 .rdi).toNat + 328 ≤ _ ∨ _ ≤ (reg m0 .rdi).toNat; omega
    · show (reg m0 .rdi).toNat + 328 ≤ _ ∨ _ ≤ (reg m0 .rdi).toNat; omega
    · apply cal_got h fr9 (by omega) hle9 (by decide)
      intro l hl b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · exact NativeRustcVm.Apart.mono_right
          (((pre_got h).1 l hl).2.2.2 (reg m0 .rdi, tstateBytes) (by simp))
          (Nat.le_refl _) (by dsimp only [Prod.fst, Prod.snd, spongeBytes, tstateBytes]; omega)
      · exact ((pre_got h).1 l hl).2.2.2 _ (by simp)
  have hR : ∀ q, NativeRustcVm.InRange (reg m0 .rdi) spongeBytes q →
      NativeRustcVm.InRange (reg m0 .rdi) tstateBytes q := fun q hq ↦ inRange_mono hq (by decide)
  simp only [PcOk] at hpc9
  refine callF h (c := 96) (Nc := squeezeStack) (lo := 0) (len := 0)
    (X := NativeRustcVm.InRange (reg m0 .rdi) spongeBytes) (by omega) hle9 (by omega)
    (fun q hq ↦ .inl (.inl (hR q hq))) (hsq s2.sponge) fr9 hpc9 hpre9
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.2.1 fun q hq' ↦ by
      rw [x9di] at hq'; exact hq'.elim .inr .inl, hq.2.2.2.2⟩)
    fun m10 fr10 hq10 hs10 hcs10 ↦ ?_
  obtain ⟨hax10, hdx10, hsp10, -, hsv10⟩ := hq10
  rw [x9di] at hsp10
  have ts10 : TStateAt m10.dmem (reg m0 .rdi) a { s2 with sponge := s2.sponge.squeeze.2 } := by
    refine ts9.with_sponge hsv10.2 (R := NativeRustcVm.InRange (stackBelow st9.data squeezeStack)
      squeezeStack) (fun q hq ↦ (ctx h).stack_not_t (callee_stack hS hsp9 (by omega) hle9 hq))
      (fun q hq ↦ hs10 q ?_) hsp10
    rintro (h' | h')
    · exact hq (.inr h')
    · obtain ⟨j, hj, hw, hq'⟩ := touch_of_inRange (o := 0) (n := spongeBytes) hfp.1.2
        (by show 0 + 328 ≤ 760; omega) (by rwa [off_zero])
      exact hq (.inl ⟨j, hj, hw.2, hq'⟩)
  have notS : ∀ {ivs : List (Nat × Nat)}, ivs.all (fun p ↦ decide (p.2 ≤ 5472)) = true →
      ∀ j, InIv ivs j → ¬ NativeRustcVm.InRange (reg m0 .rdi) spongeBytes (loc m0 j) :=
    fun hlt j hj hq ↦ notT hlt j hj (hR _ hq)
  have kA10 : KeepIv [(112, 120), (128, 144), (2808, 5472)] m0 st9.data.dmem m10.dmem :=
    keepIv_call hS hsp9 (by omega) hle9 hs10 (by decide) (by decide) (notS (by decide))
  have kW10 : KeepIv [(368, 624)] m0 st9.data.dmem m10.dmem :=
    keepIv_call hS hsp9 (by omega) hle9 hs10 (by decide) (by decide) (notS (by decide))
  have r10 : ∀ r ∈ clRegs, reg m10 r = reg d r := fun r hr' ↦
    (hcs10 r (clRegs_cs r hr').1).trans (r9 r hr')
  -- `b15`: `β` at `176`, `184`.
  rw [show k + NativeRustcVmX64.Vm.VerifyBusBalance.b14Offset + b14.length = k + NativeRustcVmX64.Vm.VerifyBusBalance.b15Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyBusBalance.b14_next]]
  have hwf11 := wf0 h fr10.frame.kept (vars := fun _ ↦ 0) (ret := 0)
  refine exec_then (infix_of b15_in_code (by simp [b15]) hp) exit_b15 hwf11 nofun
    (match_fS fr10) fun st11 hm11 hpc11 ↦ ?_
  obtain ⟨hmid11, hw11, wr11, hrax11, hk11⟩ := ok_b15
  have fr11 : St m0 104 st11.data :=
    St.blk fr10 hS hwf11 hm11 hmid11 fun q hq ↦ wr0 hS hw11 (by omega) hq
  have hs11 := blk_same hS hwf11 hm11 hw11 (by omega)
  have kA11 : KeepIv [(112, 120), (128, 144), (2808, 5472)] m0 m10.dmem st11.data.dmem :=
    keepIv_block hwf11 hm11 (writesIn_of_mid hmid11) (W0.reg0 hw11) (by decide) (by decide)
  have kW11 : KeepIv [(368, 624)] m0 m10.dmem st11.data.dmem :=
    keepIv_block hwf11 hm11 (writesIn_of_mid hmid11) (W0.reg0 hw11) (by decide) (by decide)
  have ts11 := ts_keep h (hm11.kept hwf11) hs11 (fun q hq ↦ .inl (frame_stack hS hq)) ts10
  have r11 : ∀ r ∈ clRegs, reg st11.data r = reg d r := fun r hr' ↦
    (hk11.reg hm11 (clRegs_cs r hr').2.1).trans (r10 r hr')
  have wW11 : ∀ {o : Nat} {v : Sym}, o + 8 ≤ 5520 →
      (∀ t < 8, findWrite 0 (o + t) (after b15 (fS 104)).mem = some (v, t)) →
      NativeRustcVm.WordAt st11.data.dmem (loc m0 o) (UInt64.ofBitVec (v.eval
        (frameEnv m0 m10 5520 [] (fun _ ↦ 0) 0))) :=
    fun ho hw ↦ wordAt_write hm11 (r := 0) (b := fb m0) (sz := 5520 + 8) rfl (by omega) hw
  have w176 : NativeRustcVm.WordAt st11.data.dmem (loc m0 176) s2.sponge.squeeze.1.c1 := by
    have := wW11 (o := 176) (by omega) (wr11.find (List.Mem.head _))
    rwa [show (Sym.reg .rdx).eval (frameEnv m0 m10 5520 [] (fun _ ↦ 0) 0) = _ from hdx10,
      UInt64.ofBitVec_toBitVec] at this
  have w184 : NativeRustcVm.WordAt st11.data.dmem (loc m0 184) s2.sponge.squeeze.1.c0 := by
    have := wW11 (o := 184) (by omega) (wr11.find (List.Mem.tail _ (List.Mem.head _)))
    rwa [show (Sym.reg .rax).eval (frameEnv m0 m10 5520 [] (fun _ ↦ 0) 0) = _ from hax10,
      UInt64.ofBitVec_toBitVec] at this
  have kG11 : KeepIv gIv m0 st11.data.dmem st11.data.dmem := KeepIv.rfl' rfl
  simp only [PcOk] at hpc11
  refine at_pc (hpc11.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.VerifyBusBalance.b15_next))
    (loop16_spec hp h (d0 := st11.data.dmem) (R0 := d) (s := { s2 with sponge := s2.sponge.squeeze.2 })
      ?_ 20 0 rfl st11.data fr11 kG11 r11 ts11 (hm11.regs .rax _ hrax11))
  intro d12 fr12 kG12 r12 ts12
  -- `b17`: `memcpy(1800, 672, 1008)`.
  have hwf13 := wf_copy h fr12.frame.kept (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b17Offset + b17.length)).toBitVec)
  refine exec_then (infix_of b17_in_code (by simp [b17]) hp) exit_b17 hwf13 (fun _ _ ↦ rfl)
    (match_copy h fr12) fun st13 hm13 hpc13 ↦ ?_
  obtain ⟨hmid13, hw13, hrdi13, hrsi13, hrdx13, hk13⟩ := ok_b17
  have fr13 : St m0 96 st13.data :=
    St.blk fr12 hS hwf13 hm13 hmid13 fun q hq ↦ wr0 hS hw13 (by omega) hq
  have hs13 := blk_same hS hwf13 hm13 hw13 (by omega)
  have hsp13 : rspOf st13.data = loc m0 96 := fr13.frame.sp
  have kG13 : KeepIv gIv m0 d12.dmem st13.data.dmem :=
    keepIv_block hwf13 hm13 (writesIn_of_mid hmid13) (W0.reg0 hw13) (by decide) (by decide)
  have ts13 := ts_keep h (hm13.kept hwf13) hs13 (fun q hq ↦ .inl (frame_stack hS hq)) ts12
  have r13 : ∀ r ∈ clRegs, reg st13.data r = reg d r := fun r hr' ↦
    (hk13.reg hm13 (clRegs_cs r hr').2.1).trans (r12 r hr')
  have x13di : reg st13.data .rdi = loc m0 1800 := (hm13.regs .rdi _ hrdi13).trans (eval_ptr0 1800)
  have x13si : reg st13.data .rsi = loc m0 672 := (hm13.regs .rsi _ hrsi13).trans (eval_ptr0 672)
  have x13dx : (reg st13.data .rdx).toNat = 1008 := by
    rw [show reg st13.data .rdx = _ from hm13.regs .rdx _ hrdx13]; rfl
  have hle13 : 5520 - 96 + 0 ≤ NN := le_mem
  simp only [PcOk] at hpc13
  refine callF h (c := 96) (Nc := 0) (lo := 1800) (len := 1008)
    (X := NativeRustcVm.InRange (loc m0 1800) 1008) (by omega) hle13 (by omega)
    (fun q hq ↦ .inr hq) hmc fr13 hpc13 ?_
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.1 fun q hq' ↦ by
      rw [x13di, x13dx] at hq'; exact .inr hq', hq.2.2.2⟩)
    fun m14 fr14 hq14 hs14 hcs14 ↦ ?_
  · unfold MemcpyPre
    rw [x13di, x13si, x13dx]
    have hd := cal_local h fr13 (by omega) hle13 (j := 1800) (n := 1008) (by omega) (by omega)
    have hs := cal_local h fr13 (by omega) hle13 (j := 672) (n := 1008) (by omega) (by omega)
    have e : stackBelow st13.data 0 = rspOf st13.data := by
      unfold stackBelow
      simp
    have hap := hd.2.2.2.2.1
    rw [e] at hap
    exact ⟨cal_stack h fr13 (by omega) hle13, hd.1, hs.1, hd.2.1, hs.2.1,
      loc_apart hS (by omega) (by omega) (by omega), hap⟩
  have hsv14 := hq14.2.2.2
  have kG14 : KeepIv gIv m0 st13.data.dmem m14.dmem :=
    keepIv_call hS hsp13 (by omega) hle13 hs14 (by decide) (by decide)
      (notX (by omega) (by decide) (by decide))
  have ts14 := ts_keep h hsv14.2 hs14 (fun q hq ↦ hq.elim
    (fun h' ↦ .inl (callee_stack hS hsp13 (by omega) hle13 h'))
    (fun h' ↦ .inl (loc_stack hS (by omega) h'))) ts13
  have r14 : ∀ r ∈ clRegs, reg m14 r = reg d r := fun r hr' ↦
    (hcs14 r (clRegs_cs r hr').1).trans (r13 r hr')
  -- `b18`: `verify_gkr_grand_products(672, t, depth, 1744)`.
  rw [show k + NativeRustcVmX64.Vm.VerifyBusBalance.b17Offset + b17.length = k + NativeRustcVmX64.Vm.VerifyBusBalance.b18Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyBusBalance.b17_next]]
  have hwf15 := wf0 h fr14.frame.kept (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b18Offset + b18.length)).toBitVec)
  refine exec_then (infix_of b18_in_code (by simp [b18]) hp) exit_b18 hwf15 (fun _ _ ↦ rfl)
    (match_fS fr14) fun st15 hm15 hpc15 ↦ ?_
  obtain ⟨hmid15, hw15, hrdi15, hrsi15, hrdx15, hrcx15, hk15⟩ := ok_b18
  have fr15 : St m0 96 st15.data :=
    St.blk fr14 hS hwf15 hm15 hmid15 fun q hq ↦ wr0 hS hw15 (by omega) hq
  have hs15 := blk_same hS hwf15 hm15 hw15 (by omega)
  have hsp15 : rspOf st15.data = loc m0 96 := fr15.frame.sp
  have kG15 : KeepIv gIv m0 m14.dmem st15.data.dmem :=
    keepIv_block' hwf15 hm15 (writesIn_of_mid hmid15) (by decide) (by decide +kernel)
  have ts15 := ts_keep h (hm15.kept hwf15) hs15 (fun q hq ↦ .inl (frame_stack hS hq)) ts14
  have r15 : ∀ r ∈ clRegs, reg st15.data r = reg d r := fun r hr' ↦
    (hk15.reg hm15 (clRegs_cs r hr').2.1).trans (r14 r hr')
  have x15di : reg st15.data .rdi = loc m0 672 := (hm15.regs .rdi _ hrdi15).trans (eval_ptr0 672)
  have x15si : reg st15.data .rsi = reg m0 .rdi :=
    (hm15.regs .rsi _ hrsi15).trans ((r14 .rbx (by simp)).trans A.xbx)
  have x15dx : (reg st15.data .rdx).toNat = (pushL L).depth := by
    rw [show reg st15.data .rdx = _ from hm15.regs .rdx _ hrdx15]
    show (reg m14 .r12).toNat = _
    rw [r14 .r12 (by simp), A.x12, ndep]
  have x15cx : reg st15.data .rcx = loc m0 1744 := (hm15.regs .rcx _ hrcx15).trans (eval_ptr0 1744)
  have hgb : gkrStateBytes = 1064 := rfl
  have hle15 : 5520 - 96 + verifyGkrStack ≤ NN := le_gkr
  simp only [PcOk] at hpc15
  refine callF h (c := 96) (Nc := verifyGkrStack) (lo := 672) (len := 2136)
    (X := fun q ↦ NativeRustcVm.InRange (loc m0 672) 24 q ∨
      NativeRustcVm.InRange (reg m0 .rdi) tstateBytes q ∨
      NativeRustcVm.InRange (loc m0 1744) gkrStateBytes q) (by omega) hle15 (by omega)
    (fun q hq ↦ by
      rcases hq with hq | hq | hq
      · exact .inr (loc_sub hS (by omega) (by omega) (by omega) hq)
      · exact .inl (.inl hq)
      · rw [hgb] at hq
        exact .inr (loc_sub hS (by omega) (by omega) (by omega) hq))
    (hgkr { s2 with sponge := s2.sponge.squeeze.2 }) fr15 hpc15 ?_
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.1 fun q hq' ↦ by
      rw [x15di, x15si, x15cx] at hq'
      rcases hq' with hq' | hq' | hq' | hq'
      · exact .inr (.inl hq')
      · exact .inr (.inr (.inl hq'))
      · exact .inr (.inr (.inr hq'))
      · exact .inl hq', hq.2.2.2⟩)
    fun m16 fr16 hq16 hs16 hcs16 ↦ ?_
  · unfold VerifyGkrPre GkrOk
    rw [x15di, x15si, x15cx, x15dx, hgb]
    refine ⟨cal_stack h fr15 (by omega) hle15, cal_rc h fr15 (by omega) hle15, ts15,
      cal_tok h fr15 (by omega) hle15, by unfold busPointCap; omega,
      cal_local h fr15 (by omega) hle15 (by omega) (by omega),
      cal_local h fr15 (by omega) hle15 (by omega) (by omega),
      loc_apart hS (by omega) (by omega) (by omega), cal_got h fr15 (by omega) hle15 (by decide) ?_⟩
    intro l hl b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact ((pre_got h).1 l hl).2.2.2 _ (by simp)
    · exact ((pre_got h).1 l hl).2.2.2 _ (by simp)
    · exact got_apart_frame (pre_got h) hS hl N_ge (by omega)
    · exact got_apart_frame (pre_got h) hS hl N_ge (by omega)
    · exact ((pre_got h).1 l hl).2.2.2 _ (by simp)
  obtain ⟨hopt16, hsome16, -, -⟩ := hq16
  rw [x15di, x15dx] at hopt16
  rw [x15si, x15cx, x15dx] at hsome16
  have kG16 : KeepIv gIv m0 st15.data.dmem m16.dmem :=
    keepIv_call hS hsp15 (by omega) hle15 hs16 (by decide) (by decide) fun j hj hq ↦ by
      rcases hq with hq | hq | hq
      · exact notX (by omega) (by decide) (by decide) j hj hq
      · exact notT (by decide) j hj hq
      · rw [hgb] at hq
        exact notX (by omega) (by decide) (by decide) j hj hq
  have r16 : ∀ r ∈ clRegs, reg m16 r = reg d r := fun r hr' ↦
    (hcs16 r (clRegs_cs r hr').1).trans (r15 r hr')
  -- `b19`: the count root's tag.
  rw [show k + NativeRustcVmX64.Vm.VerifyBusBalance.b18Offset + b18.length = k + NativeRustcVmX64.Vm.VerifyBusBalance.b19Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyBusBalance.b18_next]]
  cases hr4 : (verifyGkrGrandProducts (pushL L).depth).run
      { s2 with sponge := s2.sponge.squeeze.2 } with
  | none =>
    rw [hr4] at hopt16
    refine test_spec hp h (j := NativeRustcVmX64.Vm.VerifyBusBalance.b19Offset) (n := b19.length) (infix_of b19_in_code (by simp [b19]) hp) rfl
      exit_b19 ok_b19 fr16 (fun _ ↦ by rw [hrun, hr4]; rfl) fun _ _ _ _ hc ↦ ?_
    rw [tag32_true (show NativeRustcVm.WordAt m16.dmem (loc m0 672) 0 from hopt16)] at hc
    cases hc
  | some y4 =>
  obtain ⟨⟨cr, pt, tv⟩, s4⟩ := y4
  rw [hr4] at hopt16
  rw [hr4, Option.bind_some] at hrun
  obtain ⟨ts16, hgs16⟩ := hsome16 cr pt tv s4 hr4
  obtain ⟨ht16, hcr16⟩ := hopt16
  obtain ⟨hc0, hc1⟩ := ewAt_iff.mp hcr16
  rw [off_off] at hc0
  rw [off_off, off_off] at hc1
  refine test_spec hp h (j := NativeRustcVmX64.Vm.VerifyBusBalance.b19Offset) (n := b19.length) (infix_of b19_in_code (by simp [b19]) hp) rfl
    exit_b19 ok_b19 fr16 (fun hc ↦ by rw [tag32_false ht16] at hc; cases hc)
    fun d17 fr17 hd17 hk17 _ ↦ ?_
  -- `b20`: the count root not `0`.
  rw [show k + NativeRustcVmX64.Vm.VerifyBusBalance.b19Offset + b19.length = k + NativeRustcVmX64.Vm.VerifyBusBalance.b20Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyBusBalance.b19_next]]
  have hwf18 := wf0 h fr17.frame.kept (vars := fun _ ↦ 0) (ret := 0)
  refine exec_then (infix_of b20_in_code (by simp [b20]) hp) exit_b20 hwf18 nofun
    (match_fS fr17) fun st18 hm18 hpc18 ↦ ?_
  obtain ⟨hmid18, hmem18, hk18⟩ := ok_b20
  have fr18 := (fr17.block0 hS N_ge hwf18 hm18 hmid18 slots_le (by simp [hmem18])).1
  have hd18 : st18.data.dmem = d17.dmem := hm18.dmem_eq hwf18 hmem18
  have hc18 : SBool.eval (frameEnv m0 d17 5520 [] (fun _ ↦ 0) 0)
      (.cmp .eq .W64 (.bin .or .W64 (.load 0 688 8) (.load 0 680 8)) (.lit 0)) = (cr == 0) := by
    show CmpOp.apply .eq .W64 (BinOp.apply .or .W64
      ((frameEnv m0 d17 5520 [] (fun _ ↦ 0) 0).load 0 688 8)
      ((frameEnv m0 d17 5520 [] (fun _ ↦ 0) 0).load 0 680 8)) (BitVec.ofNat 64 0) = _
    rw [load_loc (show NativeRustcVm.WordAt d17.dmem (loc m0 688) cr.c1 by rw [hd17]; exact hc1),
      load_loc (show NativeRustcVm.WordAt d17.dmem (loc m0 680) cr.c0 by rw [hd17]; exact hc0),
      or_eq0]
  simp only [PcOk, hc18] at hpc18
  by_cases hz : (cr == 0) = true
  · simp only [hz, ↓reduceIte] at hpc18
    refine at_pc (hpc18.trans (lF_eq hp)) (fail_spec hp h fr18 ?_)
    rw [hrun]
    have : (require (cr != 0)).run s4 = none := by
      unfold require
      rw [show (cr != 0) = false by simp [bne, hz]]
      rfl
    rw [this]
    rfl
  have hreq : (require (cr != 0)).run s4 = some ((), s4) := by
    unfold require
    rw [show (cr != 0) = true by simp [bne, hz]]
    rfl
  rw [hreq, Option.bind_some] at hrun
  simp only [hz, Bool.false_eq_true, ↓reduceIte] at hpc18
  rw [show k + NativeRustcVmX64.Vm.VerifyBusBalance.b20Offset + b20.length = k + NativeRustcVmX64.Vm.VerifyBusBalance.b21Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyBusBalance.b20_next]] at hpc18
  refine at_pc hpc18 (hsc' w pt tv s2.sponge.squeeze.1 s4 st18.data ?_)
  -- The state at `b21`.
  have kAp : KeepIv [(112, 120), (128, 144), (2808, 5472)] m0 d.dmem st11.data.dmem :=
    (KeepIv.rfl' hd1).trans (kA2.trans (kA3.trans (kA4.trans (kA5.trans ((KeepIv.rfl' hd6).trans
      (kA7.trans (kA8.trans (kA9.trans (kA10.trans kA11)))))))))
  have kGp : KeepIv gIv m0 st11.data.dmem st18.data.dmem :=
    kG12.trans (kG13.trans (kG14.trans (kG15.trans (kG16.trans ((KeepIv.rfl' hd17).trans
      (KeepIv.rfl' hd18))))))
  have kWp : KeepIv [(368, 624)] m0 m8.dmem st11.data.dmem := kW9.trans (kW10.trans kW11)
  have sA : ∀ {lo hi o n : Nat}, (lo, hi) ∈ [(112, 120), (128, 144), (2808, 5472)] →
      (lo, hi) ∈ gIv → lo ≤ o → o + n ≤ hi → Same d.dmem st18.data.dmem (loc m0 o) n :=
    fun h1 h2 h3 h4 ↦ (kAp.sameIn h1 h3 h4).trans (kGp.sameIn h2 h3 h4)
  have hb : busLayoutBytes = 888 := busLayoutBytes_eq
  have hgs : GkrStateWAt st18.data.dmem (loc m0 1744) ⟨tv, pt⟩ := by rw [hd18, hd17]; exact hgs16
  have w1792 : NativeRustcVm.WordAt st18.data.dmem (loc m0 1792) pt.size.toUInt64 := by
    have := hgs.point.2.1
    rw [off_off, Array.length_toList] at this
    exact this
  have e1800 : off (loc m0 1744) 48 + 8#64 = loc m0 1800 := by
    show off (off (off (fb m0) 1744) 48) 8 = off (fb m0) 1800
    rw [off_off, off_off]
  have hpt : NativeRustcVm.EWsAt st18.data.dmem (loc m0 1800) pt.toList := by
    have := hgs.point.2.2
    rw [e1800] at this
    exact this
  have hpsz : pt.size ≤ 63 := by
    have := hgs.point.1
    rw [Array.length_toList] at this
    exact this
  have rf : ∀ r ∈ clRegs, reg st18.data r = reg d r := fun r hr' ↦
    (hk18.reg hm18 (clRegs_cs r hr').2.1).trans ((hk17 r (clRegs_cs r hr').2.2).trans (r16 r hr'))
  exact ⟨fr18, hrun,
    ⟨NativeRustcVm.Layout.WordAt.of_same A.w112 (sA (lo := 112) (hi := 120) (by simp) (by simp)
        (by omega) (by omega)) le_rfl,
      BusLayoutWAt.of_same A.push (sA (lo := 2808) (hi := 5472) (by simp) (by simp) (by omega)
        (by omega)),
      BusLayoutWAt.of_same A.pull (sA (lo := 2808) (hi := 5472) (by simp) (by simp) (by omega)
        (by omega)),
      BusLayoutWAt.of_same A.count (sA (lo := 2808) (hi := 5472) (by simp) (by simp) (by omega)
        (by omega)),
      NativeRustcVm.Tables.EWsAt.of_same hw8
        ((kWp.sameIn (lo := 368) (hi := 624) (o := 368) (n := 256) (by simp) (by omega)
          (by omega)).trans (kGp.sameIn (lo := 368) (hi := 624) (by simp) (by omega) (by omega)))
        (by rw [Array.length_toList, hwsz]), hwsz, hgs.values, hgs.values_size, w1792, hpt, hpsz,
      NativeRustcVm.Layout.WordAt.of_same w184 (kGp.sameIn (lo := 176) (hi := 192) (by simp)
        (by omega) (by omega)) le_rfl,
      NativeRustcVm.Layout.WordAt.of_same w176 (kGp.sameIn (lo := 176) (hi := 192) (by simp)
        (by omega) (by omega)) le_rfl,
      NativeRustcVm.Layout.WordAt.of_same A.w128 (sA (lo := 128) (hi := 144) (by simp) (by simp)
        (by omega) (by omega)) le_rfl,
      NativeRustcVm.Layout.WordAt.of_same A.w136 (sA (lo := 128) (hi := 144) (by simp) (by simp)
        (by omega) (by omega)) le_rfl⟩,
    (rf .rbx (by simp)).trans A.xbx, (rf .r13 (by simp)).trans A.x13,
    (rf .r14 (by simp)).trans A.x14, (rf .r15 (by simp)).trans A.x15,
    (rf .rbp (by simp)).trans A.xbp, by rw [hd18, hd17]; exact ts16⟩

end

end NativeRustcVmX64.Bus.VerifyBusBalance
