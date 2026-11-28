module

public import NativeRustcVmX64.Bus.VerifyBusBalance.ClaimsA
public import NativeRustcVm.Transcript.Loop
public import NativeRustcVmX64.Code.Vm.AccumulateSide.Names
public import NativeRustcVmX64.Code.Vm.BufEW63Extend.Names
public import NativeRustcVmX64.Code.Vm.BytecodeShare.Names
public import NativeRustcVmX64.Code.Vm.ComputedBytecodeValue.Names
public import NativeRustcVmX64.Code.Vm.Kpow.Names
public import NativeRustcVmX64.Code.Vm.PushClaim.Names
public import NativeRustcVmX64.Code.Vm.TStateReadScalar.Names
public import NativeRustcVmX64.Code.Vm.TStateReadScalars.Names
public import NativeRustcVmX64.Code.Vm.VerifyBusBalanceClosure0.Names

/-!
# `verify_bus_balance`'s scalars (x86-64)

`AtScal`: the state at `b21` (`k + NativeRustcVmX64.Vm.VerifyBusBalance.b21Offset`), the GKR walk done, its count root not zero. `b21`
computes the points' lengths and calls `read_scalars` for the memory's two scalars; `b22` checks
it; `b23` calls `read_scalar` for the final memory counter; `b24` checks its tag; then
`claimsA_spec` (`scal_spec`).
-/

namespace NativeRustcVmX64.Bus.VerifyBusBalance

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.VerifyBusBalance
open NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck NativeRustcVmX64.Bus.Gkr
open NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Bus NativeRustcVm.Layout

public section

/-- The locals kept from the GKR walk to the scalars. -/
structure ScalMem (m0 : MachineData) (L : LayoutW) (w pt tv : Array EW) (beta : EW)
    (d : Mem 64) : Prop where
  w112 : NativeRustcVm.WordAt d (loc m0 112) (UInt64.ofBitVec (reg m0 .r8))
  push : BusLayoutWAt d (loc m0 2808) (pushL L)
  pull : BusLayoutWAt d (loc m0 3696) (pullL L)
  count : BusLayoutWAt d (loc m0 4584) (countL L)
  hw : NativeRustcVm.EWsAt d (loc m0 368) w.toList
  wsz : w.size = 16
  htv : NativeRustcVm.EWsAt d (loc m0 1744) tv.toList
  tsz : tv.size = 3
  w1792 : NativeRustcVm.WordAt d (loc m0 1792) pt.size.toUInt64
  hpt : NativeRustcVm.EWsAt d (loc m0 1800) pt.toList
  psz : pt.size ≤ 63
  w184 : NativeRustcVm.WordAt d (loc m0 184) beta.c0
  w176 : NativeRustcVm.WordAt d (loc m0 176) beta.c1
  w128 : NativeRustcVm.WordAt d (loc m0 128) (UInt64.ofBitVec (reg m0 .rdx))
  w136 : NativeRustcVm.WordAt d (loc m0 136) (UInt64.ofBitVec (reg m0 .rcx))

/-- `ScalMem`'s intervals. -/
abbrev scalIv : List (Nat × Nat) := [(112, 120), (128, 144), (176, 192), (368, 624), (1744, 5472)]

theorem ScalMem.of_keep {m0 : MachineData} {L : LayoutW} {w pt tv : Array EW} {beta : EW}
    {d d' : Mem 64} (h : ScalMem m0 L w pt tv beta d) (hk : KeepIv scalIv m0 d d') :
    ScalMem m0 L w pt tv beta d' := by
  have psz := h.psz
  have i1 : (112, 120) ∈ scalIv := by simp
  have i2 : (128, 144) ∈ scalIv := by simp
  have i3 : (176, 192) ∈ scalIv := by simp
  have i4 : (368, 624) ∈ scalIv := by simp
  have i5 : (1744, 5472) ∈ scalIv := by simp
  have hb : busLayoutBytes = 888 := busLayoutBytes_eq
  exact ⟨NativeRustcVm.Layout.WordAt.of_same h.w112 (hk.sameIn i1 (by omega) (by omega)) le_rfl,
    BusLayoutWAt.of_same h.push (hk.sameIn i5 (by omega) (by omega)),
    BusLayoutWAt.of_same h.pull (hk.sameIn i5 (by omega) (by omega)),
    BusLayoutWAt.of_same h.count (hk.sameIn i5 (by omega) (by omega)),
    NativeRustcVm.Tables.EWsAt.of_same h.hw (hk.sameIn i4 (n := 256) (by omega) (by omega))
      (by rw [Array.length_toList, h.wsz]), h.wsz,
    NativeRustcVm.Tables.EWsAt.of_same h.htv (hk.sameIn i5 (n := 48) (by omega) (by omega))
      (by rw [Array.length_toList, h.tsz]), h.tsz,
    NativeRustcVm.Layout.WordAt.of_same h.w1792 (hk.sameIn i5 (by omega) (by omega)) le_rfl,
    NativeRustcVm.Tables.EWsAt.of_same h.hpt (hk.sameIn i5 (n := 16 * pt.size) (by omega)
      (by omega)) (by simp), psz,
    NativeRustcVm.Layout.WordAt.of_same h.w184 (hk.sameIn i3 (by omega) (by omega)) le_rfl,
    NativeRustcVm.Layout.WordAt.of_same h.w176 (hk.sameIn i3 (by omega) (by omega)) le_rfl,
    NativeRustcVm.Layout.WordAt.of_same h.w128 (hk.sameIn i2 (by omega) (by omega)) le_rfl,
    NativeRustcVm.Layout.WordAt.of_same h.w136 (hk.sameIn i2 (by omega) (by omega)) le_rfl⟩

/-- **The state at `b21`.** -/
structure AtScal (a : DecArea) (s0 : TState) (L : LayoutW) (m0 : MachineData)
    (w pt tv : Array EW) (beta : EW) (s : TState) (d : MachineData) : Prop where
  fr : St m0 104 d
  run : (verifyBusBalance L).run s0 = tailRun L w beta pt tv s
  sm : ScalMem m0 L w pt tv beta d.dmem
  xbx : reg d .rbx = reg m0 .rdi
  x13 : reg d .r13 = L.logBytecode.toUInt64.toBitVec
  x14 : reg d .r14 = reg m0 .rsi
  x15 : reg d .r15 = reg m0 .r9
  xbp : reg d .rbp = L.logMemory.toUInt64.toBitVec
  ts : TStateAt d.dmem (reg m0 .rdi) a s

theorem toU64_bv (n : Nat) : n.toUInt64.toBitVec = BitVec.ofNat 64 n := rfl

/-- `if ¬ x < n then n else x` of small numbers: their minimum. -/
theorem ite_min1 {x n : Nat} (hx : x < 2 ^ 64) (hn : n < 2 ^ 64) :
    (if (!(BitVec.ofNat 64 x).ult (BitVec.ofNat 64 n)) = true then BitVec.ofNat 64 n
      else BitVec.ofNat 64 x) = BitVec.ofNat 64 (min x n) := by
  rw [ult_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hn]
  by_cases h : x < n
  · simp only [h, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [Nat.min_eq_left (by omega)]
  · simp only [h, decide_false, Bool.not_false, ↓reduceIte]
    rw [Nat.min_eq_right (by omega)]

/-- `if x < n then x else n` of small numbers: their minimum. -/
theorem ite_min2 {x n : Nat} (hx : x < 2 ^ 64) (hn : n < 2 ^ 64) :
    (if (BitVec.ofNat 64 x).ult (BitVec.ofNat 64 n) = true then BitVec.ofNat 64 x
      else BitVec.ofNat 64 n) = BitVec.ofNat 64 (min x n) := by
  rw [ult_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hn]
  by_cases h : x < n
  · simp only [h, decide_true, ↓reduceIte]
    rw [Nat.min_eq_left (by omega)]
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
    rw [Nat.min_eq_right (by omega)]

end

public section
variable [Host] {a : DecArea} {s0 : TState} {L : LayoutW} {m0 : MachineData} {k : Nat}

/-- **The scalars** (`b21`, `k + NativeRustcVmX64.Vm.VerifyBusBalance.b21Offset`). -/
theorem scal_spec (hp : Placed code k) (h : VerifyBusBalancePre a s0 L m0)
    (hrss : ∀ s, Spec (Labels.label NativeRustcVmX64.Vm.TStateReadScalars.entryLabel) (ReadScalarsPre a s) (ReadScalarsPost a s))
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
    {w pt tv : Array EW} {beta : EW} {s : TState} {d : MachineData}
    (A : AtScal a s0 L m0 w pt tv beta s d) :
    Eventually (step1 Host.exe) (Goal a s0 L m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b21Offset)⟩ := by
  have hS := pre_stack h
  have psz := A.sm.psz
  have lm := (pre_lay h).log_memory_le
  have lb := (pre_lay h).log_bytecode_le
  -- `b21`: the points' lengths, `read_scalars(t, 216, 2)`.
  have hwf1 := wf0 h A.fr.frame.kept (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b21Offset + b21.length)).toBitVec)
  refine exec_then (infix_of b21_in_code (by simp [b21]) hp) exit_b21 hwf1 (fun _ _ ↦ rfl)
    (match_fS A.fr) fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid1, hw1, wr21, hrdi1, hrsi1, hrdx1, hrbp1, hr121, hk1⟩ := ok_b21
  have fr1 : St m0 96 st1.data := St.blk A.fr hS hwf1 hm1 hmid1 fun q hq ↦ wr0 hS hw1 (by omega) hq
  have hin1 := writesIn_of_mid hmid1
  have hs1 := blk_same hS hwf1 hm1 hw1 (by omega)
  have hsp1 : rspOf st1.data = loc m0 96 := fr1.frame.sp
  have e1792 : (frameEnv m0 d 5520 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b21Offset + b21.length)).toBitVec).load
      0 1792 8 = BitVec.ofNat 64 pt.size := load_loc A.sm.w1792
  have hlen : lenS.eval (frameEnv m0 d 5520 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b21Offset + b21.length)).toBitVec) = BitVec.ofNat 64 pt.size := by
    show (if CmpOp.apply .ult .W64 ((frameEnv m0 d 5520 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b21Offset + b21.length)).toBitVec).load 0 1792 8) (BitVec.ofNat 64 64) = true
      then (frameEnv m0 d 5520 [] (fun _ ↦ 0)
        (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b21Offset + b21.length)).toBitVec).load 0 1792 8 else BitVec.ofNat 64 0) = _
    rw [e1792]
    simp only [CmpOp.apply, low_W64, ult_toNat, BitVec.toNat_ofNat]
    split
    · rfl
    · rename_i hc
      simp only [decide_eq_true_eq, Nat.reducePow, Nat.reduceMod] at hc
      omega
  have wW1 : ∀ {o : Nat} {v : Sym}, o + 8 ≤ 5520 →
      (∀ t < 8, findWrite 0 (o + t) (after b21 (fS 104)).mem = some (v, t)) →
      NativeRustcVm.WordAt st1.data.dmem (loc m0 o) (UInt64.ofBitVec (v.eval
        (frameEnv m0 d 5520 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b21Offset + b21.length)).toBitVec))) :=
    fun ho hw ↦ wordAt_write hm1 (r := 0) (b := fb m0) (sz := 5520 + 8) rfl (by omega) hw
  have w104 : NativeRustcVm.WordAt st1.data.dmem (loc m0 104) (UInt64.ofBitVec (loc m0 1800)) := by
    have := wW1 (o := 104) (by omega) (wr21.find (List.Mem.head _))
    have e : (Sym.ite (.cmp .ult .W64 (.load 0 1792 8) (.lit 64)) (.ptr 0 1800) (.lit 8)).eval
        (frameEnv m0 d 5520 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b21Offset + b21.length)).toBitVec) =
        loc m0 1800 := by
      show (if CmpOp.apply .ult .W64 ((frameEnv m0 d 5520 [] (fun _ ↦ 0)
        (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b21Offset + b21.length)).toBitVec).load 0 1792 8) (BitVec.ofNat 64 64) = true
        then (Sym.ptr 0 1800).eval (frameEnv m0 d 5520 [] (fun _ ↦ 0)
          (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b21Offset + b21.length)).toBitVec) else BitVec.ofNat 64 8) = _
      rw [e1792]
      simp only [CmpOp.apply, low_W64, ult_toNat, BitVec.toNat_ofNat]
      split
      · exact eval_ptr0 1800
      · rename_i hc
        simp only [decide_eq_true_eq, Nat.reducePow, Nat.reduceMod] at hc
        omega
    rwa [e] at this
  have w120 : NativeRustcVm.WordAt st1.data.dmem (loc m0 120) pt.size.toUInt64 := by
    have := wW1 (o := 120) (by omega) (wr21.find (List.Mem.tail _ (List.Mem.head _)))
    rwa [hlen] at this
  have xbp1 : reg st1.data .rbp = (min L.logMemory pt.size).toUInt64.toBitVec := by
    rw [show reg st1.data .rbp = _ from hm1.regs .rbp _ hrbp1]
    show (if (!CmpOp.apply .ult .W64 (reg d .rbp) (lenS.eval (frameEnv m0 d 5520 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b21Offset + b21.length)).toBitVec))) = true then lenS.eval (frameEnv m0 d 5520 []
        (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b21Offset + b21.length)).toBitVec) else reg d .rbp) = _
    rw [hlen, A.xbp, toU64_bv, toU64_bv]
    exact ite_min1 (by omega) (by omega)
  have x121 : reg st1.data .r12 = (min L.logBytecode pt.size).toUInt64.toBitVec := by
    rw [show reg st1.data .r12 = _ from hm1.regs .r12 _ hr121]
    show (if CmpOp.apply .ult .W64 (reg d .r13) (lenS.eval (frameEnv m0 d 5520 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b21Offset + b21.length)).toBitVec)) = true then reg d .r13 else
        lenS.eval (frameEnv m0 d 5520 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b21Offset + b21.length)).toBitVec)) = _
    rw [hlen, A.x13, toU64_bv, toU64_bv]
    exact ite_min2 (by omega) (by omega)
  have x1di : reg st1.data .rdi = reg m0 .rdi := (hm1.regs .rdi _ hrdi1).trans A.xbx
  have x1si : reg st1.data .rsi = loc m0 216 := (hm1.regs .rsi _ hrsi1).trans (eval_ptr0 216)
  have x1dx : (reg st1.data .rdx).toNat = 2 := by
    rw [show reg st1.data .rdx = _ from hm1.regs .rdx _ hrdx1]; rfl
  have hts1 := ts_keep h (hm1.kept hwf1) hs1 (fun q hq ↦ .inl (frame_stack hS hq)) A.ts
  have hle : 5520 - 96 + readScalarsStack ≤ NN := le_rss
  simp only [PcOk] at hpc1
  refine callF h (c := 96) (Nc := readScalarsStack) (lo := 216) (len := 32)
    (X := fun q ↦ NativeRustcVm.InRange (loc m0 216) 32 q ∨
      NativeRustcVm.InRange (reg m0 .rdi) tstateBytes q) (by omega) hle (by omega)
    (fun q hq ↦ hq.elim .inr fun h' ↦ .inl (.inl h')) (hrss s) fr1 hpc1 ?_
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.2.1 fun q hq' ↦ ?_, hq.2.2.2.2⟩)
    fun m2 fr2 hq2 hs2 hcs2 ↦ ?_
  · unfold ReadScalarsPre
    rw [x1di, x1si, x1dx]
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
  · rw [x1di, x1si, x1dx] at hq'
    rcases hq' with hq' | hq' | hq'
    · exact .inr (.inl hq')
    · exact .inr (.inr hq')
    · exact .inl hq'
  obtain ⟨hal2, hxs2, hnx2, -, hsv2⟩ := hq2
  rw [x1dx] at hal2
  rw [x1si, x1dx] at hxs2
  rw [x1di, x1dx] at hnx2
  have hXg : ∀ {o n : Nat}, o + n ≤ 5520 → ∀ {ivs : List (Nat × Nat)},
      ivs.all (fun p ↦ decide (p.2 ≤ 5472)) = true →
      ivs.all (fun p ↦ decide (p.2 ≤ o) || decide (o + n ≤ p.1)) = true → ∀ j, InIv ivs j →
      ¬ (NativeRustcVm.InRange (loc m0 o) n (loc m0 j) ∨
        NativeRustcVm.InRange (reg m0 .rdi) tstateBytes (loc m0 j)) :=
      fun {_ _} hon {_} hlt hap j hj hq ↦ by
    have hj5 := inIv_lt hlt hj
    rcases hq with hq | hq
    · exact loc_notIn hS (j := j) (by omega) (by omega) (inIv_apart hap hj) hq
    · exact not_loc hS (pre_tok h).1 (pre_ts h).footprint.1.2 (j := j) (l := 1) (by omega) hq
        (loc_inR hS (by omega) (by omega) (by omega))
  have kv1 : KeepIv scalIv m0 d.dmem st1.data.dmem :=
    keepIv_block' hwf1 hm1 hin1 (by decide) (by decide +kernel)
  have kv2 : KeepIv scalIv m0 st1.data.dmem m2.dmem :=
    keepIv_call hS hsp1 (by omega) hle hs2 (by decide) (by decide) (hXg (by omega) (by decide)
      (by decide))
  have kt2 : KeepIv [(104, 128)] m0 st1.data.dmem m2.dmem :=
    keepIv_call hS hsp1 (by omega) hle hs2 (by decide) (by decide) (hXg (by omega) (by decide)
      (by decide))
  -- `b22`: `read_scalars`' result.
  rw [show k + NativeRustcVmX64.Vm.VerifyBusBalance.b21Offset + b21.length = k + NativeRustcVmX64.Vm.VerifyBusBalance.b22Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyBusBalance.b21_next]]
  cases hr1 : (readScalars 2).run s with
  | none =>
    rw [hr1] at hal2
    refine test_spec hp h (j := NativeRustcVmX64.Vm.VerifyBusBalance.b22Offset) (n := b22.length) (infix_of b22_in_code (by simp [b22]) hp) rfl
      exit_b22 ok_b22 fr2 (fun _ ↦ by rw [A.run]; simp only [tailRun, hr1, Option.bind_none])
      fun _ _ _ _ hc ↦ ?_
    rw [alZ_true (show boolRet m2 = 0 from hal2)] at hc
    cases hc
  | some y =>
  obtain ⟨mem, s1⟩ := y
  rw [hr1] at hal2
  have hmem2 := hxs2 _ _ hr1
  have hts2 := hnx2 _ _ hr1
  have hmsz : mem.size = 2 := NativeRustcVm.Transcript.pushes_size
    (show (pushes readScalar 2).run s = some (mem, s1) from hr1)
  refine test_spec hp h (j := NativeRustcVmX64.Vm.VerifyBusBalance.b22Offset) (n := b22.length) (infix_of b22_in_code (by simp [b22]) hp) rfl
    exit_b22 ok_b22 fr2 (fun hc ↦ by rw [alZ_false (show boolRet m2 = 1 from hal2)] at hc; cases hc)
    fun d3 fr3 hd3 hk3 _ ↦ ?_
  have sm2 := A.sm.of_keep (kv1.trans kv2)
  have base2 : BaseMem m0 L w pt tv mem beta m2.dmem :=
    ⟨⟨sm2.w112,
      NativeRustcVm.Layout.WordAt.of_same w104 (kt2.sameIn (lo := 104) (hi := 128) (by simp)
        (by omega) (by omega)) le_rfl,
      NativeRustcVm.Layout.WordAt.of_same w120 (kt2.sameIn (lo := 104) (hi := 128) (by simp)
        (by omega) (by omega)) le_rfl, sm2.hpt, psz⟩,
      sm2.push, sm2.pull, sm2.count, sm2.hw, sm2.wsz, hmem2, hmsz, sm2.htv, sm2.tsz, sm2.w184,
      sm2.w176, sm2.w128, sm2.w136⟩
  have g3 : ∀ r ∈ clRegs, reg d3 r = reg st1.data r := fun r hr' ↦
    (hk3 r (clRegs_cs r hr').2.2).trans (hcs2 r (clRegs_cs r hr').1)
  have g3' : ∀ r ∈ [Reg64.rbx, .r13, .r14, .r15], reg d3 r = reg d r := fun r hr' ↦
    (g3 r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr' ⊢
      rcases hr' with h' | h' | h' | h' <;> simp [h'])).trans (hk1.reg hm1 hr')
  -- `b23`: `read_scalar(672, t)`.
  rw [show k + NativeRustcVmX64.Vm.VerifyBusBalance.b22Offset + b22.length = k + NativeRustcVmX64.Vm.VerifyBusBalance.b23Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyBusBalance.b22_next]]
  have hwf4 := wf0 h fr3.frame.kept (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b23Offset + b23.length)).toBitVec)
  refine exec_then (infix_of b23_in_code (by simp [b23]) hp) exit_b23 hwf4 (fun _ _ ↦ rfl)
    (match_fS fr3) fun st4 hm4 hpc4 ↦ ?_
  obtain ⟨hmid4, hw4, hrdi4, hrsi4, hk4⟩ := ok_b23
  have fr4 : St m0 96 st4.data := St.blk fr3 hS hwf4 hm4 hmid4 fun q hq ↦ wr0 hS hw4 (by omega) hq
  have hin4 := writesIn_of_mid hmid4
  have hs4 := blk_same hS hwf4 hm4 hw4 (by omega)
  have hsp4 : rspOf st4.data = loc m0 96 := fr4.frame.sp
  have kv4 : KeepIv baseIv m0 d3.dmem st4.data.dmem :=
    keepIv_block hwf4 hm4 hin4 (W0.reg0 hw4) (by decide) (by decide)
  have hts4 := ts_keep h (hm4.kept hwf4) hs4 (fun q hq ↦ .inl (frame_stack hS hq))
    (show TStateAt d3.dmem (reg m0 .rdi) a s1 by rw [hd3]; exact hts2)
  have x4di : reg st4.data .rdi = loc m0 672 := (hm4.regs .rdi _ hrdi4).trans (eval_ptr0 672)
  have x4si : reg st4.data .rsi = reg m0 .rdi :=
    (hm4.regs .rsi _ hrsi4).trans ((g3' .rbx (by simp)).trans A.xbx)
  have hle4 : 5520 - 96 + readScalarStack ≤ NN := le_rs
  simp only [PcOk] at hpc4
  refine callF h (c := 96) (Nc := readScalarStack) (lo := 672) (len := 24)
    (X := fun q ↦ NativeRustcVm.InRange (loc m0 672) 24 q ∨
      NativeRustcVm.InRange (reg m0 .rdi) tstateBytes q) (by omega) hle4 (by omega)
    (fun q hq ↦ hq.elim .inr fun h' ↦ .inl (.inl h')) (hrs s1) fr4 hpc4 ?_
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.1 fun q hq' ↦ ?_, hq.2.2.2⟩)
    fun m5 fr5 hq5 hs5 hcs5 ↦ ?_
  · unfold ReadScalarPre
    rw [x4si, x4di]
    refine ⟨cal_stack h fr4 (by omega) hle4, cal_rc h fr4 (by omega) hle4, hts4,
      cal_tok h fr4 (by omega) hle4, cal_local h fr4 (by omega) hle4 (by omega) (by omega),
      cal_got h fr4 (by omega) hle4 (by decide) ?_⟩
    intro l hl b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact ((pre_got h).1 l hl).2.2.2 _ (by simp)
    · exact ((pre_got h).1 l hl).2.2.2 _ (by simp)
    · exact got_apart_frame (pre_got h) hS hl N_ge (by omega)
    · exact ((pre_got h).1 l hl).2.2.2 _ (by simp)
  · rw [x4si, x4di] at hq'
    rcases hq' with hq' | hq' | hq'
    · exact .inr (.inl hq')
    · exact .inr (.inr hq')
    · exact .inl hq'
  obtain ⟨hout5, hnext5, -, -⟩ := hq5
  rw [x4di] at hout5
  rw [x4si] at hnext5
  have kv5 : KeepIv baseIv m0 st4.data.dmem m5.dmem :=
    keepIv_call hS hsp4 (by omega) hle4 hs5 (by decide) (by decide) (hXg (by omega) (by decide)
      (by decide))
  -- `b24`: the final memory counter's tag.
  rw [show k + NativeRustcVmX64.Vm.VerifyBusBalance.b23Offset + b23.length = k + NativeRustcVmX64.Vm.VerifyBusBalance.b24Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyBusBalance.b23_next]]
  cases hr2 : readScalar.run s1 with
  | none =>
    rw [hr2] at hout5
    refine test_spec hp h (j := NativeRustcVmX64.Vm.VerifyBusBalance.b24Offset) (n := b24.length) (infix_of b24_in_code (by simp [b24]) hp) rfl
      exit_b24 ok_b24 fr5
      (fun _ ↦ by rw [A.run]; simp only [tailRun, hr1, hr2, Option.bind_some, Option.bind_none])
      fun _ _ _ _ hc' ↦ ?_
    rw [tag8_true (show NativeRustcVm.WordAt m5.dmem (loc m0 672) 0 from hout5)] at hc'
    cases hc'
  | some y =>
  obtain ⟨mf, s2⟩ := y
  rw [hr2] at hout5
  have hts5 := hnext5 _ _ hr2
  refine test_spec hp h (j := NativeRustcVmX64.Vm.VerifyBusBalance.b24Offset) (n := b24.length) (infix_of b24_in_code (by simp [b24]) hp) rfl
    exit_b24 ok_b24 fr5 (fun hc' ↦ by rw [tag8_false hout5.1] at hc'; cases hc')
    fun d6 fr6 hd6 hk6 _ ↦ ?_
  have g6 : ∀ r ∈ clRegs, reg d6 r = reg d3 r := fun r hr' ↦
    (hk6 r (clRegs_cs r hr').2.2).trans ((hcs5 r (clRegs_cs r hr').1).trans
      (hk4.reg hm4 (clRegs_cs r hr').2.1))
  have A6 : AtRs a L m0 w pt tv mem beta mf s2 d6 :=
    ⟨fr6, base2.of_keep ((KeepIv.rfl' hd3).trans (kv4.trans (kv5.trans (KeepIv.rfl' hd6)))),
      by rw [hd6]; exact hout5,
      (g6 .rbx (by simp)).trans ((g3' .rbx (by simp)).trans A.xbx),
      (g6 .r13 (by simp)).trans ((g3' .r13 (by simp)).trans A.x13),
      (g6 .r14 (by simp)).trans ((g3' .r14 (by simp)).trans A.x14),
      (g6 .r15 (by simp)).trans ((g3' .r15 (by simp)).trans A.x15),
      (g6 .rbp (by simp)).trans ((g3 .rbp (by simp)).trans xbp1),
      (g6 .r12 (by simp)).trans ((g3 .r12 (by simp)).trans x121),
      by rw [hd6]; exact hts5⟩
  rw [show k + NativeRustcVmX64.Vm.VerifyBusBalance.b24Offset + b24.length = k + NativeRustcVmX64.Vm.VerifyBusBalance.b25Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyBusBalance.b24_next]]
  exact claimsA_spec hp h hrs hpc hbs hcbv hkp hfc hacc hext A6
    (by rw [A.run]; simp only [tailRun, hr1, hr2, Option.bind_some])

end

end NativeRustcVmX64.Bus.VerifyBusBalance
