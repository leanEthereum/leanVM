module

public import NativeRustcVmArm.Code.Vm.VerifyBusBalance.Names
public import NativeRustcVmArm.Bus.VerifyBusBalance.Push
public import NativeRustcVmArm.Bus.VerifyBusBalance.ShareModel

/-!
# `verify_bus_balance`'s bytecode share: what it starts from

- `ShareMem`: the frame's locals at `b32`; `ShareMem.of_keep`, `ShareMem.push`.
- `AtShare`: the state at `b32` (`k + NativeRustcVmArm.Vm.VerifyBusBalance.b32Offset`).
- `fail_at`, `fail_cond`: a branch to `.LVerifyBusBalance_22` on a failed phase.
- `eq_lit_word`, `ult_lit_word`, `okW_eq0`: conditions on words.
- `bc_words`: the bytecode's words read as at the entry.
-/

namespace NativeRustcVmArm.Bus.VerifyBusBalance

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.VerifyBusBalance
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeRustcVm.Bus
open NativeRustcVm.Layout NativeRustcVmArm.Bus.Gkr

public section

/-- **The frame's locals at `b32`.** -/
structure ShareMem (m0 : MachineData) (L : LayoutW) (w pt tv mem : Array EW)
    (beta mf bf : EW) (d : Mem 64) : Prop where
  push : BusLayoutWAt d (loc m0 160) (pushL L)
  pull : BusLayoutWAt d (loc m0 1048) (pullL L)
  count : BusLayoutWAt d (loc m0 1936) (countL L)
  hw : NativeRustcVm.EWsAt d (loc m0 2824) w.toList
  wsz : w.size = 16
  t0a : NativeRustcVm.WordAt d (loc m0 3080) (tv.getD 0 0).c0
  t0b : NativeRustcVm.WordAt d (loc m0 3088) (tv.getD 0 0).c1
  t1a : NativeRustcVm.WordAt d (loc m0 3096) (tv.getD 1 0).c0
  t1b : NativeRustcVm.WordAt d (loc m0 3104) (tv.getD 1 0).c1
  t2a : NativeRustcVm.WordAt d (loc m0 3112) (tv.getD 2 0).c0
  t2b : NativeRustcVm.WordAt d (loc m0 3120) (tv.getD 2 0).c1
  hpt : NativeRustcVm.EWsAt d (loc m0 3136) pt.toList
  psz : pt.size ≤ 63
  hmem : NativeRustcVm.EWsAt d (loc m0 4144) mem.toList
  msz : mem.size = 2
  w88 : NativeRustcVm.WordAt d (loc m0 88) bf.c1
  w96 : NativeRustcVm.WordAt d (loc m0 96) bf.c0
  w104 : NativeRustcVm.WordAt d (loc m0 104) mf.c1
  w112 : NativeRustcVm.WordAt d (loc m0 112) mf.c0
  w120 : NativeRustcVm.WordAt d (loc m0 120) (min L.logBytecode pt.size).toUInt64
  w128 : NativeRustcVm.WordAt d (loc m0 128) beta.c0

/-- `ShareMem`'s intervals. -/
abbrev shareIv : List (Nat × Nat) := [(88, 136), (160, 4176)]

/-- **`ShareMem` through what keeps it.** -/
theorem ShareMem.of_keep {m0 : MachineData} {L : LayoutW} {w pt tv mem : Array EW}
    {beta mf bf : EW} {d d' : Mem 64} (h : ShareMem m0 L w pt tv mem beta mf bf d)
    (hk : KeepIv shareIv m0 d d') : ShareMem m0 L w pt tv mem beta mf bf d' := by
  have i1 : ((88, 136) : Nat × Nat) ∈ shareIv := by simp
  have i3 : ((160, 4176) : Nat × Nat) ∈ shareIv := by simp
  have wd : ∀ {lo hi o : Nat} {v : UInt64}, (lo, hi) ∈ shareIv → lo ≤ o → o + 8 ≤ hi →
      NativeRustcVm.WordAt d (loc m0 o) v → NativeRustcVm.WordAt d' (loc m0 o) v :=
    fun hm h1 h2 hw ↦ NativeRustcVm.Layout.WordAt.of_same hw (hk.sameIn hm h1 h2) le_rfl
  have hb : busLayoutBytes = 888 := rfl
  have hp := h.psz
  refine ⟨BusLayoutWAt.of_same h.push (hk.sameIn i3 (by omega) (by rw [hb]; omega)),
    BusLayoutWAt.of_same h.pull (hk.sameIn i3 (by omega) (by rw [hb]; omega)),
    BusLayoutWAt.of_same h.count (hk.sameIn i3 (by omega) (by rw [hb]; omega)),
    NativeRustcVm.Tables.EWsAt.of_same h.hw (hk.sameIn i3 (o := 2824) (n := 256) (by omega)
      (by omega)) (by rw [Array.length_toList, h.wsz]), h.wsz,
    wd i3 (by omega) (by omega) h.t0a, wd i3 (by omega) (by omega) h.t0b,
    wd i3 (by omega) (by omega) h.t1a, wd i3 (by omega) (by omega) h.t1b,
    wd i3 (by omega) (by omega) h.t2a, wd i3 (by omega) (by omega) h.t2b,
    NativeRustcVm.Tables.EWsAt.of_same h.hpt (hk.sameIn i3 (o := 3136) (n := 1008) (by omega)
      (by omega)) (by rw [Array.length_toList]; omega), h.psz,
    NativeRustcVm.Tables.EWsAt.of_same h.hmem (hk.sameIn i3 (o := 4144) (n := 32) (by omega)
      (by omega)) (by rw [Array.length_toList, h.msz]), h.msz,
    wd i1 (by omega) (by omega) h.w88, wd i1 (by omega) (by omega) h.w96,
    wd i1 (by omega) (by omega) h.w104, wd i1 (by omega) (by omega) h.w112,
    wd i1 (by omega) (by omega) h.w120, wd i1 (by omega) (by omega) h.w128⟩

/-- **The locals at `b37`**, the share at `5248`. -/
theorem ShareMem.push' {m0 : MachineData} {L : LayoutW} {w pt tv mem : Array EW}
    {beta mf bf share : EW} {d : Mem 64} (h : ShareMem m0 L w pt tv mem beta mf bf d)
    (hs : NativeRustcVm.EWAt d (loc m0 5248) share) :
    PushMem m0 L w pt tv mem beta mf bf share d :=
  ⟨h.push, h.pull, h.count, h.hw, h.wsz, h.t0a, h.t0b, h.t1a, h.t1b, h.t2a, h.t2b, h.hpt, h.psz,
    h.hmem, h.msz, h.w88, h.w96, h.w104, h.w112, h.w128, hs⟩

/-- `cmp x, #n` of a word. -/
theorem eq_lit_word (x : UInt64) {n : Nat} (hn : n < 2 ^ 64) :
    CmpOp.apply .eq .W64 x.toBitVec (BitVec.ofNat 64 n) = decide (x.toNat = n) := by
  simp only [CmpOp.apply, Sym.low_W64, beq_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    UInt64.toNat_toBitVec]

/-- `x < n` of a word. -/
theorem ult_lit_word (x : UInt64) {n : Nat} (hn : n < 2 ^ 64) :
    CmpOp.apply .ult .W64 x.toBitVec (BitVec.ofNat 64 n) = decide (x.toNat < n) := by
  simp only [CmpOp.apply, Sym.low_W64, ult_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    UInt64.toNat_toBitVec]

/-- `cmp w, #0` of `okWord b`'s low half: `b` false. -/
theorem okW_eq0 (b : Bool) :
    CmpOp.eq.apply .W32 (okWord b).toBitVec (BitVec.ofNat 64 0) = !b := by
  cases b <;> rfl

end

public section
variable [Host] {a : DecArea} {s0 : TState} {L : LayoutW} {m0 : MachineData} {k : Nat}

/-- `.LVerifyBusBalance_22`'s address. -/
theorem fail_at (hp : Placed code k) :
    Labels.label NativeRustcVmArm.Vm.VerifyBusBalance.label_22 = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyBusBalance.b50Offset) :=
  hp.label (label_of_infix b50_in_code rfl)

/-- **A branch to `.LVerifyBusBalance_22` taken** on a failed phase. -/
theorem fail_cond (hp : Placed code k) (h : VerifyBusBalancePre a s0 L m0) {env : Env}
    {c : SBool} {next : Int64} {st : MachineState}
    (hpc : PcOk env (.cond c NativeRustcVmArm.Vm.VerifyBusBalance.label_22) next st) (hc : c.eval env = true)
    (hfr : Fr m0 5488 verifyBusBalanceStack slots keep (outs m0) st.data)
    (hr : (verifyBusBalance L).run s0 = none) :
    Eventually (step1 Host.exe) (Goal a s0 L m0) st :=
  at_pc (((pc_of_cond hpc).1 hc).trans (fail_at hp)) (fail_spec hp h hfr hr)

/-- A branch to `.LVerifyBusBalance_22` not taken. -/
theorem pass_cond {env : Env} {c : SBool} {next : Int64} {st : MachineState}
    (hpc : PcOk env (.cond c NativeRustcVmArm.Vm.VerifyBusBalance.label_22) next st) (hc : c.eval env = false) :
    st.pc = next :=
  (pc_of_cond hpc).2 hc

omit [Host] in
/-- **The bytecode's words** in a state of the frame. -/
theorem bc_words [Labels] (h : VerifyBusBalancePre a s0 L m0) {m : MachineData}
    (hfr : Fr m0 5488 verifyBusBalanceStack slots keep (outs m0) m) :
    NativeRustcVm.wordsOf m.dmem m0.regs.X2.toBitVec m0.regs.X3.toNat = L.bytecode.toList := by
  have e := NativeRustcVm.wordsOf_of_wordsAt (pre_bc h)
  rw [Array.length_toList, pre_n h] at e
  rcases Nat.eq_zero_or_pos m0.regs.X3.toNat with h0 | h0
  · rw [h0] at e ⊢
    rw [← e]
    simp only [NativeRustcVm.wordsOf, List.range_zero, List.map_nil]
  rw [← e]
  refine NativeRustcVmArm.Bus.Fr.wordsOf_eq hfr (pre_stack h) (pre_bcR h).2 (pre_bcS h h0)
    fun j hj hq ↦ ?_
  have hnw := (pre_bcR h).2
  rcases hq with hq | hq | hq
  · exact NativeRustcVm.Apart.not_inRange_add (pre_bcT h h0) hnw (pre_ts h).footprint.1.2 hj hq
  · exact NativeRustcVm.Apart.not_inRange_add (pre_busB h h0).symm hnw (pre_bus h).2.1 hj hq
  · exact NativeRustcVm.Apart.not_inRange_add (pre_clB h h0).symm hnw (pre_cl h).2.1 hj hq

end

public section
variable [Labels]

/-- **At `b32`** (`k + NativeRustcVmArm.Vm.VerifyBusBalance.b32Offset`): the claims pushed; the share and the bytecode's value to check. -/
structure AtShare (a : DecArea) (s0 : TState) (L : LayoutW) (m0 : MachineData)
    (w pt tv mem : Array EW) (beta mf bf : EW) (s3 : TState) (m : MachineData) : Prop where
  fr : Fr m0 5488 verifyBusBalanceStack slots keep (outs m0) m
  run : (verifyBusBalance L).run s0 =
    ((bytecodeShare w (pt.extract 0 L.logBytecode)).run s3).bind fun y4 ↦
      ((computedBytecodeValue L.bytecode y4.1.2.1 y4.1.2.2).run y4.2).bind fun y5 ↦
        some (resultOf L w beta pt tv mem mf bf y4.1.1 y4.1.2.1, y5.2)
  mem' : ShareMem m0 L w pt tv mem beta mf bf m.dmem
  x19 : m.regs.getXReg .X19 = m0.regs.X4
  x20 : m.regs.getXReg .X20 = m0.regs.X1
  x21 : (m.regs.getXReg .X21).toBitVec = loc m0 3136
  x22 : m.regs.getXReg .X22 = beta.c1
  x23 : m.regs.getXReg .X23 = m0.regs.X3
  x24 : m.regs.getXReg .X24 = m0.regs.X2
  x25 : m.regs.getXReg .X25 = m0.regs.X0
  x26 : (m.regs.getXReg .X26).toNat = pt.size
  x27 : m.regs.getXReg .X27 = (min L.logMemory pt.size).toUInt64
  x29 : (m.regs.getXReg .X29).toNat = L.logBytecode
  ts : TStateAt m.dmem m0.regs.X0.toBitVec a s3
  cl : ClaimsWAt m.dmem m0.regs.X5.toBitVec (claimsOf L pt mem mf bf)

end

end NativeRustcVmArm.Bus.VerifyBusBalance
