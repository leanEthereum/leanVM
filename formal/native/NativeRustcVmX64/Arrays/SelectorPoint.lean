module

public import NativeRustcVmX64.Arrays.SelectorPoint.Exec
public import NativeRustcVmX64.Code.Vm.SelectorPoint.Names

/-!
# `selector_point` on x86-64

**`selectorPoint_spec`**: rustc's `selector_point(selector, out)`, placed anywhere in the
program, meets `SelectorPointPre`/`SelectorPointPost`: `out` holds `selectorPoint selector |out|`.
No callee-saved register touched, memory changed only in `out` (within the existing `Frame`
contract). At `|out| = 0` it returns (`b8`); at
`|out| = 1` it stores bit `0` (`b6`-`b8`); else the pair loop (`b3`: `Inv`) stores entries `2t`
and `2t + 1` for `2t + 2 ≤ |out|`, then (`b4`) it returns for an even `|out|` (`b8`) or stores the
last entry (`b5`, `b7`, `b8`). Entry `k` is bit `k` of the selector (the carry of raw
`bt`, `setb`), zero from `k = 64` on (`bitSym_entry`).
-/

namespace NativeRustcVmX64.Arrays.SelectorPoint

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.SelectorPoint NativeVm.Model
  NativeRustcVmX64.Field
open NativeRustcVm (EWsAt EWAt WordAt)

public section

/-- The selector. -/
abbrev sel (m : MachineData) : Nat := (reg m .rdi).toNat
/-- `out`. -/
abbrev out (m : MachineData) : BitVec 64 := reg m .rsi
/-- `|out|`. -/
abbrev len (m : MachineData) : Nat := (reg m .rdx).toNat
/-- The entries `out` gets. -/
abbrev pt (m : MachineData) : List EW := (selectorPoint (sel m) (len m)).toList

theorem length_pt (m : MachineData) : (pt m).length = len m := by simp [selectorPoint]

theorem getElem_pt (m : MachineData) {k : Nat} (h : k < (pt m).length) :
    (pt m)[k] = EW.ofNat ((sel m >>> k) % 2) := by
  simp [selectorPoint]

theorem take_pt_succ (m : MachineData) {j : Nat} (h : j < len m) :
    (pt m).take (j + 1) = (pt m).take j ++ [EW.ofNat ((sel m >>> j) % 2)] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by rw [length_pt]; exact h), Option.toList_some,
    getElem_pt]

/-! ## The entries' values -/

/-- The carry of raw `bt` uses the register index modulo 64. -/
theorem bt_bit (x y : BitVec 64) {t : Nat} (hs : y.toNat % 64 = t) :
    CmpOp.apply .bit .W64 x y = decide ((x.toNat >>> t) % 2 = 1) := by
  simp only [CmpOp.apply, low_W64, show Width.W64.bits = 64 from rfl, hs,
    BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]

theorem setb_entry [Labels] (env : Env) (z : Sym) {idx : Nat}
    (hs : (z.eval env).toNat % 64 = idx) :
    ewArg ((setbSym z).eval env) 0#64 = EW.ofNat (((env.regs .rdi).toNat >>> idx) % 2) := by
  show ewArg (BinOp.apply .merge .W8 (BitVec.ofNat 64 0)
    (if CmpOp.apply .bit .W64 (env.regs .rdi) (z.eval env) = true
      then BitVec.ofNat 64 1 else BitVec.ofNat 64 0)) 0#64 = _
  rw [bt_bit _ _ hs, setb_eval, ewArg_bit]

theorem zero_entry (x : BitVec 64) {idx : Nat} (h : 64 ≤ idx) :
    ewArg 0#64 0#64 = EW.ofNat ((x.toNat >>> idx) % 2) := by
  have hx := x.isLt
  rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hx
    (Nat.pow_le_pow_right (by decide) h))]
  rfl

/-- The first entry's count: R8. -/
theorem z9_shift [Labels] (env : Env) (h : (env.regs .r8).toNat < 64) :
    (z9.eval env).toNat % 64 = (env.regs .r8).toNat :=
  Nat.mod_eq_of_lt h

/-- The second entry's count: R8 + 1. -/
theorem z11_shift [Labels] (env : Env) (h : (env.regs .r8).toNat < 63) :
    (z11.eval env).toNat % 64 = (env.regs .r8).toNat + 1 := by
  have hz : (UnOp.apply (.zext .W8) .W32 (UnOp.apply .trunc .W32
      (BinOp.apply .add .W64 (env.regs .r8) (BitVec.ofNat 64 1)))).toNat =
      (env.regs .r8).toNat + 1 := by
    simp only [UnOp.apply, BinOp.apply, toNat_ext, toNat_low, low_W64, ext_W64,
      BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat,
      show Width.W32.bits = 32 from rfl, show Width.W8.bits = 8 from rfl]
    omega
  change (UnOp.apply (.zext .W8) .W32 (UnOp.apply .trunc .W32
    (BinOp.apply .add .W64 (env.regs .r8) (BitVec.ofNat 64 1)))).toNat % 64 = _
  rw [hz, Nat.mod_eq_of_lt (by omega)]

theorem ult64 (v : BitVec 64) : CmpOp.apply .ult .W64 v (BitVec.ofNat 64 64) = decide (v.toNat < 64) := by
  simp only [CmpOp.apply, low_W64]
  rw [Bool.eq_iff_iff, decide_eq_true_iff, BitVec.ult_iff_lt, BitVec.lt_def,
    toNat_ofNat_lt (by decide)]

/-- **An entry of the pair loop**: bit `idx` of RDI, `idx` the count where R8 < 64; zero (RCX)
where R8 ≥ 64 and `idx ≥ 64`. -/
theorem bitSym_entry [Labels] (env : Env) (z : Sym) {idx : Nat} (hcx : env.regs .rcx = 0#64)
    (h1 : (env.regs .r8).toNat < 64 → (z.eval env).toNat % 64 = idx ∧ idx < 64)
    (h2 : 64 ≤ (env.regs .r8).toNat → 64 ≤ idx) :
    ewArg ((bitSym z).eval env) 0#64 = EW.ofNat (((env.regs .rdi).toNat >>> idx) % 2) := by
  show ewArg (if (!(CmpOp.apply .ult .W64 (env.regs .r8) (BitVec.ofNat 64 64))) = true then
    env.regs .rcx else (setbSym z).eval env) 0#64 = _
  rw [ult64]
  by_cases h : (env.regs .r8).toNat < 64
  · rw [decide_eq_true h]
    exact setb_entry env z (h1 h).1
  · rw [decide_eq_false h]
    show ewArg (env.regs .rcx) 0#64 = _
    rw [hcx]
    exact zero_entry _ (h2 (by omega))

/-- **The last entry for an odd `|out| ≥ 3`** (`b5`): bit R8 of RDI, zero from R8 = 64 on. -/
theorem odd_entry [Labels] (env : Env) {idx : Nat} (h8 : (env.regs .r8).toNat = idx) :
    ewArg ((Sym.ite (.cmp .ult .W64 (.reg .r8) (.lit 64)) (setbSym z9) (.lit 0)).eval env) 0#64 =
      EW.ofNat (((env.regs .rdi).toNat >>> idx) % 2) := by
  show ewArg (if CmpOp.apply .ult .W64 (env.regs .r8) (BitVec.ofNat 64 64) = true then
    (setbSym z9).eval env else BitVec.ofNat 64 0) 0#64 = _
  rw [ult64]
  by_cases h : (env.regs .r8).toNat < 64
  · rw [decide_eq_true h]
    exact setb_entry env z9 ((z9_shift env h).trans h8)
  · rw [decide_eq_false h]
    exact zero_entry _ (by omega)

theorem ewArg_mod2 (x : Nat) : ewArg (BitVec.ofNat 64 (x % 2)) 0#64 = EW.ofNat (x % 2) := by
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;> rw [h] <;> rfl

/-- **The only entry for `|out| = 1`** (`b6`): bit `0` of RDI. -/
theorem one_entry [Labels] (env : Env) :
    ewArg ((Sym.bin .and .W32 (.reg .rdi) (.lit 1)).eval env) 0#64 =
      EW.ofNat (((env.regs .rdi).toNat >>> 0) % 2) := by
  show ewArg (BinOp.apply .and .W32 (env.regs .rdi) (BitVec.ofNat 64 1)) 0#64 = _
  rw [Nat.shiftRight_zero, ← ewArg_mod2]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BinOp.apply, toNat_ext, BitVec.toNat_and, toNat_low, BitVec.toNat_ofNat]
  rw [show Width.W32.bits = 32 from rfl, show (1 : Nat) % 2 ^ 64 % 2 ^ 32 = 1 from rfl,
    Nat.and_one_is_mod]
  omega

/-- `x &&& (2^64 - 2)`: `x` rounded down to even. -/
theorem and_even (x : Nat) (hx : x < 2 ^ 64) : x &&& (2 ^ 64 - 2) = 2 * (x / 2) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, show (2 : Nat) ^ 64 - 2 = (2 ^ 63 - 1) <<< 1 by decide,
    show 2 * (x / 2) = (x >>> 1) <<< 1 by rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]; omega,
    Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one,
    Nat.testBit_shiftRight]
  rcases i with _ | i
  · simp
  · rw [show 1 + (i + 1 - 1) = i + 1 by omega]
    by_cases hi : i < 63
    · simp [hi]
    · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide)
        (by omega)))]
      simp

/-- `testb $1, %dl`, `je`. -/
theorem and1_eq (v : BitVec 64) :
    CmpOp.apply .eq .W8 (BinOp.apply .and .W8 v (BitVec.ofNat 64 1)) (BitVec.ofNat 64 0) =
      decide (v.toNat % 2 = 0) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  simp only [CmpOp.apply, beq_iff_eq, BitVec.toNat_eq, BinOp.apply, toNat_low, toNat_ext,
    BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show Width.W8.bits = 8 from rfl, show (1 : Nat) % 2 ^ 64 % 2 ^ 8 = 1 from rfl,
    Nat.and_one_is_mod]
  omega

/-! ## The frame -/

/-- What every state keeps: RSP, the callee-saved registers, memory but `out` and the 16 bytes
below RSP, every mapped byte. -/
structure Frame (m0 s : MachineData) : Prop where
  rsp : rspOf s = rspOf m0
  regs : ∀ r, calleeSaved r = true → reg s r = reg m0 r
  kept : Kept m0.dmem s.dmem
  same : Changes m0 s selectorPointStack (out m0) (16 * len m0)

/-- The return address is in neither `out` nor the 16 bytes below RSP. -/
theorem ret_same {m0 s : MachineData} (hpre : SelectorPointPre m0)
    (hc : Changes m0 s selectorPointStack (out m0) (16 * len m0)) :
    ∀ j < 8, s.dmem.get? (rspOf m0 + BitVec.ofNat 64 j) =
      m0.dmem.get? (rspOf m0 + BitVec.ofNat 64 j) := by
  intro j hj
  have hS : StackOk m0 16 := hpre.1
  have hS1 := hS.1
  have hS2 := hS.2.1
  refine hc _ fun h ↦ h.elim (ret_not_in hpre.1 hpre.2.1.2 hpre.2.2 j hj) fun h ↦ ?_
  have := (rspOf m0).isLt
  simp only [selectorPointStack] at h
  rw [Sym.inRange_iff (by rw [stackBelow_toNat hS1]; omega), stackBelow_toNat hS1,
    toNat_add_ofNat _ _ (by omega)] at h
  omega

/-- A block of registers only keeps the frame. -/
theorem Frame.regs_block [Labels] {m0 s s' : MachineData} {S' : SState} {rs : List Reg64}
    (hF : Frame m0 s) (hm : Match (Env.ofMachine s []) S' s')
    (hk : keepsAll regsS S' (rs ++ Arrays.calleeRegs) = true) :
    Frame m0 s' ∧ (∀ r ∈ rs, reg s' r = reg s r) ∧ s'.dmem = s.dmem := by
  unfold keepsAll at hk
  simp only [Bool.and_eq_true, List.isEmpty_iff] at hk
  obtain ⟨hr, hmem⟩ := hk
  have he := regs_eq_of (match_nil _) hm hr
  have hdm : s'.dmem = s.dmem := hm.dmem_eq (Env.wf_nil _) hmem
  refine ⟨⟨?_, fun r h ↦ (he r (List.mem_cons_of_mem _ (List.mem_append_right _
    (mem_calleeRegs h)))).trans (hF.regs r h), by rw [hdm]; exact hF.kept,
    fun p hp ↦ by rw [hdm]; exact hF.same p hp⟩,
    fun r h ↦ he r (List.mem_cons_of_mem _ (List.mem_append_left _ h)), hdm⟩
  show reg s' .rsp = _
  rw [he .rsp (by simp)]; exact hF.rsp

variable [Host] {k : Nat}

theorem hb0 (hp : Placed code k) : b0.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.SelectorPoint.b0Offset) :=
  b0_in_code.trans hp.1 (by simp [b0])
theorem hb1 (hp : Placed code k) : b1.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.SelectorPoint.b1Offset) :=
  b1_in_code.trans hp.1 (by simp [b1])
theorem hb2 (hp : Placed code k) : b2.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.SelectorPoint.b2Offset) :=
  b2_in_code.trans hp.1 (by simp [b2])
theorem hb3 (hp : Placed code k) : b3.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.SelectorPoint.b3Offset) :=
  b3_in_code.trans hp.1 (by simp [b3])
theorem hb4 (hp : Placed code k) : b4.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.SelectorPoint.b4Offset) :=
  b4_in_code.trans hp.1 (by simp [b4])
theorem hb5 (hp : Placed code k) : b5.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.SelectorPoint.b5Offset) :=
  b5_in_code.trans hp.1 (by simp [b5])
theorem hb6 (hp : Placed code k) : b6.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.SelectorPoint.b6Offset) :=
  b6_in_code.trans hp.1 (by simp [b6])
theorem hb7 (hp : Placed code k) : b7.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.SelectorPoint.b7Offset) :=
  b7_in_code.trans hp.1 (by simp [b7])
theorem hb8 (hp : Placed code k) : b8.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.SelectorPoint.b8Offset) :=
  b8_in_code.trans hp.1 (by simp [b8])
theorem hb78 (hp : Placed code k) : (b7 ++ b8).IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.SelectorPoint.b7Offset) :=
  isInfixAt_concat (hb7 hp) (hb8 hp)
theorem hb678 (hp : Placed code k) : (b6 ++ b7 ++ b8).IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.SelectorPoint.b6Offset) :=
  isInfixAt_concat (isInfixAt_concat (hb6 hp) (hb7 hp)) (hb8 hp)

theorem lbl_entry (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.SelectorPoint.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.SelectorPoint.b0Offset) :=
  hp.label NativeRustcVmX64.Vm.SelectorPoint.entry_at
theorem lbl_2 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.SelectorPoint.label_2 = Host.addrOf (k + NativeRustcVmX64.Vm.SelectorPoint.b6Offset) :=
  hp.label NativeRustcVmX64.Vm.SelectorPoint.label_2_at
theorem lbl_4 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.SelectorPoint.label_4 = Host.addrOf (k + NativeRustcVmX64.Vm.SelectorPoint.b3Offset) :=
  hp.label NativeRustcVmX64.Vm.SelectorPoint.label_4_at
theorem lbl_7 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.SelectorPoint.label_7 = Host.addrOf (k + NativeRustcVmX64.Vm.SelectorPoint.b7Offset) :=
  hp.label NativeRustcVmX64.Vm.SelectorPoint.label_7_at
theorem lbl_8 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.SelectorPoint.label_8 = Host.addrOf (k + NativeRustcVmX64.Vm.SelectorPoint.b8Offset) :=
  hp.label NativeRustcVmX64.Vm.SelectorPoint.label_8_at

/-- The postcondition, reached. -/
abbrev Post (m0 : MachineData) (s : MachineState) : Prop :=
  s.pc = retOf m0 ∧ rspOf s.data = rspOf m0 + 8#64 ∧ SelectorPointPost m0 s.data

/-- **The return without a last entry** (`b8`), every entry stored. -/
theorem finish8 (hp : Placed code k) {m0 : MachineData} (hpre : SelectorPointPre m0)
    {s : MachineState} (hpc : s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SelectorPoint.b8Offset)) (hF : Frame m0 s.data)
    (hE : EWsAt s.data.dmem (out m0) (pt m0)) : Eventually (step1 Host.exe) (Post m0) s := by
  have hS : StackOk m0 16 := hpre.1
  have hwf := frame_wf (m := s.data) (vars := fun _ ↦ 0) (ret := 0) hS hF.kept
  have hm : Match (frameEnv m0 s.data 16) (frameS 16) s.data :=
    match_ofMachine ⟨rfl, trivial⟩
      ⟨show rspOf s.data = stackBelow m0 16 + BitVec.ofInt 64 ((16 + 0 : Nat) : Int) by
        rw [frame_rsp, hF.rsp]; simp, trivial⟩ trivial trivial trivial
  refine exec_at (hb8 hp) run_b8 hwf (by intro l h; cases h) hpc hm fun s' hm' hpc' ↦ .done _ ?_
  obtain ⟨hsp, hmem, hkeep⟩ := after_eq run_b8 ▸ b8_facts
  have hdm : s'.data.dmem = s.data.dmem := hm'.dmem_eq hwf hmem
  refine ⟨?_, ?_, ?_, fun p hp ↦ by rw [hdm]; exact hF.same p hp, fun r hr ↦ ?_,
    fun p h ↦ hm'.kept hwf p (hF.kept p h)⟩
  · simp only [PcOk] at hpc'
    rw [hpc']
    exact load_ret hS (ret_same hpre hF.same)
  · show s'.data.regs.get64 .rsp = _
    rw [hm'.regs .rsp _ hsp]
    exact frame_rsp 16 8
  · rw [hdm]; exact hE
  · exact (regs_eq_of hm hm' hkeep r (mem_calleeRegs hr)).trans (hF.regs r hr)

/-- **The last entry and the return** (`b7`-`b8` or `b6`-`b8`): entry `|out| - 1` stored from RSI,
the earlier entries already there. -/
theorem finishLast {bb : List Directive} {kb : Nat} {S : SState} {v : Sym}
    (hk : bb.IsInfixAt Host.prog kb) (hx : exec bb lastS = some (S, .ret (.load 0 16 8)))
    (hf : keepsRegs lastS S Arrays.calleeRegs = true ∧
      S.reg .rsp = some (.ptr 0 ((16 + 8 : Nat) : Int)) ∧
      (∀ w ∈ S.mem, w.r = 1 ∧ w.off + w.n ≤ 16) ∧
      (∀ i < 8, findWrite 1 (0 + i) S.mem = some (v, i)) ∧
      (∀ i < 8, findWrite 1 (0 + 8 + i) S.mem = some (.lit 0, i)))
    {m0 : MachineData} (hpre : SelectorPointPre m0) {s : MachineState}
    (hpc : s.pc = Host.addrOf kb) (hF : Frame m0 s.data) (hlen : 1 ≤ len m0)
    (hsi : reg s.data .rsi = out m0 + BitVec.ofNat 64 (16 * (len m0 - 1)))
    (hE : EWsAt s.data.dmem (out m0) ((pt m0).take (len m0 - 1)))
    (hv : ewArg (v.eval (Env.ofMachine s.data [(stackBelow m0 16, 24),
      (out m0 + BitVec.ofNat 64 (16 * (len m0 - 1)), 16)])) 0#64 =
      EW.ofNat ((sel m0 >>> (len m0 - 1)) % 2)) :
    Eventually (step1 Host.exe) (Post m0) s := by
  obtain ⟨hkeep, hsp, hw, hu, hz⟩ := hf
  obtain ⟨hS, ⟨hmO, hnO⟩, hoO⟩ := hpre
  have hS16 : StackOk m0 16 := hS
  have hS1 := hS16.1
  have hr0 := (rspOf m0).isLt
  have hnO' : (out m0).toNat + 16 * len m0 ≤ 2 ^ 64 := hnO
  have hL : len m0 = (reg m0 .rdx).toNat := rfl
  have eO : (out m0).toNat = (reg m0 .rsi).toNat := rfl
  have hfb : (stackBelow m0 16).toNat = (rspOf m0).toNat - 16 := stackBelow_toNat hS1
  have hoO' := hoO
  simp only [OffStack, Apart, selectorPointStack] at hoO'
  rw [hfb] at hoO'
  have heO : (out m0 + BitVec.ofNat 64 (16 * (len m0 - 1))).toNat =
      (out m0).toNat + 16 * (len m0 - 1) := toNat_add_ofNat _ _ (by omega)
  have hwf : (Env.ofMachine s.data [(stackBelow m0 16, 24),
      (out m0 + BitVec.ofNat 64 (16 * (len m0 - 1)), 16)]).WF := by
    refine Env.wf_of ⟨⟨fun i hi ↦ hF.kept _ (hS16.2.2 i hi), ?_⟩, ⟨fun i hi ↦ ?_, ?_⟩, trivial⟩ ?_
    · show (stackBelow m0 16).toNat + 24 ≤ 2 ^ 64
      rw [hfb]; have := hS16.2.1; omega
    · show (s.data.dmem.get? (out m0 + BitVec.ofNat 64 (16 * (len m0 - 1)) +
        BitVec.ofNat 64 i)).isSome
      rw [addr_add]; exact hF.kept _ (hmO _ (by have : i < 16 := hi; omega))
    · show (out m0 + BitVec.ofNat 64 (16 * (len m0 - 1))).toNat + 16 ≤ 2 ^ 64
      rw [heO]; omega
    · refine List.pairwise_pair.mpr ?_
      show Apart (stackBelow m0 16) 24 (out m0 + BitVec.ofNat 64 (16 * (len m0 - 1))) 16
      unfold Apart; rw [hfb, heO]; omega
  have hm : Match (Env.ofMachine s.data [(stackBelow m0 16, 24),
      (out m0 + BitVec.ofNat 64 (16 * (len m0 - 1)), 16)]) lastS s.data := by
    refine match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨?_, ?_, trivial⟩ trivial trivial trivial
    · show rspOf s.data = stackBelow m0 16 + BitVec.ofInt 64 ((16 + 0 : Nat) : Int)
      rw [frame_rsp, hF.rsp]; simp
    · show reg s.data .rsi = _ + BitVec.ofInt 64 0
      rw [hsi]; simp
  refine exec_at hk hx hwf (by intro l h; cases h) hpc hm fun s' hm' hpc' ↦ .done _ ?_
  have hwr : ∀ p, Written (Env.ofMachine s.data [(stackBelow m0 16, 24),
      (out m0 + BitVec.ofNat 64 (16 * (len m0 - 1)), 16)]) S p →
      InRange (out m0 + BitVec.ofNat 64 (16 * (len m0 - 1))) 16 p :=
    fun p h ↦ written_region (r := 1) rfl hwf le_rfl hw h
  have hnE : NoWrap (out m0 + BitVec.ofNat 64 (16 * (len m0 - 1))) 16 := by
    unfold NoWrap; rw [heO]; omega
  have hsame : Changes m0 s'.data selectorPointStack (out m0) (16 * len m0) := fun p hp ↦ by
    rw [hm'.get?_mem0 hwf fun h ↦ hp (Or.inl ?_)]
    · exact hF.same p hp
    · have h1 := hwr p h
      rw [Sym.inRange_iff hnE, heO] at h1
      rw [Sym.inRange_iff hnO]; omega
  refine ⟨?_, ?_, ?_, hsame, fun r hr ↦ ?_, fun p h ↦ hm'.kept hwf p (hF.kept p h)⟩
  · simp only [PcOk] at hpc'
    rw [hpc']
    exact load_ret2 hS16 (ret_same ⟨hS, ⟨hmO, hnO⟩, hoO⟩ hF.same)
  · show s'.data.regs.get64 .rsp = _
    rw [hm'.regs .rsp _ hsp]
    exact frame_rsp 16 8
  · have hpt : pt m0 = (pt m0).take (len m0 - 1) ++ [EW.ofNat ((sel m0 >>> (len m0 - 1)) % 2)] := by
      rw [← take_pt_succ m0 (by omega), show len m0 - 1 + 1 = len m0 by omega,
        List.take_of_length_le (by rw [length_pt])]
    have hlt : ((pt m0).take (len m0 - 1)).length = len m0 - 1 := by
      rw [List.length_take, length_pt]; omega
    show EWsAt s'.data.dmem (out m0) (pt m0)
    rw [hpt, NativeRustcVm.ewsAt_append, NativeRustcVm.ewsAt_singleton, hlt]
    constructor
    · refine ewsAt_congr hE fun i hi ↦ hm'.get?_mem0 hwf fun h ↦ ?_
      rw [hlt] at hi
      have h1 := hwr _ h
      rw [Sym.inRange_iff hnE, heO, toNat_add_ofNat _ _ (by omega)] at h1
      omega
    · have a := ewAt_of_writes hm' (r := 1) (o := 0) rfl (by decide) hu hz
      rw [add_ofNat_zero, eval_lit, hv] at a
      exact a
  · exact (regs_eq_of hm hm' hkeep r (mem_calleeRegs hr)).trans (hF.regs r hr)

/-- **The pair loop's head** `NativeRustcVmX64.Vm.SelectorPoint.label_4`, `t` pairs stored. -/
structure Inv (m0 : MachineData) (t : Nat) (s : MachineData) : Prop where
  frame : Frame m0 s
  lt : 2 * t + 2 ≤ len m0
  rax : reg s .rax = BitVec.ofNat 64 (2 * (len m0 / 2))
  r8 : reg s .r8 = BitVec.ofNat 64 (2 * t)
  rcx : reg s .rcx = 0#64
  rdi : reg s .rdi = reg m0 .rdi
  rsi : reg s .rsi = out m0 + BitVec.ofNat 64 (32 * t)
  rdx : reg s .rdx = BitVec.ofNat 64 (len m0 + (2 ^ 60 - 1))
  ents : EWsAt s.dmem (out m0) ((pt m0).take (2 * t))

/-- **After the pairs** (`b4`): the return for an even `|out|`, else the last entry (`b5`, `b7`,
`b8`). -/
theorem afterPairs (hp : Placed code k) {m0 : MachineData} (hpre : SelectorPointPre m0)
    {s : MachineState} (hpc : s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SelectorPoint.b4Offset)) (hF : Frame m0 s.data)
    (hlen : len m0 < 2 ^ 60)
    (hr8 : reg s.data .r8 = BitVec.ofNat 64 (2 * (len m0 / 2)))
    (hrdi : reg s.data .rdi = reg m0 .rdi)
    (hrsi : reg s.data .rsi = out m0 + BitVec.ofNat 64 (16 * (2 * (len m0 / 2))))
    (hrdx : reg s.data .rdx = BitVec.ofNat 64 (len m0 + (2 ^ 60 - 1)))
    (hE : EWsAt s.data.dmem (out m0) ((pt m0).take (2 * (len m0 / 2)))) :
    Eventually (step1 Host.exe) (Post m0) s := by
  refine exec_at (hb4 hp) run_b4 (Env.wf_nil _) (by intro l h; cases h) hpc (match_nil _)
    fun s4 hm4 hpc4 ↦ ?_
  obtain ⟨hF4, e4, hdm4⟩ := hF.regs_block hm4 b4_keeps
  simp only [PcOk, NativeRustcVmX64.Vm.SelectorPoint.b4_length] at hpc4
  rw [eval_not] at hpc4
  rw [show (SBool.cmp .eq .W8 (.bin .and .W8 (.reg .rdx) (.lit 1)) (.lit 0)).eval
    (Env.ofMachine s.data []) = CmpOp.apply .eq .W8 (BinOp.apply .and .W8 (reg s.data .rdx)
      (BitVec.ofNat 64 1)) (BitVec.ofNat 64 0) from rfl, and1_eq, hrdx,
    toNat_ofNat_lt (by omega)] at hpc4
  obtain ⟨hT, hFl⟩ := pc_cond hpc4
  by_cases hev : len m0 % 2 = 0
  · -- even: every entry stored.
    refine finish8 hp hpre ((hT (by simp; omega)).trans (lbl_8 hp)) hF4 ?_
    rw [hdm4, ← List.take_of_length_le (l := pt m0) (i := 2 * (len m0 / 2))
      (by rw [length_pt]; omega)]
    exact hE
  · -- odd: the last entry.
    have hpc5 := hFl (by simp; omega)
    have hS : StackOk m0 16 := hpre.1
    have hwf := frame_wf (m := s4.data) (vars := fun _ ↦ 0) (ret := 0) hS hF4.kept
    have hm : Match (frameEnv m0 s4.data 16) oddS s4.data :=
      match_ofMachine ⟨rfl, trivial⟩
        ⟨show rspOf s4.data = stackBelow m0 16 + BitVec.ofInt 64 ((16 + 0 : Nat) : Int) by
          rw [frame_rsp, hF4.rsp]; simp, trivial⟩ trivial trivial trivial
    refine exec_at (hb5 hp) run_b5 hwf (by intro l h; cases h) hpc5 hm fun s5 hm5 hpc5' ↦ ?_
    obtain ⟨hk5, hw5, hdi5⟩ := after_eq run_b5 ▸ b5_facts
    have e5 := regs_eq_of hm hm5 hk5
    have hso := frame_outside hS hF4.kept hm5 (by decide) hw5
    have hF5 : Frame m0 s5.data := by
      refine ⟨?_, fun r hr ↦ (e5 r (List.mem_append_right _ (mem_calleeRegs hr))).trans
        (hF4.regs r hr), fun p h ↦ hm5.kept hwf p (hF4.kept p h), fun p hp ↦ ?_⟩
      · show reg s5.data .rsp = _
        rw [e5 .rsp (by simp)]; exact hF4.rsp
      · rw [hso p fun h ↦ hp (Or.inr h)]; exact hF4.same p hp
    simp only [PcOk] at hpc5'
    have hl1 : len m0 - 1 = 2 * (len m0 / 2) := by omega
    refine finishLast (hb78 hp) run_b78 (after_eq run_b78 ▸ b78_facts) hpre
      (hpc5'.trans (lbl_7 hp)) hF5 (by omega) ?_ ?_ ?_
    · rw [e5 .rsi (by simp), e4 .rsi (by simp), hrsi, hl1]
    · rw [hl1]
      refine ewsAt_congr (d := s4.data.dmem) (by rw [hdm4]; exact hE) fun i hi ↦ ?_
      rw [List.length_take, length_pt] at hi
      refine hso _ fun h ↦ ?_
      have hS1 := hS.1
      have := (rspOf m0).isLt
      have hoO := hpre.2.2
      have hL : len m0 = (reg m0 .rdx).toNat := rfl
      have eO : (out m0).toNat = (reg m0 .rsi).toNat := rfl
      simp only [OffStack, Apart, selectorPointStack] at hoO
      have hnO := hpre.2.1.2
      unfold NoWrap at hnO
      rw [stackBelow_toNat hS1] at hoO
      rw [Sym.inRange_iff (by rw [stackBelow_toNat hS1]; omega), stackBelow_toNat hS1,
        toNat_add_ofNat _ _ (by omega)] at h
      omega
    · show ewArg (reg s5.data .rdi) 0#64 = _
      rw [show reg s5.data .rdi = _ from hm5.regs .rdi _ hdi5, odd_entry _ (idx := len m0 - 1)]
      · show EW.ofNat (((reg s4.data .rdi).toNat >>> _) % 2) = _
        rw [e4 .rdi (by simp), hrdi]
      · show (reg s4.data .r8).toNat = _
        rw [e4 .r8 (by simp), hr8, toNat_ofNat_lt (by omega)]; omega

/-- **A turn of the pair loop**: entries `2t`, `2t + 1` stored, back at the head or past the
pairs. -/
theorem step (hp : Placed code k) {m0 : MachineData} (hpre : SelectorPointPre m0) {t : Nat}
    {s : MachineState} (hpc : s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SelectorPoint.b3Offset)) (hI : Inv m0 t s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ Post m0 s' ∨
      (s'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SelectorPoint.b3Offset) ∧ Inv m0 (t + 1) s'.data)) s := by
  obtain ⟨hS, ⟨hmO, hnO⟩, hoO⟩ := hpre
  have hS16 : StackOk m0 16 := hS
  have hS1 := hS16.1
  have hr0 := (rspOf m0).isLt
  have hnO' : (out m0).toNat + 16 * len m0 ≤ 2 ^ 64 := hnO
  have hL : len m0 = (reg m0 .rdx).toNat := rfl
  have eO : (out m0).toNat = (reg m0 .rsi).toNat := rfl
  have hfb : (stackBelow m0 16).toNat = (rspOf m0).toNat - 16 := stackBelow_toNat hS1
  have hoO' := hoO
  simp only [OffStack, Apart, selectorPointStack] at hoO'
  rw [hfb] at hoO'
  have hlt := hI.lt
  have hlen : len m0 < 2 ^ 60 := by omega
  have heO : (out m0 + BitVec.ofNat 64 (32 * t)).toNat = (out m0).toNat + 32 * t :=
    toNat_add_ofNat _ _ (by omega)
  have hF := hI.frame
  have hwf : (Env.ofMachine s.data [(stackBelow m0 16, 24),
      (out m0 + BitVec.ofNat 64 (32 * t), 32)]).WF := by
    refine Env.wf_of ⟨⟨fun i hi ↦ hF.kept _ (hS16.2.2 i hi), ?_⟩, ⟨fun i hi ↦ ?_, ?_⟩, trivial⟩ ?_
    · show (stackBelow m0 16).toNat + 24 ≤ 2 ^ 64
      rw [hfb]; have := hS16.2.1; omega
    · show (s.data.dmem.get? (out m0 + BitVec.ofNat 64 (32 * t) + BitVec.ofNat 64 i)).isSome
      rw [addr_add]; exact hF.kept _ (hmO _ (by have : i < 32 := hi; omega))
    · show (out m0 + BitVec.ofNat 64 (32 * t)).toNat + 32 ≤ 2 ^ 64
      rw [heO]; omega
    · refine List.pairwise_pair.mpr ?_
      show Apart (stackBelow m0 16) 24 (out m0 + BitVec.ofNat 64 (32 * t)) 32
      unfold Apart; rw [hfb, heO]; omega
  have hm : Match (Env.ofMachine s.data [(stackBelow m0 16, 24),
      (out m0 + BitVec.ofNat 64 (32 * t), 32)]) pairS s.data := by
    refine match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨?_, ?_, trivial⟩ trivial trivial trivial
    · show rspOf s.data = stackBelow m0 16 + BitVec.ofInt 64 ((16 + 0 : Nat) : Int)
      rw [frame_rsp, hF.rsp]; simp
    · show reg s.data .rsi = _ + BitVec.ofInt 64 0
      rw [hI.rsi]; simp
  refine exec_at (hb3 hp) run_b3 hwf (by intro l h; cases h) hpc hm fun s3 hm3 hpc3 ↦ ?_
  obtain ⟨hk3, hw3, hu0, hz0, hu1, hz1⟩ := after_eq run_b3 ▸ b3_facts
  have e3 := regs_eq_of hm hm3 hk3
  have hsame3 := same01 hm3 hwf (k0 := 16) (k1 := 32) (by decide) le_rfl hw3
  have hnE : NoWrap (out m0 + BitVec.ofNat 64 (32 * t)) 32 := by
    unfold NoWrap; rw [heO]; omega
  have hnS : NoWrap (stackBelow m0 16) 16 := by unfold NoWrap; rw [hfb]; omega
  -- the frame
  have hF3 : Frame m0 s3.data := by
    refine ⟨?_, fun r hr ↦ (e3 r (List.mem_append_right _ (mem_calleeRegs hr))).trans
      (hF.regs r hr), fun p h ↦ hm3.kept hwf p (hF.kept p h), fun p hp ↦ ?_⟩
    · show reg s3.data .rsp = _
      rw [e3 .rsp (by simp [pairRegs])]; exact hF.rsp
    · rw [hsame3 p (fun h ↦ hp (Or.inr ?_)) (fun h ↦ hp (Or.inl ?_))]
      · exact hF.same p hp
      · simpa [selectorPointStack] using h
      · rw [Sym.inRange_iff hnE, heO] at h; rw [Sym.inRange_iff hnO]; omega
  -- the two entries
  have hcx : (Env.ofMachine s.data [(stackBelow m0 16, 24),
      (out m0 + BitVec.ofNat 64 (32 * t), 32)]).regs .rcx = 0#64 := hI.rcx
  have h8 : ((Env.ofMachine s.data [(stackBelow m0 16, 24),
      (out m0 + BitVec.ofNat 64 (32 * t), 32)]).regs .r8).toNat = 2 * t := by
    show (reg s.data .r8).toNat = _
    rw [hI.r8, toNat_ofNat_lt (by omega)]
  have hdi : ((Env.ofMachine s.data [(stackBelow m0 16, 24),
      (out m0 + BitVec.ofNat 64 (32 * t), 32)]).regs .rdi).toNat = sel m0 := by
    show (reg s.data .rdi).toNat = _
    rw [hI.rdi]
  have v0 := bitSym_entry _ z9 (idx := 2 * t) hcx
    (fun h ↦ ⟨(z9_shift _ h).trans h8, by omega⟩) (fun h ↦ by omega)
  have v1 := bitSym_entry _ z11 (idx := 2 * t + 1) hcx
    (fun h ↦ ⟨(z11_shift _ (by omega)).trans (by rw [h8]), by omega⟩) (fun h ↦ by omega)
  rw [hdi] at v0 v1
  have a0 := ewAt_of_writes hm3 (r := 1) (o := 0) rfl (by decide) hu0 hz0
  have a1 := ewAt_of_writes hm3 (r := 1) (o := 16) rfl (by decide) hu1 hz1
  rw [add_ofNat_zero, show (Sym.lit 0).eval (Env.ofMachine s.data [(stackBelow m0 16, 24),
    (out m0 + BitVec.ofNat 64 (32 * t), 32)]) = 0#64 from rfl, v0] at a0
  rw [show (Sym.lit 0).eval (Env.ofMachine s.data [(stackBelow m0 16, 24),
    (out m0 + BitVec.ofNat 64 (32 * t), 32)]) = 0#64 from rfl, v1, addr_add] at a1
  have hE : EWsAt s3.data.dmem (out m0) ((pt m0).take (2 * (t + 1))) := by
    rw [show 2 * (t + 1) = 2 * t + 1 + 1 by omega, take_pt_succ m0 (by omega),
      take_pt_succ m0 (by omega), NativeRustcVm.ewsAt_append, NativeRustcVm.ewsAt_append,
      NativeRustcVm.ewsAt_singleton, NativeRustcVm.ewsAt_singleton]
    have hl : ((pt m0).take (2 * t)).length = 2 * t := by
      rw [List.length_take, length_pt]; omega
    rw [List.length_append, hl, List.length_singleton]
    refine ⟨⟨ewsAt_congr hI.ents fun i hi ↦ ?_, ?_⟩, ?_⟩
    · rw [hl] at hi
      refine hsame3 _ ?_ ?_
      · rw [Sym.inRange_iff hnS, toNat_add_ofNat _ _ (by omega), hfb]; omega
      · rw [Sym.inRange_iff hnE, heO, toNat_add_ofNat _ _ (by omega)]; omega
    · rw [show 16 * (2 * t) = 32 * t by omega]
      exact a0
    · rw [show 16 * (2 * t + 1) = 32 * t + 16 by omega]
      exact a1
  have r3 : ∀ r ∈ [Reg64.rax, .rcx, .rdx, .rdi], reg s3.data r = reg s.data r := by
    intro r h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl <;> exact e3 _ (by simp [pairRegs])
  have h8' : reg s3.data .r8 = BitVec.ofNat 64 (2 * (t + 1)) := by
    rw [show reg s3.data .r8 = (Sym.bin .add .W64 (.lit 2) (.reg .r8)).eval
      (Env.ofMachine s.data [(stackBelow m0 16, 24), (out m0 + BitVec.ofNat 64 (32 * t), 32)])
      from hm3.regs .r8 _ (by decide +kernel), eval_add, eval_lit, eval_reg]
    show _ + reg s.data .r8 = _
    rw [hI.r8, ← BitVec.ofNat_add]
    exact congrArg _ (by omega)
  have hsi' : reg s3.data .rsi = out m0 + BitVec.ofNat 64 (32 * (t + 1)) := by
    rw [show reg s3.data .rsi = (Sym.ptr 1 32).eval
      (Env.ofMachine s.data [(stackBelow m0 16, 24), (out m0 + BitVec.ofNat 64 (32 * t), 32)])
      from hm3.regs .rsi _ (by decide +kernel)]
    show out m0 + BitVec.ofNat 64 (32 * t) + BitVec.ofInt 64 32 = _
    rw [show BitVec.ofInt 64 32 = BitVec.ofNat 64 32 from rfl, addr_add]
    exact congrArg _ (congrArg _ (by omega))
  -- the loop test
  simp only [PcOk, NativeRustcVmX64.Vm.SelectorPoint.b3_length] at hpc3
  rw [eval_not, eval_cmp_eq, eval_add, eval_lit, eval_reg, eval_reg] at hpc3
  rw [show (Env.ofMachine s.data [(stackBelow m0 16, 24),
      (out m0 + BitVec.ofNat 64 (32 * t), 32)]).regs .r8 = reg s.data .r8 from rfl,
    show (Env.ofMachine s.data [(stackBelow m0 16, 24),
      (out m0 + BitVec.ofNat 64 (32 * t), 32)]).regs .rax = reg s.data .rax from rfl,
    hI.r8, hI.rax, ← BitVec.ofNat_add, ofNat_beq (by omega) (by omega)] at hpc3
  obtain ⟨hT, hFl⟩ := pc_cond hpc3
  by_cases hM : 2 + 2 * t = 2 * (len m0 / 2)
  · refine Eventually.mono (afterPairs hp ⟨hS, ⟨hmO, hnO⟩, hoO⟩ (hFl (by simp [hM])) hF3 hlen ?_
      ((r3 .rdi (by simp)).trans hI.rdi) ?_ ((r3 .rdx (by simp)).trans hI.rdx) ?_)
      fun _ h ↦ Or.inl h
    · rw [h8']; exact congrArg _ (by omega)
    · rw [hsi']; exact congrArg _ (congrArg _ (by omega))
    · rw [← hM, show 2 + 2 * t = 2 * (t + 1) by omega]; exact hE
  · exact .done _ (Or.inr ⟨(hT (by simp [hM])).trans (lbl_4 hp), hF3, by omega,
      (r3 .rax (by simp)).trans hI.rax, h8', (r3 .rcx (by simp)).trans hI.rcx,
      (r3 .rdi (by simp)).trans hI.rdi, hsi', (r3 .rdx (by simp)).trans hI.rdx, hE⟩)

/-- **`selector_point` meets its contract.** -/
theorem selectorPoint_spec (hp : Placed code k) :
    Spec (Labels.label NativeRustcVmX64.Vm.SelectorPoint.entryLabel) SelectorPointPre SelectorPointPost := by
  intro m0 hpre
  rw [lbl_entry hp]
  have hpre' := hpre
  obtain ⟨hS, ⟨hmO, hnO⟩, hoO⟩ := hpre
  have hS16 : StackOk m0 16 := hS
  have hnO' : (out m0).toNat + 16 * len m0 ≤ 2 ^ 64 := hnO
  have hL : len m0 = (reg m0 .rdx).toNat := rfl
  have hlen : 16 * len m0 < 2 ^ 64 := lt_of_offStack hnO hoO
  have hwf := frame_wf (m := m0) (vars := fun _ ↦ 0) (ret := 0) hS16 fun _ h ↦ h
  have hm : Match (frameEnv m0 m0 16) (frameS 16) m0 := match_frame
  refine exec_then (hb0 hp) run_b0 hwf (by intro l h; cases h) hm fun s1 hm1 hpc1 ↦ ?_
  have hk0 := after_eq run_b0 ▸ b0_facts
  unfold keepsAll at hk0
  simp only [Bool.and_eq_true] at hk0
  have e1 := regs_eq_of hm hm1 hk0.1
  have hdm1 : s1.data.dmem = m0.dmem := hm1.dmem_eq hwf rfl
  have hF1 : Frame m0 s1.data :=
    ⟨by show reg s1.data .rsp = _; exact e1 .rsp (by simp),
      fun r hr ↦ e1 r (List.mem_cons_of_mem _ (List.mem_append_right _ (mem_calleeRegs hr))),
      by rw [hdm1]; exact fun _ h ↦ h, fun p _ ↦ by rw [hdm1]⟩
  have r1 : ∀ r ∈ [Reg64.rdx, .rsi, .rdi], reg s1.data r = reg m0 r :=
    fun r h ↦ e1 r (List.mem_cons_of_mem _ (List.mem_append_left _ h))
  simp only [PcOk, NativeRustcVmX64.Vm.SelectorPoint.b0_length] at hpc1
  rw [eval_test, eval_reg, Env.ofMachine_regs, beq_ofNat _ (by decide)] at hpc1
  obtain ⟨hT, hFl⟩ := pc_cond hpc1
  by_cases hz : len m0 = 0
  · -- `out` empty.
    refine finish8 hp hpre' ((hT (decide_eq_true hz)).trans (lbl_8 hp)) hF1 ?_
    rw [show pt m0 = [] from List.eq_nil_of_length_eq_zero (by rw [length_pt]; exact hz)]
    exact NativeRustcVm.ewsAt_nil _ _
  have hpc1 := hFl fun h ↦ hz (of_decide_eq_true h)
  -- `b1`: `|out| - 1`
  refine exec_at (hb1 hp) run_b1 (Env.wf_nil _) (by intro l h; cases h) hpc1 (match_nil _)
    fun s2 hm2 hpc2 ↦ ?_
  obtain ⟨hF2, e2, hdm2⟩ := hF1.regs_block hm2 b1_keeps
  have hc : (2 : Nat) ^ 60 - 1 = 1152921504606846975 := rfl
  have hdx : reg s2.data .rdx = BitVec.ofNat 64 (len m0 + (2 ^ 60 - 1)) := by
    rw [show reg s2.data .rdx = (Sym.bin .add .W64 (.lit 1152921504606846975) (.reg .rdx)).eval
      (Env.ofMachine s1.data []) from hm2.regs .rdx _ (by decide +kernel), eval_add, eval_lit,
      eval_reg]
    show _ + reg s1.data .rdx = _
    rw [r1 .rdx (by simp)]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  have hax : (reg s2.data .rax).toNat = len m0 - 1 := by
    rw [show reg s2.data .rax = (Sym.bin .and .W64 (.lit 1152921504606846975)
      (.bin .add .W64 (.lit 1152921504606846975) (.reg .rdx))).eval (Env.ofMachine s1.data [])
      from hm2.regs .rax _ (by decide +kernel)]
    show (BitVec.ofNat 64 1152921504606846975 &&& (BitVec.ofNat 64 1152921504606846975 +
      reg s1.data .rdx)).toNat = _
    rw [r1 .rdx (by simp), BitVec.toNat_and, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show 1152921504606846975 < 2 ^ 64 by decide), Nat.and_comm, ← hc,
      Nat.and_two_pow_sub_one_eq_mod]
    omega
  simp only [PcOk, NativeRustcVmX64.Vm.SelectorPoint.b1_length] at hpc2
  rw [eval_cmp_eq, eval_lit, ← show reg s2.data .rax = (Sym.bin .and .W64
      (.lit 1152921504606846975) (.bin .add .W64 (.lit 1152921504606846975) (.reg .rdx))).eval
      (Env.ofMachine s1.data []) from hm2.regs .rax _ (by decide +kernel),
    beq_ofNat _ (by decide), hax] at hpc2
  obtain ⟨hT2, hF2'⟩ := pc_cond hpc2
  by_cases h1 : len m0 = 1
  · -- `|out| = 1`: bit `0`.
    refine finishLast (hb678 hp) run_b678 (after_eq run_b678 ▸ b678_facts) hpre'
      ((hT2 (decide_eq_true (by omega))).trans (lbl_2 hp)) hF2 (by omega) ?_ ?_ ?_
    · rw [e2 .rsi (by simp), r1 .rsi (by simp), h1]; simp
    · rw [h1]; exact NativeRustcVm.ewsAt_nil _ _
    · rw [one_entry, h1]
      show EW.ofNat (((reg s2.data .rdi).toNat >>> 0) % 2) = _
      rw [e2 .rdi (by simp), r1 .rdi (by simp)]
  -- `|out| ≥ 2`: the pairs.
  have hpc3 := hF2' fun h ↦ h1 (by have := of_decide_eq_true h; omega)
  refine exec_at (hb2 hp) run_b2 (Env.wf_nil _) (by intro l h; cases h) hpc3 (match_nil _)
    fun s3 hm3 hpc3' ↦ ?_
  obtain ⟨hF3, e3, hdm3⟩ := hF2.regs_block hm3 b2_keeps
  simp only [PcOk, NativeRustcVmX64.Vm.SelectorPoint.b2_length] at hpc3'
  have hI : Inv m0 0 s3.data := by
    refine ⟨hF3, by omega, ?_, hm3.regs .r8 (.lit 0) (by decide +kernel),
      hm3.regs .rcx (.lit 0) (by decide +kernel), ?_, ?_, ?_, ?_⟩
    · rw [show reg s3.data .rax = (Sym.bin .and .W64 (.bin .add .W64 (.reg .rax) (.lit 1))
        (.lit 18446744073709551614)).eval (Env.ofMachine s2.data []) from
        hm3.regs .rax _ (by decide +kernel)]
      show (reg s2.data .rax + BitVec.ofNat 64 1) &&& BitVec.ofNat 64 18446744073709551614 = _
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_and, BitVec.toNat_add, hax, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        BitVec.toNat_ofNat, show (1 : Nat) % 2 ^ 64 = 1 from rfl,
        show (18446744073709551614 : Nat) % 2 ^ 64 = 2 ^ 64 - 2 from rfl,
        Nat.mod_eq_of_lt (show len m0 - 1 + 1 < 2 ^ 64 by omega), and_even _ (by omega)]
      omega
    · exact (e3 .rdi (by simp)).trans ((e2 .rdi (by simp)).trans (r1 .rdi (by simp)))
    · rw [e3 .rsi (by simp), e2 .rsi (by simp), r1 .rsi (by simp)]; simp
    · rw [e3 .rdx (by simp), hdx]
    · rw [hdm3, hdm2, hdm1]; exact NativeRustcVm.ewsAt_nil _ _
  refine Sym.loop (fun n s ↦ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SelectorPoint.b3Offset) ∧ ∃ t, len m0 / 2 - t = n ∧
    Inv m0 t s.data) (fun n s ⟨hpc, t, hn, hI⟩ ↦ ?_) ⟨hpc3', 0, rfl, hI⟩
  refine Eventually.mono (step hp hpre' hpc hI) fun s' h ↦ ?_
  rcases h with h | ⟨hpc', hI'⟩
  · exact Or.inl h
  · exact Or.inr ⟨len m0 / 2 - (t + 1), by have := hI'.lt; have := hI.lt; omega, hpc', t + 1,
      rfl, hI'⟩

end

end NativeRustcVmX64.Arrays.SelectorPoint
