module

public import NativeRustcVmX64.Bus.VerifyBusBalance.Tail

/-!
# `verify_bus_balance`'s state kept across blocks and calls (x86-64)

- `TailMem`: the frame's words the tail reads (the bus's address, the point's address and length,
  the point); `TailMem.of_keep` through `KeepIv tailIv`.
- `tc_keep`: the `TState` and the claims kept by changes in the stack and the bus.
- `blk_same`: a block writing only the frame changes nothing else.
- `stackArg_loc`, `wr_loc`, `tag8_false`, `tag32_false`: a stack argument the frame holds, a word a
  block wrote, a `Some` tag's tests.
-/

namespace NativeRustcVmX64.Bus.VerifyBusBalance

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.VerifyBusBalance
open NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck NativeRustcVmX64.Bus.Gkr
open NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Bus NativeRustcVm.Layout

public section

/-- The tail's words: the bus's address at `112`, the point's address and length at `104`, `120`,
the point at `1800`. -/
structure TailMem (m0 : MachineData) (pt : Array EW) (d : Mem 64) : Prop where
  w112 : NativeRustcVm.WordAt d (loc m0 112) (UInt64.ofBitVec (reg m0 .r8))
  w104 : NativeRustcVm.WordAt d (loc m0 104) (UInt64.ofBitVec (loc m0 1800))
  w120 : NativeRustcVm.WordAt d (loc m0 120) pt.size.toUInt64
  hpt : NativeRustcVm.EWsAt d (loc m0 1800) pt.toList
  psz : pt.size ≤ 63

/-- The tail's words' intervals. -/
abbrev tailIv : List (Nat × Nat) := [(104, 128), (1800, 2808)]

theorem TailMem.of_keep {m0 : MachineData} {pt : Array EW} {d d' : Mem 64} (h : TailMem m0 pt d)
    (hk : KeepIv tailIv m0 d d') : TailMem m0 pt d' :=
  ⟨NativeRustcVm.Layout.WordAt.of_same h.w112 (hk.sameIn (lo := 104) (hi := 128) (by simp)
      (by omega) (by omega)) le_rfl,
    NativeRustcVm.Layout.WordAt.of_same h.w104 (hk.sameIn (lo := 104) (hi := 128) (by simp)
      (by omega) (by omega)) le_rfl,
    NativeRustcVm.Layout.WordAt.of_same h.w120 (hk.sameIn (lo := 104) (hi := 128) (by simp)
      (by omega) (by omega)) le_rfl,
    NativeRustcVm.Tables.EWsAt.of_same h.hpt (hk.sameIn (lo := 1800) (hi := 2808)
      (n := 16 * pt.size) (by simp) (by omega) (by have := h.psz; omega)) (by simp),
    h.psz⟩

/-- A stack argument the frame holds, RSP at its base. -/
theorem stackArg_loc {m0 d : MachineData} (hsp : rspOf d = loc m0 0) {i : Nat} {w : UInt64}
    (h : NativeRustcVm.WordAt d.dmem (loc m0 (8 + 8 * i)) w) : stackArg d i = w.toBitVec := by
  unfold stackArg
  rw [hsp, show loc m0 0 + BitVec.ofNat 64 (8 + 8 * i) = loc m0 (8 + 8 * i) by
    rw [off_add, Nat.zero_add]]
  exact congrArg UInt64.toBitVec (NativeRustcVm.wordOf_of_wordAt h)

end

public section
variable [Labels] {a : DecArea} {s0 : TState} {L : LayoutW} {m0 : MachineData}

/-- **The `TState` and the claims kept** by changes in the stack and the bus. -/
theorem tc_keep (h : VerifyBusBalancePre a s0 L m0) {d d' : Mem 64} (hk : Kept d d')
    {X : BitVec 64 → Prop} (hs : NativeRustcVm.SameOutside d d' X)
    (hX : ∀ q, X q → NativeRustcVm.InRange (stackBelow m0 NN) NN q ∨
      NativeRustcVm.InRange (reg m0 .r8) busBytes q)
    {s : TState} {cs : Array ColumnClaimW} (hts : TStateAt d (reg m0 .rdi) a s)
    (hcl : ClaimsWAt d (reg m0 .r9) cs) :
    TStateAt d' (reg m0 .rdi) a s ∧ ClaimsWAt d' (reg m0 .r9) cs := by
  refine ⟨ts_keep h hk hs (fun q hq ↦ (hX q hq).elim .inl fun h' ↦ .inr (.inl h')) hts,
    NativeRustcVm.Tables.ClaimsWAt.of_same hcl (Same.of_sameOutside hs fun j hj hq ↦ ?_)⟩
  rcases hX _ hq with hq | hq
  · exact NativeRustcVm.Apart.not_inRange_add (pre_cl h).2.2.2.2.1 (pre_cl h).2.1
      (noWrap_stackBelow (pre_stack h)) hj (inRange_mono hq (by omega))
  · exact NativeRustcVm.Apart.not_inRange_add (pre_busCl h).symm (pre_cl h).2.1 (pre_bus h).2.1 hj
      hq

omit [Labels] in
/-- **A block writing only the frame** changes nothing else. -/
theorem blk_same [Labels] (hS : StackOk m0 NN) {rest : List (BitVec 64 × Nat)} {ret : BitVec 64}
    {S : SState} {d d' : MachineData} (hwf : (frameEnv m0 d 5520 rest (fun _ ↦ 0) ret).WF)
    (hm : Match (frameEnv m0 d 5520 rest (fun _ ↦ 0) ret) S d') {lo hi : Nat} (h0 : W0 lo hi S)
    (hhi : hi ≤ 5520) : NativeRustcVm.SameOutside d.dmem d'.dmem (NativeRustcVm.InRange (fb m0) 5520) :=
  fun _ hq ↦ hm.get?_mem0 hwf fun hw ↦ hq (written_fb hS N_ge (fun w hw ↦
    ⟨(h0 w hw).1, by have := h0 w hw; omega⟩) hw)

omit [Labels] in
theorem frame_stack (hS : StackOk m0 NN) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (fb m0) 5520 q) : NativeRustcVm.InRange (stackBelow m0 NN) NN q :=
  inRange_frame_stack (rsp_top hS) (rsp_ge hS) N_ge hq

omit [Labels] in
/-- A callee's stack below the frame's offset `c` is in the stack. -/
theorem callee_stack (hS : StackOk m0 NN) {c Nc : Nat} {st : MachineData}
    (hsp : rspOf st = loc m0 c) (hc : c ≤ 5520) (hle : 5520 - c + Nc ≤ NN) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (stackBelow st Nc) Nc q) :
    NativeRustcVm.InRange (stackBelow m0 NN) NN q := by
  have := callee_iv hS hsp hc hle hq
  have := rsp_ge hS
  have := N_ge
  rw [inRange_stack hS]
  omega

omit [Labels] in
/-- A range of the frame is in the stack. -/
theorem loc_stack (hS : StackOk m0 NN) {j n : Nat} (hjn : j + n ≤ 5520) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (loc m0 j) n q) : NativeRustcVm.InRange (stackBelow m0 NN) NN q :=
  frame_stack hS (inRange_of_off (NativeRustcVm.NoWrap.mono (frame_noWrap hS N_ge) (by omega))
    hjn hq)

/-- The bus apart from a range of the frame. -/
theorem bus_notLoc (h : VerifyBusBalancePre a s0 L m0) {o n j l : Nat} (hon : o + n ≤ 107768)
    (hjl : j + l ≤ 5520) {q : BitVec 64} (hq : NativeRustcVm.InRange (off (reg m0 .r8) o) n q) :
    ¬ NativeRustcVm.InRange (loc m0 j) l q := by
  have hbus := pre_bus h
  have hbnw : (reg m0 .r8).toNat + 107768 ≤ 2 ^ 64 := hbus.2.1
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0; exact absurd hq (by unfold NativeRustcVm.InRange; omega)
  have ho : (off (reg m0 .r8) o).toNat = (reg m0 .r8).toNat + o := toNat_off (by omega)
  refine not_loc (pre_stack h) (x := off (reg m0 .r8) o) (n := n)
    (NativeRustcVm.Apart.mono hbus.2.2.2.2.1 (by rw [ho]; omega)
      (by rw [ho, busBytes_eq]; omega) (Nat.le_refl _) (Nat.le_refl _))
    (by unfold NativeRustcVm.NoWrap; rw [ho]; omega) hjl hq

end

public section
variable [Labels] {m0 : MachineData}

/-- A `Some` tag's low byte is not `0`. -/
theorem tag8_false {d : MachineData} {rest : List (BitVec 64 × Nat)} {ret : BitVec 64} {o : Nat}
    (hw : NativeRustcVm.WordAt d.dmem (loc m0 o) 1) :
    (tag8 o).eval (frameEnv m0 d 5520 rest (fun _ ↦ 0) ret) = false := by
  have hl : (frameEnv m0 d 5520 rest (fun _ ↦ 0) ret).load 0 o 1 = BitVec.ofNat 64 1 :=
    load1_of_tag (w := 1) (.inr rfl) hw
  show CmpOp.apply .eq .W8 ((frameEnv m0 d 5520 rest (fun _ ↦ 0) ret).load 0 o 1)
    (BitVec.ofNat 64 0) = false
  rw [hl]
  rfl

/-- A `Some` tag's low half is `1`. -/
theorem tag32_false {d : MachineData} {rest : List (BitVec 64 × Nat)} {ret : BitVec 64} {o : Nat}
    (hw : NativeRustcVm.WordAt d.dmem (loc m0 o) 1) :
    (tag32 o).eval (frameEnv m0 d 5520 rest (fun _ ↦ 0) ret) = false := by
  have hl : (frameEnv m0 d 5520 rest (fun _ ↦ 0) ret).load 0 o 4 = BitVec.ofNat 64 1 :=
    load4_of_tag (w := 1) (.inr rfl) hw
  show (!CmpOp.apply .eq .W32 ((frameEnv m0 d 5520 rest (fun _ ↦ 0) ret).load 0 o 4)
    (BitVec.ofNat 64 1)) = false
  rw [hl]
  rfl

/-- AL = `1`: `testb %al, %al` is not zero. -/
theorem alZ_false {d : MachineData} {rest : List (BitVec 64 × Nat)} {ret : BitVec 64}
    (hal : boolRet d = 1) : alZ.eval (frameEnv m0 d 5520 rest (fun _ ↦ 0) ret) = false := by
  show CmpOp.apply .eq .W8 (BinOp.apply .and .W8 (reg d .rax) (reg d .rax))
    (BitVec.ofNat 64 0) = false
  rw [testAl_eq]
  unfold boolRet at hal
  simp [hal]

/-- AL = `0`: `testb %al, %al` is zero. -/
theorem alZ_true {d : MachineData} {rest : List (BitVec 64 × Nat)} {ret : BitVec 64}
    (hal : boolRet d = 0) : alZ.eval (frameEnv m0 d 5520 rest (fun _ ↦ 0) ret) = true := by
  show CmpOp.apply .eq .W8 (BinOp.apply .and .W8 (reg d .rax) (reg d .rax))
    (BitVec.ofNat 64 0) = true
  rw [testAl_eq]
  unfold boolRet at hal
  simp [hal]

end

end NativeRustcVmX64.Bus.VerifyBusBalance
