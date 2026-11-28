module

public import NativeRustcVmArm.Code.Vm.BitLength.Names
public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.TStateGrind.Names
public import NativeRustcVmArm.Code.Vm.TStateSumcheckRoundPoly.Names
public import NativeRustcVmArm.Sumcheck.RoundPoly.Post
public import NativeRustcVm.Arrays.ReadLemmas

/-!
# `sumcheck_round_poly` in equality mode, after the tail is read

From `.L2` (`b2`) after `read_scalars` (`some_b2`): the tail's sum (`sum_e`, `b3`); from `b4`
(`some_b4`): the grind's bits (`bit_length`, `b4`), the grind (`b5`), the product of the equality
factor and the sum (`EW::mul`, `b7`), the derived coefficient into the message (`b8`); a rejection
at either test.
-/

namespace NativeRustcVmArm.Sumcheck.RoundPoly

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.TStateSumcheckRoundPoly
open NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Sumcheck

@[expose] public section

/-- The count: X1 at the entry. -/
abbrev cnt (m0 : MachineData) : Nat := m0.regs.X1.toNat

/-- The claim: X2, X3 at the entry. -/
abbrev claimOf (m0 : MachineData) : EW := ⟨m0.regs.X2, m0.regs.X3⟩

/-- The registers `sumcheck_round_poly` keeps in equality mode. -/
structure SomeRegs (m0 : MachineData) (ev : EW) (m : MachineData) : Prop where
  x19 : m.regs.getXReg .X19 = m0.regs.X5
  x20 : m.regs.getXReg .X20 = m0.regs.X3
  x21 : m.regs.getXReg .X21 = m0.regs.X2
  x22 : m.regs.getXReg .X22 = m0.regs.X0
  x23 : m.regs.getXReg .X23 = ev.c0
  x24 : m.regs.getXReg .X24 = ev.c1
  x27 : (m.regs.getXReg .X27).toNat = cnt m0 - 1

/-- The tail read, its state. -/
structure TailAt [Labels] (m0 : MachineData) (a : DecArea) (tail : Array EW) (s1 : TState)
    (m : MachineData) : Prop where
  frame : RFrame m0 m
  tail : NativeRustcVm.EWsAt m.dmem (msgAt m0 + BitVec.ofNat 64 16) tail.toList
  ts : TStateAt m.dmem (tAt m0) a s1

end

public section

variable [Host] {a : DecArea} {s : TState} {ev : EW} {e : Option EW} {m0 : MachineData} {k : Nat}

omit [Host] in
theorem SomeRegs.of_saved {m m' : MachineData} (h : SomeRegs m0 ev m) (hsv : Saved m m') :
    SomeRegs m0 ev m' :=
  ⟨(hsv.1 .X19 rfl).trans h.x19, (hsv.1 .X20 rfl).trans h.x20, (hsv.1 .X21 rfl).trans h.x21,
    (hsv.1 .X22 rfl).trans h.x22, (hsv.1 .X23 rfl).trans h.x23, (hsv.1 .X24 rfl).trans h.x24,
    by rw [hsv.1 .X27 rfl]; exact h.x27⟩

/-- X19 of a state after a body block: the message. -/
theorem x19_of_match {m m' : MachineData} {S : SState} (hm : Match (envB m0 m) S m')
    (h : S.reg .X19 = some (.ptr 1 0)) : m'.regs.getXReg .X19 = m0.regs.X5 := by
  apply UInt64.toBitVec_inj.mp
  rw [reg_msg (o := 0) hm h, NativeRustcVm.addr_add_zero]

/-- The registers through a body block that keeps them. -/
theorem SomeRegs.of_block {m m' : MachineData} {S : SState} (h : SomeRegs m0 ev m)
    (hm : Match (envB m0 m) S m') (h19 : S.reg .X19 = some (.ptr 1 0))
    (h20 : S.reg .X20 = some (.reg .X20)) (h21 : S.reg .X21 = some (.reg .X21))
    (h22 : S.reg .X22 = some (.reg .X22)) (h23 : S.reg .X23 = some (.reg .X23))
    (h24 : S.reg .X24 = some (.reg .X24)) (h27 : S.reg .X27 = some (.reg .X27)) :
    SomeRegs m0 ev m' :=
  ⟨x19_of_match hm h19, (reg_of_match hm h20).trans h.x20, (reg_of_match hm h21).trans h.x21,
    (reg_of_match hm h22).trans h.x22, (reg_of_match hm h23).trans h.x23,
    (reg_of_match hm h24).trans h.x24, by rw [reg_of_match hm h27]; exact h.x27⟩

/-- **The tail through a call** that changes `R` (in the `TState`) and its stack. -/
theorem TailAt.after (hpre : RoundPolyPre a s e m0) {tail : Array EW} {s1 : TState}
    {m m' : MachineData} (ht : TailAt m0 a tail s1 m) (hsz : tail.size + 1 ≤ maxCount)
    {Nc : Nat} (hle : 112 + Nc ≤ roundPolyStack) {R : BitVec 64 → Prop}
    (hR : ∀ p, R p → InRange (tAt m0) tstateBytes p)
    (hs : SameOutside m.dmem m'.dmem (fun p ↦ R p ∨ InRange (stackBelow m Nc) Nc p))
    (hsv : Saved m m') {s2 : TState} (hts : TStateAt m'.dmem (tAt m0) a s2) :
    TailAt m0 a tail s2 m' :=
  ⟨ht.frame.after_call hpre hle (fun p hp ↦ ⟨Or.inr (Or.inl (hR p hp)), t_not_fr hpre (hR p hp)⟩)
      hs hsv,
    msg_keep hpre hs (fun p hp ↦ hp.elim (fun h ↦ t_not_msg hpre (hR p h))
      (fun h ↦ stack_not_msg hpre (callee_stack hpre ht.frame hle h)))
      (by simp only [Array.length_toList]; omega) ht.tail, hts⟩

/-- **The tail through a call** that changes only its stack. -/
theorem TailAt.of_call (hpre : RoundPolyPre a s e m0) {tail : Array EW} {s1 : TState}
    {m m' : MachineData} (ht : TailAt m0 a tail s1 m) (hsz : tail.size + 1 ≤ maxCount)
    {Nc : Nat} (hle : 112 + Nc ≤ roundPolyStack)
    (hs : SameOutside m.dmem m'.dmem (InRange (stackBelow m Nc) Nc)) (hsv : Saved m m') :
    TailAt m0 a tail s1 m' :=
  ht.after hpre hsz hle (R := fun _ ↦ False) (fun _ h ↦ h.elim)
    (fun p hp ↦ hs p fun h ↦ hp (Or.inr h)) hsv
    (tstate_keep hpre hs hsv.2.2 (fun _ hp ↦ Or.inr (callee_stack hpre ht.frame hle hp)) ht.ts)

omit [Host] in
theorem bitLenNat_le (v : Nat) (hv : v < 2 ^ 64) : bitLenNat v ≤ 64 := by
  unfold bitLenNat
  split
  · omega
  · have := (Nat.log2_lt (by assumption)).2 hv
    omega

/-- **After the tail's sum**, at `b4`: the grind's bits, the grind, the product, the result. -/
theorem some_b4 (hp : Placed code k)
    (hbl : Spec (Labels.label NativeRustcVmArm.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost)
    (hgr : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hpre : RoundPolyPre a s (some ev) m0) {tail : Array EW} {s1 : TState}
    (hr1 : (readScalars (cnt m0 - 1)).run s = some (tail, s1)) {m : MachineData}
    (hg : SomeRegs m0 ev m) (ht : TailAt m0 a tail s1 m)
    (hx0 : m.regs.X0 = (sumE tail).c0) (hx1 : m.regs.X1 = (sumE tail).c1) :
    Eventually (step1 Host.exe)
      (fun st ↦ st.pc = retOf m0 ∧ RoundPolyPost a s (some ev) m0 st.data)
      ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.b4Offset)⟩ := by
  have c := ctx_of hpre
  have hc2 : 2 ≤ cnt m0 := hpre.2.2.2.2.1
  have hc5 : cnt m0 ≤ maxCount := hpre.2.2.2.2.2.1
  have hmc : maxCount = 5 := rfl
  have htl : tail.size = cnt m0 - 1 := readScalars_size hr1
  have hsz : tail.size + 1 ≤ maxCount := by omega
  have hk4 : b4.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.b4Offset) := b4_in_code.trans hp.1 (by simp [b4])
  have hk5 : b5.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.b5Offset) := b5_in_code.trans hp.1 (by simp [b5])
  have hk6 : b6.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.b6Offset) := b6_in_code.trans hp.1 (by simp [b6])
  have hk7 : b7.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.b7Offset) := b7_in_code.trans hp.1 (by simp [b7])
  have hk8 : b8.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.b8Offset) := b8_in_code.trans hp.1 (by simp [b8])
  have hl9 : Labels.label NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.label_9 = Host.addrOf (k + NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.b19Offset) :=
    hp.label (j := NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.b19Offset) NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.label_9_at
  -- `b4`: `bit_length(count - 1)`.
  refine exec_then hk4 run_b4 (wf_envB hpre ht.frame) (match_bodyS hpre ht.frame hg.x19)
    fun st4 hm4 hpc4 ↦ ?_
  obtain ⟨hf4, hd4⟩ := RFrame.of_block hpre ht.frame hm4 rfl rfl rfl rfl
  have hg4 := hg.of_block hm4 rfl rfl rfl rfl rfl rfl rfl
  have h25 : st4.data.regs.getXReg .X25 = (sumE tail).c0 := (reg_of_match' (r := .X25) (r' := .X0) hm4 rfl).trans hx0
  have h26 : st4.data.regs.getXReg .X26 = (sumE tail).c1 := (reg_of_match' (r := .X26) (r' := .X1) hm4 rfl).trans hx1
  have h40 : st4.data.regs.X0.toNat = cnt m0 - 1 := by
    have := reg_of_match' (r := .X0) (r' := .X27) hm4 rfl
    rw [show st4.data.regs.X0 = st4.data.regs.getXReg .X0 from rfl, this]
    exact hg.x27
  have ht4 : TailAt m0 a tail s1 st4.data := ⟨hf4, hd4 ▸ ht.tail, hd4 ▸ ht.ts⟩
  refine call_then hpc4 hbl trivial fun st5 hpc5 ⟨hbits, hs5, hsv5⟩ ↦ ?_
  have ht5 := ht4.of_call hpre hsz (Nc := bitLengthStack) (by decide) hs5 hsv5
  have hg5 := hg4.of_saved hsv5
  have h525 : st5.data.regs.getXReg .X25 = (sumE tail).c0 := (hsv5.1 .X25 rfl).trans h25
  have h526 : st5.data.regs.getXReg .X26 = (sumE tail).c1 := (hsv5.1 .X26 rfl).trans h26
  have hb5 : st5.data.regs.X0.toNat = bitLenNat (cnt m0 - 1) := by rw [hbits, h40]; rfl
  -- `b5`: `grind(bits)`.
  refine exec_at hk5 run_b5 (wf_envB hpre ht5.frame) hpc5 (match_bodyS hpre ht5.frame hg5.x19)
    fun st6 hm6 hpc6 ↦ ?_
  obtain ⟨hf6, hd6⟩ := RFrame.of_block hpre ht5.frame hm6 rfl rfl rfl rfl
  have hg6 := hg5.of_block hm6 rfl rfl rfl rfl rfl rfl rfl
  have h625 : st6.data.regs.getXReg .X25 = (sumE tail).c0 := (reg_of_match (r := .X25) hm6 rfl).trans h525
  have h626 : st6.data.regs.getXReg .X26 = (sumE tail).c1 := (reg_of_match (r := .X26) hm6 rfl).trans h526
  have ht6 : TailAt m0 a tail s1 st6.data := ⟨hf6, hd6 ▸ ht5.tail, hd6 ▸ ht5.ts⟩
  have h60 : st6.data.regs.X0 = m0.regs.X0 := (reg_of_match' (r := .X0) (r' := .X22) hm6 rfl).trans hg5.x22
  have hbl64 : bitLenNat (cnt m0 - 1) ≤ 64 := bitLenNat_le _ (by omega)
  have hbits6 : grindBits st6.data = grindingBits (cnt m0 - 1 + 1) := by
    have h1 := hm6.regs .X1 _ rfl
    have h2 := grind_bits (envB m0 st5.data) (by
      show st5.data.regs.X0.toNat ≤ 64
      rw [hb5]; exact hbl64)
    unfold grindBits
    rw [grindingBits_succ, show st6.data.regs.X1.toNat =
      (st6.data.regs.getXReg .X1).toBitVec.toNat from rfl, h1, h2]
    show (st5.data.regs.X0.toNat - 3) % 2 ^ 32 = _
    rw [hb5]
    omega
  refine call_then hpc6 (hgr a s1) ?pre fun st7 hpc7 hpost7 ↦ ?_
  case pre =>
    simp only [GrindPre, h60, hbits6]
    refine ⟨c.stackOk hf6.at_ (by decide), c.rcAt hf6.at_ (by decide), ht6.ts,
      c.tstateOk hf6.at_ (by decide), ?_⟩
    rw [grindingBits_succ]; omega
  simp only [GrindPost, h60, hbits6] at hpost7
  obtain ⟨hok7, hnext7, hs7, hsv7⟩ := hpost7
  have hf7 : RFrame m0 st7.data := hf6.after_call hpre (Nc := grindStack) (by decide)
    (R := InRange (tAt m0) tstateBytes) (fun p hp ↦ ⟨Or.inr (Or.inl hp), t_not_fr hpre hp⟩)
    hs7 hsv7
  have hg7 := hg6.of_saved hsv7
  -- `b6`: the grind's test.
  refine exec_at hk6 run_b6 (wf_envB hpre hf7) hpc7 (match_bodyS hpre hf7 hg7.x19)
    fun st8 hm8 hpc8 ↦ ?_
  obtain ⟨hf8, hd8⟩ := RFrame.of_block hpre hf7 hm8 rfl rfl rfl rfl
  have h80 : st8.data.regs.X0 = st7.data.regs.X0 := reg_of_match (r := .X0) hm8 rfl
  have hX0 : (envB m0 st7.data).regs .X0 = st7.data.regs.X0.toBitVec := rfl
  simp only [PcOk, SBool.eval, CmpOp.apply, Sym.eval, hX0] at hpc8
  cases hr2 : (grind (grindingBits (cnt m0 - 1 + 1))).run s1 with
  | none =>
    rw [hr2] at hok7
    have hpc : st8.pc = Host.addrOf (k + NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.b19Offset) := by
      rw [hpc8, hok7, Option.isSome_none]
      have hc : (low .W32 (okWord false).toBitVec == low .W32 0#64) = true := by decide
      simp only [hc, ↓reduceIte, hl9]
    obtain ⟨d8, pc8⟩ := st8
    simp only at hpc
    subst hpc
    refine Eventually.mono (exit_spec hp hpre hf8) fun st ⟨h1, h2, h3, h4⟩ ↦ ⟨h1, ?_⟩
    refine post_none ?_ (h2.trans (h80.trans hok7)) (h3 ▸ hf8.same) h4
    simp [runR, roundPoly_some_run, hr1, hr2]
  | some q =>
    obtain ⟨⟨⟩, s2⟩ := q
    rw [hr2] at hok7
    have hts2 : TStateAt st7.data.dmem (tAt m0) a s2 := hnext7 () s2 hr2
    have ht7 : TailAt m0 a tail s2 st7.data :=
      ht6.after hpre hsz (Nc := grindStack) (by decide) (R := InRange (tAt m0) tstateBytes)
        (fun _ h ↦ h) hs7 hsv7 hts2
    have hpc : st8.pc = Host.addrOf (k + NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.b7Offset) := by
      rw [hpc8, hok7, Option.isSome_some]
      have hc : (low .W32 (okWord true).toBitVec == low .W32 0#64) = false := by decide
      simp only [hc, Bool.false_eq_true, ↓reduceIte]
      rfl
    have hg8 := hg7.of_block hm8 rfl rfl rfl rfl rfl rfl rfl
    have ht8 : TailAt m0 a tail s2 st8.data := ⟨hf8, hd8 ▸ ht7.tail, hd8 ▸ ht7.ts⟩
    have h825 : st8.data.regs.getXReg .X25 = (sumE tail).c0 :=
      (reg_of_match (r := .X25) hm8 rfl).trans ((hsv7.1 .X25 rfl).trans h625)
    have h826 : st8.data.regs.getXReg .X26 = (sumE tail).c1 :=
      (reg_of_match (r := .X26) hm8 rfl).trans ((hsv7.1 .X26 rfl).trans h626)
    -- `b7`: `EW::mul(eq, sum)`.
    refine exec_at hk7 run_b7 (wf_envB hpre hf8) hpc (match_bodyS hpre hf8 hg8.x19)
      fun st9 hm9 hpc9 ↦ ?_
    obtain ⟨hf9, hd9⟩ := RFrame.of_block hpre hf8 hm9 rfl rfl rfl rfl
    have hg9 := hg8.of_block hm9 rfl rfl rfl rfl rfl rfl rfl
    have ht9 : TailAt m0 a tail s2 st9.data := ⟨hf9, hd9 ▸ ht8.tail, hd9 ▸ ht8.ts⟩
    have h90 : st9.data.regs.X0 = ev.c0 := (reg_of_match' (r := .X0) (r' := .X23) hm9 rfl).trans hg8.x23
    have h91 : st9.data.regs.X1 = ev.c1 := (reg_of_match' (r := .X1) (r' := .X24) hm9 rfl).trans hg8.x24
    have h92 : st9.data.regs.X2 = (sumE tail).c0 := (reg_of_match' (r := .X2) (r' := .X25) hm9 rfl).trans h825
    have h93 : st9.data.regs.X3 = (sumE tail).c1 := (reg_of_match' (r := .X3) (r' := .X26) hm9 rfl).trans h826
    refine call_then hpc9 hmul (c.stackOk hf9.at_ (by decide)) fun st10 hpc10 hpost10 ↦ ?_
    obtain ⟨hm0', hm1', hs10, hsv10⟩ := hpost10
    rw [h90, h91, h92, h93] at hm0' hm1'
    have ht10 := ht9.of_call hpre hsz (Nc := ewMulStack) (by decide) hs10 hsv10
    have hg10 := hg9.of_saved hsv10
    -- `b8`: the derived coefficient into `msg[0]`, `Some`.
    have hwf10 := wf_envB hpre ht10.frame
    have hm10 := match_bodyS hpre ht10.frame hg10.x19
    refine exec_at hk8 run_b8 hwf10 hpc10 hm10 fun st11 hm11 hpc11 ↦ ?_
    have hm11' : Match (envB m0 st10.data) (after b8 bodyS) st11.data := by
      rw [after_eq run_b8]; exact hm11
    have hno := (msgOk hpre).2.1
    unfold NoWrap at hno
    rw [hmc] at hno
    have hW : ∀ p, Written (envB m0 st10.data) (after b8 bodyS) p →
        (msgAt m0).toNat ≤ p.toNat ∧ p.toNat < (msgAt m0).toNat + 16 := fun p h ↦ by
      have := Written.toNat (r := 1) (lo := 0) (hi := 16) rfl (by rw [after_eq run_b8]; decide) h
      omega
    have hWr : ∀ p, Written (envB m0 st10.data) (after b8 bodyS) p → InRange (msgAt m0) (16 * maxCount) p :=
      fun p h ↦ by
        have := hW p h
        rw [Sym.inRange_iff (by rw [hmc]; omega)]
        rw [hmc]; omega
    have hs11 := hm11'.sameOutside hwf10
    have hsv11 : Saved st10.data st11.data := Match.saved hm10 hm11' hwf10 rfl (by rw [after_eq run_b8]; decide)
    have hf11 : RFrame m0 st11.data := ht10.frame.after_call hpre (Nc := 0) (by decide)
      (R := Written (envB m0 st10.data) (after b8 bodyS)) (fun p hp ↦ ⟨Or.inl (hWr p hp), msg_not_fr hpre (hWr p hp)⟩)
      (fun p hp ↦ hs11 p fun h ↦ hp (Or.inl h)) hsv11
    have htail11 : NativeRustcVm.EWsAt st11.data.dmem (msgAt m0 + BitVec.ofNat 64 16)
        tail.toList := by
      refine NativeRustcVm.BytesAt.of_sameOutside ht10.tail hs11 fun i hi hw ↦ ?_
      have := hW _ hw
      rw [NativeRustcVm.length_ewsBytes] at hi
      simp only [Array.length_toList] at hi
      rw [NativeRustcVm.addr_add_add, NativeRustcVm.toNat_add_ofNat (by omega)] at this
      omega
    have hts11 : TStateAt st11.data.dmem (tAt m0) a s2 :=
      tstate_keep hpre hs11 hsv11.2.2 (fun p hp ↦ Or.inl (hWr p hp)) ht10.ts
    have hx11 : (envB m0 st10.data).regs .X21 = m0.regs.X2.toBitVec := by
      show (st10.data.regs.getXReg .X21).toBitVec = _; rw [hg10.x21]
    have hx11' : (envB m0 st10.data).regs .X20 = m0.regs.X3.toBitVec := by
      show (st10.data.regs.getXReg .X20).toBitVec = _; rw [hg10.x20]
    have hhead : NativeRustcVm.EWAt st11.data.dmem (msgAt m0) (claimOf m0 + ev * sumE tail) := by
      have w0 := NativeRustcVmArm.Sumcheck.Match.wordAt_write hm11 (r := 1) (o := 0) rfl
        (by decide) (fun i hi ↦ by
          match i, hi with
          | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => rfl)
      have w1 := NativeRustcVmArm.Sumcheck.Match.wordAt_write hm11 (r := 1) (o := 8) rfl
        (by decide) (fun i hi ↦ by
          match i, hi with
          | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => rfl)
      rw [NativeRustcVm.addr_add_zero] at w0
      rw [NativeRustcVm.ewAt_iff]
      refine ⟨?_, ?_⟩
      · convert w0 using 1
        simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, hx11]
        show _ = UInt64.ofBitVec (st10.data.regs.X0.toBitVec ^^^ _)
        rw [hm0']
        show m0.regs.X2 ^^^ (ev * sumE tail).c0 = _
        rw [UInt64.xor_comm]; rfl
      · convert w1 using 1
        simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, hx11']
        show _ = UInt64.ofBitVec (st10.data.regs.X1.toBitVec ^^^ _)
        rw [hm1']
        show m0.regs.X3 ^^^ (ev * sumE tail).c1 = _
        rw [UInt64.xor_comm]; rfl
    have h110 : st11.data.regs.X0 = 1 := UInt64.toBitVec_inj.mp (hm11.regs .X0 _ rfl)
    simp only [PcOk] at hpc11
    rw [hl9] at hpc11
    obtain ⟨d11, pc11⟩ := st11
    simp only at hpc11
    subst hpc11
    refine Eventually.mono (exit_spec hp hpre hf11) fun st ⟨h1, h2, h3, h4⟩ ↦ ⟨h1, ?_⟩
    refine post_some (msg := #[claimOf m0 + ev * sumE tail] ++ tail) (s' := s2) ?_
      (h2.trans h110) ?_ (h3 ▸ hts11) (h3 ▸ hf11.same) h4
    · simp [runR, roundPoly_some_run, hr1, hr2]
    · rw [h3, Array.toList_append, NativeRustcVm.ewsAt_append]
      exact ⟨NativeRustcVm.ewsAt_singleton.2 hhead, by simpa using htail11⟩

end

end NativeRustcVmArm.Sumcheck.RoundPoly
