module

public import NativeRustcVmArm.Code.Vm.SpongeWAbsorbNonce.Names
public import NativeRustcVmArm.Code.Vm.TStateGrind.Names
public import NativeRustcVmArm.Code.Vm.TStateNextScalar.Names
public import NativeRustcVmArm.Transcript.Callee
public import NativeRustcVmArm.Transcript.Grind.Exec
public import NativeVm.Equiv.Transcript

/-!
# `TState::grind` on AArch64

**`grind_spec`**: X0 becomes `grind bits`'s `Some`/`None` and the `TState` at X0 its state, given
the contracts of `next_scalar` and `absorb_nonce`. `bits = 0` returns `1` at once (`b0`, `b5`).
Otherwise `b1` saves X30, X20, X19 and calls `next_scalar` with its output in the frame; `b2` tests
its tag: `0`, `b6` returns `0`; `1`, `b3` calls `absorb_nonce` on the nonce and `b4` returns whether
the lane's low `bits` bits are zero (`pow & !(-1 << bits) == 0`, `bits < 64`).
-/

namespace NativeRustcVmArm.Transcript.Grind

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.TStateGrind
open NativeRustcVm.Transcript NativeVm.Model NativeRustcArm

public section

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 64 := by decide

theorem grind_zero (s : TState) : (grind 0).run s = some ((), s) := rfl

/-- `!(-1 << b)`: the low `b` bits. -/
theorem mask_toNat {b : Nat} (hb : b < 64) :
    (~~~(BitVec.ofNat 64 18446744073709551615 <<< b)).toNat = 2 ^ b - 1 := by
  have h1 : (2 : Nat) ^ b ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega)
  have h2 : 1 ≤ (2 : Nat) ^ b := Nat.one_le_two_pow
  rw [BitVec.toNat_not, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  have e : 18446744073709551615 % 2 ^ 64 * 2 ^ b = (2 ^ 64 - 2 ^ b) + 2 ^ 64 * (2 ^ b - 1) := by
    generalize (2 : Nat) ^ b = P at *
    rw [show (18446744073709551615 : Nat) % 2 ^ 64 = 18446744073709551615 from rfl]
    omega
  rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  omega

/-- The test `b4` computes: `powOkW`. -/
theorem okSym_eval [Labels] {env : Env} {pow : UInt64} {bits : Nat} (hx : env.regs .X0 = pow.toBitVec)
    (hy : (env.regs .X19).toNat = bits) (hb : bits < 64) :
    okSym.eval env = (okWord (powOkW bits pow)).toBitVec := by
  have key : (pow.toBitVec &&& ~~~(BitVec.ofNat 64 18446744073709551615 <<< bits) ==
      BitVec.ofNat 64 0) = decide (pow.toNat % 2 ^ bits = 0) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj, BitVec.toNat_and,
      mask_toNat hb, Nat.and_two_pow_sub_one_eq_mod, UInt64.toNat_toBitVec]
    simp
  simp only [okSym, Sym.eval, SBool.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64, hx]
  rw [show (env.regs .X19).toNat % RegWidth.W64.bits = bits from by
    rw [hy]; exact Nat.mod_eq_of_lt hb, key, NativeVm.Equiv.powOkW_eq]
  unfold LeanVM.Protocol.Compile.powOk okWord
  by_cases h : pow.toNat % 2 ^ bits = 0 <;> simp [h]


variable [Host] {k : Nat}

/-- **`TState::grind` meets its contract.** -/
theorem grind_spec (hp : Placed code k)
    (hns : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateNextScalar.entryLabel) (NextScalarPre a s) (NextScalarPost a s))
    (han : ∀ sp, Spec (Labels.label NativeRustcVmArm.Vm.SpongeWAbsorbNonce.entryLabel) (AbsorbNoncePre sp) (AbsorbNoncePost sp))
    (a : DecArea) (s : TState) :
    Spec (Labels.label NativeRustcVmArm.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s) := by
  rintro m0 ⟨hst, hrc, hts, htok, hbits⟩
  set t := m0.regs.X0.toBitVec with htdef
  set bits := grindBits m0 with hbdef
  set fb := frameBase m0 64 with hfb
  have hG : grindStack = 544 := rfl
  have hn : grindStack ≤ m0.regs.SP.toNat := hst.2.1
  have hfnw : fb.toNat + 64 ≤ 2 ^ 64 := frame_noWrap (m := m0) (F := 64) (by omega)
  obtain ⟨⟨hTm, hTn⟩, ⟨hAm, hAn⟩, -⟩ := hts.footprint
  have hTn' : t.toNat + 760 ≤ 2 ^ 64 := hTn
  have hTF : NativeRustcVm.Apart t 760 fb 64 := apart_frame htok.1 hn (by decide)
  have hAF : NativeRustcVm.Apart a.words (8 * a.len) fb 64 := apart_frame htok.2.1 hn (by decide)
  have hRF : ∀ q, NativeRustcVm.InRange fb 64 q →
      ¬ NativeRustcVm.InRange t tstateBytes q ∧ ¬ NativeRustcVm.InRange a.words (8 * a.len) q :=
    fun q hq ↦ ⟨fun h ↦ not_inRange_of_apart hTF hTn hfnw h hq,
      fun h ↦ not_inRange_of_apart hAF hAn hfnw h hq⟩
  have hslot : ∀ p ∈ slots, ∀ i < 8, NativeRustcVm.InRange fb 64 (off fb (p.1 + i)) :=
    fun p hp i hi ↦ inRange_off_self (by have := slots_le p hp; omega) (by omega)
  have hsnw : NativeRustcVm.NoWrap (stackBelow m0 grindStack) grindStack := by
    show _ + grindStack ≤ _
    rw [toNat_stackBelow hn]; have := m0.regs.SP.toNat_lt; omega
  have hRS : ∀ q, NativeRustcVm.InRange (stackBelow m0 grindStack) grindStack q →
      ¬ NativeRustcVm.InRange t tstateBytes q ∧ ¬ NativeRustcVm.InRange a.words (8 * a.len) q :=
    fun q hq ↦ ⟨fun h ↦ not_inRange_of_apart htok.1 hTn hsnw h hq,
      fun h ↦ not_inRange_of_apart htok.2.1 hAn hsnw h hq⟩
  -- `b0`: `bits = 0`?
  unfold NativeRustcVmArm.Vm.TStateGrind.entryLabel
  rw [hp.label (j := NativeRustcVmArm.Vm.TStateGrind.entryOffset) NativeRustcVmArm.Vm.TStateGrind.entry_at]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 (Env.wf_nil m0) (match_nil m0)
    fun st1 hm1 hpc1 => ?_
  obtain ⟨hmem1, hk1⟩ := after_eq run_b0 ▸ ok_b0
  have hd1 : st1.data.dmem = m0.dmem := hm1.dmem_eq (Env.wf_nil _) hmem1
  have hsv1 : Saved m0 st1.data := Match.saved (match_nil m0) hm1 (Env.wf_nil _) rfl hk1
  have hX0 : st1.data.regs.X0 = m0.regs.X0 := Match.reg_eq (r := .X0) (match_nil m0) hm1 rfl rfl
  have hX1 : st1.data.regs.X1 = m0.regs.X1 := Match.reg_eq (r := .X1) (match_nil m0) hm1 rfl rfl
  have hX30 : st1.data.regs.X30 = m0.regs.X30 :=
    Match.reg_eq (r := .X30) (match_nil m0) hm1 rfl rfl
  simp only [PcOk] at hpc1
  split at hpc1
  · -- `bits = 0`: `1`.
    rename_i hc
    have hb0 : bits = 0 := by
      sym_simp at hc
      simp only [Env.ofMachine_regs, beq_iff_eq] at hc
      have := congrArg BitVec.toNat hc
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at this
      exact this
    have hr0 : (grind bits).run s = some ((), s) := by rw [hb0]; rfl
    refine exec_at (infix_of b5_in_code (by simp [b5]) hp) run_b5 (Env.wf_nil _)
      (hpc1.trans (hp.label (j := NativeRustcVmArm.Vm.TStateGrind.b5Offset) NativeRustcVmArm.Vm.TStateGrind.label_3_at)) (match_nil _) fun st2 hm2 hpc2 => ?_
    obtain ⟨hmem2, hk2, h30, hx0⟩ := after_eq run_b5 ▸ ok_b5
    have hd2 : st2.data.dmem = m0.dmem := (hm2.dmem_eq (Env.wf_nil _) hmem2).trans hd1
    have hx30 : st2.data.regs.X30 = m0.regs.X30 :=
      (Match.reg_eq (match_nil _) hm2 rfl h30).trans hX30
    refine .done _ ⟨by simp only [PcOk] at hpc2; rw [hpc2]; simp only [retOf, hx30], ?_, ?_,
      fun q _ ↦ by rw [hd2], hsv1.trans (Match.saved (match_nil _) hm2 (Env.wf_nil _) rfl hk2)⟩
    · show st2.data.regs.X0 = okWord ((grind bits).run s).isSome
      rw [hr0]
      exact UInt64.toBitVec_inj.mp (hm2.regs .X0 _ hx0)
    · intro x s' h
      rw [hr0] at h
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      rw [hd2]; exact hts
  rename_i hc
  have hb0 : bits ≠ 0 := by
    intro h0
    apply hc
    sym_simp
    simp only [Env.ofMachine_regs, beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    exact h0
  -- `b1`: the prologue, `bl next_scalar`.
  have hwf1 : (frameEnv m0 st1.data 64 []).WF :=
    Env.wf_of ⟨⟨Mapped.keeps (frame_mapped (F := 64) hst (by decide)) hsv1.2.2, hfnw⟩, trivial⟩
      (List.pairwise_singleton _ _)
  have hm1' : Match (frameEnv m0 st1.data 64 []) proS st1.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), trivial⟩
      (by rw [show st1.data.regs.SP = m0.regs.SP from hsv1.2.1]; exact frameBase_add.symm)
      trivial trivial trivial trivial
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) run_b1 hwf1
    (hpc1.trans (by change Host.addrOf (k + NativeRustcVmArm.Vm.TStateGrind.b0Offset + NativeRustcVmArm.Vm.TStateGrind.b0.length) = Host.addrOf (k + NativeRustcVmArm.Vm.TStateGrind.b1Offset); rw [Nat.add_assoc, NativeRustcVmArm.Vm.TStateGrind.b0_next])) hm1' fun st2 hm2 hpc2 => ?_
  obtain ⟨hpro, hws2, hx0, hx1, hx19, hx20⟩ := after_eq run_b1 ▸ ok_b1
  have hf2 : Frame m0 64 slots st2.data :=
    Frame.of_prologue_from hsv1 (fun p hp ↦ by
      simp only [slots, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact hX30
      all_goals exact hsv1.1 _ rfl) hwf1 hm2 hpro slots_le
  have hs2 : SameOutside m0.dmem st2.data.dmem (NativeRustcVm.InRange fb 64) := fun q hq ↦ by
    rw [sameOutside_region hwf1 hm2 rfl hws2 q hq]
    show st1.data.dmem.get? q = _
    rw [hd1]
  have hX0₂ : st2.data.regs.X0.toBitVec = off fb 8 := by
    show (st2.data.regs.getXReg .X0).toBitVec = _
    rw [hm2.regs .X0 _ hx0]; rfl
  have hX1₂ : st2.data.regs.X1.toBitVec = t := by
    show (st2.data.regs.getXReg .X1).toBitVec = _
    rw [hm2.regs .X1 _ hx1]
    show st1.data.regs.X0.toBitVec = _; rw [hX0]
  have hX20₂ : st2.data.regs.X20.toBitVec = t := by
    show (st2.data.regs.getXReg .X20).toBitVec = _
    rw [hm2.regs .X20 _ hx20]
    show st1.data.regs.X0.toBitVec = _; rw [hX0]
  have hX19₂ : st2.data.regs.X19.toNat = bits := by
    show (st2.data.regs.getXReg .X19).toBitVec.toNat = _
    rw [hm2.regs .X19 _ hx19]
    sym_simp
    simp only [Env.ofMachine_regs, BitVec.toNat_setWidth]
    show st1.data.regs.X1.toBitVec.toNat % 2 ^ 32 % 2 ^ 64 = _
    rw [hX1]
    show m0.regs.X1.toNat % 2 ^ 32 % 2 ^ 64 = m0.regs.X1.toNat % 2 ^ 32
    omega
  have hts2 : TStateAt st2.data.dmem t a s := hts.frame hf2.kept hRF hs2
  -- `next_scalar`, its output at `fb + 8`.
  have hpre2 : NextScalarPre a s st2.data := by
    unfold NextScalarPre
    rw [hX1₂, hX0₂]
    exact ⟨stackOk_callee hst hf2.kept hf2.sp (by decide) (by decide) (by decide), hts2,
      TStateOk.callee htok hf2.sp hn (by decide) (by decide),
      OutOk.frame hst (by decide) (by decide) hf2.sp hf2.kept (by decide) htok hrc⟩
  refine call_then hpc2 (hns a s) hpre2 fun st3 hpc3 ⟨hout3, hnext3, hs3, hsv3⟩ => ?_
  rw [hX0₂] at hout3
  rw [hX1₂] at hnext3
  rw [hX0₂, hX1₂] at hs3
  have hcal3 : ∀ q, NativeRustcVm.InRange (stackBelow st2.data nextScalarStack) nextScalarStack q →
      NativeRustcVm.InRange (stackBelow m0 grindStack) grindStack q ∧
        ¬ NativeRustcVm.InRange fb 64 q :=
    fun q hq ↦ inRange_callee hf2.sp hn (by decide) (by decide) hq
  have hf3 : Frame m0 64 slots st3.data := by
    refine Frame.call_slots hf2 hsv3 hs3 fun p hp i hi h ↦ ?_
    rcases h with h | h | h
    · exact not_slot_out hfnw (by decide) slots_le (by decide) p hp i hi h
    · exact not_inRange_of_apart hTF hTn hfnw h (hslot p hp i hi)
    · exact (hcal3 _ h).2 (hslot p hp i hi)
  have hso3 : SameOutside m0.dmem st3.data.dmem (fun q ↦ NativeRustcVm.InRange t tstateBytes q ∨
      NativeRustcVm.InRange (stackBelow m0 grindStack) grindStack q) := fun q hq ↦ by
    simp only [not_or] at hq
    have hqf : ¬ NativeRustcVm.InRange fb 64 q :=
      fun h ↦ hq.2 (inRange_frame_stack hn (by decide) h)
    rw [hs3 q (by
      rintro (h | h | h)
      · exact hqf (inRange_of_off hfnw (by decide) h)
      · exact hq.1 h
      · exact hq.2 (hcal3 q h).1)]
    exact hs2 q hqf
  have hX19₃ : st3.data.regs.X19.toNat = bits := by
    rw [show st3.data.regs.X19 = st2.data.regs.X19 from hsv3.1 .X19 rfl]; exact hX19₂
  have hX20₃ : st3.data.regs.X20.toBitVec = t := by
    rw [show st3.data.regs.X20 = st2.data.regs.X20 from hsv3.1 .X20 rfl]; exact hX20₂
  -- `b2`: the tag's bit `0`.
  have hwf3 : (frameEnv m0 st3.data 64 []).WF :=
    Env.wf_of ⟨⟨Mapped.keeps (frame_mapped (F := 64) hst (by decide)) hf3.kept, hfnw⟩, trivial⟩
      (List.pairwise_singleton _ _)
  have hm3 : Match (frameEnv m0 st3.data 64 []) tagS st3.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), trivial⟩
      (by rw [hf3.sp]; exact (eval_ptr rfl).symm) trivial trivial trivial trivial
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) run_b2 hwf3
    (hpc3.trans (by rw [Nat.add_assoc, NativeRustcVmArm.Vm.TStateGrind.b1_next])) hm3 fun st4 hm4 hpc4 => ?_
  obtain ⟨hmid4, hmem4, hx19₄, hx20₄⟩ := after_eq run_b2 ▸ ok_b2
  have hf4 : Frame m0 64 slots st4.data := Frame.of_block hf3 hwf3 hm4 hmid4 slots_le
  have hd4 : st4.data.dmem = st3.data.dmem := hm4.dmem_eq hwf3 hmem4
  have hX19₄ : st4.data.regs.X19.toNat = bits := by
    rw [show st4.data.regs.X19 = st3.data.regs.X19 from Match.reg_eq hm3 hm4 rfl hx19₄]
    exact hX19₃
  have hX20₄ : st4.data.regs.X20.toBitVec = t := by
    rw [show st4.data.regs.X20 = st3.data.regs.X20 from Match.reg_eq hm3 hm4 rfl hx20₄]
    exact hX20₃
  simp only [PcOk] at hpc4
  sym_simp at hpc4
  cases hns2 : nextScalar.run s with
  | none =>
    -- `None`: `0`.
    rw [hns2] at hout3
    have h0 : NativeRustcVm.WordAt st3.data.dmem (off fb 8) 0 := hout3
    rw [load4_of_tag (Or.inl rfl) h0] at hpc4
    simp (config := { decide := true }) only [↓reduceIte] at hpc4
    have hnone : (grind bits).run s = none := by
      rw [NativeVm.Equiv.grind_run hb0, hns2]; rfl
    have hwf4 : (frameEnv m0 st4.data 64 []).WF :=
      Env.wf_of ⟨⟨Mapped.keeps (frame_mapped (F := 64) hst (by decide)) hf4.kept, hfnw⟩, trivial⟩
        (List.pairwise_singleton _ _)
    have hm4' : Match (frameEnv m0 st4.data 64 []) failS st4.data :=
      match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), trivial⟩
        (by rw [hf4.sp]; exact (eval_ptr rfl).symm) trivial trivial trivial trivial
    refine exec_at (infix_of b6_in_code (by simp [b6]) hp) run_b6 hwf4
      (hpc4.trans (hp.label (j := NativeRustcVmArm.Vm.TStateGrind.b6Offset) NativeRustcVmArm.Vm.TStateGrind.label_4_at)) hm4' fun st5 hm5 hpc5 => ?_
    obtain ⟨hepi, hmem5, hx0'⟩ := after_eq run_b6 ▸ ok_b6
    obtain ⟨hsv5, hsl5⟩ := Frame.epilogue hf4 hwf4 hm5 hepi
    have hx30 : st5.data.regs.X30 = m0.regs.X30 := hsl5 (32, .X30) (List.mem_cons_self ..)
    have hd5 : st5.data.dmem = st4.data.dmem := hm5.dmem_eq hwf4 hmem5
    refine .done _ ⟨by simp only [PcOk] at hpc5; rw [hpc5]; simp only [retOf, hx30], ?_, ?_, ?_,
      hsv5⟩
    · show st5.data.regs.X0 = okWord ((grind bits).run s).isSome
      rw [hnone]
      exact UInt64.toBitVec_inj.mp (hm5.regs .X0 _ hx0')
    · intro x s' h; rw [hnone] at h; cases h
    · intro q hq; rw [hd5, hd4]; exact hso3 q hq
  | some p =>
  obtain ⟨x, s1⟩ := p
  rw [hns2] at hout3
  obtain ⟨ht1, hel⟩ := (hout3 : OptEWAt st3.data.dmem (off fb 8) (some x))
  rw [ewAt_iff, off_off, off_off] at hel
  have hts3 : TStateAt st3.data.dmem t a s1 := hnext3 x s1 hns2
  rw [load4_of_tag (Or.inr rfl) ht1] at hpc4
  simp (config := { decide := true }) only [↓reduceIte] at hpc4
  -- `b3`: `bl absorb_nonce`.
  have hwf4 : (frameEnv m0 st4.data 64 []).WF :=
    Env.wf_of ⟨⟨Mapped.keeps (frame_mapped (F := 64) hst (by decide)) hf4.kept, hfnw⟩, trivial⟩
      (List.pairwise_singleton _ _)
  have hm4' : Match (frameEnv m0 st4.data 64 []) callS st4.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), trivial⟩
      (by rw [hf4.sp]; exact (eval_ptr rfl).symm) trivial trivial trivial trivial
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) run_b3 hwf4
    (hpc4.trans (by rw [Nat.add_assoc, NativeRustcVmArm.Vm.TStateGrind.b2_next])) hm4' fun st5 hm5 hpc5 => ?_
  obtain ⟨hmid5, hmem5, hx0₅, hx1₅, hx2₅, hx19₅⟩ := after_eq run_b3 ▸ ok_b3
  have hf5 : Frame m0 64 slots st5.data := Frame.of_block hf4 hwf4 hm5 hmid5 slots_le
  have hd5 : st5.data.dmem = st4.data.dmem := hm5.dmem_eq hwf4 hmem5
  have hX0₅ : st5.data.regs.X0.toBitVec = t := by
    show (st5.data.regs.getXReg .X0).toBitVec = _
    rw [hm5.regs .X0 _ hx0₅]; exact hX20₄
  have hX1₅ : st5.data.regs.X1 = x.c0 := UInt64.toBitVec_inj.mp ((hm5.regs .X1 _ hx1₅).trans
    (load_ofMachine (o := 16) rfl (hd4 ▸ hel.1)))
  have hX2₅ : st5.data.regs.X2 = x.c1 := UInt64.toBitVec_inj.mp ((hm5.regs .X2 _ hx2₅).trans
    (load_ofMachine (o := 24) rfl (hd4 ▸ hel.2)))
  have hX19₅ : st5.data.regs.X19.toNat = bits := by
    rw [show st5.data.regs.X19 = st4.data.regs.X19 from Match.reg_eq hm4' hm5 rfl hx19₅]
    exact hX19₄
  -- `absorb_nonce`.
  have h5sp : st5.data.regs.SP.toNat = m0.regs.SP.toNat - 64 := by
    rw [← UInt64.toNat_toBitVec, hf5.sp, frameBase_toNat hn (by decide)]
  have hrcOut : ∀ q, (NativeRustcVm.InRange t tstateBytes q ∨
      NativeRustcVm.InRange (stackBelow m0 grindStack) grindStack q) →
      ¬ NativeRustcVm.InRange rcAddr 192 q := by
    rintro q (hq | hq) h
    · exact not_inRange_of_apart (Apart.symm' htok.2.2) hrc.2.1 hTn h hq
    · exact not_inRange_of_apart hrc.2.2 hrc.2.1 hsnw h hq
  have hso5 : SameOutside m0.dmem st5.data.dmem (fun q ↦ NativeRustcVm.InRange t tstateBytes q ∨
      NativeRustcVm.InRange (stackBelow m0 grindStack) grindStack q) := by
    rw [hd5, hd4]; exact hso3
  have hts5 : TStateAt st5.data.dmem t a s1 := by rw [hd5, hd4]; exact hts3
  have hpre5 : AbsorbNoncePre s1.sponge st5.data := by
    unfold AbsorbNoncePre
    rw [hX0₅]
    have h1 : t.toNat + 760 ≤ (stackBelow m0 grindStack).toNat ∨
        (stackBelow m0 grindStack).toNat + grindStack ≤ t.toNat := htok.1
    have h2 : t.toNat + 760 ≤ rcAddr.toNat ∨ rcAddr.toNat + 192 ≤ t.toNat := htok.2.2
    refine ⟨stackOk_callee hst hf5.kept hf5.sp (by decide) (by decide) (by decide),
      RcAt.callee hrc (rc_keep hso5 hrcOut) hn (by decide) h5sp (by decide),
      ⟨fun j hj ↦ hts5.footprint.1.1 j (by simp only [spongeBytes] at hj; show j < 760; omega), ?_,
        apart_callee (n := grindStack) (F := 64) ?_ hf5.sp hn (by decide) (by decide), ?_⟩,
      hts5.sponge⟩
    · show t.toNat + 328 ≤ 2 ^ 64; omega
    · show t.toNat + 328 ≤ _ ∨ _ ≤ t.toNat; omega
    · show t.toNat + 328 ≤ _ ∨ _ ≤ t.toNat; omega
  refine call_then hpc5 (han s1.sponge) hpre5 fun st6 hpc6 ⟨hx0₆, hsp6, hs6, hsv6⟩ => ?_
  rw [hX1₅, hX2₅] at hx0₆ hsp6
  rw [hX0₅] at hsp6 hs6
  have hcal6 : ∀ q, NativeRustcVm.InRange (stackBelow st5.data absorbNonceStack) absorbNonceStack q →
      NativeRustcVm.InRange (stackBelow m0 grindStack) grindStack q ∧
        ¬ NativeRustcVm.InRange fb 64 q :=
    fun q hq ↦ inRange_callee hf5.sp hn (by decide) (by decide) hq
  have hT328 : ∀ q, NativeRustcVm.InRange t spongeBytes q → NativeRustcVm.InRange t 760 q :=
    fun q h ↦ inRange_sub hTn (le_refl _) (by simp only [spongeBytes]; omega) h
  have hf6 : Frame m0 64 slots st6.data := by
    refine Frame.call hf5 hsv6 hs6 (fun q hq ↦ ?_) hfnw slots_le
    rcases hq with hq | hq
    · exact not_inRange_of_apart hTF hTn hfnw (hT328 q hq)
    · exact (hcal6 q hq).2
  set r := s1.sponge.absorbNonce x with hrdef
  have hts6 : TStateAt st6.data.dmem t a { s1 with sponge := r.2 } := by
    refine hts5.with_sponge hsv6.2.2 (fun q hq ↦ hRS q (hcal6 q hq).1) (fun q hq ↦ hs6 q ?_) hsp6
    rintro (h | h)
    · obtain ⟨j, hj, hw, hq'⟩ := touch_of_inRange (o := 0) (n := 328)
        (hTn' : NativeRustcVm.NoWrap t 760) (by decide) (by rwa [off_zero])
      exact hq (Or.inl ⟨j, hj, hw.2, hq'⟩)
    · exact hq (Or.inr h)
  have hso6 : SameOutside m0.dmem st6.data.dmem (fun q ↦ NativeRustcVm.InRange t tstateBytes q ∨
      NativeRustcVm.InRange (stackBelow m0 grindStack) grindStack q) := fun q hq ↦ by
    simp only [not_or] at hq
    rw [hs6 q (by
      rintro (h | h)
      · exact hq.1 (hT328 q h)
      · exact hq.2 (hcal6 q h).1)]
    exact hso5 q (by simp only [not_or]; exact hq)
  have hX19₆ : st6.data.regs.X19.toNat = bits := by
    rw [show st6.data.regs.X19 = st5.data.regs.X19 from hsv6.1 .X19 rfl]; exact hX19₅
  -- `b4`: the test, the epilogue.
  have hwf6 : (frameEnv m0 st6.data 64 []).WF :=
    Env.wf_of ⟨⟨Mapped.keeps (frame_mapped (F := 64) hst (by decide)) hf6.kept, hfnw⟩, trivial⟩
      (List.pairwise_singleton _ _)
  have hm6 : Match (frameEnv m0 st6.data 64 []) maskS st6.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), trivial⟩
      (by rw [hf6.sp]; exact (eval_ptr rfl).symm) trivial trivial trivial trivial
  refine exec_at (infix_of b4_in_code (by simp [b4]) hp) run_b4 hwf6
    (hpc6.trans (by rw [Nat.add_assoc, NativeRustcVmArm.Vm.TStateGrind.b3_next])) hm6 fun st7 hm7 hpc7 => ?_
  obtain ⟨hepi, hmem7, hx0₇⟩ := after_eq run_b4 ▸ ok_b4
  obtain ⟨hsv7, hsl7⟩ := Frame.epilogue hf6 hwf6 hm7 hepi
  have hx30 : st7.data.regs.X30 = m0.regs.X30 := hsl7 (32, .X30) (List.mem_cons_self ..)
  have hd7 : st7.data.dmem = st6.data.dmem := hm7.dmem_eq hwf6 hmem7
  have hrun : (grind bits).run s = if powOkW bits r.1 then some ((), { s1 with sponge := r.2 })
      else none := by
    rw [NativeVm.Equiv.grind_run hb0, hns2]; rfl
  refine .done _ ⟨by simp only [PcOk] at hpc7; rw [hpc7]; simp only [retOf, hx30], ?_, ?_, ?_,
    hsv7⟩
  · show st7.data.regs.X0 = okWord ((grind bits).run s).isSome
    have hiso : ((grind bits).run s).isSome = powOkW bits r.1 := by
      rw [hrun]; split <;> simp_all
    rw [hiso]
    exact UInt64.toBitVec_inj.mp ((hm7.regs .X0 _ hx0₇).trans
      (okSym_eval (by rw [Env.ofMachine_regs]; exact congrArg UInt64.toBitVec hx0₆)
        (by rw [Env.ofMachine_regs]; exact hX19₆) hbits))
  · intro u s' h
    rw [hrun] at h
    split at h
    · obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      rw [hd7]; exact hts6
    · cases h
  · intro q hq; rw [hd7]; exact hso6 q hq

end

end NativeRustcVmArm.Transcript.Grind
