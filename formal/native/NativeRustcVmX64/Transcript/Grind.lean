module

public import NativeRustcVmX64.Transcript.Callee
public import NativeRustcVmX64.Transcript.Grind.Exec
public import NativeRustcVmX64.Transcript.Arith
public import NativeVm.Equiv.Transcript
public import NativeRustcVmX64.Code.Vm.SpongeWAbsorbNonce.Names
public import NativeRustcVmX64.Code.Vm.TStateGrind.Names
public import NativeRustcVmX64.Code.Vm.TStateNextScalar.Names

/-!
# `TState::grind` on x86-64

**`grind_spec`**: AL becomes `grind bits`'s `Some`/`None` and the `TState` at RDI its state, given
the contracts of `next_scalar` and `absorb_nonce`. `bits = 0` returns AL = `1` at once (`b0`,
`b5`). Otherwise `b1` pushes R14, RBX and calls `next_scalar` with its output in the frame; `b2`
tests its tag: `0`, `b6` returns `0`; `1`, `b3` calls `absorb_nonce` on the nonce and `b4` returns
whether the lane's low `bits` bits are zero (`pow & !(-1 << bits) == 0`, `bits < 64`).
-/

namespace NativeRustcVmX64.Transcript.Grind

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.TStateGrind
open NativeRustcVm.Transcript NativeVm.Model

public section

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 48 := by decide

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

/-- The test `b4` computes, in AL: `powOkW`. -/
theorem okSym_eval [Labels] {env : Env} {pow : UInt64} {bits : Nat}
    (hx : env.regs .rax = pow.toBitVec) (hy : (env.regs .rbx).toNat = bits) (hb : bits < 64) :
    (okSym.eval env).toNat % 256 = (okWord (powOkW bits pow)).toNat := by
  have hsc : shiftCount .W64 (UnOp.apply .trunc .W32 (env.regs .rbx)) = bits := by
    unfold shiftCount
    rw [toNat_low, show (UnOp.apply .trunc .W32 (env.regs .rbx)).toNat = bits by
      rw [UnOp.apply, toNat_ext, toNat_low, hy]
      exact Nat.mod_eq_of_lt (by show bits < 2 ^ 32; omega)]
    show bits % 2 ^ 8 &&& 63 = bits
    rw [Nat.mod_eq_of_lt (by omega), show (63 : Nat) = 2 ^ 6 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]
  have key : (pow.toBitVec &&& ~~~(BitVec.ofNat 64 18446744073709551615 <<< bits) ==
      BitVec.ofNat 64 0) = decide (pow.toNat % 2 ^ bits = 0) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj, BitVec.toNat_and,
      mask_toNat hb, Nat.and_two_pow_sub_one_eq_mod, UInt64.toNat_toBitVec]
    simp
  have hm : ∀ (x : BitVec 64) (c : Bool),
      (BinOp.apply .merge .W8 x (if c then BitVec.ofNat 64 1 else BitVec.ofNat 64 0)).toNat % 256 =
        (if c then 1 else 0) := by
    intro x c
    cases c
    · have h := congrArg BitVec.toNat (low8_replaceLow x (low .W8 (BitVec.ofNat 64 0)))
      rw [toNat_low] at h
      exact h
    · have h := congrArg BitVec.toNat (low8_replaceLow x (low .W8 (BitVec.ofNat 64 1)))
      rw [toNat_low] at h
      exact h
  simp only [okSym, Sym.eval]
  rw [hm]
  simp only [SBool.eval, CmpOp.apply, BinOp.apply, Sym.eval, low_W64, ext_W64, hx]
  rw [hsc]
  simp only [UnOp.apply, low_W64, ext_W64]
  rw [key, NativeVm.Equiv.powOkW_eq]
  unfold LeanVM.Protocol.Compile.powOk okWord
  by_cases h : pow.toNat % 2 ^ bits = 0 <;> simp [h]

variable [Host] {k : Nat}

/-- **`TState::grind` meets its contract.** -/
theorem grind_spec (hp : Placed code k)
    (hns : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.TStateNextScalar.entryLabel) (NextScalarPre a s) (NextScalarPost a s))
    (han : ∀ sp, Spec (Labels.label NativeRustcVmX64.Vm.SpongeWAbsorbNonce.entryLabel) (AbsorbNoncePre sp) (AbsorbNoncePost sp))
    (a : DecArea) (s : TState) :
    Spec (Labels.label NativeRustcVmX64.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s) := by
  rintro m0 ⟨hst, hrc, hts, htok, hbits, hgot⟩
  set t := reg m0 .rdi with htdef
  set bits := grindBits m0 with hbdef
  set fb := stackBelow m0 48 with hfb
  have hn : grindStack ≤ (rspOf m0).toNat := hst.1
  have h8 : (rspOf m0).toNat + 8 ≤ 2 ^ 64 := hst.2.1
  have hfnw : NativeRustcVm.NoWrap fb (48 + 8) := frame_noWrap hst (by decide)
  have hfnw48 : NativeRustcVm.NoWrap fb 48 := by unfold NativeRustcVm.NoWrap at hfnw ⊢; omega
  obtain ⟨⟨hTm, hTn⟩, ⟨hAm, hAn⟩, -⟩ := hts.footprint
  have hTn' : t.toNat + 760 ≤ 2 ^ 64 := hTn
  have hTF : NativeRustcVm.Apart t 760 fb (48 + 8) := apart_frame htok.1 hn (by decide)
  have hAF : NativeRustcVm.Apart a.words (8 * a.len) fb (48 + 8) :=
    apart_frame htok.2.1 hn (by decide)
  have hRF : ∀ q, NativeRustcVm.InRange fb (48 + 8) q →
      ¬ NativeRustcVm.InRange t tstateBytes q ∧ ¬ NativeRustcVm.InRange a.words (8 * a.len) q :=
    fun q hq ↦ ⟨fun h ↦ not_inRange_of_apart hTF hTn hfnw h hq,
      fun h ↦ not_inRange_of_apart hAF hAn hfnw h hq⟩
  have hsnw := noWrap_stackBelow hst
  have hRS : ∀ q, NativeRustcVm.InRange (stackBelow m0 grindStack) grindStack q →
      ¬ NativeRustcVm.InRange t tstateBytes q ∧ ¬ NativeRustcVm.InRange a.words (8 * a.len) q :=
    fun q hq ↦ ⟨fun h ↦ not_inRange_of_apart htok.1 hTn hsnw h (inRange_mono hq (by omega)),
      fun h ↦ not_inRange_of_apart htok.2.1 hAn hsnw h (inRange_mono hq (by omega))⟩
  have hfS : ∀ q, NativeRustcVm.InRange fb 48 q →
      NativeRustcVm.InRange (stackBelow m0 grindStack) grindStack q :=
    fun q h ↦ inRange_frame_stack h8 hn (by decide) h
  -- `b0`: `bits = 0`?
  have hwf0 := frame_wf (m0 := m0) (d := m0) (F := 48) (rest := []) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.TStateGrind.b1Offset + b1.length)).toBitVec) ⟨frame_mapped hst (by decide), hfnw⟩
    (by simp) (List.pairwise_singleton _ _)
  have hm0 : Match (frameEnv m0 m0 48 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.TStateGrind.b1Offset + b1.length)).toBitVec)
      entryS m0 :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨match_rsp, trivial⟩ trivial trivial trivial
  unfold NativeRustcVmX64.Vm.TStateGrind.entryLabel
  rw [hp.label NativeRustcVmX64.Vm.TStateGrind.entry_at]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) exit_b0 hwf0 nofun hm0
    fun st1 hm1 hpc1 => ?_
  have hesi : (low .W32 (m0.regs.get64 .rsi)).toNat = bits := by
    rw [toNat_low]; rfl
  simp only [PcOk] at hpc1
  split at hpc1
  · -- `bits = 0`: AL = `1`.
    rename_i hc
    have hb0 : bits = 0 := by
      sym_simp_at hc
      simp only [Env.ofMachine_regs, BitVec.and_self, low_ext, beq_iff_eq] at hc
      have := congrArg BitVec.toNat hc
      rw [hesi] at this
      rw [this]; rfl
    have hr0 : (grind bits).run s = some ((), s) := by rw [hb0]; rfl
    refine exec_at (infix_of b5_in_code (by simp [b5]) hp) exit_b5 hwf0 nofun
      (hpc1.trans (hp.label NativeRustcVmX64.Vm.TStateGrind.label_3_at)) hm1 fun st2 hm2 hpc2 => ?_
    obtain ⟨hk2, hmem2, hrsp2, hrax2⟩ := ok_b5
    have hd2 : st2.data.dmem = m0.dmem := hm2.dmem_eq hwf0 hmem2
    simp only [PcOk] at hpc2
    refine .done _ ⟨by rw [hpc2]; exact Frame.entry.load_ret hst (by decide),
      (hm2.regs .rsp _ hrsp2).trans ((eval_ptr0 (o := 56)).trans (frame_add 48 8)), ?_, ?_,
      fun q _ ↦ by rw [hd2], Match.saved hm0 hm2 hwf0 rfl hk2⟩
    · show (reg st2.data .rax).toNat % 256 = (okWord ((grind bits).run s).isSome).toNat
      rw [hr0, show reg st2.data .rax = _ from hm2.regs .rax _ hrax2]
      exact merge_one_mod _
    · intro x s' h
      rw [hr0] at h
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      rw [hd2]; exact hts
  rename_i hc
  have hb0 : bits ≠ 0 := by
    intro h0
    apply hc
    sym_simp
    simp only [Env.ofMachine_regs, BitVec.and_self, low_ext, beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    rw [hesi, h0]; rfl
  -- `b1`: the prologue, `call next_scalar`.
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) run_b1 hwf0 (fun _ _ ↦ rfl)
    (hpc1.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.TStateGrind.b0_next)) hm1 fun st2 hm2 hpc2 => ?_
  obtain ⟨hpro, hws2, hx7, hx6, hx3, hx14⟩ := after_eq run_b1 ▸ ok_b1
  have hf2 : Frame m0 48 slots 0 st2.data :=
    Frame.of_prologue Frame.entry hwf0 hm2 hpro slots_le (by decide)
  have hs2 : NativeRustcVm.SameOutside m0.dmem st2.data.dmem (NativeRustcVm.InRange fb 48) :=
    sameOutside_low hwf0 hm2 (r := 0) rfl (by decide) hws2
  have hsp2 : rspOf st2.data = fb := by rw [hf2.sp, off_zero]
  have hX7 : reg st2.data .rdi = off fb 8 := (hm2.regs .rdi _ hx7).trans (eval_ptr0 8)
  have hX6 : reg st2.data .rsi = t := hm2.regs .rsi _ hx6
  have hX14 : reg st2.data .r14 = t := hm2.regs .r14 _ hx14
  have hX3 : (reg st2.data .rbx).toNat = bits := by
    rw [show reg st2.data .rbx = _ from hm2.regs .rbx _ hx3]
    simp only [Sym.eval, UnOp.apply, Env.ofMachine_regs]
    rw [toNat_ext, toNat_low]
    rfl
  have hts2 : TStateAt st2.data.dmem t a s :=
    hts.frame hf2.kept (fun q hq ↦ hRF q (inRange_mono hq (by omega))) hs2
  -- `next_scalar`, its output at `fb + 8`.
  have hpre2 : NextScalarPre a s st2.data := by
    unfold NextScalarPre
    rw [hX6, hX7]
    exact ⟨stackOk_callee hst hf2.kept hsp2 (by decide), hts2,
      TStateOk.callee htok hsp2 hn (by decide),
      OutOk.frame hst (by decide) hsp2 hf2.kept (by decide) (by decide) htok hrc⟩
  refine call_then hpc2 (hns a s) hpre2 fun st3 hpc3 hrsp3 ⟨hout3, hnext3, hs3, hsv3⟩ => ?_
  rw [hX7] at hout3
  rw [hX6] at hnext3
  rw [hX7, hX6] at hs3
  have hcal3 : ∀ q, NativeRustcVm.InRange (stackBelow st2.data nextScalarStack) nextScalarStack q →
      NativeRustcVm.InRange (stackBelow m0 grindStack) grindStack q ∧
        ¬ NativeRustcVm.InRange fb (48 + 8) q :=
    fun q hq ↦ inRange_callee hsp2 h8 hn (by decide) hq
  have hslot : ∀ j, 8 + 24 ≤ j → j < 48 + 8 → ∀ q, q = off fb j →
      ¬ (NativeRustcVm.InRange (off fb 8) 24 q ∨ NativeRustcVm.InRange t tstateBytes q ∨
        NativeRustcVm.InRange (stackBelow st2.data nextScalarStack) nextScalarStack q) := by
    rintro j hj1 hj2 q rfl (h | h | h)
    · rw [inRange_off_iff (by omega) (by omega)] at h; omega
    · exact not_inRange_of_apart hTF hTn hfnw h (inRange_off_self hj2 (by omega))
    · exact (hcal3 _ h).2 (inRange_off_self hj2 (by omega))
  have hf3 : Frame m0 48 slots 8 st3.data :=
    Frame.call_slots hf2 hsv3 hrsp3 hs3
      (fun p hp i hi ↦ hslot _ (by
        simp only [slots, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl <;> dsimp only <;> omega)
        (by have := slots_le p hp; omega) _ rfl)
      (fun j hj ↦ hslot _ (by omega) (by omega) _ rfl)
  have hso3 : NativeRustcVm.SameOutside m0.dmem st3.data.dmem (fun q ↦
      NativeRustcVm.InRange t tstateBytes q ∨
        NativeRustcVm.InRange (stackBelow m0 grindStack) grindStack q) := fun q hq ↦ by
    simp only [not_or] at hq
    have hqf : ¬ NativeRustcVm.InRange fb 48 q := fun h ↦ hq.2 (hfS q h)
    rw [hs3 q (by
      rintro (h | h | h)
      · exact hqf (inRange_of_off hfnw48 (by decide) h)
      · exact hq.1 h
      · exact hq.2 (hcal3 q h).1)]
    exact hs2 q hqf
  have hX3₃ : (reg st3.data .rbx).toNat = bits := by
    show (st3.data.regs.get64 .rbx).toNat = bits; rw [hsv3.1 .rbx rfl]; exact hX3
  have hX14₃ : reg st3.data .r14 = t := (hsv3.1 .r14 rfl).trans hX14
  -- `b2`: the tag's low byte.
  have hwf3 := frame_wf (m0 := m0) (d := st3.data) (F := 48) (rest := []) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.TStateGrind.b3Offset + b3.length)).toBitVec)
    ⟨Mapped.keeps (frame_mapped hst (by decide)) hf3.kept, hfnw⟩ (by simp)
    (List.pairwise_singleton _ _)
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) exit_b2 hwf3 nofun
    (hpc3.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.TStateGrind.b1_next))
    (match_ofMachine ⟨rfl, trivial⟩ ⟨hf3.rsp_eval, trivial⟩ trivial trivial trivial)
    fun st4 hm4 hpc4 => ?_
  obtain ⟨hmid4, hmem4, hx3₄, hx14₄⟩ := ok_b2
  simp only [PcOk] at hpc4
  sym_simp_at hpc4
  cases hns2 : nextScalar.run s with
  | none =>
    -- `None`: `0`.
    rw [hns2] at hout3
    have h0 : NativeRustcVm.WordAt st3.data.dmem (off fb 8) 0 := hout3
    have ht0 : (frameEnv m0 st3.data 48 [] (fun _ ↦ 0)
        (Host.addrOf (k + NativeRustcVmX64.Vm.TStateGrind.b3Offset + b3.length)).toBitVec).load 0 8 1 = BitVec.ofNat 64 0 :=
      load1_of_tag (Or.inl rfl) h0
    simp only [ht0] at hpc4
    simp (config := { decide := true }) only [↓reduceIte] at hpc4
    have hnone : (grind bits).run s = none := by
      rw [NativeVm.Equiv.grind_run hb0, hns2]; rfl
    refine exec_at (infix_of b6_in_code (by simp [b6]) hp) exit_b6 hwf3 nofun
      (hpc4.trans (hp.label NativeRustcVmX64.Vm.TStateGrind.label_4_at)) hm4 fun st5 hm5 hpc5 => ?_
    obtain ⟨hepi, hmem5, hrax5⟩ := end_b6
    obtain ⟨hsv5, hrsp5⟩ := Frame.epilogue hf3 hwf3 hm5 hepi
    have hd5 : st5.data.dmem = st3.data.dmem := hm5.dmem_eq hwf3 hmem5
    simp only [PcOk] at hpc5
    refine .done _ ⟨by rw [hpc5]; exact hf3.load_ret hst (by decide), hrsp5, ?_, ?_, ?_, hsv5⟩
    · show (reg st5.data .rax).toNat % 256 = (okWord ((grind bits).run s).isSome).toNat
      rw [hnone, show reg st5.data .rax = _ from hm5.regs .rax _ hrax5]; rfl
    · intro x s' h; rw [hnone] at h; cases h
    · intro q hq; rw [hd5]; exact hso3 q hq
  | some p =>
  obtain ⟨x, s1⟩ := p
  rw [hns2] at hout3
  obtain ⟨ht1, hel⟩ := (hout3 : OptEWAt st3.data.dmem (off fb 8) (some x))
  rw [ewAt_iff, off_off, off_off] at hel
  have hts3 : TStateAt st3.data.dmem t a s1 := hnext3 x s1 hns2
  have ht1' : (frameEnv m0 st3.data 48 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.TStateGrind.b3Offset + b3.length)).toBitVec).load 0 8 1 = BitVec.ofNat 64 1 :=
    load1_of_tag (Or.inr rfl) ht1
  simp only [ht1'] at hpc4
  simp (config := { decide := true }) only [↓reduceIte] at hpc4
  -- `b3`: `call absorb_nonce`.
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) (exec_after exit_b2 run_b3) hwf3
    (fun _ _ ↦ rfl) (hpc4.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.TStateGrind.b2_next)) hm4
    fun st5 hm5 hpc5 => ?_
  obtain ⟨hmid5, hws5, hx7₅, hx6₅, hx2₅, hx3₅, hx14₅⟩ := after_eq run_b3 ▸ ok_b3
  have hf5 : Frame m0 48 slots 0 st5.data := Frame.of_block hf3 hwf3 hm5 hmid5 slots_le
  have hs5 : NativeRustcVm.SameOutside st3.data.dmem st5.data.dmem (NativeRustcVm.InRange fb 8) :=
    sameOutside_low hwf3 hm5 (r := 0) rfl (by decide) hws5
  have hsp5 : rspOf st5.data = fb := by rw [hf5.sp, off_zero]
  have hX7₅ : reg st5.data .rdi = t := (hm5.regs .rdi _ hx7₅).trans hX14₃
  have hX6₅ : reg st5.data .rsi = x.c0.toBitVec :=
    (hm5.regs .rsi _ hx6₅).trans (load_ofMachine (o := 16) rfl hel.1)
  have hX2₅ : reg st5.data .rdx = x.c1.toBitVec :=
    (hm5.regs .rdx _ hx2₅).trans (load_ofMachine (o := 24) rfl hel.2)
  have hX3₅ : (reg st5.data .rbx).toNat = bits := by
    rw [show reg st5.data .rbx = _ from hm5.regs .rbx _ hx3₅]; exact hX3₃
  -- `absorb_nonce`.
  have hrcOut : ∀ q, (NativeRustcVm.InRange t tstateBytes q ∨
      NativeRustcVm.InRange (stackBelow m0 grindStack) grindStack q) →
      ¬ NativeRustcVm.InRange rcAddr 192 q := by
    rintro q (hq | hq) h
    · exact not_inRange_of_apart (Apart.symm' htok.2.2) hrc.2.1 hTn h hq
    · exact not_inRange_of_apart hrc.2.2 hrc.2.1 hsnw h (inRange_mono hq (by omega))
  have hso5 : NativeRustcVm.SameOutside m0.dmem st5.data.dmem (fun q ↦
      NativeRustcVm.InRange t tstateBytes q ∨
        NativeRustcVm.InRange (stackBelow m0 grindStack) grindStack q) := fun q hq ↦ by
    rw [hs5 q fun h ↦ hq (Or.inr (hfS q (inRange_mono h (by decide))))]
    exact hso3 q hq
  have hts5 : TStateAt st5.data.dmem t a s1 :=
    hts3.frame (hm5.kept hwf3) (fun q hq ↦ hRF q (inRange_mono hq (by omega))) hs5
  have hpre5 : AbsorbNoncePre s1.sponge st5.data := by
    unfold AbsorbNoncePre
    rw [hX7₅]
    have h1 : t.toNat + 760 ≤ (stackBelow m0 grindStack).toNat ∨
        (stackBelow m0 grindStack).toNat + (grindStack + 8) ≤ t.toNat := htok.1
    have h2 : t.toNat + 760 ≤ rcAddr.toNat ∨ rcAddr.toNat + 192 ≤ t.toNat := htok.2.2
    refine ⟨stackOk_callee hst hf5.kept hsp5 (by decide),
      RcAt.callee hrc (rc_keep hso5 hrcOut) hsp5 hn (by decide),
      ⟨fun j hj ↦ hts5.footprint.1.1 j (by simp only [spongeBytes] at hj; show j < 760; omega), ?_,
        apart_callee (n := grindStack) (F := 48) ?_ hsp5 hn (by decide), ?_⟩,
      hts5.sponge, ?_⟩
    · show t.toNat + 328 ≤ 2 ^ 64; omega
    · show t.toNat + 328 ≤ _ ∨ _ ≤ t.toNat; omega
    · show t.toNat + 328 ≤ _ ∨ _ ≤ t.toNat; omega
    · refine got_callee hgot (got_keep hgot hst (writes := [(t, tstateBytes)])
        (by simp [t]) (by simpa using hTn) (by simpa using hso5))
        hsp5 hn (by decide) ?_
      intro l hl b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · exact Apart.sub ((hgot.1 l hl).2.2.2 (t, tstateBytes) (by simp [t]))
          (Nat.le_refl _) (by simp only [spongeBytes, tstateBytes]; omega)
      · exact (hgot.1 l hl).2.2.2 (rcAddr, 192) (by simp)
  refine call_then hpc5 (han s1.sponge) hpre5 fun st6 hpc6 hrsp6 ⟨hx0₆, hsp6, hs6, hsv6⟩ => ?_
  rw [hX6₅, hX2₅] at hx0₆ hsp6
  rw [hX7₅] at hsp6 hs6
  have hcal6 : ∀ q, NativeRustcVm.InRange (stackBelow st5.data absorbNonceStack) absorbNonceStack q →
      NativeRustcVm.InRange (stackBelow m0 grindStack) grindStack q ∧
        ¬ NativeRustcVm.InRange fb (48 + 8) q :=
    fun q hq ↦ inRange_callee hsp5 h8 hn (by decide) hq
  have hT328 : ∀ q, NativeRustcVm.InRange t spongeBytes q → NativeRustcVm.InRange t 760 q :=
    fun q h ↦ inRange_mono h (by simp only [spongeBytes]; omega)
  have hf6 : Frame m0 48 slots 8 st6.data := by
    refine Frame.call hf5 hsv6 hrsp6 hs6 (fun q hq ↦ ?_) hfnw slots_le
    rcases hq with hq | hq
    · exact not_inRange_of_apart hTF hTn hfnw (hT328 q hq)
    · exact (hcal6 q hq).2
  have hxc : (⟨UInt64.ofBitVec x.c0.toBitVec, UInt64.ofBitVec x.c1.toBitVec⟩ : EW) = x := rfl
  rw [hxc] at hx0₆ hsp6
  set r := s1.sponge.absorbNonce x with hrdef
  have hts6 : TStateAt st6.data.dmem t a { s1 with sponge := r.2 } := by
    refine hts5.with_sponge hsv6.2 (fun q hq ↦ hRS q (hcal6 q hq).1) (fun q hq ↦ hs6 q ?_) hsp6
    rintro (h | h)
    · obtain ⟨j, hj, hw, hq'⟩ := touch_of_inRange (o := 0) (n := 328)
        (hTn' : NativeRustcVm.NoWrap t 760) (by decide) (by rwa [off_zero])
      exact hq (Or.inl ⟨j, hj, hw.2, hq'⟩)
    · exact hq (Or.inr h)
  have hso6 : NativeRustcVm.SameOutside m0.dmem st6.data.dmem (fun q ↦
      NativeRustcVm.InRange t tstateBytes q ∨
        NativeRustcVm.InRange (stackBelow m0 grindStack) grindStack q) := fun q hq ↦ by
    simp only [not_or] at hq
    rw [hs6 q (by
      rintro (h | h)
      · exact hq.1 (hT328 q h)
      · exact hq.2 (hcal6 q h).1)]
    exact hso5 q (by simp only [not_or]; exact hq)
  have hX3₆ : (reg st6.data .rbx).toNat = bits := by
    show (st6.data.regs.get64 .rbx).toNat = bits; rw [hsv6.1 .rbx rfl]; exact hX3₅
  -- `b4`: the test, the epilogue.
  have hwf6 := frame_wf (m0 := m0) (d := st6.data) (F := 48) (rest := []) (vars := fun _ ↦ 0)
    (ret := 0) ⟨Mapped.keeps (frame_mapped hst (by decide)) hf6.kept, hfnw⟩ (by simp)
    (List.pairwise_singleton _ _)
  refine exec_at (infix_of b4_in_code (by simp [b4]) hp) exit_b4 hwf6 nofun
    (hpc6.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.TStateGrind.b3_next))
    (match_ofMachine ⟨rfl, trivial⟩ ⟨hf6.rsp_eval, trivial⟩ trivial trivial trivial)
    fun st7 hm7 hpc7 => ?_
  obtain ⟨hepi, hmem7, hrax7⟩ := end_b4
  obtain ⟨hsv7, hrsp7⟩ := Frame.epilogue hf6 hwf6 hm7 hepi
  have hd7 : st7.data.dmem = st6.data.dmem := hm7.dmem_eq hwf6 hmem7
  have hrun : (grind bits).run s = if powOkW bits r.1 then some ((), { s1 with sponge := r.2 })
      else none := by
    rw [NativeVm.Equiv.grind_run hb0, hns2]; rfl
  simp only [PcOk] at hpc7
  refine .done _ ⟨by rw [hpc7]; exact hf6.load_ret hst (by decide), hrsp7, ?_, ?_, ?_, hsv7⟩
  · show (reg st7.data .rax).toNat % 256 = (okWord ((grind bits).run s).isSome).toNat
    have hiso : ((grind bits).run s).isSome = powOkW bits r.1 := by
      rw [hrun]; split <;> simp_all
    rw [hiso, show reg st7.data .rax = _ from hm7.regs .rax _ hrax7]
    exact okSym_eval (by rw [Env.ofMachine_regs]; exact hx0₆)
      (by rw [Env.ofMachine_regs]; exact hX3₆) hbits
  · intro u s' h
    rw [hrun] at h
    split at h
    · obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      rw [hd7]; exact hts6
    · cases h
  · intro q hq; rw [hd7]; exact hso6 q hq

end

end NativeRustcVmX64.Transcript.Grind
