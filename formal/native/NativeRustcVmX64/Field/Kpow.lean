module

public import NativeRustcVmX64.Field.Kpow.Exec
public import NativeRustcVmX64.Field.Call
public import NativeRustcVmX64.Field.W32
public import NativeRustcVmX64.Field.LinSound
public import NativeRustcVm.Field.Pow
public import NativeRustcVmX64.Code.Vm.Kmul.Names
public import NativeRustcVmX64.Code.Vm.Kpow.Names

/-!
# `kpow` on x86-64

`kpow_spec`: rustc's `kpow(n)` (its base, `2`, constant-folded by rustc), placed anywhere in the
program, given `kmul`'s contract, returns `gpowK n`. The loop runs `Field.kpowLoop`
(`NativeRustcVm.Field.Rust`): at its head `NativeRustcVmX64.Vm.Kpow.label_4` (`Head`) R15, R14, RBX hold base, accumulator
and exponent with `kpowLoop base acc n` the result; at `NativeRustcVmX64.Vm.Kpow.label_6` (`Mid`) the accumulator has taken
the exponent's low bit. `Field.kpow_eq` makes the result the model's.
-/

namespace NativeRustcVmX64.Field.Kpow

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Field NativeRustcVmX64.Vm.Kpow
open NativeRustcVm.Field (kpowLoop)

@[expose] public section

/-- The pushed registers' slots. -/
def slots : List (Reg64 × Nat) := [(.rbx, 8), (.r14, 16), (.r15, 24)]

/-- The callee-saved registers it uses. -/
def used : List Reg64 := [.rbx, .r14, .r15]

/-- The result: `2^n` by the transcription. -/
def target (m0 : MachineData) : BitVec 64 := NativeRustcVm.Field.kpow 2#64 (reg m0 .rdi)

end

public section

theorem kpowLoop_ne {base acc n : BitVec 64} (h : n ≠ 0) :
    kpowLoop base acc n = kpowLoop (NativeRustcVm.Field.kmul base base)
      (if n &&& 1#64 = 1#64 then NativeRustcVm.Field.kmul acc base else acc) (n >>> 1) := by
  rw [kpowLoop, dite_eq_right_iff.mpr (fun h' ↦ absurd h' h)]

theorem kpowLoop_zero (base acc : BitVec 64) : kpowLoop base acc 0 = acc := by
  rw [kpowLoop, dite_eq_left_iff.mpr (fun h' ↦ absurd rfl h')]

theorem kmul_bv {x y z : BitVec 64}
    (h : z = (NativeVm.Model.kmul (.ofBitVec x) (.ofBitVec y)).toBitVec) :
    z = NativeRustcVm.Field.kmul x y := by
  rw [h, ← NativeRustcVm.Field.kmul_toBitVec]

theorem bit8_zero (x : BitVec 64) :
    CmpOp.apply .eq .W8 (BinOp.apply .and .W8 x (BitVec.ofNat 64 1)) (BitVec.ofNat 64 0) =
      decide (x.toNat % 2 = 0) := by
  simp only [CmpOp.apply, BinOp.apply, low_ext, low_zero, low_one]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj, BitVec.toNat_and,
    toNat_low]
  simp only [BitVec.toNat_ofNat, show Width.W8.bits = 8 from rfl]
  rw [Nat.and_one_is_mod]
  omega

variable [Host] {k : Nat}

theorem hb (hp : Placed code k) {ds : List Directive} {j : Nat} (h : ds.IsInfixAt code j)
    (hne : ds ≠ []) : ds.IsInfixAt Host.prog (k + j) :=
  h.trans hp.1 hne

/-- **The loop's head** `NativeRustcVmX64.Vm.Kpow.label_4`, exponent `n` left. -/
structure Head (m0 m1 : MachineData) (k : Nat) (n : BitVec 64) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Kpow.b5Offset)
  fr : Fr m0 m1 32 kpowStack 8 used st.data
  rbx : reg st.data .rbx = n
  nz : n ≠ 0
  eq : kpowLoop (reg st.data .r15) (reg st.data .r14) n = target m0

/-- **`NativeRustcVmX64.Vm.Kpow.label_6`**: the accumulator has taken the low bit of `n`. -/
structure Mid (m0 m1 : MachineData) (k : Nat) (n : BitVec 64) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Kpow.b3Offset)
  fr : Fr m0 m1 32 kpowStack 8 used st.data
  rbx : reg st.data .rbx = n
  nz : n ≠ 0
  eq : kpowLoop (NativeRustcVm.Field.kmul (reg st.data .r15) (reg st.data .r15))
    (reg st.data .r14) (n >>> 1) = target m0

/-- `kpow`'s postcondition, reached. -/
abbrev Post (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧ KpowPost m0 st.data

omit [Host] in
theorem geo {m0 : MachineData} (hpre : KpowPre m0) : Geo m0 32 kpowStack :=
  ⟨hpre, by decide, by decide⟩

/-- **From the head to `NativeRustcVmX64.Vm.Kpow.label_6`.** -/
theorem head_step (hp : Placed code k) (hkmul : Spec (Labels.label NativeRustcVmX64.Vm.Kmul.entryLabel) KmulPre KmulPost)
    {m0 m1 : MachineData} (hpre : KpowPre m0) {n : BitVec 64} {st : MachineState}
    (hH : Head m0 m1 k n st) : Eventually (step1 Host.exe) (Mid m0 m1 k n) st := by
  have g := geo hpre
  obtain ⟨d, pc⟩ := st
  obtain ⟨hpc, hF, hbx, hnz, heq⟩ := hH
  simp only at hpc hF hbx heq
  subst hpc
  rw [kpowLoop_ne hnz] at heq
  refine block g hF (vars := fun _ ↦ 0) (hb hp b5_in_code (List.cons_ne_nil _ _)) run_b5 (o := 8)
    rfl (by decide) (by decide +kernel) fun st5 hm5 hpc5 hF5 ↦ ?_
  have k5bx : reg st5.data .rbx = reg d .rbx := hm5.regs .rbx _ rfl
  have k514 : reg st5.data .r14 = reg d .r14 := hm5.regs .r14 _ rfl
  have k515 : reg st5.data .r15 = reg d .r15 := hm5.regs .r15 _ rfl
  simp only [PcOk] at hpc5
  have hc : (SBool.cmp .eq .W8 (.bin .and .W8 (.reg .rbx) (.lit 1)) (.lit 0)).eval
      (frameEnv m0 d 32 (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.Kpow.b5Offset + b5.length)).toBitVec) =
      decide (n.toNat % 2 = 0) := by
    simp only [SBool.eval, Sym.eval, Env.ofMachine_regs, bit8_zero]
    rw [show d.regs.get64 .rbx = n from hbx]
  rw [hc] at hpc5
  by_cases hbit : n.toNat % 2 = 0
  · simp only [hbit, decide_true, ite_true] at hpc5
    rw [ite_eq_right (fun h ↦ by
      have := (NativeRustcVm.Field.and_one_eq_one_iff n).mp h; omega)] at heq
    refine .done _ ⟨hpc5.trans (hp.label NativeRustcVmX64.Vm.Kpow.label_6_at), hF5, k5bx.trans hbx, hnz, ?_⟩
    rw [k514, k515]
    exact heq
  · simp only [hbit, decide_false, Bool.false_eq_true, ite_false] at hpc5
    rw [ite_eq_left ((NativeRustcVm.Field.and_one_eq_one_iff n).mpr (by omega))] at heq
    obtain ⟨d5, pc5⟩ := st5
    simp only [show k + NativeRustcVmX64.Vm.Kpow.b5Offset + b5.length = k + NativeRustcVmX64.Vm.Kpow.b6Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.Kpow.b5_next]] at hpc5
    subst hpc5
    simp only at hF5 k5bx k514 k515
    refine block g hF5 (vars := fun _ ↦ 0) (hb hp b6_in_code (List.cons_ne_nil _ _)) run_b6
      (o := 0) rfl (by decide) (by decide +kernel) fun st6 hm6 hpc6 hF6 ↦ ?_
    have h6di : reg st6.data .rdi = reg d5 .r14 := hm6.regs .rdi _ rfl
    have h6si : reg st6.data .rsi = reg d5 .r15 := hm6.regs .rsi _ rfl
    have h6bx : reg st6.data .rbx = reg d5 .rbx := hm6.regs .rbx _ rfl
    have h615 : reg st6.data .r15 = reg d5 .r15 := hm6.regs .r15 _ rfl
    refine call g hF6 hpc6 (S := kmulStack) (by decide) hkmul id (fun _ _ h ↦ h.2)
      fun st' hpc' hq hF' ↦ ?_
    have hacc := kmul_bv hq.1
    have h'bx : reg st'.data .rbx = reg d5 .rbx := (hq.2.2.1 .rbx rfl).trans h6bx
    have h'15 : reg st'.data .r15 = reg d5 .r15 := (hq.2.2.1 .r15 rfl).trans h615
    obtain ⟨d', pc'⟩ := st'
    simp only [show k + NativeRustcVmX64.Vm.Kpow.b6Offset + b6.length = k + NativeRustcVmX64.Vm.Kpow.b7Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.Kpow.b6_next]] at hpc'
    subst hpc'
    simp only at hF' hacc h'bx h'15
    refine block g hF' (vars := fun _ ↦ 0) (hb hp b7_in_code (List.cons_ne_nil _ _)) run_b7
      (o := 8) rfl (by decide) (by decide +kernel) fun st7 hm7 hpc7 hF7 ↦ .done _ ?_
    have h714 : reg st7.data .r14 = reg d' .rax := hm7.regs .r14 _ rfl
    have h7bx : reg st7.data .rbx = reg d' .rbx := hm7.regs .rbx _ rfl
    have h715 : reg st7.data .r15 = reg d' .r15 := hm7.regs .r15 _ rfl
    simp only [PcOk] at hpc7
    refine ⟨hpc7.trans (hp.label NativeRustcVmX64.Vm.Kpow.label_6_at), hF7, ?_, hnz, ?_⟩
    · rw [h7bx, h'bx, k5bx, hbx]
    · rw [h715, h714, hacc, h'15, h6di, h6si, k514, k515]
      exact heq

/-- **From `NativeRustcVmX64.Vm.Kpow.label_6`**: the base squared, then back to the head with `n >>> 1` or returned. -/
theorem mid_step (hp : Placed code k) (hkmul : Spec (Labels.label NativeRustcVmX64.Vm.Kmul.entryLabel) KmulPre KmulPost)
    {m0 m1 : MachineData} (hpre : KpowPre m0) (hsl : Slots m0 m1 32 slots) {n : BitVec 64}
    {st : MachineState} (hM : Mid m0 m1 k n st) :
    Eventually (step1 Host.exe) (fun st' ↦ Post m0 st' ∨ Head m0 m1 k (n >>> 1) st') st := by
  have g := geo hpre
  obtain ⟨d, pc⟩ := st
  obtain ⟨hpc, hF, hbx, hnz, heq⟩ := hM
  simp only at hpc hF hbx heq
  subst hpc
  refine block g hF (vars := fun _ ↦ 0) (hb hp b3_in_code (List.cons_ne_nil _ _)) run_b3 (o := 0)
    rfl (by decide) (by decide +kernel) fun st3 hm3 hpc3 hF3 ↦ ?_
  have h3di : reg st3.data .rdi = reg d .r15 := hm3.regs .rdi _ rfl
  have h3si : reg st3.data .rsi = reg d .r15 := hm3.regs .rsi _ rfl
  have h3bx : reg st3.data .rbx = reg d .rbx := hm3.regs .rbx _ rfl
  have h314 : reg st3.data .r14 = reg d .r14 := hm3.regs .r14 _ rfl
  refine call g hF3 hpc3 (S := kmulStack) (by decide) hkmul id (fun _ _ h ↦ h.2)
    fun st' hpc' hq hF' ↦ ?_
  have hbase := kmul_bv hq.1
  have h'bx : reg st'.data .rbx = reg d .rbx := (hq.2.2.1 .rbx rfl).trans h3bx
  have h'14 : reg st'.data .r14 = reg d .r14 := (hq.2.2.1 .r14 rfl).trans h314
  obtain ⟨d', pc'⟩ := st'
  simp only [show k + NativeRustcVmX64.Vm.Kpow.b3Offset + b3.length = k + NativeRustcVmX64.Vm.Kpow.b4Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.Kpow.b3_next]] at hpc'
  subst hpc'
  simp only at hF' hbase h'bx h'14
  refine block g hF' (vars := fun _ ↦ 0) (hb hp b4_in_code (List.cons_ne_nil _ _)) run_b4 (o := 8)
    rfl (by decide) (by decide +kernel) fun st4 hm4 hpc4 hF4 ↦ ?_
  have h4bx : reg st4.data .rbx = n >>> 1 := by
    rw [show reg st4.data .rbx = _ from hm4.regs .rbx _ rfl]
    show BinOp.apply .shr .W64 (reg d' .rbx) (BitVec.ofNat 64 1) = _
    rw [Lin.shr_apply _ (by decide), h'bx, hbx]
  have h414 : reg st4.data .r14 = reg d .r14 := (hm4.regs .r14 _ rfl).trans h'14
  have h415 : reg st4.data .r15 =
      NativeRustcVm.Field.kmul (reg d .r15) (reg d .r15) := by
    rw [show reg st4.data .r15 = reg d' .rax from hm4.regs .r15 _ rfl, hbase, h3di, h3si]
  simp only [PcOk] at hpc4
  have hc : (SBool.cmp .eq .W64 (.bin .shr .W64 (.reg .rbx) (.lit 1)) (.lit 0)).eval
      (frameEnv m0 d' 32 (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.Kpow.b4Offset + b4.length)).toBitVec) =
      decide ((n >>> 1).toNat = 0) := by
    simp only [SBool.eval, Sym.eval, Env.ofMachine_regs, Lin.shr_apply _ (show 1 < 64 by decide),
      eq64_zero]
    rw [show d'.regs.get64 .rbx = n from h'bx.trans hbx]
  rw [hc] at hpc4
  by_cases hz : (n >>> 1).toNat = 0
  · simp only [hz, decide_true, ite_true] at hpc4
    have hz' : n >>> 1 = 0 := BitVec.eq_of_toNat_eq (by rw [hz]; rfl)
    obtain ⟨d4, pc4⟩ := st4
    simp only at hpc4
    rw [hp.label NativeRustcVmX64.Vm.Kpow.label_2_at] at hpc4
    subst hpc4
    simp only at hF4 h414
    refine Eventually.mono (epilogue_ret g hF4 hsl (vars := fun _ ↦ 0)
      (hb hp b9_in_code (List.cons_ne_nil _ _)) run_b9 (by decide +kernel) rfl rfl)
      fun st ⟨hm, hret, hrsp, hso, hsv⟩ ↦ Or.inl ⟨hret, hrsp, ?_, hso, hsv⟩
    have hx0 : reg st.data .rax = reg d4 .r14 := hm.regs .rax _ rfl
    have ht := NativeRustcVm.Field.kpow_eq 2#64 (reg m0 .rdi)
    rw [← target, ← heq, hz', kpowLoop_zero, ← h414, ← hx0] at ht
    exact ht
  · simp only [hz, decide_false, Bool.false_eq_true, ite_false] at hpc4
    refine .done _ (Or.inr ⟨hpc4, hF4, h4bx, fun h ↦ hz (by rw [h]; rfl), ?_⟩)
    rw [h415, h414]
    exact heq

omit [Host] in
theorem shr_lt {n : BitVec 64} (h : n ≠ 0) : (n >>> 1).toNat < n.toNat := by
  have : n.toNat ≠ 0 := fun h0 ↦ h (BitVec.eq_of_toNat_eq (by rw [h0]; rfl))
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega

/-- **`kpow` computes `2^n`.** -/
theorem kpow_spec (hp : Placed code k) (hkmul : Spec (Labels.label NativeRustcVmX64.Vm.Kmul.entryLabel) KmulPre KmulPost) :
    Spec (Labels.label NativeRustcVmX64.Vm.Kpow.entryLabel) KpowPre KpowPost := by
  intro m0 hpre
  have g := geo hpre
  rw [show Labels.label NativeRustcVmX64.Vm.Kpow.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.Kpow.b0Offset) from hp.label NativeRustcVmX64.Vm.Kpow.entry_at]
  refine prologue (used := used) (slots := slots) (vars := fun _ ↦ 0) g
    (hb hp b0_in_code (List.cons_ne_nil _ _)) run_b0 (o := 8) rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel) fun st1 hm1 hpc1 hF1 hsl ↦ ?_
  have h1di : reg st1.data .rdi = reg m0 .rdi := hm1.regs .rdi _ rfl
  simp only [PcOk] at hpc1
  have hc : (SBool.cmp .eq .W64 (.bin .and .W64 (.reg .rdi) (.reg .rdi)) (.lit 0)).eval
      (frameEnv m0 m0 32 (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.Kpow.b0Offset + b0.length)).toBitVec) =
      decide ((reg m0 .rdi).toNat = 0) := by
    simp only [SBool.eval, Sym.eval, Env.ofMachine_regs, and_self_apply, eq64_zero]
  rw [hc] at hpc1
  by_cases hz : (reg m0 .rdi).toNat = 0
  · simp only [hz, decide_true, ite_true] at hpc1
    obtain ⟨d1, pc1⟩ := st1
    simp only at hpc1
    rw [hp.label NativeRustcVmX64.Vm.Kpow.label_1_at] at hpc1
    subst hpc1
    simp only at hF1 hsl
    refine block g hF1 (vars := fun _ ↦ 0) (hb hp b8_in_code (List.cons_ne_nil _ _)) run_b8
      (o := 8) rfl (by decide) (by decide +kernel) fun st8 hm8 hpc8 hF8 ↦ ?_
    have h814 : reg st8.data .r14 = 1#64 := hm8.regs .r14 (.lit 1) rfl
    obtain ⟨d8, pc8⟩ := st8
    simp only [PcOk, show k + NativeRustcVmX64.Vm.Kpow.b8Offset + b8.length = k + NativeRustcVmX64.Vm.Kpow.b9Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.Kpow.b8_next]] at hpc8
    subst hpc8
    simp only at hF8 h814
    refine Eventually.mono (epilogue_ret g hF8 hsl (vars := fun _ ↦ 0)
      (hb hp b9_in_code (List.cons_ne_nil _ _)) run_b9 (by decide +kernel) rfl rfl)
      fun st ⟨hm, hret, hrsp, hso, hsv⟩ ↦ ⟨hret, hrsp, ?_, hso, hsv⟩
    rw [show reg st.data .rax = reg d8 .r14 from hm.regs .rax _ rfl, h814, hz]
    rfl
  · simp only [hz, decide_false, Bool.false_eq_true, ite_false] at hpc1
    obtain ⟨d1, pc1⟩ := st1
    simp only [show k + NativeRustcVmX64.Vm.Kpow.b0Offset + b0.length = k + NativeRustcVmX64.Vm.Kpow.b1Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.Kpow.b0_next]] at hpc1
    subst hpc1
    simp only at hF1 hsl h1di
    refine block g hF1 (vars := fun _ ↦ 0) (hb hp b1_in_code (List.cons_ne_nil _ _)) run_b1
      (o := 8) rfl (by decide) (by decide +kernel) fun st2 hm2 hpc2 hF2 ↦ ?_
    simp only [PcOk] at hpc2
    have hH : Head m0 d1 k (reg m0 .rdi) st2 := by
      refine ⟨hpc2.trans (hp.label NativeRustcVmX64.Vm.Kpow.label_4_at), hF2, ?_, fun h ↦ hz (by rw [h]; rfl), ?_⟩
      · rw [show reg st2.data .rbx = reg d1 .rdi from hm2.regs .rbx _ rfl, h1di]
      · rw [show reg st2.data .r15 = _ from hm2.regs .r15 (.lit 2) rfl,
          show reg st2.data .r14 = _ from hm2.regs .r14 (.lit 1) rfl]
        rfl
    exact Sym.loop (fun μ st ↦ ∃ n, μ = n.toNat ∧ Head m0 d1 k n st)
      (fun _ _ ⟨n, hμ, hH⟩ ↦ Eventually.bind (head_step hp hkmul hpre hH) fun _ hM ↦
        Eventually.mono (mid_step hp hkmul hpre hsl hM) fun _ h ↦
          h.imp_right fun h' ↦ ⟨(n >>> 1).toNat, hμ ▸ shr_lt hH.nz, n >>> 1, rfl, h'⟩)
      ⟨_, rfl, hH⟩

end

end NativeRustcVmX64.Field.Kpow
