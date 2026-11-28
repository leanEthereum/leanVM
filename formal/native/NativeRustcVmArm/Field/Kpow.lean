module

public import NativeRustcVmArm.Code.Vm.Kmul.Names
public import NativeRustcVmArm.Code.Vm.Kpow.Names
public import NativeRustcVmArm.Field.Kpow.Exec
public import NativeRustcVmArm.Field.Prologue
public import NativeRustcVmArm.Field.W32
public import NativeRustcVm.Field.Pow

/-!
# `kpow` on AArch64

`kpow_spec`: rustc's `kpow(n)` (its base, `2`, constant-folded by rustc), placed anywhere in the
program, given `kmul`'s contract, returns `gpowK n`. The loop runs `Field.kpowLoop`
(`NativeRustcVm.Field.Rust`): at its head `.LKpow_3` (`Head`) X21, X20, X19 hold base, accumulator
and exponent with `kpowLoop base acc n` the result; at `.LKpow_2` (`Mid`) the accumulator has taken
the exponent's low bit. `Field.kpow_eq` makes the result the model's.
-/

namespace NativeRustcVmArm.Field.Kpow

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Field NativeRustcVmArm.Vm.Kpow
open NativeRustcVm.Field (kpowLoop)

@[expose] public section

/-- The saved registers' slots. -/
def slots : List (XReg × Nat) := [(.X30, 0), (.X21, 8), (.X20, 16), (.X19, 24)]

/-- The callee-saved registers it uses. -/
def used : List XReg := [.X19, .X20, .X21]

/-- The result: `2^n` by the transcription. -/
def target (m0 : MachineData) : BitVec 64 := NativeRustcVm.Field.kpow 2#64 m0.regs.X0.toBitVec

end

public section

theorem kpowLoop_ne {base acc n : BitVec 64} (h : n ≠ 0) :
    kpowLoop base acc n = kpowLoop (NativeRustcVm.Field.kmul base base)
      (if n &&& 1#64 = 1#64 then NativeRustcVm.Field.kmul acc base else acc) (n >>> 1) := by
  rw [kpowLoop, dite_eq_right_iff.mpr (fun h' ↦ absurd h' h)]

theorem kpowLoop_zero (base acc : BitVec 64) : kpowLoop base acc 0 = acc := by
  rw [kpowLoop, dite_eq_left_iff.mpr (fun h' ↦ absurd rfl h')]

theorem kmul_bv {a b c : UInt64} (h : c = NativeVm.Model.kmul a b) :
    c.toBitVec = NativeRustcVm.Field.kmul a.toBitVec b.toBitVec := by
  rw [h, NativeRustcVm.Field.kmul_toBitVec]

variable [Host] {k : Nat}

theorem hb0 (hp : Placed code k) : b0.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Kpow.b0Offset) :=
  b0_in_code.trans hp.1 (by rw [b0]; exact List.cons_ne_nil _ _)
theorem hb1 (hp : Placed code k) : b1.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Kpow.b1Offset) :=
  b1_in_code.trans hp.1 (by rw [b1]; exact List.cons_ne_nil _ _)
theorem hb2 (hp : Placed code k) : b2.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Kpow.b2Offset) :=
  b2_in_code.trans hp.1 (by rw [b2]; exact List.cons_ne_nil _ _)
theorem hb3 (hp : Placed code k) : b3.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Kpow.b3Offset) :=
  b3_in_code.trans hp.1 (by rw [b3]; exact List.cons_ne_nil _ _)
theorem hb4 (hp : Placed code k) : b4.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Kpow.b4Offset) :=
  b4_in_code.trans hp.1 (by rw [b4]; exact List.cons_ne_nil _ _)
theorem hb5 (hp : Placed code k) : b5.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Kpow.b5Offset) :=
  b5_in_code.trans hp.1 (by rw [b5]; exact List.cons_ne_nil _ _)
theorem hb6 (hp : Placed code k) : b6.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Kpow.b6Offset) :=
  b6_in_code.trans hp.1 (by rw [b6]; exact List.cons_ne_nil _ _)
theorem hb7 (hp : Placed code k) : b7.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Kpow.b7Offset) :=
  b7_in_code.trans hp.1 (by rw [b7]; exact List.cons_ne_nil _ _)
theorem hb8 (hp : Placed code k) : b8.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Kpow.b8Offset) :=
  b8_in_code.trans hp.1 (by rw [b8]; exact List.cons_ne_nil _ _)

/-- **The loop's head** `.LKpow_3`, exponent `n` left. -/
structure Head (m0 m1 : MachineData) (k : Nat) (n : BitVec 64) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.Kpow.b4Offset)
  fr : Fr m0 m1 32 kpowStack used st.data
  x19 : st.data.regs.X19.toBitVec = n
  nz : n ≠ 0
  eq : kpowLoop st.data.regs.X21.toBitVec st.data.regs.X20.toBitVec n = target m0

/-- **`.LKpow_2`**: the accumulator has taken the low bit of `n`. -/
structure Mid (m0 m1 : MachineData) (k : Nat) (n : BitVec 64) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.Kpow.b2Offset)
  fr : Fr m0 m1 32 kpowStack used st.data
  x19 : st.data.regs.X19.toBitVec = n
  nz : n ≠ 0
  eq : kpowLoop (NativeRustcVm.Field.kmul st.data.regs.X21.toBitVec st.data.regs.X21.toBitVec)
    st.data.regs.X20.toBitVec (n >>> 1) = target m0

/-- `kpow`'s postcondition, reached. -/
abbrev Post (m0 : MachineData) (st : MachineState) : Prop := st.pc = retOf m0 ∧ KpowPost m0 st.data

omit [Host] in
theorem geo {m0 : MachineData} (hpre : KpowPre m0) : Geo m0 32 kpowStack :=
  ⟨hpre, rfl, by decide⟩

omit [Host] in
/-- A register a block from `regS` sets to a register's value. -/
theorem keep [Labels] {d : MachineData} {S : SState} {st : MachineData}
    (hm : Match (Env.ofMachine d []) S st) {r r' : XReg} (h : S.reg r = some (.reg r')) :
    st.regs.getXReg r = d.regs.getXReg r' :=
  UInt64.toBitVec_inj.mp (hm.regs r _ h)

/-- **From the head to `.LKpow_2`.** -/
theorem head_step (hp : Placed code k) (hkmul : Spec (Labels.label NativeRustcVmArm.Vm.Kmul.entryLabel) KmulPre KmulPost)
    {m0 m1 : MachineData} (hpre : KpowPre m0) {n : BitVec 64} {st : MachineState}
    (hH : Head m0 m1 k n st) : Eventually (step1 Host.exe) (Mid m0 m1 k n) st := by
  have g := geo hpre
  obtain ⟨d, pc⟩ := st
  obtain ⟨hpc, hF, hx19, hnz, heq⟩ := hH
  simp only at hpc hF hx19 heq
  subst hpc
  rw [kpowLoop_ne hnz] at heq
  refine block hF (hb4 hp) run_b4 rfl rfl (by decide +kernel) fun st4 hm4 hpc4 hF4 ↦ ?_
  have k19 : st4.data.regs.X19 = d.regs.X19 := keep hm4 (r := .X19) rfl
  have k20 : st4.data.regs.X20 = d.regs.X20 := keep hm4 (r := .X20) rfl
  have k21 : st4.data.regs.X21 = d.regs.X21 := keep hm4 (r := .X21) rfl
  simp only [PcOk] at hpc4
  have hc : (SBool.not (.bit .W32 (.reg .X19) 0)).eval (Env.ofMachine d []) =
      !decide (n.toNat % 2 = 1) := by
    simp only [SBool.eval, Sym.eval, Env.ofMachine_regs, bit32_zero]
    show (!decide (d.regs.X19.toBitVec.toNat % 2 = 1)) = _
    rw [hx19]
  rw [hc] at hpc4
  by_cases hbit : n.toNat % 2 = 1
  · simp only [hbit, decide_true, Bool.not_true, Bool.false_eq_true, ite_false] at hpc4
    rw [ite_eq_left ((NativeRustcVm.Field.and_one_eq_one_iff n).mpr hbit)] at heq
    obtain ⟨d4, pc4⟩ := st4
    simp only [show k + NativeRustcVmArm.Vm.Kpow.b4Offset + b4.length = k + NativeRustcVmArm.Vm.Kpow.b5Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.Kpow.b4_next]] at hpc4
    subst hpc4
    simp only at hF4 k19 k20 k21
    refine block hF4 (hb5 hp) run_b5 rfl rfl (by decide +kernel) fun st5 hm5 hpc5 hF5 ↦ ?_
    have h50 : st5.data.regs.X0 = d4.regs.X20 := keep hm5 (r := .X0) (r' := .X20) rfl
    have h51 : st5.data.regs.X1 = d4.regs.X21 := keep hm5 (r := .X1) (r' := .X21) rfl
    have h519 : st5.data.regs.X19 = d4.regs.X19 := keep hm5 (r := .X19) rfl
    have h521 : st5.data.regs.X21 = d4.regs.X21 := keep hm5 (r := .X21) rfl
    refine call g hF5 hpc5 (S := kmulStack) (by decide) hkmul id (fun _ _ h ↦ h.2)
      fun st' hpc' hq hF' ↦ ?_
    have hacc := kmul_bv hq.1
    have h'19 : st'.data.regs.X19 = d4.regs.X19 := (hq.2.2.1 .X19 rfl).trans h519
    have h'21 : st'.data.regs.X21 = d4.regs.X21 := (hq.2.2.1 .X21 rfl).trans h521
    obtain ⟨d', pc'⟩ := st'
    simp only [show k + NativeRustcVmArm.Vm.Kpow.b5Offset + b5.length = k + NativeRustcVmArm.Vm.Kpow.b6Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.Kpow.b5_next]] at hpc'
    subst hpc'
    simp only at hF' hacc h'19 h'21
    refine block hF' (hb6 hp) run_b6 rfl rfl (by decide +kernel) fun st6 hm6 hpc6 hF6 ↦ .done _ ?_
    have h620 : st6.data.regs.X20 = d'.regs.X0 := keep hm6 (r := .X20) (r' := .X0) rfl
    have h619 : st6.data.regs.X19 = d'.regs.X19 := keep hm6 (r := .X19) rfl
    have h621 : st6.data.regs.X21 = d'.regs.X21 := keep hm6 (r := .X21) rfl
    simp only [PcOk] at hpc6
    refine ⟨hpc6.trans (hp.label (j := NativeRustcVmArm.Vm.Kpow.b2Offset) NativeRustcVmArm.Vm.Kpow.label_2_at), hF6, ?_, hnz, ?_⟩
    · rw [h619, h'19, k19, hx19]
    · rw [h621, h620, hacc, h'21, h50, h51, k20, k21]
      exact heq
  · simp only [hbit, decide_false, Bool.not_false, ite_true] at hpc4
    rw [ite_eq_right (fun h ↦ hbit ((NativeRustcVm.Field.and_one_eq_one_iff n).mp h))] at heq
    refine .done _ ⟨hpc4.trans (hp.label (j := NativeRustcVmArm.Vm.Kpow.b2Offset) NativeRustcVmArm.Vm.Kpow.label_2_at), hF4, by rw [k19, hx19], hnz, ?_⟩
    rw [k20, k21]
    exact heq

/-- **From `.LKpow_2`**: the base squared, then back to the head with `n >>> 1` or returned. -/
theorem mid_step (hp : Placed code k) (hkmul : Spec (Labels.label NativeRustcVmArm.Vm.Kmul.entryLabel) KmulPre KmulPost)
    {m0 m1 : MachineData} (hpre : KpowPre m0) (hsl : Slots m0 m1 32 slots) {n : BitVec 64}
    {st : MachineState} (hM : Mid m0 m1 k n st) :
    Eventually (step1 Host.exe) (fun st' ↦ Post m0 st' ∨ Head m0 m1 k (n >>> 1) st') st := by
  have g := geo hpre
  obtain ⟨d, pc⟩ := st
  obtain ⟨hpc, hF, hx19, hnz, heq⟩ := hM
  simp only at hpc hF hx19 heq
  subst hpc
  refine block hF (hb2 hp) run_b2 rfl rfl (by decide +kernel) fun st2 hm2 hpc2 hF2 ↦ ?_
  have h20 : st2.data.regs.X0 = d.regs.X21 := keep hm2 (r := .X0) (r' := .X21) rfl
  have h21 : st2.data.regs.X1 = d.regs.X21 := keep hm2 (r := .X1) (r' := .X21) rfl
  have h219 : st2.data.regs.X19 = d.regs.X19 := keep hm2 (r := .X19) rfl
  have h220 : st2.data.regs.X20 = d.regs.X20 := keep hm2 (r := .X20) rfl
  refine call g hF2 hpc2 (S := kmulStack) (by decide) hkmul id (fun _ _ h ↦ h.2)
    fun st' hpc' hq hF' ↦ ?_
  have hbase := kmul_bv hq.1
  have h'19 : st'.data.regs.X19 = d.regs.X19 := (hq.2.2.1 .X19 rfl).trans h219
  have h'20 : st'.data.regs.X20 = d.regs.X20 := (hq.2.2.1 .X20 rfl).trans h220
  obtain ⟨d', pc'⟩ := st'
  simp only [show k + NativeRustcVmArm.Vm.Kpow.b2Offset + b2.length = k + NativeRustcVmArm.Vm.Kpow.b3Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.Kpow.b2_next]] at hpc'
  subst hpc'
  simp only at hF' hbase h'19 h'20
  refine block hF' (hb3 hp) run_b3 rfl rfl (by decide +kernel) fun st3 hm3 hpc3 hF3 ↦ ?_
  have h319 : st3.data.regs.X19.toBitVec = n >>> 1 := by
    show (st3.data.regs.getXReg .X19).toBitVec = _
    rw [hm3.regs .X19 _ rfl]
    show UnOp.apply (.ubfm 1 63) .W64 (d'.regs.X19.toBitVec) = _
    rw [ubfm_lsr _ _ (by decide), h'19, hx19]
  have h320 : st3.data.regs.X20 = d.regs.X20 := (keep hm3 (r := .X20) rfl).trans h'20
  have h321 : st3.data.regs.X21.toBitVec =
      NativeRustcVm.Field.kmul d.regs.X21.toBitVec d.regs.X21.toBitVec := by
    rw [show st3.data.regs.X21 = d'.regs.X0 from keep hm3 (r := .X21) (r' := .X0) rfl, hbase,
      h20, h21]
  simp only [PcOk] at hpc3
  have hc : (SBool.cmp .eq .W64 (.un (.ubfm 1 63) .W64 (.reg .X19)) (.lit 0)).eval
      (Env.ofMachine d' []) = decide ((n >>> 1).toNat = 0) := by
    simp only [SBool.eval, Sym.eval, Env.ofMachine_regs, ubfm_lsr _ _ (show 1 < 64 by decide),
      eq64_lit _ 0 (by decide)]
    show decide ((d'.regs.X19.toBitVec >>> 1).toNat = 0) = _
    rw [h'19, hx19]
  rw [hc] at hpc3
  by_cases hz : (n >>> 1).toNat = 0
  · simp only [hz, decide_true, ite_true] at hpc3
    have hz' : n >>> 1 = 0 := BitVec.eq_of_toNat_eq (by rw [hz]; rfl)
    obtain ⟨d3, pc3⟩ := st3
    simp only at hpc3
    rw [hp.label (j := NativeRustcVmArm.Vm.Kpow.b8Offset) NativeRustcVmArm.Vm.Kpow.label_6_at] at hpc3
    subst hpc3
    simp only at hF3 h320
    refine Eventually.mono (epilogue g hF3 hsl (hb8 hp) run_b8 (by decide +kernel) rfl rfl)
      fun st ⟨hret, hso, hsv, hm⟩ ↦ Or.inl ⟨hret, ?_, hso, hsv⟩
    have hx0 : st.data.regs.X0.toBitVec = d3.regs.X20.toBitVec := hm.regs .X0 (.reg .X20) rfl
    have ht := NativeRustcVm.Field.kpow_eq 2#64 m0.regs.X0.toBitVec
    rw [← target, ← heq, hz', kpowLoop_zero, ← h320, ← hx0] at ht
    exact UInt64.toBitVec_inj.mp ht
  · simp only [hz, decide_false, Bool.false_eq_true, ite_false] at hpc3
    refine .done _ (Or.inr ⟨hpc3, hF3, h319, fun h ↦ hz (by rw [h]; rfl), ?_⟩)
    rw [h321, h320]
    exact heq

omit [Host] in
theorem shr_lt {n : BitVec 64} (h : n ≠ 0) : (n >>> 1).toNat < n.toNat := by
  have : n.toNat ≠ 0 := fun h0 ↦ h (BitVec.eq_of_toNat_eq (by rw [h0]; rfl))
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega

/-- **`kpow` computes `2^n`.** -/
theorem kpow_spec (hp : Placed code k) (hkmul : Spec (Labels.label NativeRustcVmArm.Vm.Kmul.entryLabel) KmulPre KmulPost) :
    Spec (Labels.label NativeRustcVmArm.Vm.Kpow.entryLabel) KpowPre KpowPost := by
  intro m0 hpre
  have g := geo hpre
  rw [show Labels.label NativeRustcVmArm.Vm.Kpow.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.Kpow.b0Offset) from hp.label (j := NativeRustcVmArm.Vm.Kpow.entryOffset) NativeRustcVmArm.Vm.Kpow.entry_at]
  refine prologue (used := used) (slots := slots) g (hb0 hp) run_b0 rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel) fun st1 hm1 hpc1 hF1 hsl ↦ ?_
  have h10 : st1.data.regs.X0 = m0.regs.X0 := UInt64.toBitVec_inj.mp (hm1.regs .X0 _ rfl)
  simp only [PcOk] at hpc1
  have hc : (SBool.cmp .eq .W64 (.reg .X0) (.lit 0)).eval (frameEnv m0 m0 32) =
      decide (m0.regs.X0.toNat = 0) := by
    simp only [SBool.eval, Sym.eval, Env.ofMachine_regs, eq64_lit _ 0 (by decide)]
    rfl
  rw [hc] at hpc1
  by_cases hz : m0.regs.X0.toNat = 0
  · simp only [hz, decide_true, ite_true] at hpc1
    obtain ⟨d1, pc1⟩ := st1
    simp only at hpc1
    rw [hp.label (j := NativeRustcVmArm.Vm.Kpow.b7Offset) NativeRustcVmArm.Vm.Kpow.label_5_at] at hpc1
    subst hpc1
    simp only at hF1 hsl
    refine block hF1 (hb7 hp) run_b7 rfl rfl (by decide +kernel) fun st7 hm7 hpc7 hF7 ↦ ?_
    have h720 : st7.data.regs.X20.toBitVec = 1#64 := hm7.regs .X20 (.lit 1) rfl
    obtain ⟨d7, pc7⟩ := st7
    simp only [PcOk, show k + NativeRustcVmArm.Vm.Kpow.b7Offset + b7.length = k + NativeRustcVmArm.Vm.Kpow.b8Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.Kpow.b7_next]] at hpc7
    subst hpc7
    simp only at hF7 h720
    refine Eventually.mono (epilogue g hF7 hsl (hb8 hp) run_b8 (by decide +kernel) rfl rfl)
      fun st ⟨hret, hso, hsv, hm⟩ ↦ ⟨hret, ?_, hso, hsv⟩
    have hx0 : st.data.regs.X0.toBitVec = d7.regs.X20.toBitVec := hm.regs .X0 (.reg .X20) rfl
    rw [h720] at hx0
    apply UInt64.toBitVec_inj.mp
    rw [hx0, hz]
    rfl
  · simp only [hz, decide_false, Bool.false_eq_true, ite_false] at hpc1
    obtain ⟨d1, pc1⟩ := st1
    simp only [show k + NativeRustcVmArm.Vm.Kpow.b0Offset + b0.length = k + NativeRustcVmArm.Vm.Kpow.b1Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.Kpow.b0_next]] at hpc1
    subst hpc1
    simp only at hF1 hsl h10
    refine block hF1 (hb1 hp) run_b1 rfl rfl (by decide +kernel) fun st2 hm2 hpc2 hF2 ↦ ?_
    simp only [PcOk] at hpc2
    have hH : Head m0 d1 k m0.regs.X0.toBitVec st2 := by
      refine ⟨hpc2.trans (hp.label (j := NativeRustcVmArm.Vm.Kpow.b4Offset) NativeRustcVmArm.Vm.Kpow.label_3_at), hF2, ?_, fun h ↦ hz ?_, ?_⟩
      · rw [show st2.data.regs.X19 = d1.regs.X0 from keep hm2 (r := .X19) (r' := .X0) rfl, h10]
      · rw [← UInt64.toNat_toBitVec, h]; rfl
      · show kpowLoop (st2.data.regs.getXReg .X21).toBitVec
          (st2.data.regs.getXReg .X20).toBitVec _ = _
        rw [hm2.regs .X21 (.lit 2) rfl, hm2.regs .X20 (.lit 1) rfl]
        rfl
    exact Sym.loop (fun μ st ↦ ∃ n, μ = n.toNat ∧ Head m0 d1 k n st)
      (fun _ _ ⟨n, hμ, hH⟩ ↦ Eventually.bind (head_step hp hkmul hpre hH) fun _ hM ↦
        Eventually.mono (mid_step hp hkmul hpre hsl hM) fun _ h ↦
          h.imp_right fun h' ↦ ⟨(n >>> 1).toNat, hμ ▸ shr_lt hH.nz, n >>> 1, rfl, h'⟩)
      ⟨_, rfl, hH⟩

end

end NativeRustcVmArm.Field.Kpow
