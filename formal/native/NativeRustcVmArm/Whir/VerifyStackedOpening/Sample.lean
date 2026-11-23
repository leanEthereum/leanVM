module

public import NativeRustcVmArm.Code.Vm.SpongeWSqueeze.Names
public import NativeRustcVmArm.Code.Vm.VerifyStackedOpening.Names
public import NativeRustcVmArm.Whir.VerifyStackedOpening.Words

/-!
# `verify_stacked_opening`: the batching challenge

`count_run`: the counting loop to `b5`. `b5`, `b7` check the claims' count (`placed + 2`, at most
`162`: never too many); `b6` (or, with no claim, `b9`) saves the `TState`, squeezes the challenge
(`tsqueeze`); `b8` (or `b10`) saves the Keccak output and the rate: `.LVerifyStackedOpening_9`
(`AtB11`).
-/

namespace NativeRustcVmArm.Whir.VerifyStackedOpening

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir NativeRustcVmArm.Vm.VerifyStackedOpening

@[expose] public section

/-- **At `b11`**: the challenge squeezed, the count of the stack claims in X27. -/
structure AtB11 [Labels] (a : DecArea) (s : TState) (layout : LayoutW) (cs : Array ColumnClaimW)
    (m0 st : MachineData) : Prop where
  fr : VFr m0 st
  ts : TStateAt st.dmem (tA m0) a (sq s).2
  x0 : st.regs.getXReg .X0 = (sq s).1.c0
  x1 : st.regs.getXReg .X1 = (sq s).1.c1
  x27 : st.regs.getXReg .X27 = (placedOf layout cs cs.size + 2).toUInt64
  fw : FW st.dmem m0 [(16, m0.regs.X0), (24, m0.regs.X4), (48, m0.regs.X2)]
  x20 : st.regs.getXReg .X20 = m0.regs.X6
  x21 : st.regs.getXReg .X21 = m0.regs.X5
  x22 : st.regs.getXReg .X22 = m0.regs.X1
  x24 : st.regs.getXReg .X24 = m0.regs.X3
  x26 : st.regs.getXReg .X26 = m0.regs.X7
  x28 : (st.regs.getXReg .X28).toBitVec = m0.regs.X5.toBitVec + BitVec.ofNat 64 8
  x29 : st.regs.getXReg .X29 = cs.size.toUInt64

end

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {layout : LayoutW} {target : EW}
  {coefficients point slices : Array EW} {cs : Array ColumnClaimW} {z : Array EW} {value : EW}
  {m0 : MachineData}

/-- **The counting loop** to `b5`. -/
theorem count_run (hp : Placed code k)
    (h : Parts a s layout target coefficients point slices cs z value m0) {R : MachineState → Prop}
    (fin : ∀ st', AtB5 layout cs m0 st' →
      Eventually (step1 Host.exe) R ⟨st', Host.addrOf (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b5Offset)⟩) :
    ∀ n i st, cs.size - i = n → CntInv layout cs m0 i st →
      Eventually (step1 Host.exe) R ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b3Offset)⟩ := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro i st hn hc
    exact cnt_step hp h hc (fun st' hc' ↦
      ih (cs.size - (i + 1)) (by have := hc.hi; omega) (i + 1) st' rfl hc') fin

omit [Host] in
/-- The squeeze's change keeps the frame's words. -/
theorem sq_out {st : MachineData} {q : BitVec 64}
    (hq : InRange (tA m0) spongeBytes q ∨ InRange (stackBelow st squeezeStack) squeezeStack q)
    (hnt : NoWrap (tA m0) tstateBytes) :
    InRange (stackBelow st squeezeStack) squeezeStack q ∨ outs m0 q := by
  rcases hq with hq | hq
  · exact .inr (.inr (.inr (NativeRustcVm.InRange.mono hq (NativeRustcVm.NoWrap.mono hnt sponge_le')
      hnt (Nat.le_refl _) (Nat.add_le_add_left sponge_le' _))))
  · exact .inl hq

/-- **From `b5`**: the checks, the squeeze, the words. -/
theorem sample_b5 (hp : Placed code k)
    (h : Parts a s layout target coefficients point slices cs z value m0)
    (hsq : ∀ sp, Spec (Labels.label NativeRustcVmArm.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp))
    {R : MachineState → Prop}
    (cont : ∀ st, AtB11 a s layout cs m0 st →
      Eventually (step1 Host.exe) R ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b11Offset)⟩)
    {st : MachineData} (hb5 : AtB5 layout cs m0 st) :
    Eventually (step1 Host.exe) R ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b5Offset)⟩ := by
  have hb := hb5.base
  have c := h.ctx
  have hnt : NoWrap (tA m0) tstateBytes := h.ts.footprint.1.2
  have hP : placedOf layout cs cs.size ≤ 160 :=
    (placedOf_le_self _).trans h.cl.len_le
  -- `b5`
  have hk5 : b5.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b5Offset) := b5_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine hb.fr.regsBlock (st := ⟨st, _⟩) hk5 run_b5 rfl rfl rfl rfl fun st1 hf1 hd1 hm1 hpc1 ↦ ?_
  have hx8 : (Env.ofMachine st []).regs .X8 = (placedOf layout cs cs.size).toUInt64.toBitVec := by
    show (st.regs.getXReg .X8).toBitVec = _; rw [hb5.x8]
  have hsum : (placedOf layout cs cs.size).toUInt64.toBitVec + BitVec.ofNat 64 2 =
      (placedOf layout cs cs.size + 2).toUInt64.toBitVec := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, UInt64.toNat_toBitVec, BitVec.toNat_ofNat,
      natCast_toUInt64_toNat (show placedOf layout cs cs.size < 2 ^ 64 by omega),
      natCast_toUInt64_toNat (show placedOf layout cs cs.size + 2 < 2 ^ 64 by omega)]
    omega
  simp only [PcOk] at hpc1
  sym_simp at hpc1
  rw [hx8, hsum, toBitVec_ult_ofNat (by decide),
    natCast_toUInt64_toNat (show placedOf layout cs cs.size + 2 < 2 ^ 64 by omega)] at hpc1
  have hne : ((placedOf layout cs cs.size + 2).toUInt64.toBitVec == BitVec.ofNat 64 512) =
      false := by
    apply beq_eq_false_iff_ne.mpr
    intro he
    have := congrArg BitVec.toNat he
    rw [UInt64.toNat_toBitVec, natCast_toUInt64_toNat (by omega)] at this
    simp at this
    omega
  simp only [show decide (placedOf layout cs cs.size + 2 < 512) = true from
      decide_eq_true (by omega),
    hne, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hpc1
  have e1x27 : st1.data.regs.getXReg .X27 = (placedOf layout cs cs.size + 2).toUInt64 :=
    (rv hm1 (r := .X27) rfl).trans (by sym_simp; rw [hx8, hsum])
  have k1 : ∀ r ∈ baseRegs, st1.data.regs.getXReg r = st.regs.getXReg r := fun r hr ↦ by
    simp only [baseRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (rv hm1 rfl).trans rfl
  have hb1 : Base cs m0 st1.data := hb.keep hf1 hd1 k1
  -- `b6`: the `TState` saved, `squeeze`
  obtain ⟨hwf6, hm6⟩ := h.frame_env hf1
  have hk6 : b6.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b6Offset) := b6_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_at hk6 run_b6 hwf6 hpc1 hm6 fun st6 hm6' hpc6 ↦ ?_
  have hf6 : VFr m0 st6.data := Fr.ofBlockW hb1.fr hm6 hm6' hwf6 rfl rfl
    (fun _ h ↦ absurd h (by simp)) rfl (by rw [stack_eq]; decide) h.hN slots_le
    (writeOk_of (F := 512) (slots := slots) (wr := []) hm6' (by decide) (fun _ h ↦ by cases h))
  have hs6 : SameOutside st1.data.dmem st6.data.dmem (InRange (base m0 512) 512) :=
    NativeRustcVm.SameOutside.mono (hm6'.sameOutside hwf6) fun q hq ↦
      written_r0 hwf6 rfl (by decide) hq
  have hts6 : TStateAt st6.data.dmem (tA m0) a s :=
    h.ts_frame (h.ts_frame h.ts hb1.fr.kept hb1.fo) (hm6'.kept hwf6) hs6
  have k6 : ∀ r, (after b6 frameS).reg r = some (.reg r) →
      st6.data.regs.getXReg r = st1.data.regs.getXReg r := fun r hr ↦
    (rv hm6' (by rw [← after_eq run_b6]; exact hr)).trans rfl
  have hx0 : st6.data.regs.X0.toBitVec = tA m0 := by
    show (st6.data.regs.getXReg .X0).toBitVec = _
    rw [k6 .X0 rfl, hb1.x0]
  have hw16 : NativeRustcVm.WordAt st6.data.dmem (loc m0 16) m0.regs.X0 := by
    have := fw_write (m0 := m0) hm6' rfl (o := 16) (by decide) (v := .reg .X0) (by decide)
    rwa [show UInt64.ofBitVec ((Sym.reg XReg.X0).eval (Env.ofMachine st1.data [(base m0 512, 512)]))
      = m0.regs.X0 from hb1.x0] at this
  have e6x23 : st6.data.regs.getXReg .X23 = m0.regs.X4 := (rv hm6' (r := .X23) rfl).trans hb1.x4
  have e6x19 : st6.data.regs.getXReg .X19 = m0.regs.X2 := (rv hm6' (r := .X19) rfl).trans hb1.x2
  refine tsqueeze c hsq hf6 (by rw [stack_eq]; decide) (fun _ h ↦ by cases h) slots_le hpc6 hx0
    hts6 fun m2 hf2 hts2 ha0 ha1 hcs2 hs2 ↦ ?_
  have hfw2 : FW m2.dmem m0 [(16, m0.regs.X0)] :=
    fw_call h hf6 (by rw [stack_eq]; decide)
      (NativeRustcVm.SameOutside.mono hs2 fun q hq ↦ sq_out hq hnt) (by simp)
      (FW.cons hw16 (FW.nil _ _))
  -- `b7`: the count's cap
  have hk7 : b7.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b7Offset) := b7_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine hf2.regsBlock (st := ⟨m2, _⟩) hk7 run_b7 rfl rfl rfl rfl fun st7 hf7 hd7 hm7 hpc7 ↦ ?_
  have hc27 : m2.regs.getXReg .X27 = (placedOf layout cs cs.size + 2).toUInt64 :=
    (hcs2 .X27 rfl).trans ((k6 .X27 rfl).trans e1x27)
  simp only [PcOk] at hpc7
  sym_simp at hpc7
  have hx27 : (Env.ofMachine m2 []).regs .X27 =
      (placedOf layout cs cs.size + 2).toUInt64.toBitVec := by
    show (m2.regs.getXReg .X27).toBitVec = _; rw [hc27]
  rw [hx27, toBitVec_ult_ofNat (by decide),
    natCast_toUInt64_toNat (show placedOf layout cs cs.size + 2 < 2 ^ 64 by omega)] at hpc7
  have hc7 : (!decide (placedOf layout cs cs.size + 2 < 162) &&
      !((placedOf layout cs cs.size + 2).toUInt64.toBitVec == 162#64)) = false := by
    by_cases hl : placedOf layout cs cs.size + 2 < 162
    · simp [hl]
    · have h162 : placedOf layout cs cs.size + 2 = 162 := by omega
      rw [h162]
      rfl
  rw [hc7] at hpc7
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc7
  -- `b8`: the Keccak output and the rate saved
  obtain ⟨hwf8, hm8⟩ := h.frame_env hf7
  have hk8 : b8.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b8Offset) := b8_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_at hk8 run_b8 hwf8 hpc7 hm8 fun st8 hm8' hpc8 ↦ ?_
  simp only [PcOk] at hpc8
  rw [show Labels.label NativeRustcVmArm.Vm.VerifyStackedOpening.label_9 = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b11Offset) from hp.label (j := NativeRustcVmArm.Vm.VerifyStackedOpening.b11Offset) NativeRustcVmArm.Vm.VerifyStackedOpening.label_9_at]
    at hpc8
  obtain ⟨d8, pc8⟩ := st8
  simp only at hpc8
  subst hpc8
  have hf8 : VFr m0 d8 := Fr.ofBlockW hf7 hm8 hm8' hwf8 rfl rfl
    (fun _ h ↦ absurd h (by simp)) rfl (by rw [stack_eq]; decide) h.hN slots_le
    (writeOk_of (F := 512) (slots := slots) (wr := []) hm8' (by decide) (fun _ h ↦ by cases h))
  have hs8 : SameOutside st7.data.dmem d8.dmem (InRange (base m0 512) 512) :=
    NativeRustcVm.SameOutside.mono (hm8'.sameOutside hwf8) fun q hq ↦
      written_r0 hwf8 rfl (by decide) hq
  have k8 : ∀ r, d8.regs.getXReg r = st7.data.regs.getXReg r := fun r ↦
    (rv hm8' (v := .reg r) (by cases r <;> rfl)).trans rfl
  have k7 : ∀ r, st7.data.regs.getXReg r = m2.regs.getXReg r := fun r ↦
    (rv hm7 (v := .reg r) (by cases r <;> rfl)).trans rfl
  have kc : ∀ r ∈ baseRegs, calleeSaved r = true → d8.regs.getXReg r = st.regs.getXReg r :=
    fun r hr hc ↦ by
      rw [k8, k7, hcs2 r hc, k6 r (by
        simp only [baseRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl), k1 r hr]
  have hw24 : NativeRustcVm.WordAt d8.dmem (loc m0 24) m0.regs.X4 := by
    have := fw_write (m0 := m0) hm8' rfl (o := 24) (by decide) (v := .reg .X23) (by decide)
    rwa [show UInt64.ofBitVec
      ((Sym.reg XReg.X23).eval (Env.ofMachine st7.data [(base m0 512, 512)]))
      = m0.regs.X4 from (k7 .X23).trans ((hcs2 .X23 rfl).trans e6x23)] at this
  have hw48 : NativeRustcVm.WordAt d8.dmem (loc m0 48) m0.regs.X2 := by
    have := fw_write (m0 := m0) hm8' rfl (o := 48) (by decide) (v := .reg .X19) (by decide)
    rwa [show UInt64.ofBitVec
      ((Sym.reg XReg.X19).eval (Env.ofMachine st7.data [(base m0 512, 512)]))
      = m0.regs.X2 from (k7 .X19).trans ((hcs2 .X19 rfl).trans e6x19)] at this
  have hw16' : NativeRustcVm.WordAt d8.dmem (loc m0 16) m0.regs.X0 :=
    bytes_block hm8' hwf8 rfl (o := 16) (n := 8) (by decide) (by decide)
      (NativeRustcVm.length_wordBytes _) (by
        show NativeRustcVm.WordAt st7.data.dmem _ _
        rw [hd7]; exact hfw2.get (by simp))
  exact cont d8 {
    fr := hf8
    ts := h.ts_frame (show TStateAt st7.data.dmem _ _ _ by rw [hd7]; exact hts2) (hm8'.kept hwf8)
      hs8
    x0 := (k8 .X0).trans ((k7 .X0).trans ha0)
    x1 := (k8 .X1).trans ((k7 .X1).trans ha1)
    x27 := (k8 .X27).trans ((k7 .X27).trans hc27)
    fw := FW.cons hw16' (FW.cons hw24 (FW.cons hw48 (FW.nil _ _)))
    x20 := (kc .X20 (by simp [baseRegs]) rfl).trans hb.x20
    x21 := (kc .X21 (by simp [baseRegs]) rfl).trans hb.x21
    x22 := (kc .X22 (by simp [baseRegs]) rfl).trans hb.x22
    x24 := (kc .X24 (by simp [baseRegs]) rfl).trans hb.x24
    x26 := (kc .X26 (by simp [baseRegs]) rfl).trans hb.x26
    x28 := (kc .X28 (by simp [baseRegs]) rfl) ▸ hb.x28
    x29 := (kc .X29 (by simp [baseRegs]) rfl).trans hb.x29 }

/-- **From `b9`** (no claim): the words, the squeeze, the count `2`. -/
theorem sample_b9 (hp : Placed code k)
    (h : Parts a s layout target coefficients point slices cs z value m0)
    (hsq : ∀ sp, Spec (Labels.label NativeRustcVmArm.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp))
    {R : MachineState → Prop}
    (cont : ∀ st, AtB11 a s layout cs m0 st →
      Eventually (step1 Host.exe) R ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b11Offset)⟩)
    {st : MachineData} (hb : Base cs m0 st) (hz : cs.size = 0) :
    Eventually (step1 Host.exe) R ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b9Offset)⟩ := by
  have c := h.ctx
  have hnt : NoWrap (tA m0) tstateBytes := h.ts.footprint.1.2
  obtain ⟨hwf9, hm9⟩ := h.frame_env hb.fr
  have hk9 : b9.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b9Offset) := b9_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk9 run_b9 hwf9 hm9 fun st9 hm9' hpc9 ↦ ?_
  have hf9 : VFr m0 st9.data := Fr.ofBlockW hb.fr hm9 hm9' hwf9 rfl rfl
    (fun _ h ↦ absurd h (by simp)) rfl (by rw [stack_eq]; decide) h.hN slots_le
    (writeOk_of (F := 512) (slots := slots) (wr := []) hm9' (by decide) (fun _ h ↦ by cases h))
  have hs9 : SameOutside st.dmem st9.data.dmem (InRange (base m0 512) 512) :=
    NativeRustcVm.SameOutside.mono (hm9'.sameOutside hwf9) fun q hq ↦
      written_r0 hwf9 rfl (by decide) hq
  have hts9 : TStateAt st9.data.dmem (tA m0) a s :=
    h.ts_frame (h.ts_frame h.ts hb.fr.kept hb.fo) (hm9'.kept hwf9) hs9
  have k9 : ∀ r, (after b9 frameS).reg r = some (.reg r) →
      st9.data.regs.getXReg r = st.regs.getXReg r := fun r hr ↦
    (rv hm9' (by rw [← after_eq run_b9]; exact hr)).trans rfl
  have hx0 : st9.data.regs.X0.toBitVec = tA m0 := by
    show (st9.data.regs.getXReg .X0).toBitVec = _
    rw [k9 .X0 rfl, hb.x0]
  have hw : ∀ (o : Nat) (r : XReg) (v : UInt64), o + 8 ≤ 512 → st.regs.getXReg r = v →
      (∀ i < 8, findWrite 0 (o + i) (after b9 frameS).mem = some (.reg r, i)) →
      NativeRustcVm.WordAt st9.data.dmem (loc m0 o) v := fun o r v ho hv hwr ↦ by
    have := fw_write (m0 := m0) hm9' rfl ho (v := .reg r) (by rw [← after_eq run_b9]; exact hwr)
    rwa [show UInt64.ofBitVec ((Sym.reg r).eval (Env.ofMachine st [(base m0 512, 512)])) = v
      from hv] at this
  have hfw9 : FW st9.data.dmem m0 [(16, m0.regs.X0), (24, m0.regs.X4), (48, m0.regs.X2)] :=
    FW.cons (hw 16 .X0 _ (by decide) hb.x0 (by rw [after_eq run_b9]; decide))
      (FW.cons (hw 24 .X4 _ (by decide) hb.x4 (by rw [after_eq run_b9]; decide))
        (FW.cons (hw 48 .X2 _ (by decide) hb.x2 (by rw [after_eq run_b9]; decide)) (FW.nil _ _)))
  refine tsqueeze c hsq hf9 (by rw [stack_eq]; decide) (fun _ h ↦ by cases h) slots_le hpc9 hx0
    hts9 fun m2 hf2 hts2 ha0 ha1 hcs2 hs2 ↦ ?_
  have hfw2 := fw_call h hf9 (by rw [stack_eq]; decide)
    (NativeRustcVm.SameOutside.mono hs2 fun q hq ↦ sq_out hq hnt) (by simp) hfw9
  -- `b10`: the count `2`
  have hk10 : b10.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b10Offset) := b10_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine hf2.regsBlock (st := ⟨m2, _⟩) hk10 run_b10 rfl rfl rfl rfl
    fun st10 hf10 hd10 hm10 hpc10 ↦ ?_
  simp only [PcOk] at hpc10
  obtain ⟨d10, pc10⟩ := st10
  simp only at hpc10
  subst hpc10
  have k10 : ∀ r, r ≠ .X27 → d10.regs.getXReg r = m2.regs.getXReg r := fun r hr ↦
    (rv hm10 (v := .reg r) (by cases r <;> first | rfl | exact absurd rfl hr)).trans rfl
  have kc : ∀ r, calleeSaved r = true → r ≠ .X27 → (after b9 frameS).reg r = some (.reg r) →
      d10.regs.getXReg r = st.regs.getXReg r := fun r hc h27 hr ↦ by
    rw [k10 r h27, hcs2 r hc, k9 r hr]
  have hP0 : placedOf layout cs cs.size = 0 := by
    unfold placedOf; rw [hz]; rfl
  exact cont d10 {
    fr := hf10
    ts := by rw [hd10]; exact hts2
    x0 := (k10 .X0 (by decide)).trans ha0
    x1 := (k10 .X1 (by decide)).trans ha1
    x27 := (rv hm10 (r := .X27) rfl).trans (by rw [hP0]; rfl)
    fw := by rw [hd10]; exact hfw2
    x20 := (kc .X20 rfl (by decide) rfl).trans hb.x20
    x21 := (kc .X21 rfl (by decide) rfl).trans hb.x21
    x22 := (kc .X22 rfl (by decide) rfl).trans hb.x22
    x24 := (kc .X24 rfl (by decide) rfl).trans hb.x24
    x26 := (kc .X26 rfl (by decide) rfl).trans hb.x26
    x28 := (kc .X28 rfl (by decide) rfl) ▸ hb.x28
    x29 := (kc .X29 rfl (by decide) rfl).trans hb.x29 }

end

end NativeRustcVmArm.Whir.VerifyStackedOpening
