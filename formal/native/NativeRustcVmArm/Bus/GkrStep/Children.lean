module

public import NativeRustcVmArm.Code.Vm.TStateReadScalars.Names
public import NativeRustcVmArm.Bus.GkrStep.Calls

/-!
# `gkr_step`'s children

`b7` keeps the sumcheck's claim in X29, X28, clears the children and reads the first
(`read_scalars` into the frame at `1024`); `b8`, `b10`, `b12` check each read, `b9`, `b11` read
the second (`1088`) and the third (`1152`): `AtProds`, at `b13`.
-/

namespace NativeRustcVmArm.Bus.GkrStep

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.GkrStep
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeRustcVm.Bus
open NativeRustcVmArm.Bus.Gkr
open NativeRustcVmArm.Sumcheck (Ctx At)
open NativeRustcVm.Sumcheck (readScalars_size)

public section

/-- **At `b13`** (`k + NativeRustcVmArm.Vm.GkrStep.b13Offset`): the three children read, the claim in X29, X28. -/
structure AtProds [Labels] (a : DecArea) (s0 : TState) (g0 : GkrStateW) (m0 : MachineData)
    (c cl : EW) (xs h0 h1 h2 : Array EW) (s3 : TState) (m : MachineData) : Prop where
  fr : Fr m0 1392 gkrStepStack slots keep (outs m0) m
  regs : Regs m0 c xs.size m
  x28 : m.regs.getXReg .X28 = cl.c1
  x29 : m.regs.getXReg .X29 = cl.c0
  size : xs.size + m0.regs.X1.toNat ≤ busPointCap
  hxs : NativeRustcVm.EWsAt m.dmem (loc m0 16) xs.toList
  c0 : NativeRustcVm.EWsAt m.dmem (loc m0 1024) h0.toList
  c1 : NativeRustcVm.EWsAt m.dmem (loc m0 1088) h1.toList
  c2 : NativeRustcVm.EWsAt m.dmem (loc m0 1152) h2.toList
  s0' : h0.size = 2 ^ m0.regs.X1.toNat
  s1' : h1.size = 2 ^ m0.regs.X1.toNat
  s2' : h2.size = 2 ^ m0.regs.X1.toNat
  ts : TStateAt m.dmem m0.regs.X0.toBitVec a s3
  run : run0 s0 g0 m0 = gkrFinish m0.regs.X1.toNat c cl xs h0 h1 h2 s3

variable [Host] {a : DecArea} {s0 : TState} {g0 : GkrStateW} {m0 : MachineData} {k : Nat}

omit [Host] in
theorem xs_le {xs : Array EW} (h : xs.size + m0.regs.X1.toNat ≤ busPointCap) :
    16 + 16 * xs.toList.length ≤ 1024 := by
  rw [Array.length_toList]; unfold busPointCap at h; omega

/-- The frame's bytes kept by `read_scalars` into `n ≤ 64` bytes at `o'`: those at `o` apart. -/
theorem ews_rs (h : GkrStepPre a s0 g0 m0) {m d : MachineData} {o' n : Nat}
    (hfr : Fr m0 1392 gkrStepStack slots keep (outs m0) m)
    (hs : SameOutside m.dmem d.dmem (fun q ↦
      InRange (stackBelow m readScalarsStack) readScalarsStack q ∨
        (InRange (loc m0 o') n q ∨ InRange m0.regs.X0.toBitVec tstateBytes q)))
    {o : Nat} {xs : List EW} (ho : o + 16 * xs.length ≤ 1392) (hon : o' + n ≤ 1392)
    (hd : o + 16 * xs.length ≤ o' ∨ o' + n ≤ o)
    (hx : NativeRustcVm.EWsAt m.dmem (loc m0 o) xs) : NativeRustcVm.EWsAt d.dmem (loc m0 o) xs :=
  ews_call (pre_stack h) hfr.sp le_rs hs ho (fun i hi hq ↦ hq.elim
    (fun h' ↦ not_loc' (pre_stack h) hon (by omega) (by omega) h')
    (fun h' ↦ loc_not_ts h (by omega) h')) hx

/-- **The children** (`b7` to `b12`). -/
theorem reads_spec (hp : Placed code k) (h : GkrStepPre a s0 g0 m0)
    (hrs : ∀ s, Spec (Labels.label NativeRustcVmArm.Vm.TStateReadScalars.entryLabel) (ReadScalarsPre a s) (ReadScalarsPost a s))
    {c cl : EW} {xs : Array EW} {s2 : TState}
    (hprods : ∀ h0 h1 h2 s3 m, AtProds a s0 g0 m0 c cl xs h0 h1 h2 s3 m →
      Eventually (step1 Host.exe) (Goal a s0 g0 m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.GkrStep.b13Offset)⟩)
    {m : MachineData} (hi : AtChildren a s0 g0 m0 c cl xs s2 m) :
    Eventually (step1 Host.exe) (Goal a s0 g0 m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.GkrStep.b7Offset)⟩ := by
  have hS := pre_stack h
  have hN : gkrStepStack ≤ m0.regs.SP.toNat := hS.2.1
  have hn := two_pow_le h
  have hxl := xs_le hi.size
  have R0 : Regs m0 c xs.size m :=
    ⟨hi.x19, hi.x20, hi.x21, hi.x22, hi.x23, hi.x24, hi.x25, hi.x26, hi.x27⟩
  -- `b7`
  have hwf := Bus.wf_frame hS N_ge hi.fr.kept
  have hm := Bus.match_frame hS N_ge rfl hi.fr.sp
  refine exec_then (b7_in_code.trans hp.1 (by simp [b7])) run_b7 hwf hm fun st hm' hpc ↦ ?_
  have hfr : Fr m0 1392 gkrStepStack slots keep (outs m0) st.data :=
    Bus.Fr.block hi.fr hN N_ge hm' hwf rfl (by decide +kernel) (by decide) slots_le
  have R1 := R0.block hm' (by decide +kernel)
  have hxs1 := ews_block hm' hwf (o := 16) (L := 1008) (by omega) (by decide +kernel)
    (by omega) hi.hxs
  have hts1 := ts_block h hm' hwf (by decide +kernel) hi.ts
  have e28 : st.data.regs.getXReg .X28 = cl.c1 := UInt64.toBitVec_inj.mp ((hm'.regs .X28 _ rfl).trans
    (Transcript.load_ofMachine (b := base m0 1392) (n := 1392) rfl hi.cl1))
  have e29 : st.data.regs.getXReg .X29 = cl.c0 := UInt64.toBitVec_inj.mp ((hm'.regs .X29 _ rfl).trans
    (Transcript.load_ofMachine (b := base m0 1392) (n := 1392) rfl hi.cl0))
  have e0 : st.data.regs.X0 = m0.regs.X0 := (reg_of hm' (r := .X0) (r' := .X21) rfl).trans hi.x21
  have e1 : st.data.regs.X1.toBitVec = loc m0 1024 := by
    show (st.data.regs.getXReg .X1).toBitVec = _
    rw [hm'.regs .X1 _ rfl]; rfl
  have e2 : st.data.regs.X2.toNat = 2 ^ m0.regs.X1.toNat := by
    show (st.data.regs.getXReg .X2).toBitVec.toNat = _
    rw [reg_of hm' (r := .X2) (r' := .X26) rfl, hi.x26,
      NativeRustcVm.toNat_ofNat_of_lt (by omega)]
  simp only [PcOk, NativeRustcVmArm.Vm.GkrStep.b7_length, NativeRustcVmArm.Vm.GkrStep.b7Length, show k + NativeRustcVmArm.Vm.GkrStep.b7Offset + 30 = k + NativeRustcVmArm.Vm.GkrStep.b8Offset by simpa only [NativeRustcVmArm.Vm.GkrStep.b7_length, NativeRustcVmArm.Vm.GkrStep.b7Length, Nat.add_assoc] using congrArg (k + ·) NativeRustcVmArm.Vm.GkrStep.b7_next] at hpc
  refine rs_call h hrs (o := 1024) (by omega) hfr hpc e0 e1 e2 hts1
    fun m2 hfr2 hx2 hok2 hcs2 hs2 ↦ ?_
  have R2 := R1.call hcs2
  have f28 := (hcs2 .X28 rfl).trans e28
  have f29 := (hcs2 .X29 rfl).trans e29
  have hxs2 := ews_rs h hfr hs2 (o := 16) (by omega) (by omega) (by omega) hxs1
  -- `b8`
  refine Fr.runBlock hS N_ge rfl hfr2 (b8_in_code.trans hp.1 (by simp [b8])) run_b8 rfl rfl
    (by decide) (by decide) fun st8 hfr8 hd8 hm8 hpc8 ↦ ?_
  have hc8 : SBool.eval (Env.ofMachine m2 [(base m0 1392, 1392)]) (.not (.bit .W32 (.reg .X0) 0)) =
      !((readScalars (2 ^ m0.regs.X1.toNat)).run s2).isSome := by
    show (!(low .W32 (m2.regs.getXReg .X0).toBitVec).getLsbD 0) = _
    rw [show m2.regs.getXReg .X0 = m2.regs.X0 from rfl, hx2, okWord_bit]
  simp only [PcOk, hc8, NativeRustcVmArm.Vm.GkrStep.b8_length, NativeRustcVmArm.Vm.GkrStep.b8Length, show k + NativeRustcVmArm.Vm.GkrStep.b8Offset + 1 = k + NativeRustcVmArm.Vm.GkrStep.b9Offset by simpa only [NativeRustcVmArm.Vm.GkrStep.b8_length, NativeRustcVmArm.Vm.GkrStep.b8Length, Nat.add_assoc] using congrArg (k + ·) NativeRustcVmArm.Vm.GkrStep.b8_next] at hpc8
  cases hr0 : (readScalars (2 ^ m0.regs.X1.toNat)).run s2 with
  | none =>
    simp only [hr0, Option.isSome_none, Bool.not_false, ↓reduceIte] at hpc8
    exact at_pc (hpc8.trans (hp.label (j := NativeRustcVmArm.Vm.GkrStep.b32Offset) NativeRustcVmArm.Vm.GkrStep.label_14_at)) (fail_spec hp h hfr8
      (by rw [hi.run, gkrChildren, hr0]; rfl))
  | some p0 =>
    obtain ⟨h0v, s3a⟩ := p0
    simp only [hr0, Option.isSome_some, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc8
    obtain ⟨hc0, hts2⟩ := hok2 h0v s3a hr0
    have hs0 : h0v.size = 2 ^ m0.regs.X1.toNat := readScalars_size hr0
    -- `b9`
    refine at_pc hpc8 (Fr.runBlock hS N_ge rfl hfr8 (b9_in_code.trans hp.1 (by simp [b9])) run_b9
      rfl rfl (by decide) (by decide) fun st9 hfr9 hd9 hm9 hpc9 ↦ ?_)
    have R8 := R2.block hm8 (by decide +kernel)
    have R9 := R8.block hm9 (by decide +kernel)
    have g0' : st9.data.regs.X0 = m0.regs.X0 := (reg_of hm9 (r := .X0) (r' := .X21) rfl).trans R8.x21
    have g1 : st9.data.regs.X1.toBitVec = loc m0 1088 := by
      show (st9.data.regs.getXReg .X1).toBitVec = _
      rw [hm9.regs .X1 _ rfl]
      show BinOp.apply .add .W64 (st8.data.regs.getXReg .X27).toBitVec (BitVec.ofNat 64 64) = _
      rw [R8.x27, add_loc]
    have g2 : st9.data.regs.X2.toNat = 2 ^ m0.regs.X1.toNat := by
      show (st9.data.regs.getXReg .X2).toBitVec.toNat = _
      rw [reg_of hm9 (r := .X2) (r' := .X26) rfl, R8.x26,
        NativeRustcVm.toNat_ofNat_of_lt (by omega)]
    simp only [PcOk, NativeRustcVmArm.Vm.GkrStep.b9_length, NativeRustcVmArm.Vm.GkrStep.b9Length, show k + NativeRustcVmArm.Vm.GkrStep.b9Offset + 4 = k + NativeRustcVmArm.Vm.GkrStep.b10Offset by simpa only [NativeRustcVmArm.Vm.GkrStep.b9_length, NativeRustcVmArm.Vm.GkrStep.b9Length, Nat.add_assoc] using congrArg (k + ·) NativeRustcVmArm.Vm.GkrStep.b9_next] at hpc9
    have hxs9 : NativeRustcVm.EWsAt st9.data.dmem (loc m0 16) xs.toList := by
      rw [hd9, hd8]; exact hxs2
    have hc09 : NativeRustcVm.EWsAt st9.data.dmem (loc m0 1024) h0v.toList := by
      rw [hd9, hd8]; exact hc0
    refine rs_call h hrs (o := 1088) (by omega) hfr9 hpc9 g0' g1 g2 (by rw [hd9, hd8]; exact hts2)
      fun m3 hfr3 hx3 hok3 hcs3 hs3 ↦ ?_
    have R3 := R9.call hcs3
    have hxs3 := ews_rs h hfr9 hs3 (o := 16) (by omega) (by omega) (by omega) hxs9
    have hl0 : h0v.toList.length = 2 ^ m0.regs.X1.toNat := by rw [Array.length_toList, hs0]
    have hc03 := ews_rs h hfr9 hs3 (o := 1024) (by omega) (by omega) (by omega) hc09
    -- `b10`
    refine Fr.runBlock hS N_ge rfl hfr3 (b10_in_code.trans hp.1 (by simp [b10])) run_b10 rfl rfl
      (by decide) (by decide) fun st10 hfr10 hd10 hm10 hpc10 ↦ ?_
    have hc10 : SBool.eval (Env.ofMachine m3 [(base m0 1392, 1392)])
        (.cmp .eq .W32 (.reg .X0) (.lit 0)) =
        !((readScalars (2 ^ m0.regs.X1.toNat)).run s3a).isSome := by
      show CmpOp.eq.apply .W32 (m3.regs.getXReg .X0).toBitVec (BitVec.ofNat 64 0) = _
      rw [show m3.regs.getXReg .X0 = m3.regs.X0 from rfl, hx3, okWord_eq0]
    simp only [PcOk, hc10, NativeRustcVmArm.Vm.GkrStep.b10_length, NativeRustcVmArm.Vm.GkrStep.b10Length, show k + NativeRustcVmArm.Vm.GkrStep.b10Offset + 1 = k + NativeRustcVmArm.Vm.GkrStep.b11Offset by simpa only [NativeRustcVmArm.Vm.GkrStep.b10_length, NativeRustcVmArm.Vm.GkrStep.b10Length, Nat.add_assoc] using congrArg (k + ·) NativeRustcVmArm.Vm.GkrStep.b10_next]
      at hpc10
    cases hr1 : (readScalars (2 ^ m0.regs.X1.toNat)).run s3a with
    | none =>
      simp only [hr1, Option.isSome_none, Bool.not_false, ↓reduceIte] at hpc10
      exact at_pc (hpc10.trans (hp.label (j := NativeRustcVmArm.Vm.GkrStep.b32Offset) NativeRustcVmArm.Vm.GkrStep.label_14_at)) (fail_spec hp h hfr10
        (by rw [hi.run, gkrChildren, hr0]; simp only [Option.bind_some]; rw [hr1]; rfl))
    | some p1 =>
      obtain ⟨h1v, s3b⟩ := p1
      simp only [hr1, Option.isSome_some, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc10
      obtain ⟨hc1, hts3⟩ := hok3 h1v s3b hr1
      have hs1 : h1v.size = 2 ^ m0.regs.X1.toNat := readScalars_size hr1
      have hl1 : h1v.toList.length = 2 ^ m0.regs.X1.toNat := by rw [Array.length_toList, hs1]
      -- `b11`
      refine at_pc hpc10 (Fr.runBlock hS N_ge rfl hfr10 (b11_in_code.trans hp.1 (by simp [b11]))
        run_b11 rfl rfl (by decide) (by decide) fun st11 hfr11 hd11 hm11 hpc11 ↦ ?_)
      have R10 := R3.block hm10 (by decide +kernel)
      have R11 := R10.block hm11 (by decide +kernel)
      have k0 : st11.data.regs.X0 = m0.regs.X0 :=
        (reg_of hm11 (r := .X0) (r' := .X21) rfl).trans R10.x21
      have k1 : st11.data.regs.X1.toBitVec = loc m0 1152 := by
        show (st11.data.regs.getXReg .X1).toBitVec = _
        rw [hm11.regs .X1 _ rfl]
        show BinOp.apply .add .W64 (st10.data.regs.getXReg .X27).toBitVec (BitVec.ofNat 64 128) = _
        rw [R10.x27, add_loc]
      have k2 : st11.data.regs.X2.toNat = 2 ^ m0.regs.X1.toNat := by
        show (st11.data.regs.getXReg .X2).toBitVec.toNat = _
        rw [reg_of hm11 (r := .X2) (r' := .X26) rfl, R10.x26,
          NativeRustcVm.toNat_ofNat_of_lt (by omega)]
      simp only [PcOk, NativeRustcVmArm.Vm.GkrStep.b11_length, NativeRustcVmArm.Vm.GkrStep.b11Length, show k + NativeRustcVmArm.Vm.GkrStep.b11Offset + 4 = k + NativeRustcVmArm.Vm.GkrStep.b12Offset by simpa only [NativeRustcVmArm.Vm.GkrStep.b11_length, NativeRustcVmArm.Vm.GkrStep.b11Length, Nat.add_assoc] using congrArg (k + ·) NativeRustcVmArm.Vm.GkrStep.b11_next] at hpc11
      have hd' : st11.data.dmem = m3.dmem := hd11.trans hd10
      refine rs_call h hrs (o := 1152) (by omega) hfr11 hpc11 k0 k1 k2 (by rw [hd']; exact hts3)
        fun m4 hfr4 hx4 hok4 hcs4 hs4 ↦ ?_
      have R4 := R11.call hcs4
      have hxs4 := ews_rs h hfr11 hs4 (o := 16) (xs := xs.toList) (by omega) (by omega) (by omega)
        (by rw [hd']; exact hxs3)
      have hc04 := ews_rs h hfr11 hs4 (o := 1024) (xs := h0v.toList) (by omega) (by omega) (by omega)
        (by rw [hd']; exact hc03)
      have hc14 := ews_rs h hfr11 hs4 (o := 1088) (xs := h1v.toList) (by omega) (by omega) (by omega)
        (by rw [hd']; exact hc1)
      -- `b12`
      refine Fr.runBlock hS N_ge rfl hfr4 (b12_in_code.trans hp.1 (by simp [b12])) run_b12 rfl
        rfl (by decide) (by decide) fun st12 hfr12 hd12 hm12 hpc12 ↦ ?_
      have hc12 : SBool.eval (Env.ofMachine m4 [(base m0 1392, 1392)])
          (.cmp .eq .W32 (.reg .X0) (.lit 0)) =
          !((readScalars (2 ^ m0.regs.X1.toNat)).run s3b).isSome := by
        show CmpOp.eq.apply .W32 (m4.regs.getXReg .X0).toBitVec (BitVec.ofNat 64 0) = _
        rw [show m4.regs.getXReg .X0 = m4.regs.X0 from rfl, hx4, okWord_eq0]
      simp only [PcOk, hc12, NativeRustcVmArm.Vm.GkrStep.b12_length, NativeRustcVmArm.Vm.GkrStep.b12Length, show k + NativeRustcVmArm.Vm.GkrStep.b12Offset + 1 = k + NativeRustcVmArm.Vm.GkrStep.b13Offset by simpa only [NativeRustcVmArm.Vm.GkrStep.b12_length, NativeRustcVmArm.Vm.GkrStep.b12Length, Nat.add_assoc] using congrArg (k + ·) NativeRustcVmArm.Vm.GkrStep.b12_next]
        at hpc12
      cases hr2 : (readScalars (2 ^ m0.regs.X1.toNat)).run s3b with
      | none =>
        simp only [hr2, Option.isSome_none, Bool.not_false, ↓reduceIte] at hpc12
        exact at_pc (hpc12.trans (hp.label (j := NativeRustcVmArm.Vm.GkrStep.b32Offset) NativeRustcVmArm.Vm.GkrStep.label_14_at)) (fail_spec hp h hfr12
          (by rw [hi.run, gkrChildren, hr0]; simp only [Option.bind_some]; rw [hr1]
              simp only [Option.bind_some]; rw [hr2]; rfl))
      | some p2 =>
        obtain ⟨h2v, s3⟩ := p2
        simp only [hr2, Option.isSome_some, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          at hpc12
        obtain ⟨hc2, hts4⟩ := hok4 h2v s3 hr2
        refine at_pc hpc12 (hprods h0v h1v h2v s3 st12.data
          { fr := hfr12
            regs := R4.block hm12 (by decide +kernel)
            x28 := (reg_of hm12 rfl).trans ((hcs4 .X28 rfl).trans ((reg_of hm11 rfl).trans
              ((reg_of hm10 rfl).trans ((hcs3 .X28 rfl).trans ((reg_of hm9 rfl).trans
              ((reg_of hm8 rfl).trans f28))))))
            x29 := (reg_of hm12 rfl).trans ((hcs4 .X29 rfl).trans ((reg_of hm11 rfl).trans
              ((reg_of hm10 rfl).trans ((hcs3 .X29 rfl).trans ((reg_of hm9 rfl).trans
              ((reg_of hm8 rfl).trans f29))))))
            size := hi.size
            hxs := by rw [hd12]; exact hxs4
            c0 := by rw [hd12]; exact hc04
            c1 := by rw [hd12]; exact hc14
            c2 := by rw [hd12]; exact hc2
            s0' := hs0
            s1' := hs1
            s2' := readScalars_size hr2
            ts := by rw [hd12]; exact hts4
            run := by
              rw [hi.run, gkrChildren, hr0]; simp only [Option.bind_some]; rw [hr1]
              simp only [Option.bind_some]; rw [hr2]; rfl })

end

end NativeRustcVmArm.Bus.GkrStep
