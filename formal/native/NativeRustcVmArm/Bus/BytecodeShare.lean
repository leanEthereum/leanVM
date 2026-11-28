module

public import NativeRustcVmArm.Code.Vm.BytecodeShare.Names
public import NativeRustcVmArm.Code.Vm.Dot.Names
public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.EqKernel.Names
public import NativeRustcVmArm.Code.Vm.SumcheckOfSumcheckPlain.Names
public import NativeRustcVmArm.Code.Vm.TStateReadScalar.Names
public import NativeRustcVmArm.Bus.BytecodeShare.Check

/-!
# `bytecode_share`

`b0` saves X19 to X30 in the 432-byte frame, keeps the output in X19, the transcript in X25, the
weights in X27, `bytecode_low` in X24, X22 and the point in X23, and reads the share into the
`Option<EW>` at SP + 80 (`b1`: none, the tag `0`). `b2` keeps the share in X20, X21, zeroes the
slot point (SP + 16) and runs the sumcheck over it (`b3`: none, the tag `0`); `b4` keeps its claim
in X29, X28 and reads the value (`b5`); then the kernel, the check and the copy
(`BytecodeShare/Check.lean`, `Copy.lean`, `Loop.lean`, `Pair.lean`). `bytecodeShare_spec`.
-/

namespace NativeRustcVmArm.Bus.BytecodeShare

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.BytecodeShare
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeRustcVm.Bus
open NativeRustcVmArm.Bus.Gkr
open NativeRustcVmArm.Sumcheck (Ctx At)
open LeanVM.Protocol.Verifier (busBits)

public section

/-- The registers `b0` sets that the whole body keeps. -/
structure R0 (m0 : MachineData) (st : MachineData) : Prop where
  x19 : st.regs.getXReg .X19 = m0.regs.X0
  x22 : st.regs.getXReg .X22 = m0.regs.X4
  x23 : st.regs.getXReg .X23 = m0.regs.X5
  x24 : st.regs.getXReg .X24 = m0.regs.X3
  x25 : st.regs.getXReg .X25 = m0.regs.X1
  x27 : st.regs.getXReg .X27 = m0.regs.X2

theorem R0.call {m0 m m' : MachineData} (h : R0 m0 m)
    (hcs : ∀ r, calleeSaved r = true → m'.regs.getXReg r = m.regs.getXReg r) : R0 m0 m' :=
  ⟨(hcs .X19 rfl).trans h.x19, (hcs .X22 rfl).trans h.x22, (hcs .X23 rfl).trans h.x23,
    (hcs .X24 rfl).trans h.x24, (hcs .X25 rfl).trans h.x25, (hcs .X27 rfl).trans h.x27⟩

theorem R0.block [Labels] {m0 m m' : MachineData} {rs : List (BitVec 64 × Nat)} {S : SState}
    (h : R0 m0 m) (hm : Match (Env.ofMachine m rs) S m')
    (hk : ([.X19, .X22, .X23, .X24, .X25, .X27] : List XReg).all
      (fun r ↦ S.reg r == some (.reg r)) = true) : R0 m0 m' := by
  have k := fun r (hr : r ∈ ([.X19, .X22, .X23, .X24, .X25, .X27] : List XReg)) ↦
    mov_reg hm (beq_iff_eq.mp (List.all_eq_true.mp hk r hr))
  exact ⟨(k .X19 (by simp)).trans h.x19, (k .X22 (by simp)).trans h.x22,
    (k .X23 (by simp)).trans h.x23, (k .X24 (by simp)).trans h.x24,
    (k .X25 (by simp)).trans h.x25, (k .X27 (by simp)).trans h.x27⟩

variable [Host] {a : DecArea} {s0 : TState} {m0 : MachineData} {k : Nat}

/-- **A call to `read_scalar`** into the `Option<EW>` at SP + 80. -/
theorem rs_call (h : BytecodeSharePre a s0 m0)
    (hrs : ∀ s, Spec (Labels.label NativeRustcVmArm.Vm.TStateReadScalar.entryLabel) (ReadScalarPre a s) (ReadScalarPost a s))
    {s : TState} {st : MachineState} {next : Int64} {R : MachineState → Prop}
    (hfr : Fr m0 432 bytecodeShareStack slots keep (outsT m0) st.data)
    (hpc : st.pc = Labels.label NativeRustcVmArm.Vm.TStateReadScalar.entryLabel ∧ retOf st.data = next)
    (h0 : st.data.regs.X0.toBitVec = base m0 432 + BitVec.ofNat 64 80)
    (h1 : st.data.regs.X1 = m0.regs.X1) (hts : TStateAt st.data.dmem m0.regs.X1.toBitVec a s)
    (cont : ∀ m2, Fr m0 432 bytecodeShareStack slots keep (outsT m0) m2 →
      OptEWAt m2.dmem (base m0 432 + BitVec.ofNat 64 80) ((readScalar.run s).map (·.1)) →
      NextAt m2.dmem m0.regs.X1.toBitVec a (readScalar.run s) →
      (∀ r, calleeSaved r = true → m2.regs.getXReg r = st.data.regs.getXReg r) →
      SameOutside st.data.dmem m2.dmem (fun q ↦ InRange (stackBelow st.data readScalarStack)
        readScalarStack q ∨ (InRange (base m0 432 + BitVec.ofNat 64 80) 24 q ∨
          InRange m0.regs.X1.toBitVec tstateBytes q)) →
      Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st := by
  obtain ⟨hS, hrc, hts0, htok, -⟩ := pre_parts h
  have c : Ctx m0 m0.regs.X1.toBitVec a bytecodeShareStack 432 :=
    ctx_of hS hrc hts0 htok N_ge rfl
  have hat := Fr.at_ c hfr (fun q hq ↦ c.not_rc_tstate hq)
  refine Fr.callLocal (o := 80) (n := 24) (X := fun q ↦
      InRange (base m0 432 + BitVec.ofNat 64 80) 24 q ∨ InRange m0.regs.X1.toBitVec tstateBytes q)
    hfr hS.2.1 le_rs keep_callee (by decide) (by omega) (fun q hq ↦ tstate_not_frame c hq)
    (fun q hq ↦ hq.elim .inr .inl) (hrs s) hpc ?_
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.1 fun q hq' ↦ ?_, hq.2.2.2⟩)
    fun m2 hfr2 hq2 hcs2 hs2 ↦ ?_
  · refine ⟨hfr.stackOk hS rfl le_rs, c.rcAt hat le_rs, ?_, ?_, ?_⟩
    · rw [h1]; exact hts
    · rw [h1]; exact c.tstateOk hat le_rs
    · rw [h1, h0]; exact c.outOk hat le_rs (o := 80) (n := 24) (by omega)
  · rw [h0, h1] at hq'
    rcases hq' with hq' | hq' | hq'
    · exact .inr (.inl hq')
    · exact .inr (.inr hq')
    · exact .inl hq'
  · obtain ⟨hopt, hnext, -, -⟩ := hq2
    rw [h0] at hopt
    rw [h1] at hnext
    exact cont m2 hfr2 hopt hnext hcs2 hs2

/-- The tag of an `Option<EW>` at SP + 80, as `tbz w8, #0` reads it. -/
theorem tag_bit {st : MachineData} {x : Option EW}
    (h : OptEWAt st.dmem (base m0 432 + BitVec.ofNat 64 80) x) :
    SBool.eval (Env.ofMachine st [(base m0 432, 432)]) (.not (.bit .W32 (.load 0 80 4) 0)) =
      x.isNone := by
  cases x with
  | none =>
    simp only [OptEWAt] at h
    have hl : (Env.ofMachine st [(base m0 432, 432)]).load 0 80 4 = BitVec.ofNat 64 0 :=
      Transcript.load4_of_tag (w := 0) (.inl rfl) h
    show (!(low .W32 ((Env.ofMachine st [(base m0 432, 432)]).load 0 80 4)).getLsbD 0) = _
    rw [hl]; rfl
  | some y =>
    simp only [OptEWAt] at h
    have hl : (Env.ofMachine st [(base m0 432, 432)]).load 0 80 4 = BitVec.ofNat 64 1 :=
      Transcript.load4_of_tag (w := 1) (.inr rfl) h.1
    show (!(low .W32 ((Env.ofMachine st [(base m0 432, 432)]).load 0 80 4)).getLsbD 0) = _
    rw [hl]; rfl

omit [Host] in
/-- The element of a `some` at SP + 80. -/
theorem opt_ew {d : DataMem} {y : EW}
    (h : OptEWAt d (base m0 432 + BitVec.ofNat 64 80) (some y)) :
    NativeRustcVm.EWAt d (base m0 432 + BitVec.ofNat 64 88) y := by
  have := h.2
  rwa [off, NativeRustcVm.addr_add_add] at this

/-- **After the sumcheck** (`b4`, `b5`): the value read; the check. -/
theorem after_sc (hp : Placed code k) (h : BytecodeSharePre a s0 m0)
    (hrs : ∀ s, Spec (Labels.label NativeRustcVmArm.Vm.TStateReadScalar.entryLabel) (ReadScalarPre a s) (ReadScalarPost a s))
    (hek : Spec (Labels.label NativeRustcVmArm.Vm.EqKernel.entryLabel) EqKernelPre EqKernelPost)
    (hdot : Spec (Labels.label NativeRustcVmArm.Vm.Dot.entryLabel) DotPre DotPost)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {sh cl : EW} {sp : Array EW} {s2 : TState} {st : MachineData}
    (hfr : Fr m0 432 bytecodeShareStack slots keep (outsT m0) st) (hR : R0 m0 st)
    (h20 : st.regs.getXReg .X20 = sh.c0) (h21 : st.regs.getXReg .X21 = sh.c1)
    (hcl : NativeRustcVm.EWAt st.dmem (base m0 432 + BitVec.ofNat 64 88) cl)
    (hsp : NativeRustcVm.EWsAt st.dmem (base m0 432 + BitVec.ofNat 64 16) sp.toList)
    (hsz : sp.size = 4) (hts : TStateAt st.dmem m0.regs.X1.toBitVec a s2)
    (hres : res s0 m0 = (readScalar.run s2).bind fun z ↦
      if (cl == dot (eqKernel sp) (wts m0) * z.1) = true then
        some ((sh, slice m0 m0.regs.X3 m0.regs.X4 ++ sp, z.1), z.2) else none) :
    Eventually (step1 Host.exe) (Goal a s0 m0) ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.BytecodeShare.b4Offset)⟩ := by
  obtain ⟨hS, -⟩ := pre_parts h
  have hN := hS.2.1
  have hbnw := base_noWrap (m0 := m0) (F := 432) (by have := N_ge; omega)
  obtain ⟨hc0, hc1⟩ := NativeRustcVm.ewAt_iff.mp hcl
  rw [NativeRustcVm.addr_add_add] at hc1
  refine Fr.runBlock hS N_ge rfl hfr (b4_in_code.trans hp.1 (by simp [b4])) run_b4 rfl rfl
    (by decide) (by decide) fun st4 hfr4 hd4 hm4 hpc4 ↦ ?_
  have hR4 := R0.block hR hm4 (by decide)
  have e29 : st4.data.regs.getXReg .X29 = cl.c0 := reg_load hm4 rfl hc0
  have e28 : st4.data.regs.getXReg .X28 = cl.c1 := reg_load hm4 rfl hc1
  have e20 : st4.data.regs.getXReg .X20 = sh.c0 := (mov_reg hm4 rfl).trans h20
  have e21 : st4.data.regs.getXReg .X21 = sh.c1 := (mov_reg hm4 rfl).trans h21
  have e0 : st4.data.regs.X0.toBitVec = base m0 432 + BitVec.ofNat 64 80 := by
    rw [show st4.data.regs.X0 = st4.data.regs.getXReg .X0 from rfl, hm4.regs .X0 _ rfl]; rfl
  have e1 : st4.data.regs.X1 = m0.regs.X1 := (mov_reg hm4 (r := .X1) (r' := .X25) rfl).trans hR.x25
  simp only [PcOk] at hpc4
  have c : Ctx m0 m0.regs.X1.toBitVec a bytecodeShareStack 432 :=
    ctx_of hS (pre_parts h).2.1 (pre_parts h).2.2.1 (pre_parts h).2.2.2.1 N_ge rfl
  refine rs_call h hrs hfr4 hpc4 e0 e1 (by rw [hd4]; exact hts)
    fun m5 hfr5 hopt hnext hcs5 hs5 ↦ ?_
  have hR5 := hR4.call hcs5
  have hsp5 : NativeRustcVm.EWsAt m5.dmem (base m0 432 + BitVec.ofNat 64 16) sp.toList :=
    keep_frame hfr4.sp (by have := le_rs; omega) hs5 (by
      rw [NativeRustcVm.length_ewsBytes, Array.length_toList, hsz]; omega) (fun i hi hq ↦ by
        rw [NativeRustcVm.length_ewsBytes, Array.length_toList, hsz] at hi
        rcases hq with hq | hq
        · exact not_loc (by have := N_ge; omega) (by omega) (by omega) (by omega) hq
        · exact (frame_not_tstate c (NativeRustcVm.inRange_add (by omega) (by omega))).1 hq)
      (by rw [hd4]; exact hsp)
  refine Fr.runBlock hS N_ge rfl hfr5 (b5_in_code.trans hp.1 (by simp [b5])) run_b5 rfl rfl
    (by decide) (by decide) fun st6 hfr6 hd6 hm6 hpc6 ↦ ?_
  simp only [PcOk, tag_bit hopt] at hpc6
  cases hr3 : readScalar.run s2 with
  | none =>
    simp only [hr3, Option.map_none, Option.isNone_none, ↓reduceIte] at hpc6
    refine at_pc (hpc6.trans (hp.label (j := NativeRustcVmArm.Vm.BytecodeShare.b15Offset) NativeRustcVmArm.Vm.BytecodeShare.label_9_at)) (none15 hp h
      (Bus.Fr.mono hfr6 fun q hq ↦ outsP_all q (outsT_P q hq))
      ((mov_reg hm6 rfl).trans hR5.x19) (by rw [hres, hr3]; rfl))
  | some z =>
    obtain ⟨v, s3⟩ := z
    simp only [hr3, Option.map_some, Option.isNone_some, Bool.false_eq_true, ↓reduceIte] at hpc6
    rw [hr3] at hopt hnext
    refine at_pc hpc6 (check hp h hek hdot hmul (sh := sh) (cl := cl) (v := v) hfr6
      (R6.block ⟨hR5.x19, (hcs5 .X20 rfl).trans e20, (hcs5 .X21 rfl).trans e21, hR5.x22, hR5.x23,
        hR5.x24, hR5.x27, (hcs5 .X28 rfl).trans e28, (hcs5 .X29 rfl).trans e29⟩ hm6 (by decide))
      (by rw [hd6]; exact opt_ew hopt) (by rw [hd6]; exact hsp5) hsz
      (by rw [hd6]; exact hnext v s3 rfl) (by rw [hres, hr3]; rfl))

/-- **After the share** (`b2`, `b3`): the sumcheck over the slot point. -/
theorem after_share (hp : Placed code k) (h : BytecodeSharePre a s0 m0)
    (hrs : ∀ s, Spec (Labels.label NativeRustcVmArm.Vm.TStateReadScalar.entryLabel) (ReadScalarPre a s) (ReadScalarPost a s))
    (hsc : ∀ s, Spec (Labels.label NativeRustcVmArm.Vm.SumcheckOfSumcheckPlain.entryLabel) (SumcheckPlainPre a s)
      (SumcheckPlainPost a s))
    (hek : Spec (Labels.label NativeRustcVmArm.Vm.EqKernel.entryLabel) EqKernelPre EqKernelPost)
    (hdot : Spec (Labels.label NativeRustcVmArm.Vm.Dot.entryLabel) DotPre DotPost)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {sh : EW} {s1 : TState} {st : MachineData}
    (hfr : Fr m0 432 bytecodeShareStack slots keep (outsT m0) st) (hR : R0 m0 st)
    (hsh : NativeRustcVm.EWAt st.dmem (base m0 432 + BitVec.ofNat 64 88) sh)
    (hts : TStateAt st.dmem m0.regs.X1.toBitVec a s1)
    (hres : res s0 m0 = ((sumcheckPlain sh 3 4).run s1).bind fun y ↦
      (readScalar.run y.2).bind fun z ↦
        if (y.1.2 == dot (eqKernel y.1.1) (wts m0) * z.1) = true then
          some ((sh, slice m0 m0.regs.X3 m0.regs.X4 ++ y.1.1, z.1), z.2) else none) :
    Eventually (step1 Host.exe) (Goal a s0 m0) ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.BytecodeShare.b2Offset)⟩ := by
  obtain ⟨hS, hrc, hts0, htok, -⟩ := pre_parts h
  have hN := hS.2.1
  have c : Ctx m0 m0.regs.X1.toBitVec a bytecodeShareStack 432 :=
    ctx_of hS hrc hts0 htok N_ge rfl
  have hbnw := base_noWrap (m0 := m0) (F := 432) (by have := N_ge; omega)
  have hb432 := base_toNat (m0 := m0) (F := 432) (by have := N_ge; omega)
  have hspl := m0.regs.SP.toNat_lt
  obtain ⟨hs0, hs1⟩ := NativeRustcVm.ewAt_iff.mp hsh
  rw [NativeRustcVm.addr_add_add] at hs1
  have hwf := Bus.wf_frame (F := 432) hS N_ge hfr.kept
  have hm := Bus.match_frame (m := st) hS N_ge rfl hfr.sp
  refine exec_then (b2_in_code.trans hp.1 (by simp [b2])) run_b2 hwf hm fun st2 hm2 hpc2 ↦ ?_
  have hfr2 : Fr m0 432 bytecodeShareStack slots keep (outsT m0) st2.data :=
    Bus.Fr.block hfr hN N_ge hm2 hwf rfl (by decide) (by decide) slots_le
  have hR2 := R0.block hR hm2 (by decide)
  have e20 : st2.data.regs.getXReg .X20 = sh.c0 := reg_load hm2 rfl hs0
  have e21 : st2.data.regs.getXReg .X21 = sh.c1 := reg_load hm2 rfl hs1
  have e2 : st2.data.regs.X2 = sh.c0 := reg_load hm2 (x := .X2) rfl hs0
  have e3 : st2.data.regs.X3 = sh.c1 := reg_load hm2 (x := .X3) rfl hs1
  have e0 : st2.data.regs.X0.toBitVec = base m0 432 + BitVec.ofNat 64 80 := by
    rw [show st2.data.regs.X0 = st2.data.regs.getXReg .X0 from rfl, hm2.regs .X0 _ rfl]; rfl
  have e5 : st2.data.regs.X5.toBitVec = base m0 432 + BitVec.ofNat 64 16 := by
    rw [show st2.data.regs.X5 = st2.data.regs.getXReg .X5 from rfl, hm2.regs .X5 _ rfl]; rfl
  have e1 : st2.data.regs.X1 = m0.regs.X1 := (mov_reg hm2 (r := .X1) (r' := .X25) rfl).trans hR.x25
  have e4 : st2.data.regs.X4.toNat = 3 := by
    rw [show st2.data.regs.X4 = st2.data.regs.getXReg .X4 from rfl, ← UInt64.toNat_toBitVec,
      reg_lit hm2 (r := .X4) (n := 3) rfl]; rfl
  have e6 : st2.data.regs.X6.toNat = 4 := by
    rw [show st2.data.regs.X6 = st2.data.regs.getXReg .X6 from rfl, ← UInt64.toNat_toBitVec,
      reg_lit hm2 (r := .X6) (n := 4) rfl]; rfl
  have hts2 : TStateAt st2.data.dmem m0.regs.X1.toBitVec a s1 :=
    ts_keep c hts (hm2.kept hwf) (NativeRustcVm.SameOutside.mono (hm2.sameOutside hwf)
      fun q hq ↦ frame_inRange hN N_ge (Written.inRange (r := 0) rfl hbnw (by decide) hq))
  have hat := Fr.at_ c hfr2 (fun q hq ↦ c.not_rc_tstate hq)
  have hsub : ∀ q, InRange (base m0 432 + BitVec.ofNat 64 80) 24 q ∨
      InRange (base m0 432 + BitVec.ofNat 64 16) 64 q →
      InRange (base m0 432 + BitVec.ofNat 64 16) 88 q := fun q hq ↦ by
    have t80 : (base m0 432 + BitVec.ofNat 64 80).toNat = (base m0 432).toNat + 80 :=
      NativeRustcVm.toNat_add_ofNat (by omega)
    have t16 : (base m0 432 + BitVec.ofNat 64 16).toNat = (base m0 432).toNat + 16 :=
      NativeRustcVm.toNat_add_ofNat (by omega)
    rw [Sym.inRange_iff (by rw [t16]; omega), t16]
    rcases hq with hq | hq
    · rw [Sym.inRange_iff (by rw [t80]; omega), t80] at hq; omega
    · rw [Sym.inRange_iff (by rw [t16]; omega), t16] at hq; omega
  simp only [PcOk] at hpc2
  refine Fr.callLocal (o := 16) (n := 88) (X := fun q ↦
      InRange (base m0 432 + BitVec.ofNat 64 16) 88 q ∨ InRange m0.regs.X1.toBitVec tstateBytes q)
    hfr2 hN le_sc keep_callee (by decide) (by omega) (fun q hq ↦ tstate_not_frame c hq)
    (fun q hq ↦ hq.elim .inr .inl) (hsc s1) hpc2 ?_
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun q hq' ↦ ?_, hq.2.2⟩)
    fun m3 hfr3 hq3 hcs3 hs3 ↦ ?_
  · refine ⟨hfr2.stackOk hS rfl le_sc, c.rcAt hat le_sc, by rw [e1]; exact hts2,
      by rw [e1]; exact c.tstateOk hat le_sc, by rw [e4]; decide, by rw [e4]; decide, ?_, ?_, ?_⟩
    · rw [e1, e0]; exact c.outOk hat le_sc (o := 80) (n := 24) (by omega)
    · rw [e1, e5, e6]; exact c.outOk hat le_sc (o := 16) (n := 64) (by omega)
    · rw [e0, e5, e6]
      unfold Apart
      rw [NativeRustcVm.toNat_add_ofNat (by omega), NativeRustcVm.toNat_add_ofNat (by omega)]
      omega
  · rw [e0, e1, e5, e6] at hq'
    rcases hq' with hq' | hq' | hq' | hq'
    · exact .inr (.inl (hsub q (.inl hq')))
    · exact .inr (.inl (hsub q (.inr hq')))
    · exact .inr (.inr hq')
    · exact .inl hq'
  obtain ⟨hout, -, -⟩ := hq3
  rw [e0, e1, e5, e6, e2, e3, e4] at hout
  rw [show (⟨sh.c0, sh.c1⟩ : EW) = sh from rfl] at hout
  obtain ⟨hopt, hslots, hnext⟩ := hout
  have hR3 := hR2.call hcs3
  refine Fr.runBlock hS N_ge rfl hfr3 (b3_in_code.trans hp.1 (by simp [b3])) run_b3 rfl rfl
    (by decide) (by decide) fun st4 hfr4 hd4 hm4 hpc4 ↦ ?_
  simp only [PcOk, tag_bit hopt] at hpc4
  cases hr2 : (sumcheckPlain sh 3 4).run s1 with
  | none =>
    simp only [hr2, Option.map_none, Option.isNone_none, ↓reduceIte] at hpc4
    refine at_pc (hpc4.trans (hp.label (j := NativeRustcVmArm.Vm.BytecodeShare.b15Offset) NativeRustcVmArm.Vm.BytecodeShare.label_9_at)) (none15 hp h
      (Bus.Fr.mono hfr4 fun q hq ↦ outsP_all q (outsT_P q hq))
      ((mov_reg hm4 rfl).trans hR3.x19) (by rw [hres, hr2]; rfl))
  | some y =>
    obtain ⟨⟨sp, cl⟩, s2⟩ := y
    simp only [hr2, Option.map_some, Option.isNone_some, Bool.false_eq_true, ↓reduceIte] at hpc4
    rw [hr2] at hopt hnext
    have hsz : sp.size = 4 := by
      have := hr2
      rw [← NativeRustcVm.Sumcheck.sumcheckFn_none] at this
      exact sumcheckFn_size _ _ _ 4 this
    refine at_pc hpc4 (after_sc hp h hrs hek hdot hmul (sh := sh) (cl := cl) hfr4
      (R0.block hR3 hm4 (by decide))
      ((mov_reg hm4 rfl).trans ((hcs3 .X20 rfl).trans e20))
      ((mov_reg hm4 rfl).trans ((hcs3 .X21 rfl).trans e21))
      (by rw [hd4]; exact opt_ew hopt) (by rw [hd4]; exact hslots sp cl s2 hr2) hsz
      (by rw [hd4]; exact hnext _ s2 rfl) ?_)
    rw [hres, hr2]
    rfl

/-- **`bytecode_share`'s contract.** -/
theorem bytecodeShare_spec (hp : Placed code k)
    (hrs : ∀ s, Spec (Labels.label NativeRustcVmArm.Vm.TStateReadScalar.entryLabel) (ReadScalarPre a s) (ReadScalarPost a s))
    (hsc : ∀ s, Spec (Labels.label NativeRustcVmArm.Vm.SumcheckOfSumcheckPlain.entryLabel) (SumcheckPlainPre a s)
      (SumcheckPlainPost a s))
    (hek : Spec (Labels.label NativeRustcVmArm.Vm.EqKernel.entryLabel) EqKernelPre EqKernelPost)
    (hdot : Spec (Labels.label NativeRustcVmArm.Vm.Dot.entryLabel) DotPre DotPost)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) :
    Spec (Labels.label NativeRustcVmArm.Vm.BytecodeShare.entryLabel) (BytecodeSharePre a s0) (BytecodeSharePost a s0) := by
  intro m0 h
  obtain ⟨hS, hrc, hts0, htok, -⟩ := pre_parts h
  have hN : bytecodeShareStack ≤ m0.regs.SP.toNat := hS.2.1
  have c : Ctx m0 m0.regs.X1.toBitVec a bytecodeShareStack 432 :=
    ctx_of hS hrc hts0 htok N_ge rfl
  have hwf := Bus.wf_env0 hS (F := 432) N_ge
  have hm : Match (Bus.env0 m0 432) entryS m0 := Bus.match_entry hS N_ge rfl
  rw [show Labels.label NativeRustcVmArm.Vm.BytecodeShare.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.BytecodeShare.b0Offset) from hp.label (j := NativeRustcVmArm.Vm.BytecodeShare.entryOffset) NativeRustcVmArm.Vm.BytecodeShare.entry_at]
  refine exec_then (b0_in_code.trans hp.1 (by simp [b0])) run_b0 hwf hm fun st hm1 hpc ↦ ?_
  have hfr : Fr m0 432 bytecodeShareStack slots keep (outsT m0) st.data :=
    Fr.ofPrologue hN N_ge hm1 hwf rfl (by decide) slots_le (by decide) (by decide)
  have hsame : NativeRustcVm.SameOutside m0.dmem st.data.dmem (InRange (base m0 432) 432) :=
    NativeRustcVm.SameOutside.mono (hm1.sameOutside hwf) fun q hq ↦
      Written.inRange (r := 0) rfl (Bus.frame_mapped hS N_ge).2 (by decide) hq
  have hts : TStateAt st.data.dmem m0.regs.X1.toBitVec a s0 :=
    hts0.frame (fun q hq ↦ hm1.kept hwf q hq) (fun q hq ↦ frame_not_tstate c hq) hsame
  have e0 : st.data.regs.X0.toBitVec = base m0 432 + BitVec.ofNat 64 80 := by
    rw [show st.data.regs.X0 = st.data.regs.getXReg .X0 from rfl, hm1.regs .X0 _ rfl]; rfl
  have e1 : st.data.regs.X1 = m0.regs.X1 := reg_of hm1 (r := .X1) (r' := .X1) rfl
  have hR : R0 m0 st.data := ⟨reg_of hm1 (r' := .X0) rfl, reg_of hm1 (r' := .X4) rfl,
    reg_of hm1 (r' := .X5) rfl, reg_of hm1 (r' := .X3) rfl, reg_of hm1 (r' := .X1) rfl,
    reg_of hm1 (r' := .X2) rfl⟩
  simp only [PcOk] at hpc
  refine rs_call h hrs hfr hpc e0 e1 hts fun m2 hfr2 hopt hnext hcs2 _ ↦ ?_
  have hR2 := hR.call hcs2
  refine Fr.runBlock hS N_ge rfl hfr2 (b1_in_code.trans hp.1 (by simp [b1])) run_b1 rfl rfl
    (by decide) (by decide) fun st1 hfr1 hd1 hm1' hpc1 ↦ ?_
  have hR1 := R0.block hR2 hm1' (by decide)
  cases hr1 : readScalar.run s0 with
  | none =>
    rw [hr1] at hopt
    simp only [Option.map_none, OptEWAt] at hopt
    have hc : SBool.eval (Env.ofMachine m2 [(base m0 432, 432)])
        (.cmp .eq .W64 (.load 0 80 8) (.lit 0)) = true := by
      show CmpOp.eq.apply .W64 ((Sym.load 0 80 8).eval (Env.ofMachine m2 [(base m0 432, 432)]))
        (BitVec.ofNat 64 0) = true
      rw [show (Sym.load 0 80 8).eval (Env.ofMachine m2 [(base m0 432, 432)]) = (0 : UInt64).toBitVec
        from Transcript.load_ofMachine rfl hopt]
      rfl
    simp only [PcOk, hc, ↓reduceIte] at hpc1
    exact at_pc (hpc1.trans (hp.label (j := NativeRustcVmArm.Vm.BytecodeShare.b15Offset) NativeRustcVmArm.Vm.BytecodeShare.label_9_at)) (none15 hp h
      (Bus.Fr.mono hfr1 fun q hq ↦ outsP_all q (outsT_P q hq)) hR1.x19
      (by rw [res, bytecodeShare_run, hr1]; rfl))
  | some x =>
    obtain ⟨sh, s1⟩ := x
    rw [hr1] at hopt hnext
    simp only [Option.map_some] at hopt
    have hc : SBool.eval (Env.ofMachine m2 [(base m0 432, 432)])
        (.cmp .eq .W64 (.load 0 80 8) (.lit 0)) = false := by
      show CmpOp.eq.apply .W64 ((Sym.load 0 80 8).eval (Env.ofMachine m2 [(base m0 432, 432)]))
        (BitVec.ofNat 64 0) = false
      rw [show (Sym.load 0 80 8).eval (Env.ofMachine m2 [(base m0 432, 432)]) = (1 : UInt64).toBitVec
        from Transcript.load_ofMachine rfl hopt.1]
      rfl
    simp only [PcOk, hc, Bool.false_eq_true, ↓reduceIte] at hpc1
    exact at_pc hpc1 (after_share hp h hrs hsc hek hdot hmul hfr1 hR1
      (by rw [hd1]; exact opt_ew hopt) (by rw [hd1]; exact hnext sh s1 rfl)
      (by rw [res, bytecodeShare_run, hr1]; rfl))

end

end NativeRustcVmArm.Bus.BytecodeShare
