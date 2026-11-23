module

public import NativeRustcVmArm.Code.Vm.Dot.Names
public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.EqKernel.Names
public import NativeRustcVmArm.Bus.BytecodeShare.Pair
public import NativeRustcVm.Arrays.EqKernel

/-!
# `bytecode_share`: the kernel, the dot product, the check

From `b6` (the value read): `eq_kernel` of the slot point into the kernel (`b6`; it cannot fail,
`b7`), `dot` of the kernel and the weights (`b8`), times the value (`b9`), compared with the
sumcheck's claim limb by limb (`b10`, `b11`); a mismatch is the tag `0`, else the copy.
-/

namespace NativeRustcVmArm.Bus.BytecodeShare

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.BytecodeShare
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeRustcVm.Bus
open NativeRustcVmArm.Bus.Gkr
open NativeRustcVmArm.Sumcheck (Ctx At)

public section

theorem beq_ew (x y : EW) : (x == y) = (x.c0 == y.c0 && x.c1 == y.c1) := by
  cases x; cases y; rfl

/-- A register a block loaded from the frame. -/
theorem reg_load [Labels] {m m' : MachineData} {F : Nat} {b : BitVec 64} {S : SState} {x : XReg}
    {o : Nat} (hm : Match (Env.ofMachine m [(b, F)]) S m') (h : S.reg x = some (.load 0 o 8))
    {w : UInt64} (hw : NativeRustcVm.WordAt m.dmem (b + BitVec.ofNat 64 o) w) :
    m'.regs.getXReg x = w :=
  UInt64.toBitVec_inj.mp ((hm.regs x _ h).trans (Transcript.load_ofMachine rfl hw))

/-- **The `TState` kept** by changes in the stack. -/
theorem ts_keep [Labels] {m0 : MachineData} {t : BitVec 64} {a : DecArea} {N F : Nat}
    {d d' : DataMem} {s : TState} (c : Ctx m0 t a N F) (hts : TStateAt d t a s)
    (hk : Kept d d') (hs : SameOutside d d' (InRange (base m0 N) N)) : TStateAt d' t a s :=
  hts.frame hk (fun q hq ↦ by
    have hnw : NativeRustcVm.NoWrap (stackBelow m0 N) N := by
      unfold NativeRustcVm.NoWrap; rw [c.stk]; have := c.spN; have := Sumcheck.Ctx.sp_lt m0
      omega
    exact ⟨NativeRustcVm.Apart.not_inRange c.tok.1.symm hnw hts.footprint.1.2 hq,
      NativeRustcVm.Apart.not_inRange c.tok.2.1.symm hnw hts.footprint.2.1.2 hq⟩) hs

/-- A call's changes, below the frame and in `n` bytes of the frame at `o`, are in the stack. -/
theorem call_in_stack {m0 st : MachineData} {N N' o n : Nat} {d' : DataMem}
    (hN : N ≤ m0.regs.SP.toNat) (hsp : st.regs.SP.toBitVec = base m0 432) (hle : 432 + N' ≤ N)
    (hon : o + n ≤ 432)
    (hs : SameOutside st.dmem d' (fun q ↦ InRange (stackBelow st N') N' q ∨
      InRange (base m0 432 + BitVec.ofNat 64 o) n q)) :
    SameOutside st.dmem d' (InRange (base m0 N) N) :=
  NativeRustcVm.SameOutside.mono hs fun q hq ↦ hq.elim (inRange_callee hN hsp hle)
    (inRange_local hN (by omega) hon)

/-- The registers at `b6`. -/
structure R6 (m0 : MachineData) (sh cl : EW) (st : MachineData) : Prop where
  x19 : st.regs.getXReg .X19 = m0.regs.X0
  x20 : st.regs.getXReg .X20 = sh.c0
  x21 : st.regs.getXReg .X21 = sh.c1
  x22 : st.regs.getXReg .X22 = m0.regs.X4
  x23 : st.regs.getXReg .X23 = m0.regs.X5
  x24 : st.regs.getXReg .X24 = m0.regs.X3
  x27 : st.regs.getXReg .X27 = m0.regs.X2
  x28 : st.regs.getXReg .X28 = cl.c1
  x29 : st.regs.getXReg .X29 = cl.c0

/-- The registers through a call. -/
theorem R6.call {m0 m m' : MachineData} {sh cl : EW} (h : R6 m0 sh cl m)
    (hcs : ∀ r, calleeSaved r = true → m'.regs.getXReg r = m.regs.getXReg r) : R6 m0 sh cl m' :=
  ⟨(hcs .X19 rfl).trans h.x19, (hcs .X20 rfl).trans h.x20, (hcs .X21 rfl).trans h.x21,
    (hcs .X22 rfl).trans h.x22, (hcs .X23 rfl).trans h.x23, (hcs .X24 rfl).trans h.x24,
    (hcs .X27 rfl).trans h.x27, (hcs .X28 rfl).trans h.x28, (hcs .X29 rfl).trans h.x29⟩

/-- The registers through a block that leaves them alone. -/
theorem R6.block [Labels] {m0 m m' : MachineData} {sh cl : EW} {rs : List (BitVec 64 × Nat)}
    {S : SState} (h : R6 m0 sh cl m) (hm : Match (Env.ofMachine m rs) S m')
    (hk : ([.X19, .X20, .X21, .X22, .X23, .X24, .X27, .X28, .X29] : List XReg).all
      (fun r ↦ S.reg r == some (.reg r)) = true) : R6 m0 sh cl m' := by
  have k := fun r (hr : r ∈ ([.X19, .X20, .X21, .X22, .X23, .X24, .X27, .X28, .X29] :
      List XReg)) ↦ mov_reg hm (beq_iff_eq.mp (List.all_eq_true.mp hk r hr))
  exact ⟨(k .X19 (by simp)).trans h.x19, (k .X20 (by simp)).trans h.x20,
    (k .X21 (by simp)).trans h.x21, (k .X22 (by simp)).trans h.x22,
    (k .X23 (by simp)).trans h.x23, (k .X24 (by simp)).trans h.x24,
    (k .X27 (by simp)).trans h.x27, (k .X28 (by simp)).trans h.x28,
    (k .X29 (by simp)).trans h.x29⟩

variable [Host] {a : DecArea} {s0 s3 : TState} {m0 : MachineData} {k : Nat}

/-- The weights as the model reads them. -/
abbrev wts (m0 : MachineData) : Array EW := (NativeRustcVm.ewsOf m0.dmem m0.regs.X2.toBitVec 16).toArray

/-- **From `b6` to the copy or the tag `0`.** -/
theorem check (hp : Placed code k) (h : BytecodeSharePre a s0 m0)
    (hek : Spec (Labels.label NativeRustcVmArm.Vm.EqKernel.entryLabel) EqKernelPre EqKernelPost)
    (hdot : Spec (Labels.label NativeRustcVmArm.Vm.Dot.entryLabel) DotPre DotPost)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {sh cl v : EW} {sp : Array EW} {st : MachineData}
    (hfr : Fr m0 432 bytecodeShareStack slots keep (outsT m0) st) (hR : R6 m0 sh cl st)
    (hv : NativeRustcVm.EWAt st.dmem (base m0 432 + BitVec.ofNat 64 88) v)
    (hsp : NativeRustcVm.EWsAt st.dmem (base m0 432 + BitVec.ofNat 64 16) sp.toList)
    (hsz : sp.size = 4) (hts : TStateAt st.dmem m0.regs.X1.toBitVec a s3)
    (hres : res s0 m0 = if (cl == dot (eqKernel sp) (wts m0) * v) = true then
      some ((sh, slice m0 m0.regs.X3 m0.regs.X4 ++ sp, v), s3) else none) :
    Eventually (step1 Host.exe) (Goal a s0 m0) ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.BytecodeShare.b6Offset)⟩ := by
  obtain ⟨hS, hrc, hts0, htok, hw, hlen, hbl, hoo, hpo, hop, hpb, hwt, hbt⟩ := pre_parts h
  have hN := hS.2.1
  have c : Ctx m0 m0.regs.X1.toBitVec a bytecodeShareStack 432 :=
    ctx_of hS hrc hts0 htok N_ge rfl
  have hbnw := base_noWrap (m0 := m0) (F := 432) (by have := N_ge; omega)
  have hb432 := base_toNat (m0 := m0) (F := 432) (by have := N_ge; omega)
  have hspl := m0.regs.SP.toNat_lt
  have hfrT : ∀ q, outsT m0 q → ¬InRange (base m0 432) 432 q := fun q hq ↦ tstate_not_frame c hq
  -- `b6`: the value, the kernel zeroed, `eq_kernel` called.
  have hwf := Bus.wf_frame (F := 432) hS N_ge hfr.kept
  have hm := Bus.match_frame (m := st) hS N_ge rfl hfr.sp
  refine exec_then (b6_in_code.trans hp.1 (by simp [b6])) run_b6 hwf hm fun st1 hm1 hpc1 ↦ ?_
  have hfr1 : Fr m0 432 bytecodeShareStack slots keep (outsT m0) st1.data :=
    Bus.Fr.block hfr hN N_ge hm1 hwf rfl (by decide) (by decide) slots_le
  have hs1 : SameOutside st.dmem st1.data.dmem (InRange (base m0 432 + BitVec.ofNat 64 80) (336 - 80)) :=
    same_of_writes_in hm1 hwf (r := 0) rfl hbnw (by omega) (by omega) (by decide)
  obtain ⟨hv0, hv1⟩ := NativeRustcVm.ewAt_iff.mp hv
  rw [NativeRustcVm.addr_add_add] at hv1
  have e25 : st1.data.regs.getXReg .X25 = v.c0 := reg_load hm1 rfl hv0
  have e26 : st1.data.regs.getXReg .X26 = v.c1 := reg_load hm1 rfl hv1
  have hR1 := R6.block hR hm1 (by decide)
  have hsp1 : NativeRustcVm.EWsAt st1.data.dmem (base m0 432 + BitVec.ofNat 64 16) sp.toList :=
    NativeRustcVm.BytesAt.of_sameOutside hsp hs1 fun i hi hq ↦ by
      rw [NativeRustcVm.length_ewsBytes, Array.length_toList, hsz] at hi
      rw [NativeRustcVm.addr_add_add] at hq
      exact NativeRustcVm.not_inRange_sub hbnw (by omega) (by omega) (by omega) hq
  have hts1 : TStateAt st1.data.dmem m0.regs.X1.toBitVec a s3 :=
    ts_keep c hts (hm1.kept hwf) (NativeRustcVm.SameOutside.mono (hm1.sameOutside hwf)
      fun q hq ↦ frame_inRange hN N_ge
        (Written.inRange (r := 0) rfl hbnw (by decide) hq))
  have e0 : st1.data.regs.X0.toBitVec = base m0 432 + BitVec.ofNat 64 16 := by
    rw [show st1.data.regs.X0 = st1.data.regs.getXReg .X0 from rfl, hm1.regs .X0 _ rfl]; rfl
  have e2 : st1.data.regs.X2.toBitVec = base m0 432 + BitVec.ofNat 64 80 := by
    rw [show st1.data.regs.X2 = st1.data.regs.getXReg .X2 from rfl, hm1.regs .X2 _ rfl]; rfl
  have e1 : st1.data.regs.X1.toNat = 4 := by
    rw [show st1.data.regs.X1 = st1.data.regs.getXReg .X1 from rfl, ← UInt64.toNat_toBitVec,
      reg_lit hm1 (r := .X1) (n := 4) rfl]; rfl
  have e3 : st1.data.regs.X3.toNat = 16 := by
    rw [show st1.data.regs.X3 = st1.data.regs.getXReg .X3 from rfl, ← UInt64.toNat_toBitVec,
      reg_lit hm1 (r := .X3) (n := 16) rfl]; rfl
  simp only [PcOk] at hpc1
  have lk16 := local_ok (o := 16) (n := 64) hS le_ek (by omega) hfr1.kept hfr1.sp
  have lk80 := local_ok (o := 80) (n := 256) hS le_ek (by omega) hfr1.kept hfr1.sp
  refine Fr.callLocal (o := 80) (n := 256) (X := InRange (base m0 432 + BitVec.ofNat 64 80) 256)
    hfr1 hN le_ek keep_callee (by decide) (by omega) hfrT (fun q hq ↦ .inr hq) hek hpc1 ?_
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun q hq' ↦ ?_, hq.2.2⟩)
    fun m2 hfr2 hq2 hcs2 hs2 ↦ ?_
  · refine ⟨hfr1.stackOk hS rfl le_ek, by rw [e1]; decide, ?_, ?_, ?_⟩
    · unfold SliceOk; rw [e0, e1]; exact lk16
    · unfold SliceOk; rw [e2, e3]; exact lk80
    · rw [e0, e1, e2, e3]
      unfold Apart
      rw [NativeRustcVm.toNat_add_ofNat (by omega), NativeRustcVm.toNat_add_ofNat (by omega)]
      omega
  · rw [e2, e3] at hq'
    exact hq'.elim .inr .inl
  -- after `eq_kernel`: the kernel.
  obtain ⟨hk2, -, hsv2⟩ := hq2
  rw [e1, e3, ite_eq_left_of_eq_true _ _ (eq_true (by decide))] at hk2
  obtain ⟨hx0, -, hker⟩ := hk2
  rw [e2] at hker
  have hsl : slice st1.data st1.data.regs.X0 st1.data.regs.X1 = sp := by
    unfold slice
    rw [e0, e1, ← hsz, ← Array.length_toList, NativeRustcVm.ewsOf_of_ewsAt hsp1,
      Array.toArray_toList]
  rw [hsl] at hker
  have hsp2 : NativeRustcVm.EWsAt m2.dmem (base m0 432 + BitVec.ofNat 64 16) sp.toList :=
    keep_frame hfr1.sp (by have := le_ek; omega) hs2 (by
      rw [NativeRustcVm.length_ewsBytes, Array.length_toList, hsz]; omega) (fun i hi hq ↦ by
        rw [NativeRustcVm.length_ewsBytes, Array.length_toList, hsz] at hi
        exact not_loc (by have := N_ge; omega) (by omega) (by omega) (by omega) hq) hsp1
  have hts2 : TStateAt m2.dmem m0.regs.X1.toBitVec a s3 :=
    ts_keep c hts1 hsv2.2.2
      (call_in_stack hN hfr1.sp le_ek (by omega) hs2)
  have hR2 := hR1.call hcs2
  have f25 : m2.regs.getXReg .X25 = v.c0 := (hcs2 .X25 rfl).trans e25
  have f26 : m2.regs.getXReg .X26 = v.c1 := (hcs2 .X26 rfl).trans e26
  -- `b7`: `eq_kernel` succeeded.
  refine Fr.runBlock hS N_ge rfl hfr2 (b7_in_code.trans hp.1 (by simp [b7])) run_b7 rfl rfl
    (by decide) (by decide) fun st7 hfr7 hd7 hm7 hpc7 ↦ ?_
  have hc7 : SBool.eval (Env.ofMachine m2 [(base m0 432, 432)]) (.not (.bit .W32 (.reg .X0) 0)) =
      false := by
    show (!(low .W32 (m2.regs.getXReg .X0).toBitVec).getLsbD 0) = false
    rw [show m2.regs.getXReg .X0 = m2.regs.X0 from rfl, hx0]; rfl
  simp only [PcOk, hc7, Bool.false_eq_true, ↓reduceIte] at hpc7
  -- `b8`: `dot` of the kernel and the weights.
  refine at_pc hpc7 (Fr.runBlock hS N_ge rfl hfr7 (b8_in_code.trans hp.1 (by simp [b8])) run_b8
    rfl rfl (by decide) (by decide) fun st8 hfr8 hd8 hm8 hpc8 ↦ ?_)
  have hR7 := R6.block hR2 hm7 (by decide)
  have hR8 := R6.block hR7 hm8 (by decide)
  have g25 : st8.data.regs.getXReg .X25 = v.c0 := (mov_reg hm8 rfl).trans ((mov_reg hm7 rfl).trans f25)
  have g26 : st8.data.regs.getXReg .X26 = v.c1 := (mov_reg hm8 rfl).trans ((mov_reg hm7 rfl).trans f26)
  have e80 : st8.data.regs.X0.toBitVec = base m0 432 + BitVec.ofNat 64 80 := by
    rw [show st8.data.regs.X0 = st8.data.regs.getXReg .X0 from rfl, hm8.regs .X0 _ rfl]; rfl
  have e81 : st8.data.regs.X1 = 16 :=
    UInt64.toBitVec_inj.mp (by rw [show st8.data.regs.X1 = st8.data.regs.getXReg .X1 from rfl,
      reg_lit hm8 (r := .X1) (n := 16) rfl]; rfl)
  have e83 : st8.data.regs.X3 = 16 :=
    UInt64.toBitVec_inj.mp (by rw [show st8.data.regs.X3 = st8.data.regs.getXReg .X3 from rfl,
      reg_lit hm8 (r := .X3) (n := 16) rfl]; rfl)
  have e82 : st8.data.regs.X2 = m0.regs.X2 :=
    (mov_reg hm8 (r := .X2) (r' := .X27) rfl).trans hR7.x27
  simp only [PcOk] at hpc8
  refine Fr.callSpec hfr8 hN le_dot keep_callee slots_le hfrT hdot hpc8 ?_
    (fun m' hq ↦ ⟨changes_zero hq.2.1, hq.2.2⟩) fun m3 hfr3 hq3 hcs3 ↦ ?_
  · refine ⟨hfr8.stackOk hS rfl le_dot, ?_, ?_⟩
    · unfold SliceOk; rw [e80, e81]
      exact local_ok (o := 80) (n := 256) hS le_dot (by omega) hfr8.kept hfr8.sp
    · unfold SliceOk; rw [e82, e83]
      exact ⟨Bus.Fr.readable hfr8 hw.1, Bus.Fr.offStack hfr8 hS hw.2 le_dot⟩
  obtain ⟨hd3, hch3, hsv3⟩ := hq3
  have hnotw : ∀ j < 16 * (16 : UInt64).toNat, ¬outsT m0 (m0.regs.X2.toBitVec + BitVec.ofNat 64 j) :=
    fun j hj ↦ NativeRustcVm.Apart.not_inRange hwt hw.1.2 hts0.footprint.1.2
      (NativeRustcVm.inRange_add hj (by have := hw.1.2; unfold NoWrap at this; omega))
  have hkz : (eqKernel sp).size = 16 := by rw [NativeRustcVm.size_eqKernel, hsz]; rfl
  have hsl8 : slice st8.data st8.data.regs.X0 16 = eqKernel sp := by
    unfold slice
    rw [e80, hd8, hd7, show (16 : UInt64).toNat = (eqKernel sp).toList.length by simp [hkz],
      NativeRustcVm.ewsOf_of_ewsAt hker, Array.toArray_toList]
  have hdotv : ewRet m3 = dot (eqKernel sp) (wts m0) := by
    rw [hd3, e81, e82, e83, Bus.Fr.slice_eq hfr8 hS ⟨hw.1, hw.2⟩ hnotw, hsl8]
    rfl
  have hR3 := hR8.call hcs3
  -- `b9`: times the value.
  refine Fr.runBlock hS N_ge rfl hfr3 (b9_in_code.trans hp.1 (by simp [b9])) run_b9 rfl rfl
    (by decide) (by decide) fun st9 hfr9 hd9 hm9 hpc9 ↦ ?_
  have hR9 := R6.block hR3 hm9 (by decide)
  simp only [PcOk] at hpc9
  refine Fr.callSpec hfr9 hN le_mul keep_callee slots_le hfrT hmul hpc9 (hfr9.stackOk hS rfl le_mul)
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.1 fun q h ↦ .inl h, hq.2.2.2⟩)
    fun m4 hfr4 hq4 hcs4 ↦ ?_
  obtain ⟨hm40, hm41, hs4, hsv4⟩ := hq4
  have hprod : (⟨m4.regs.X0, m4.regs.X1⟩ : EW) = dot (eqKernel sp) (wts m0) * v := by
    rw [hm40, hm41]
    have q0 : st9.data.regs.X0 = m3.regs.X0 := mov_reg hm9 (r := .X0) (r' := .X0) rfl
    have q1 : st9.data.regs.X1 = m3.regs.X1 := mov_reg hm9 (r := .X1) (r' := .X1) rfl
    have q2 : st9.data.regs.X2 = v.c0 := (mov_reg hm9 (r := .X2) (r' := .X25) rfl).trans
      ((hcs3 .X25 rfl).trans g25)
    have q3 : st9.data.regs.X3 = v.c1 := (mov_reg hm9 (r := .X3) (r' := .X26) rfl).trans
      ((hcs3 .X26 rfl).trans g26)
    rw [q0, q1, q2, q3]
    show EW.mul (ewRet m3) v = _
    rw [hdotv]
    rfl
  have hR4 := hR9.call hcs4
  -- the memory at the check
  have hsp4 : NativeRustcVm.EWsAt m4.dmem (base m0 432 + BitVec.ofNat 64 16) sp.toList := by
    have h3 : NativeRustcVm.EWsAt m3.dmem (base m0 432 + BitVec.ofNat 64 16) sp.toList :=
      keep_frame (X := fun _ ↦ False) hfr8.sp (by have := le_dot; omega) (changes_zero hch3) (by
        rw [NativeRustcVm.length_ewsBytes, Array.length_toList, hsz]; omega) (fun _ _ h ↦ h)
        (by rw [hd8, hd7]; exact hsp2)
    refine keep_frame (X := fun _ ↦ False) hfr9.sp (by have := le_mul; omega)
      (NativeRustcVm.SameOutside.mono hs4 fun q h ↦ .inl h) (by
        rw [NativeRustcVm.length_ewsBytes, Array.length_toList, hsz]; omega) (fun _ _ h ↦ h)
      (by rw [hd9]; exact h3)
  have hts4 : TStateAt m4.dmem m0.regs.X1.toBitVec a s3 := by
    have h3 : TStateAt m3.dmem m0.regs.X1.toBitVec a s3 :=
      ts_keep c (by rw [hd8, hd7]; exact hts2) hsv3.2.2 (NativeRustcVm.SameOutside.mono hch3
        fun q hq ↦ hq.elim (fun h ↦ absurd h (by unfold InRange; omega))
          (inRange_callee hN hfr8.sp le_dot))
    exact ts_keep c (by rw [hd9]; exact h3) hsv4.2.2
      (NativeRustcVm.SameOutside.mono hs4 fun _ hq ↦ inRange_callee hN hfr9.sp le_mul hq)
  -- `b10`, `b11`: the check, limb by limb.
  refine Fr.runBlock hS N_ge rfl hfr4 (b10_in_code.trans hp.1 (by simp [b10])) run_b10 rfl rfl
    (by decide) (by decide) fun st10 hfr10 hd10 hm10 hpc10 ↦ ?_
  have c10 : SBool.eval (Env.ofMachine m4 [(base m0 432, 432)])
      (.not (.cmp .eq .W64 (.reg .X29) (.reg .X0))) = !decide (cl.c0.toNat = m4.regs.X0.toNat) := by
    show (!(SBool.cmp .eq .W64 (.reg .X29) (.reg .X0)).eval _) = _
    rw [eval_eq_reg, hR4.x29]; rfl
  simp only [PcOk, c10] at hpc10
  have hprod0 : m4.regs.X0 = (dot (eqKernel sp) (wts m0) * v).c0 := by rw [← hprod]
  have hprod1 : m4.regs.X1 = (dot (eqKernel sp) (wts m0) * v).c1 := by rw [← hprod]
  have none_of : (cl == dot (eqKernel sp) (wts m0) * v) = false → ∀ {st : MachineData},
      Fr m0 432 bytecodeShareStack slots keep (outsT m0) st → st.regs.getXReg .X19 = m0.regs.X0 →
      Eventually (step1 Host.exe) (Goal a s0 m0) ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.BytecodeShare.b15Offset)⟩ := fun hf st hfr h19 ↦
    none15 hp h (Bus.Fr.mono hfr fun q hq ↦ outsP_all q (outsT_P q hq)) h19 (by
      rw [hres, hf]; rfl)
  by_cases h0 : cl.c0 = (dot (eqKernel sp) (wts m0) * v).c0
  · rw [← hprod0] at h0
    have hf : (!decide (cl.c0.toNat = m4.regs.X0.toNat)) = false := by rw [h0]; simp
    rw [hf] at hpc10
    simp only [Bool.false_eq_true, ↓reduceIte] at hpc10
    refine at_pc hpc10 (Fr.runBlock hS N_ge rfl hfr10 (b11_in_code.trans hp.1 (by simp [b11]))
      run_b11 rfl rfl (by decide) (by decide) fun st11 hfr11 hd11 hm11 hpc11 ↦ ?_)
    have hR10 := R6.block hR4 hm10 (by decide)
    have c11 : SBool.eval (Env.ofMachine st10.data [(base m0 432, 432)])
        (.not (.cmp .eq .W64 (.reg .X28) (.reg .X1))) =
        !decide (cl.c1.toNat = m4.regs.X1.toNat) := by
      show (!(SBool.cmp .eq .W64 (.reg .X28) (.reg .X1)).eval _) = _
      rw [eval_eq_reg, hR10.x28, mov_reg hm10 (r := .X1) (r' := .X1) rfl]; rfl
    simp only [PcOk, c11] at hpc11
    have hR11 := R6.block hR10 hm11 (by decide)
    by_cases h1 : cl.c1 = (dot (eqKernel sp) (wts m0) * v).c1
    · rw [← hprod1] at h1
      have hf1 : (!decide (cl.c1.toNat = m4.regs.X1.toNat)) = false := by rw [h1]; simp
      rw [hf1] at hpc11
      simp only [Bool.false_eq_true, ↓reduceIte] at hpc11
      have heq : cl = dot (eqKernel sp) (wts m0) * v := by
        rw [← hprod]; cases cl; simp only at h0 h1; rw [h0, h1]
      have hr' : res s0 m0 = some ((sh, slice m0 m0.regs.X3 m0.regs.X4 ++ sp, v), s3) := by
        rw [hres, heq, beq_self_eq_true]; rfl
      have hd' : st11.data.dmem = m4.dmem := hd11.trans hd10
      refine at_pc hpc11 (copy_spec hp h ⟨fun st hc ↦ finish hp h hc (by rw [hd']; exact hsp4)
        hsz (by rw [hd']; exact hts4) hr'⟩ (Bus.Fr.mono hfr11 outsT_P) ⟨hR11.x19, hR11.x20,
        hR11.x21, hR11.x22, hR11.x23, hR11.x24, ?_, ?_⟩)
      · exact (mov_reg hm11 rfl).trans ((mov_reg hm10 rfl).trans ((hcs4 .X25 rfl).trans
          ((mov_reg hm9 rfl).trans ((hcs3 .X25 rfl).trans g25))))
      · exact (mov_reg hm11 rfl).trans ((mov_reg hm10 rfl).trans ((hcs4 .X26 rfl).trans
          ((mov_reg hm9 rfl).trans ((hcs3 .X26 rfl).trans g26))))
    · have hf1 : (!decide (cl.c1.toNat = m4.regs.X1.toNat)) = true := by
        rw [← hprod1] at h1
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
        exact fun h' ↦ h1 (UInt64.toNat_inj.mp h')
      rw [hf1] at hpc11
      simp only [↓reduceIte] at hpc11
      refine at_pc (hpc11.trans (hp.label (j := NativeRustcVmArm.Vm.BytecodeShare.b15Offset) NativeRustcVmArm.Vm.BytecodeShare.label_9_at)) (none_of ?_ hfr11 hR11.x19)
      rw [beq_ew]; simp [h1]
  · have hf : (!decide (cl.c0.toNat = m4.regs.X0.toNat)) = true := by
      rw [← hprod0] at h0
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
      exact fun h' ↦ h0 (UInt64.toNat_inj.mp h')
    rw [hf] at hpc10
    simp only [↓reduceIte] at hpc10
    refine at_pc (hpc10.trans (hp.label (j := NativeRustcVmArm.Vm.BytecodeShare.b15Offset) NativeRustcVmArm.Vm.BytecodeShare.label_9_at)) (none_of ?_ hfr10
      (R6.block hR4 hm10 (by decide)).x19)
    rw [beq_ew]; simp [h0]

end

end NativeRustcVmArm.Bus.BytecodeShare
