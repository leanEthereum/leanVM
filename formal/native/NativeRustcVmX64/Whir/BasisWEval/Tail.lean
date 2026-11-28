module

public import NativeRustcVmX64.Whir.BasisWEval.Loop
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.EqEval.Names

/-!
# `BasisW::eval`: the out-of-domain claim and the result (x86-64)

From `End` (`b21`): the next scale (`b22`), or `0` once the scales run out (`b23`): `A24` at
`NativeRustcVmX64.Vm.BasisWEval.label_19` (`ood_scale`). `b24` calls `eq_eval` on the out-of-domain point (at most 30
coordinates) and the point, `b25` multiplies its weight by the scale, `b26` adds the product to
the sum and stores it at the output, `b27` stores `Some`'s tag, restores the registers and returns
(`finish`). The sum is `BasisW.eval` (`In.eval_eq`).
-/

namespace NativeRustcVmX64.Whir.BasisWEval

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model LeanVM.Parameters
open NativeRustcVmX64.Transcript NativeRustcVm.Whir NativeRustcVm.Layout NativeRustcVm.Ring
open NativeRustcVmX64.Vm.BasisWEval
open NativeRustcVm.Transcript (off off_add off_zero toNat_off OptEWAt)
open LeanVM.Protocol.Verifier (qkeccak Placement)

@[expose] public section

/-- **At `NativeRustcVmX64.Vm.BasisWEval.label_19`** (`b24`): the sum over the weights met (the frame's `24`, `64`), the
next scale (R14, R15). -/
structure A24 (m0 : MachineData) (ba : BasisAddrs) (b : BasisW) (v : Vals) (d : MachineData) :
    Prop where
  base : Base m0 ba 24 d
  w56 : FW m0 d 56 (reg m0 .rsi)
  w24 : FW m0 d 24 (dot b.scales (ws v (xpt m0) v.cs.size)).c0.toBitVec
  w64 : FW m0 d 64 (dot b.scales (ws v (xpt m0) v.cs.size)).c1.toBitVec
  r14 : reg d .r14 = (sAt b.scales (ws v (xpt m0) v.cs.size).size).c0.toBitVec
  r15 : reg d .r15 = (sAt b.scales (ws v (xpt m0) v.cs.size).size).c1.toBitVec

/-- What `BasisW::eval` reaches. -/
abbrev Goal (m0 : MachineData) (b : BasisW) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧ BasisWEvalPost b m0 st.data

end

public section

variable {m0 : MachineData} {ba : BasisAddrs} {b : BasisW} {v : Vals}

theorem inRange_zero {q : BitVec 64} : ¬ NativeRustcVm.InRange 0 0 q := by
  unfold NativeRustcVm.InRange; omega

theorem ewRet_c0 {m : MachineData} {x : EW} (h : ewRet m = x) : reg m .rax = x.c0.toBitVec := by
  rw [← h]; rfl

theorem ewRet_c1 {m : MachineData} {x : EW} (h : ewRet m = x) : reg m .rdx = x.c1.toBitVec := by
  rw [← h]; rfl

variable [Host] {k : Nat}

/-- **The out-of-domain claim's scale**, from `End` at `b21` to `b24`. -/
theorem ood_scale (hp : Placed code k) (h : In m0 ba b v) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BasisWEval.b21Offset)) (he : End m0 ba b v st.data) {R : MachineState → Prop}
    (cont : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BasisWEval.b24Offset) → A24 m0 ba b v st'.data →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hf := he.base.fr
  obtain ⟨hmid, hmem, hk⟩ := ok_b21
  have hwf := h.wf0 hf (ret := 0)
  refine at_pc hpc (h.block hf hwf (inf hp b21_in_code (by simp [b21])) exit_b21 nofun
    (match_body hf ⟨rfl, trivial⟩) hmid (h0_of_nil hmem) fun st1 hm1 hpc1 hf1 ↦ ?_)
  simp only [PcOk, cScale_eval (env := envB m0 st.data [] 0) (j := (ws v (xpt m0) v.cs.size).size)
    he.acc.r13 he.acc.rbp h.scales.1.2 h.scalesPos] at hpc1
  have base1 := he.base.nil hf1 hwf hm1 hmem
  have u56 := he.w56.nil hwf hm1 hmem
  have u24 := he.acc.w24.nil hwf hm1 hmem
  have u64 := he.acc.w64.nil hwf hm1 hmem
  have hsz := h.pre.2.1.scales_size
  by_cases hj : ba.count ≤ (ws v (xpt m0) v.cs.size).size
  · simp only [hj, decide_true, ↓reduceIte] at hpc1
    rw [hp.label NativeRustcVmX64.Vm.BasisWEval.label_11_at] at hpc1
    obtain ⟨hmid3, hmem3, hr14, hr15⟩ := ok_b23
    have hwf3 := h.wf0 hf1 (ret := 0)
    refine at_pc hpc1 (h.block hf1 hwf3 (inf hp b23_in_code (by simp [b23])) exit_b23 nofun
      (match_body hf1 ⟨rfl, trivial⟩) hmid3 (h0_of_nil hmem3) fun st2 hm2 hpc2 hf2 ↦ ?_)
    simp only [PcOk] at hpc2
    have hs0 : sAt b.scales (ws v (xpt m0) v.cs.size).size = 0 := sAt_ge (by omega)
    refine cont st2 hpc2 ⟨base1.nil hf2 hwf3 hm2 hmem3, u56.nil hwf3 hm2 hmem3,
      u24.nil hwf3 hm2 hmem3, u64.nil hwf3 hm2 hmem3, ?_, ?_⟩
    · rw [reg_eval hm2 hr14, hs0]; rfl
    · rw [reg_eval hm2 hr15, hs0]; rfl
  · simp only [hj, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc1
    rw [show k + NativeRustcVmX64.Vm.BasisWEval.b21Offset + b21.length = k + NativeRustcVmX64.Vm.BasisWEval.b22Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.BasisWEval.b21_next]] at hpc1
    have hlt : (ws v (xpt m0) v.cs.size).size < ba.count := by omega
    obtain ⟨hmid3, hmem3, hr14, hr15⟩ := ok_b22
    have hwf3 := h.wf1 (ret := 0) hf1.frame.kept (h.scaleIn hlt)
    have e13 : reg st1.data .r13 = sA ba (ws v (xpt m0) v.cs.size).size := by
      rw [keeps_reg hm1 hk (by simp), he.acc.r13, Nat.min_eq_left (by omega)]
    have hm3 : Match (envB m0 st1.data [(sA ba (ws v (xpt m0) v.cs.size).size, 16)] 0)
        (scaleS .r13) st1.data :=
      match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hf1.frame.rsp_eval, known_ptr rfl e13, trivial⟩
        trivial trivial trivial
    have ⟨s0, s1⟩ := h.scaleAt hf1 hlt
    refine at_pc hpc1 (h.block hf1 hwf3 (inf hp b22_in_code (by simp [b22])) exit_b22 nofun hm3
      hmid3 (h0_of_nil hmem3) fun st2 hm2 hpc2 hf2 ↦ ?_)
    simp only [PcOk] at hpc2
    rw [hp.label NativeRustcVmX64.Vm.BasisWEval.label_19_at] at hpc2
    exact cont st2 hpc2 ⟨base1.nil hf2 hwf3 hm2 hmem3, u56.nil hwf3 hm2 hmem3,
      u24.nil hwf3 hm2 hmem3, u64.nil hwf3 hm2 hmem3,
      (reg_eval hm2 hr14).trans (load_ofMachine (r := 1) (o := 0) rfl s0),
      (reg_eval hm2 hr15).trans (load_ofMachine (r := 1) (o := 8) rfl s1)⟩

/-- **The out-of-domain claim's weight and the result**, from `b24` to the return. -/
theorem finish (hp : Placed code k) (h : In m0 ba b v)
    (heq : Spec (Labels.label NativeRustcVmX64.Vm.EqEval.entryLabel) EqEvalPre EqEvalPost)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BasisWEval.b24Offset)) (ha : A24 m0 ba b v st.data) :
    Eventually (step1 Host.exe) (Goal m0 b) st := by
  have hS := h.stackOk
  have hf := ha.base.fr
  let W := ws v (xpt m0) v.cs.size
  -- b24
  have hoin := h.oodIn
  have ho8 : WhirIn m0 ba.ood 8 basisWEvalStack := WhirIn.mono' hoin (by decide)
  have hbo : NativeRustcVm.Apart (reg m0 .rsi) 56 ba.ood 8 :=
    NativeRustcVm.Apart.mono h.aparts.2.2.1 (Nat.le_refl _) (by unfold basisBytes; omega)
      (Nat.le_refl _) (by unfold eqClaimBytes; omega)
  let ret := (Host.addrOf (k + NativeRustcVmX64.Vm.BasisWEval.b24Offset + b24.length)).toBitVec
  have hwf : (envB m0 st.data [(reg m0 .rsi, 56), (ba.ood, 8)] ret).WF :=
    h.wf2 hf.frame.kept h.basis ho8 hbo
  have hZ : NativeRustcVm.BufEWAt st.data.dmem ba.ood NativeRustcVm.Layout.stackCap v.z.toList :=
    NativeRustcVm.Layout.BufEWAt.of_same h.ood.1 (h.same_of hf hoin) (by decide)
  have hzl : v.z.toList.length ≤ 30 := hZ.1
  have l48 : (envB m0 st.data [(reg m0 .rsi, 56), (ba.ood, 8)] ret).load 1 48 8 = ba.ood :=
    load_ofMachine (r := 1) rfl (h.word hf 6 (by decide))
  have l20 : (envB m0 st.data [(reg m0 .rsi, 56), (ba.ood, 8)] ret).load 2 0 8 =
      v.z.toList.length.toUInt64.toBitVec :=
    load_ofMachine (r := 2) (o := 0) rfl (by rw [off_zero]; exact hZ.2.1)
  have hm : Match (envB m0 st.data [(reg m0 .rsi, 56), (ba.ood, 8)] ret) oodS st.data :=
    match_ofMachine ⟨rfl, rfl, rfl, trivial⟩ ⟨hf.frame.rsp_eval, trivial⟩ trivial trivial
      ⟨ha.w56.load.trans (eval_ptr (i := 1) rfl).symm,
        l48.trans (eval_ptr (i := 2) rfl).symm, trivial⟩
  obtain ⟨hmid, h0, hmiss, hrdi, hrsi, hrdx, hrcx, hk⟩ := ok_b24
  refine at_pc hpc (h.block hf hwf (inf hp b24_in_code (by simp [b24])) exit_b24
    (fun _ _ ↦ rfl) hm hmid h0 fun st1 hm1 hpc1 hf1 ↦ ?_)
  have hw := missWs_spec hmiss
  have hzlt : (v.z.toList.length.toUInt64.toBitVec).toNat < 31 := by
    rw [toNat_bv_toUInt64 (by omega)]; omega
  have edi : reg st1.data .rdi = off ba.ood 8 := (reg_eval hm1 hrdi).trans (rdi24_eval l20 l48 hzlt)
  have esi : reg st1.data .rsi = v.z.toList.length.toUInt64.toBitVec :=
    (reg_eval hm1 hrsi).trans (rsi24_eval l20 hzlt)
  have edx : reg st1.data .rdx = reg m0 .rdx := (reg_eval hm1 hrdx).trans ha.base.w40.load
  have ecx : reg st1.data .rcx = reg m0 .rcx := (reg_eval hm1 hrcx).trans ha.base.w48.load
  have hle : 160 - 16 + eqEvalStack ≤ basisWEvalStack := stack_le.2.2.2.1
  have hzin : WhirIn m0 (off ba.ood 8) (16 * v.z.toList.length) basisWEvalStack :=
    WhirIn.sub hoin (by unfold eqClaimBytes; omega)
  have hpre : EqEvalPre st1.data := by
    refine ⟨h.stackOk_at hf1 (by omega) hle, ?_, ?_⟩
    · unfold SliceOk
      rw [edi, esi, toNat_bv_toUInt64 (by omega)]
      exact h.argIn hf1 (by omega) hle hzin
    · rw [edx, ecx]; exact h.argIn hf1 (by omega) hle h.point
  obtain ⟨hpcc, hretc⟩ := hpc1
  refine Fr.call (c := 16) (Nc := eqEvalStack) (lo := 24) (len := 0) (X := fun _ ↦ False)
    hS N_ge (by omega) hle slots_c16 (by omega) (fun _ h ↦ h.elim) (fun _ h ↦ h.elim) heq hf1
    ⟨hpcc, hretc⟩ hpre
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun _ h ↦ h.elim
      (fun h ↦ absurd h inRange_zero) .inl, hq.2.2⟩)
    fun m2 hf2 hq2 hk2 hcs2 ↦ ?_
  have hz : slice st1.data (reg st1.data .rdi) (reg st1.data .rsi) = v.z := by
    unfold slice
    rw [edi, esi, toNat_bv_toUInt64 (by omega), h.ewsOf_eq hf1 hzin le_rfl]
    have := NativeRustcVm.ewsOf_of_ewsAt h.ood.1.2.2
    rw [this, Array.toArray_toList]
  have hx : slice st1.data (reg st1.data .rdx) (reg st1.data .rcx) = xpt m0 :=
    h.xpt_eq hf1 edx ecx
  have hy := hq2.1
  rw [hz, hx] at hy
  let w := eqEval v.z (xpt m0)
  have kp1 : ∀ {o : Nat} {x : BitVec 64}, FW m0 st.data o x → o ∈ [24, 32, 64] →
      FW m0 m2 o x := fun hx ho ↦
    (hx.block hwf hm1 hmid (by simp at ho; omega) (hw _ ho)).call hk2 (by simp at ho; omega)
      (by simp at ho; omega) (.inr (by simp at ho; omega))
  have f24 := kp1 ha.w24 (by simp)
  have f32 := kp1 ha.base.w32 (by simp)
  have f64 := kp1 ha.w64 (by simp)
  have e14 : reg m2 .r14 = (sAt b.scales W.size).c0.toBitVec :=
    (hcs2 .r14 rfl).trans ((keeps_reg hm1 hk (by simp)).trans ha.r14)
  have e15 : reg m2 .r15 = (sAt b.scales W.size).c1.toBitVec :=
    (hcs2 .r15 rfl).trans ((keeps_reg hm1 hk (by simp)).trans ha.r15)
  rw [show k + NativeRustcVmX64.Vm.BasisWEval.b24Offset + b24.length = k + NativeRustcVmX64.Vm.BasisWEval.b25Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.BasisWEval.b24_next]]
  -- b25
  obtain ⟨hmid5, h05, hmiss5, hrcx5, hrdx5, hrsi5, hrdi5⟩ := ok_b25
  let ret5 := (Host.addrOf (k + NativeRustcVmX64.Vm.BasisWEval.b25Offset + b25.length)).toBitVec
  have hwf5 := h.wf0 hf2 (ret := ret5)
  refine h.block hf2 hwf5 (inf hp b25_in_code (by simp [b25])) exit_b25 (fun _ _ ↦ rfl)
    (match_body hf2 ⟨rfl, trivial⟩) hmid5 h05 fun st3 hm3 hpc3 hf3 ↦ ?_
  have hw5 := missWs_spec hmiss5
  have g0 : reg st3.data .rdi = (sAt b.scales W.size).c0.toBitVec := (reg_eval hm3 hrdi5).trans e14
  have g1 : reg st3.data .rsi = (sAt b.scales W.size).c1.toBitVec := (reg_eval hm3 hrsi5).trans e15
  have g2 : reg st3.data .rdx = w.c0.toBitVec := (reg_eval hm3 hrdx5).trans (ewRet_c0 hy)
  have g3 : reg st3.data .rcx = w.c1.toBitVec := (reg_eval hm3 hrcx5).trans (ewRet_c1 hy)
  have hlem : 160 - 16 + ewMulStack ≤ basisWEvalStack := by have := stack_le.1; omega
  obtain ⟨hpcc3, hretc3⟩ := hpc3
  refine Fr.call (c := 16) (Nc := ewMulStack) (lo := 24) (len := 0) (X := fun _ ↦ False)
    hS N_ge (by omega) hlem slots_c16 (by omega) (fun _ h ↦ h.elim) (fun _ h ↦ h.elim) hmul hf3
    ⟨hpcc3, hretc3⟩ (h.stackOk_at hf3 (by omega) hlem)
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.1 fun _ h ↦ .inl h, hq.2.2.2⟩)
    fun m4 hf4 hq4 hk4 hcs4 ↦ ?_
  obtain ⟨hy0, hy1, -, -⟩ := hq4
  rw [g0, g1, g2, g3] at hy0 hy1
  have kp2 : ∀ {o : Nat} {x : BitVec 64}, FW m0 m2 o x → o ∈ [24, 32, 64] →
      FW m0 m4 o x := fun hx ho ↦
    (hx.block hwf5 hm3 hmid5 (by simp at ho; omega) (hw5 _ ho)).call hk4
      (by simp at ho; omega) (by simp at ho; omega) (.inr (by simp at ho; omega))
  have q24 := kp2 f24 (by simp)
  have q32 := kp2 f32 (by simp)
  have q64 := kp2 f64 (by simp)
  rw [show k + NativeRustcVmX64.Vm.BasisWEval.b25Offset + b25.length = k + NativeRustcVmX64.Vm.BasisWEval.b26Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.BasisWEval.b25_next]]
  -- b26, b27
  let o := reg m0 .rdi
  have hwf6 : (envB m0 m4 [(o, 24)] 0).WF := h.wf1 hf4.frame.kept h.out
  have hm6 : Match (envB m0 m4 [(o, 24)] 0) outS m4 :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hf4.frame.rsp_eval, trivial⟩ trivial trivial
      ⟨q32.load.trans (eval_ptr (i := 1) rfl).symm, trivial⟩
  refine exec_then (inf hp b26_in_code (by simp [b26])) exit_b26 hwf6 nofun hm6
    fun st5 hm5 hpc5 ↦ ?_
  simp only [PcOk] at hpc5
  have hfo : Fr m0 160 basisWEvalStack slots (NativeRustcVm.InRange o 24) 24 m4 :=
    hf4.mono_outs fun _ h ↦ h.elim
  obtain ⟨hepi, hall, t0, t8, t16⟩ := ok_b27
  have hnw : NativeRustcVm.NoWrap o 24 := h.out.1.2
  refine hfo.exit hS N_ge (inf hp b27_in_code (by simp [b27])) exit_b27 hwf6
    (hpc5.trans rfl) hm5 hepi (fun q hq ↦ ?_) fun st6 hm7 hpc7 hrsp7 hso7 hsv7 ↦ ?_
  · obtain ⟨w', hw', b', sz, hb, h1, h2⟩ := hq
    obtain ⟨hr, hle'⟩ := hall w' hw'
    rw [hr] at hb
    cases hb
    rw [NativeRustcVm.Transcript.inRange_iff' hnw]
    omega
  · refine .done _ ⟨hpc7, hrsp7, ?_, ?_, hsv7⟩
    · have hev := h.eval_eq
      have hdot := dot_push_c b.scales W w
      have v0 := wordAt_write hm7 (r := 1) (o := 0) rfl (by omega) (wrote_spec t0)
      have v8 := wordAt_write hm7 (r := 1) (o := 8) rfl (by omega) (wrote_spec t8)
      have v16 := wordAt_write hm7 (r := 1) (o := 16) rfl (by omega) (wrote_spec t16)
      have x8 : UInt64.ofBitVec ((Sym.bin .xor .W64 (.reg .rax) (.load 0 24 8)).eval
          (envB m0 m4 [(o, 24)] 0)) = (b.eval (xpt m0)).c0 := by
        rw [xor_eval (env := envB m0 m4 [(o, 24)] 0) (a := .reg .rax) (b := .load 0 24 8) hy0
          q24.load, hev, hdot.1, UInt64.xor_comm]
      have x16 : UInt64.ofBitVec ((Sym.bin .xor .W64 (.reg .rdx) (.load 0 64 8)).eval
          (envB m0 m4 [(o, 24)] 0)) = (b.eval (xpt m0)).c1 := by
        rw [xor_eval (env := envB m0 m4 [(o, 24)] 0) (a := .reg .rdx) (b := .load 0 64 8) hy1
          q64.load, hev, hdot.2, UInt64.xor_comm]
      rw [x8] at v8
      rw [x16] at v16
      rw [off_zero] at v0
      refine ⟨v0, NativeRustcVm.Transcript.ewAt_iff.mpr ⟨v8, ?_⟩⟩
      rw [NativeRustcVm.Transcript.off_off]
      exact v16
    · refine NativeRustcVm.SameOutside.mono hso7 fun q hq ↦ ?_
      rcases hq with hq | hq
      · exact .inr hq
      · exact .inl ⟨_, List.mem_singleton_self _, hq⟩

end

end NativeRustcVmX64.Whir.BasisWEval
