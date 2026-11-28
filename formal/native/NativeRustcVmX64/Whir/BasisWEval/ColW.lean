module

public import NativeRustcVmX64.Whir.BasisWEval.Col
public import NativeRustcVmX64.Code.Vm.ColumnWeight.Names
public import NativeRustcVmX64.Code.Vm.EWMul.Names

/-!
# `BasisW::eval`: a column claim's weight (x86-64)

From `A16` (`b16`): `b16` pushes the point as `column_weight`'s two stack arguments and calls it on
the placement, the claim's point (at most 36 coordinates) and the stack's log-size (at most 30),
its `Option<EW>` at the frame's `80`, `Some` since `36 + 30 ≤ 66`; `b17` drops the argument words,
`b18` multiplies the weight by the scale, `b19` adds the product to the sum and reloads the
placements' address: `Mid i (i + 1)` at `b10` (`col_weight`).
-/

namespace NativeRustcVmX64.Whir.BasisWEval

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model LeanVM.Parameters
open NativeRustcVmX64.Transcript NativeRustcVm.Whir NativeRustcVm.Layout NativeRustcVm.Ring
open NativeRustcVmX64.Vm.BasisWEval
open NativeRustcVm.Transcript (off off_add off_zero toNat_off OptEWAt)
open LeanVM.Protocol.Verifier (qkeccak Placement)

public section

variable {m0 : MachineData} {ba : BasisAddrs} {b : BasisW} {v : Vals}

theorem missWs4 {S : SState} {l : List Nat} (h : missWs l S = true) (hs : [32, 40, 48, 72] ⊆ l) :
    missWs [32, 40, 48, 72] S = true := by
  unfold missWs at h ⊢
  rw [List.all_eq_true] at h ⊢
  exact fun o ho ↦ h o (hs ho)

/-- The areas `b16` reads apart. -/
theorem In.apart16 (h : In m0 ba b v) {i : Nat} (hi : i < v.cs.size) :
    NativeRustcVm.Apart (cA ba i) 608 ba.layout 24 := by
  have hL := h.layoutIn
  have hC := h.claimsIn
  have hle := h.claims.len_le
  unfold claimCap at hle
  have := apart_sub (o := 0) (n' := 24) (o' := 8 + 608 * i) (m' := 608) h.aparts.2.2.2 hL.1.2
    hC.1.2 (by unfold layoutBytes; omega) (by unfold claimsBytes columnClaimBytes claimCap; omega)
  rw [off_zero] at this
  exact Apart.symm' this

/-- The weight's sum: the product xored in. -/
theorem xor_eval [Labels] {env : Env} {a b : Sym} {x y : UInt64} (ha : a.eval env = x.toBitVec)
    (hb : b.eval env = y.toBitVec) : (Sym.bin .xor .W64 a b).eval env = (x ^^^ y).toBitVec := by
  simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, ha, hb, UInt64.toBitVec_xor]

variable [Host] {k : Nat}

/-- **Column claim `i`'s weight**, from `b16` to `b10`. -/
theorem col_weight (hp : Placed code k) (h : In m0 ba b v)
    (hcw : Spec (Labels.label NativeRustcVmX64.Vm.ColumnWeight.entryLabel) ColumnWeightPre ColumnWeightPost)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {i : Nat} {pl : Placement}
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BasisWEval.b16Offset)) (ha : A16 m0 ba b v i pl st.data)
    {R : MachineState → Prop}
    (cont : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BasisWEval.b10Offset) →
      Mid m0 ba b v i (i + 1) st'.data → Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hS := h.stackOk
  have hf := ha.base.fr
  have hi := ha.ilt
  have hcin := h.claimIn hi
  have hcl := h.claimAt hf hi
  have hLa := h.layoutAt hf
  have hL24 : WhirIn m0 ba.layout 24 basisWEvalStack := WhirIn.mono' h.layoutIn (by decide)
  let ret := (Host.addrOf (k + NativeRustcVmX64.Vm.BasisWEval.b16Offset + b16.length)).toBitVec
  have hwf : (envB m0 st.data [(cA ba i, 608), (ba.layout, 24)] ret).WF :=
    h.wf2 hf.frame.kept hcin hL24 (h.apart16 hi)
  have hm : Match (envB m0 st.data [(cA ba i, 608), (ba.layout, 24)] ret) cwS st.data :=
    match_ofMachine ⟨rfl, rfl, rfl, trivial⟩ ⟨hf.frame.rsp_eval, ha.r12.trans (cA_16 ba i), trivial⟩
      trivial trivial ⟨ha.base.w72.load.trans (eval_ptr (i := 2) rfl).symm, trivial⟩
  have hplen := hcl.point.1
  have l8 : (envB m0 st.data [(cA ba i, 608), (ba.layout, 24)] ret).load 1 8 8 =
      v.cs[i].point.toList.length.toUInt64.toBitVec :=
    load_ofMachine (r := 1) (o := 8) rfl hcl.point.2.1
  have hlt : ((envB m0 st.data [(cA ba i, 608), (ba.layout, 24)] ret).load 1 8 8).toNat < 37 := by
    rw [l8, toNat_bv_toUInt64 (by unfold pointCap at hplen; omega)]
    unfold pointCap at hplen; omega
  have l16 : (envB m0 st.data [(cA ba i, 608), (ba.layout, 24)] ret).load 2 16 8 =
      v.L.stackLog.toUInt64.toBitVec :=
    load_ofMachine (r := 2) (o := 16) rfl hLa.stack_log
  obtain ⟨hmid, h0, hmiss, w8, w16, hrcx, hr8, hrdi, hr9, hr12, hk⟩ := ok_b16
  refine at_pc hpc (h.block hf hwf (inf hp b16_in_code (by simp [b16])) exit_b16
    (fun _ _ ↦ rfl) hm hmid h0 fun st1 hm1 hpc1 hf1 ↦ ?_)
  have hw := missWs_spec hmiss
  have hb1 : Base m0 ba 0 st1.data :=
    ha.base.block hf1 hwf hm1 hmid (missWs4 hmiss (by simp))
  have hlen' : v.cs[i].point.toList.length < 2 ^ 64 := by unfold pointCap at hplen; omega
  have e8 : reg st1.data .r8 = v.cs[i].point.toList.length.toUInt64.toBitVec :=
    (reg_eval hm1 hr8).trans ((r816_eval hlt).trans l8)
  have ercx : reg st1.data .rcx = off (cA ba i) 16 :=
    (reg_eval hm1 hrcx).trans ((rcx16_eval hlt).trans rfl)
  have er9 : reg st1.data .r9 = v.L.stackLog.toUInt64.toBitVec := (reg_eval hm1 hr9).trans l16
  have erdi : reg st1.data .rdi = off (fb m0) 80 := (reg_eval hm1 hrdi).trans (eval_ptr0 80)
  have ersi : reg st1.data .rsi = pl.variableCount.toUInt64.toBitVec :=
    (keeps_reg hm1 hk (by simp)).trans ha.rsi
  have erdx : reg st1.data .rdx = pl.index.toUInt64.toBitVec :=
    (keeps_reg hm1 hk (by simp)).trans ha.rdx
  have ha0 : stackArg st1.data 0 = reg m0 .rdx :=
    stackArg_of hf1 (FW.wrote hm1 (by omega) w8 ha.base.w40.load)
  have ha1 : stackArg st1.data 1 = reg m0 .rcx :=
    stackArg_of hf1 (FW.wrote hm1 (by omega) w16 ha.base.w48.load)
  have hle : 160 - 0 + columnWeightStack ≤ basisWEvalStack := stack_le.2.2.1
  have hpt : NativeRustcVm.EWsAt st1.data.dmem (off (cA ba i) 16) v.cs[i].point.toList := by
    have := (h.claimAt hf1 hi).point.2.2
    rwa [off_add] at this
  have hpre : ColumnWeightPre st1.data := by
    refine ⟨h.stackOk_at hf1 (by omega) hle, h.argsOk hf1, ?_, ?_, ?_, ?_⟩
    · unfold SliceOk
      rw [ercx, e8, toNat_bv_toUInt64 hlen']
      exact h.argIn hf1 (by omega) hle (WhirIn.sub hcin (by unfold pointCap at hplen; omega))
    · rw [ha0, ha1]; exact h.argIn hf1 (by omega) hle h.point
    · rw [erdi]; exact h.optOut hf1 hle
    · rw [e8, toNat_bv_toUInt64 hlen']; unfold pointCap at hplen; omega
  obtain ⟨hpcc, hretc⟩ := hpc1
  refine Fr.call (c := 0) (Nc := columnWeightStack) (lo := 80) (len := 24)
    (X := NativeRustcVm.InRange (off (fb m0) 80) 24) hS N_ge (by omega) hle slots_c0 (by omega)
    (fun _ h ↦ h.elim) (fun _ h ↦ .inr h) hcw hf1 ⟨hpcc, hretc⟩ hpre
    (fun m' hq ↦ ⟨?_, hq.2.2⟩) fun m2 hf2 hq2 hk2 hcs2 ↦ ?_
  · refine NativeRustcVm.SameOutside.mono hq.2.1 fun q hq ↦ ?_
    rcases hq with hq | hq
    · rw [erdi] at hq; exact .inr hq
    · exact .inl hq
  -- the weight
  have hlog := h.log
  have hslt := hLa.stack_log_lt
  have hfit : (reg st1.data .r8).toNat + ((reg st1.data .r9).toNat - (reg st1.data .rsi).toNat)
      ≤ stackPointOut := by
    rw [e8, er9, toNat_bv_toUInt64 hlen', toNat_bv_toUInt64 hslt]
    unfold stackPointOut; unfold pointCap at hplen; omega
  have epl : placementArg st1.data = pl := placementArg_eq ha.pl_lt ersi erdx
  have ept : slice st1.data (reg st1.data .rcx) (reg st1.data .r8) = v.cs[i].point := by
    unfold slice
    rw [ercx, e8, toNat_bv_toUInt64 hlen', NativeRustcVm.ewsOf_of_ewsAt hpt, Array.toArray_toList]
  have ex : slice st1.data (stackArg st1.data 0) (stackArg st1.data 1) = xpt m0 :=
    h.xpt_eq hf1 ha0 ha1
  have hout := hq2.1
  simp only [hfit, ↓reduceIte] at hout
  rw [epl, ept, ex, er9, toNat_bv_toUInt64 hslt, erdi] at hout
  obtain ⟨t80, t88, t96⟩ := optSome hout
  let w := eqEval (stackPoint pl v.cs[i].point v.L.stackLog) (xpt m0)
  have hb2 : Base m0 ba 8 m2 := hb1.call hf2 hk2 (by omega) (.inl (by omega))
  have f24 : FW m0 m2 24 (dot b.scales (ws v (xpt m0) i)).c0.toBitVec :=
    (ha.w24.block hwf hm1 hmid (by omega) (hw 24 (by simp))).call hk2 (by omega) (by omega)
      (.inl (by omega))
  have f64 : FW m0 m2 64 (dot b.scales (ws v (xpt m0) i)).c1.toBitVec :=
    (ha.w64.block hwf hm1 hmid (by omega) (hw 64 (by simp))).call hk2 (by omega) (by omega)
      (.inl (by omega))
  have f56 : FW m0 m2 56 (reg m0 .rsi) :=
    (ha.w56.block hwf hm1 hmid (by omega) (hw 56 (by simp))).call hk2 (by omega) (by omega)
      (.inl (by omega))
  have f104 : FW m0 m2 104 (off ba.layout 120) :=
    (ha.w104.block hwf hm1 hmid (by omega) (hw 104 (by simp))).call hk2 (by omega) (by omega)
      (.inr (by omega))
  have k2 : ∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15], reg m2 r = reg st.data r :=
    fun r hr ↦ (hcs2 r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)).trans
      (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        · exact keeps_reg hm1 hk (by simp)
        · exact keeps_reg hm1 hk (by simp)
        · exact (reg_eval hm1 hr12).trans (hm.regs .r12 _ rfl).symm
        · exact keeps_reg hm1 hk (by simp)
        · exact keeps_reg hm1 hk (by simp)
        · exact keeps_reg hm1 hk (by simp))
  rw [show k + NativeRustcVmX64.Vm.BasisWEval.b16Offset + b16.length = k + NativeRustcVmX64.Vm.BasisWEval.b17Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.BasisWEval.b16_next]]
  -- b17
  obtain ⟨hmid7, hmem7, hk7⟩ := ok_b17
  have hwf7 := h.wf0 hf2 (ret := 0)
  refine h.block hf2 hwf7 (inf hp b17_in_code (by simp [b17])) exit_b17 nofun
    (match_body hf2 ⟨rfl, trivial⟩) hmid7 (h0_of_nil hmem7) fun st3 hm3 hpc3 hf3 ↦ ?_
  simp only [PcOk, tag_false t80, Bool.false_eq_true, ↓reduceIte] at hpc3
  rw [show k + NativeRustcVmX64.Vm.BasisWEval.b17Offset + b17.length = k + NativeRustcVmX64.Vm.BasisWEval.b18Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.BasisWEval.b17_next]] at hpc3
  have hb3 := hb2.nil hf3 hwf7 hm3 hmem7
  have g24 := f24.nil hwf7 hm3 hmem7
  have g64 := f64.nil hwf7 hm3 hmem7
  have g56 := f56.nil hwf7 hm3 hmem7
  have g104 := f104.nil hwf7 hm3 hmem7
  have g88 := t88.nil hwf7 hm3 hmem7
  have g96 := t96.nil hwf7 hm3 hmem7
  have k3 : ∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15], reg st3.data r = reg st.data r :=
    fun r hr ↦ (keeps_reg hm3 hk7 hr).trans (k2 r hr)
  -- b18
  obtain ⟨hmid8, h08, hmiss8, hrcx8, hrdx8, hrsi8, hrdi8, hk8⟩ := ok_b18
  let ret8 := (Host.addrOf (k + NativeRustcVmX64.Vm.BasisWEval.b18Offset + b18.length)).toBitVec
  have hwf8 := h.wf0 hf3 (ret := ret8)
  refine at_pc hpc3 (h.block hf3 hwf8 (inf hp b18_in_code (by simp [b18])) exit_b18
    (fun _ _ ↦ rfl) (match_body hf3 ⟨rfl, trivial⟩) hmid8 h08 fun st4 hm4 hpc4 hf4 ↦ ?_)
  have hw8 := missWs_spec hmiss8
  have hb4 := hb3.block hf4 hwf8 hm4 hmid8 (missWs4 hmiss8 (by simp))
  have e0 : reg st4.data .rdi = (sAt b.scales (ws v (xpt m0) i).size).c0.toBitVec :=
    (reg_eval hm4 hrdi8).trans ((k3 .r14 (by simp)).trans ha.r14)
  have e1 : reg st4.data .rsi = (sAt b.scales (ws v (xpt m0) i).size).c1.toBitVec :=
    (reg_eval hm4 hrsi8).trans ((k3 .r15 (by simp)).trans ha.r15)
  have e2 : reg st4.data .rdx = w.c0.toBitVec := (reg_eval hm4 hrdx8).trans g88.load
  have e3 : reg st4.data .rcx = w.c1.toBitVec := (reg_eval hm4 hrcx8).trans g96.load
  have k4 : ∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13], reg st4.data r = reg st.data r :=
    fun r hr ↦ (keeps_reg hm4 hk8 hr).trans (k3 r (mem_sub (by decide) hr))
  have hlem : 160 - 16 + ewMulStack ≤ basisWEvalStack := by have := stack_le.1; omega
  obtain ⟨hpcc4, hretc4⟩ := hpc4
  refine Fr.call (c := 16) (Nc := ewMulStack) (lo := 24) (len := 0) (X := fun _ ↦ False)
    hS N_ge (by omega) hlem slots_c16 (by omega) (fun _ h ↦ h.elim) (fun _ h ↦ h.elim) hmul hf4
    ⟨hpcc4, hretc4⟩ (h.stackOk_at hf4 (by omega) hlem)
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.1 fun _ h ↦ .inl h, hq.2.2.2⟩)
    fun m5 hf5 hq5 hk5 hcs5 ↦ ?_
  obtain ⟨hy0, hy1, -, -⟩ := hq5
  rw [e0, e1, e2, e3] at hy0 hy1
  have hb5 : Base m0 ba 24 m5 := hb4.call hf5 hk5 (by omega) (.inr (by omega))
  have kp : ∀ {o : Nat} {x : BitVec 64}, FW m0 st3.data o x → o + 8 ≤ 168 → 24 ≤ o →
      o ∈ [24, 32, 40, 48, 56, 64, 72, 104] → FW m0 m5 o x := fun hx ho h24 hmo ↦
    (hx.block hwf8 hm4 hmid8 ho (hw8 _ hmo)).call hk5 (by omega) ho (.inr (by omega))
  have h24 := kp g24 (by omega) (by omega) (by simp)
  have h64 := kp g64 (by omega) (by omega) (by simp)
  have h56 := kp g56 (by omega) (by omega) (by simp)
  have h104 := kp g104 (by omega) (by omega) (by simp)
  have k5 : ∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13], reg m5 r = reg st.data r :=
    fun r hr ↦ (hcs5 r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> rfl)).trans
      (k4 r hr)
  rw [show k + NativeRustcVmX64.Vm.BasisWEval.b18Offset + b18.length = k + NativeRustcVmX64.Vm.BasisWEval.b19Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.BasisWEval.b18_next]]
  -- b19
  obtain ⟨hmid9, h09, w64', w24', hmiss9, hrcx9, hk9⟩ := ok_b19
  have hwf9 := h.wf0 hf5 (ret := 0)
  refine h.block hf5 hwf9 (inf hp b19_in_code (by simp [b19])) exit_b19 nofun
    (match_body hf5 ⟨rfl, trivial⟩) hmid9 h09 fun st6 hm6 hpc6 hf6 ↦ ?_
  simp only [PcOk] at hpc6
  rw [hp.label NativeRustcVmX64.Vm.BasisWEval.label_15_at] at hpc6
  have hw9 := missWs_spec hmiss9
  have hws : ws v (xpt m0) (i + 1) = (ws v (xpt m0) i).push w := by
    rw [ws_succ _ _ hi, ha.hpl]
  have hdot := dot_push_c b.scales (ws v (xpt m0) i) w
  refine cont st6 hpc6 {
    base := hb5.block hf6 hwf9 hm6 hmid9 (missWs4 hmiss9 (by simp))
    w56 := h56.block hwf9 hm6 hmid9 (by omega) (hw9 56 (by simp))
    w104 := h104.block hwf9 hm6 hmid9 (by omega) (hw9 104 (by simp))
    acc := {
      w24 := FW.wrote hm6 (by omega) w24' (by rw [hws, hdot.1]; exact xor_eval h24.load hy0)
      w64 := FW.wrote hm6 (by omega) w64' (by rw [hws, hdot.2]; exact xor_eval h64.load hy1)
      r13 := by
        rw [keeps_reg hm6 hk9 (by simp), k5 .r13 (by simp), hws, Array.size_push]
        exact ha.r13
      rbp := (keeps_reg hm6 hk9 (by simp)).trans ((k5 .rbp (by simp)).trans ha.rbp) }
    ilt := hi
    rbx := by rw [keeps_reg hm6 hk9 (by simp), k5 .rbx (by simp)]; exact ha.rbx
    r12 := (keeps_reg hm6 hk9 (by simp)).trans ((k5 .r12 (by simp)).trans ha.r12)
    rcx := (reg_eval hm6 hrcx9).trans h104.load }

end

end NativeRustcVmX64.Whir.BasisWEval
