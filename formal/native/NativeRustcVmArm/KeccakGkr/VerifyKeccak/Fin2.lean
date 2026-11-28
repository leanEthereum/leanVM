module

public import NativeRustcVmArm.Code.Vm.Dot.Names
public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.MultilinearEvalByOfMultilinearEval.Names
public import NativeRustcVmArm.KeccakGkr.VerifyKeccak.Fin1

/-!
# `verify_keccak`: the final check

`b61`: `multilinear_eval(claim.mu, low)`; `b62`: its value into X19, X20, `dot(rows[0], slices)`;
`b63`: their product (`EW::mul`); `b64`, `b65`: the product against the second opening's value,
limb by limb. At `b66` (`AtX`).
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyKeccak

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Ring
open NativeRustcVm.Transcript NativeRustcVmArm.Vm.VerifyKeccak
open NativeRustcVm.KeccakGkr (ClaimAt WeightsAt)

public section

/-- Registers a block keeps symbolically and a call keeps (callee-saved). -/
theorem regs_keptL [Labels] {env : Env} {S0 S : SState} {m st m2 : MachineData} (L : List XReg)
    (hL : L.all calleeSaved = true) (hm0 : Match env S0 m) (hm : Match env S st)
    (h0 : L.all (fun r ↦ (S0.reg r).isSome && S.reg r == S0.reg r) = true)
    (hcs : ∀ r, calleeSaved r = true → m2.regs.getXReg r = st.regs.getXReg r) :
    ∀ r ∈ L, m2.regs.getXReg r = m.regs.getXReg r :=
  fun r hr ↦ (hcs r (List.all_eq_true.mp hL r hr)).trans (Match.regs_keep hm0 hm L h0 r hr)

theorem inRange_zero {x q : BitVec 64} (h : InRange x 0 q) : False := by
  unfold InRange at h; omega

/-- The registers the final check keeps. -/
@[expose] def f2L : List XReg := [.X21, .X22, .X23, .X24]

/-- The registers the comparisons keep. -/
@[expose] def f3L : List XReg := [.X1, .X21, .X22, .X23, .X24]

variable [Host] {k : Nat} {a : DecArea} {s : TState} {cs : Array ColumnClaimW}
  {inst output : Array EW} {m0 : MachineData}

/-- **The final check** (`b61` to `b65`). -/
theorem stepFin2 (hp : Placed code k) (h : P0 a s cs inst output m0) (hn : Nums a inst m0)
    (hmle : Spec (Labels.label NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.entryLabel) MleOfMultilinearEvalPre
      MleOfMultilinearEvalPost)
    (hdot : Spec (Labels.label NativeRustcVmArm.Vm.Dot.entryLabel) DotPre DotPost)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {m : MachineData} {s1 s3 : TState} {cj : KeccakClaimW} {outs : Array ColumnClaimW}
    {low sl ws xs : Array EW} {v : EW}
    (hy : AtY a s cs inst output m0 m s1 s3 cj outs low sl ws v xs)
    (cont : ∀ m', AtX a s cs inst output m0 m' s3 cj outs low sl xs →
      Eventually (step1 Host.exe) (Goal a s cs inst output m0) ⟨m', Host.addrOf (k + NativeRustcVmArm.Vm.VerifyKeccak.b66Offset)⟩) :
    Eventually (step1 Host.exe) (Goal a s cs inst output m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyKeccak.b61Offset)⟩ := by
  have hN := hn.hN
  have hSP := m0.regs.SP.toNat_lt
  have hwf := envM_wf hn hy.fr
  have hmu := hy.claim.2.1
  have hmul16 := hmu.1
  rw [show NativeRustcVm.KeccakGkr.off (loc m0 960) NativeRustcVm.KeccakGkr.muOff =
    loc m0 976 from loc_add m0 960 16] at hmu
  have hmuw := hmu.2.1
  have hmue := hmu.2.2
  rw [show loc m0 976 + 8#64 = loc m0 984 from loc_add m0 976 8] at hmue
  have l976 : (Sym.load 0 976 8).eval (envM m0 m) = cj.mu.toList.length.toUInt64.toBitVec :=
    Sumcheck.load_word hmuw
  have hmus : cj.mu.toList.length ≤ 16 := hmul16
  have hlt : ((Sym.load 0 976 8).eval (envM m0 m)).toNat < 17 := by
    rw [l976, u64_toNat (by omega)]; omega
  have ex0 : (Sym.ite (.cmp .ult .W64 (.load 0 976 8) (.lit 17)) (.load 0 976 8) (.lit 0)).eval
      (envM m0 m) = cj.mu.toList.length.toUInt64.toBitVec := by
    rw [eval_ite_lt (by decide) hlt, l976]
  -- `b61`
  refine callC hn (b61_in_code.trans hp.1 (by simp [b61])) run_b61 hy.fr (matchM hn hy.fr) hwf
    rfl (Lb := []) (L := []) (O := []) (lo := 0) (n := 0) (by decide) (by decide) (by decide)
    (by decide) (by decide) hmle (fun st hm1 hfr1 ↦ ?_) (fun st m' hm1 hfr1 hq ↦ ?_)
    fun st m2 hm1 hfr1 hq hfr2 hcs hb hc hkt ↦ ?_
  all_goals
    have hd : st.dmem = m.dmem := hm1.dmem_eq hwf rfl
    have e0 : st.regs.X0 = cj.mu.toList.length.toUInt64 := reg_of hm1 (r := .X0) rfl ex0
    have e2 : st.regs.X2 = cj.mu.toList.length.toUInt64 := reg_of hm1 (r := .X2) rfl ex0
    have e1 : st.regs.X1.toBitVec = loc m0 984 := by
      rw [show st.regs.X1 = st.regs.getXReg .X1 from rfl, hm1.regs .X1 _ rfl,
        eval_ite_lt (by decide) hlt]
      exact eval_ptr0
    have e3 : st.regs.X3.toBitVec = loc m0 3176 := reg_loc hm1 (r := .X3) (o := 3176) rfl
    have e4 : st.regs.X4 = (4 : UInt64) := reg_of hm1 (r := .X4) (v := .lit 4) rfl rfl
  · have hms : mleStack = 1824 := rfl
    refine ⟨stackOk_of hn hfr1 (by decide), e0.trans e2.symm, by rw [e4]; decide, ?_, ?_⟩
    · unfold SliceOk
      rw [e2, u64_toNat' (by omega), e1]
      refine ⟨⟨frame_mapped' hn hfr1 (by omega), loc_noWrap hn (by omega)⟩, ?_⟩
      unfold OffStack Apart
      rw [sb_toNat hn.hN hfr1 (by decide), loc_toNat hn.hN (by decide)]; omega
    · unfold SliceOk
      rw [e3, e4]
      refine ⟨⟨frame_mapped' hn hfr1 (by decide), loc_noWrap hn (by decide)⟩, ?_⟩
      unfold OffStack Apart
      rw [sb_toNat hn.hN hfr1 (by decide), loc_toNat hn.hN (by decide)]; omega
  · obtain ⟨-, hs, hsv⟩ := hq
    refine ⟨NativeRustcVm.SameOutside.mono hs fun q hq ↦ ?_, hsv⟩
    rcases hq with hq | hq
    · exact (inRange_zero hq).elim
    · exact ws_stk hn hfr1 (by decide) hq
  obtain ⟨hret, -, -⟩ := hq
  have hsl1 : slice st st.regs.X1 st.regs.X2 = cj.mu := by
    unfold slice
    rw [e1, e2, u64_toNat' (by omega), hd, NativeRustcVm.ewsOf_of_ewsAt hmue,
      Array.toArray_toList]
  have hsl2 : slice st st.regs.X3 st.regs.X4 = low := by
    unfold slice
    rw [e3, e4, show (4 : UInt64).toNat = low.toList.length by simp [hy.lowsz], hd,
      NativeRustcVm.ewsOf_of_ewsAt hy.lowv, Array.toArray_toList]
  rw [hsl1, hsl2] at hret
  have T1 := hb.trans hc
  have k1 := regs_keptL f2L (by decide) (matchM hn hy.fr) hm1 (by decide) hcs
  rw [show k + NativeRustcVmArm.Vm.VerifyKeccak.b61Offset + b61.length = k + NativeRustcVmArm.Vm.VerifyKeccak.b62Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyKeccak.b61_next]]
  -- `b62`
  have hwf2 := envM_wf hn hfr2
  have l64 : (Sym.load 0 64 8).eval (envM m0 m2) = scA m0 + BitVec.ofNat 64 140288 :=
    Sumcheck.load_word (T1.word hn (by decide) (by decide) (by decide) hy.w64)
  have l72 : (envM m0 m2).load 0 72 8 = oA m0 :=
    Sumcheck.load_word (T1.word hn (by decide) (by decide) (by decide) hy.w72)
  refine callC hn (b62_in_code.trans hp.1 (by simp [b62])) run_b62 hfr2 (matchM hn hfr2) hwf2
    rfl (Lb := []) (L := []) (O := []) (lo := 0) (n := 0) (by decide) (by decide) (by decide)
    (by decide) (by decide) hdot (fun st3 hm3 hfr1 ↦ ?_) (fun st3 m' hm3 hfr1 hq ↦ ?_)
    fun st3 m3 hm3 hfr1 hq hfr3 hcs3 hb3 hc3 hkt3 ↦ ?_
  all_goals
    have hd3 : st3.dmem = m2.dmem := hm3.dmem_eq hwf2 rfl
    have e0 : st3.regs.X0.toBitVec = scA m0 + BitVec.ofNat 64 140288 := by
      rw [show st3.regs.X0 = st3.regs.getXReg .X0 from rfl, hm3.regs .X0 _ rfl]; exact l64
    have e1 : st3.regs.X1 = (64 : UInt64) := reg_of hm3 (r := .X1) (v := .lit 64) rfl rfl
    have e2 : st3.regs.X2.toBitVec = oA m0 + BitVec.ofNat 64 584 := by
      rw [show st3.regs.X2 = st3.regs.getXReg .X2 from rfl, hm3.regs .X2 _ rfl]
      simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, l72]
    have e3 : st3.regs.X3 = (64 : UInt64) := reg_of hm3 (r := .X3) (v := .lit 64) rfl rfl
  · have hds : dotStack = 640 := rfl
    refine ⟨stackOk_of hn hfr1 (by decide), ?_, ?_⟩ <;> unfold SliceOk OffStack
    · rw [e0, e1, show (64 : UInt64).toNat = 64 from rfl]
      refine ⟨readable_of (ok_sc h) hn.sW hfr1.kept (by decide), ?_⟩
      unfold Apart; rw [scN hn (by decide), sb_toNat hn.hN hfr1 (by decide)]
      obtain h1 | h1 := hn.sS <;> omega
    · rw [e2, e3, show (64 : UInt64).toNat = 64 from rfl]
      refine ⟨readable_of (ok_out h) hn.oW hfr1.kept (by decide), ?_⟩
      unfold Apart; rw [oN hn (by decide), sb_toNat hn.hN hfr1 (by decide)]
      obtain h1 | h1 := hn.oS <;> omega
  · obtain ⟨-, hs, hsv⟩ := hq
    refine ⟨NativeRustcVm.SameOutside.mono hs fun q hq ↦ ?_, hsv⟩
    rcases hq with hq | hq
    · exact (inRange_zero hq).elim
    · exact ws_stk hn hfr1 (by decide) hq
  obtain ⟨hret3, -, -⟩ := hq
  have hrows2 : NativeRustcVm.EWsAt m2.dmem (scA m0 + BitVec.ofNat 64 140288) ws.toList :=
    T1.ewsOut hn (by decide) (by decide) (i := 1) (o := 140288) (k := 1024)
    (by decide) (by decide) (by decide) (by decide) (by simp [Array.length_toList, hy.wsz]) hy.rows
  have hxs2 : NativeRustcVm.EWsAt m2.dmem (oA m0 + BitVec.ofNat 64 584) xs.toList :=
    T1.ewsOut hn (by decide) (by decide) (i := 3) (o := 584) (k := 1024)
    (by decide) (by decide) (by decide) (by decide) (by simp [Array.length_toList, hy.xsz])
    hy.slices
  have hsl3 : slice st3 st3.regs.X0 st3.regs.X1 = ws := by
    unfold slice
    rw [e0, e1, show (64 : UInt64).toNat = ws.toList.length by simp [hy.wsz], hd3,
      NativeRustcVm.ewsOf_of_ewsAt hrows2, Array.toArray_toList]
  have hsl4 : slice st3 st3.regs.X2 st3.regs.X3 = xs := by
    unfold slice
    rw [e2, e3, show (64 : UInt64).toNat = xs.toList.length by simp [hy.xsz], hd3,
      NativeRustcVm.ewsOf_of_ewsAt hxs2, Array.toArray_toList]
  rw [hsl3, hsl4] at hret3
  have T2 := hb3.trans hc3
  have k2 := regs_keptL f2L (by decide) (matchM hn hfr2) hm3 (by decide) hcs3
  have x19 : m3.regs.getXReg .X19 = (multilinearEval cj.mu low).c0 := by
    rw [hcs3 .X19 rfl]
    exact (reg_of hm3 (r := .X19) (v := .reg .X0) rfl rfl).trans (congrArg EW.c0 hret)
  have x20 : m3.regs.getXReg .X20 = (multilinearEval cj.mu low).c1 := by
    rw [hcs3 .X20 rfl]
    exact (reg_of hm3 (r := .X20) (v := .reg .X1) rfl rfl).trans (congrArg EW.c1 hret)
  rw [show k + NativeRustcVmArm.Vm.VerifyKeccak.b62Offset + b62.length = k + NativeRustcVmArm.Vm.VerifyKeccak.b63Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyKeccak.b62_next]]
  -- `b63`
  have hwf3 := envM_wf hn hfr3
  refine callC hn (b63_in_code.trans hp.1 (by simp [b63])) run_b63 hfr3 (matchM hn hfr3) hwf3
    rfl (Lb := []) (L := []) (O := []) (lo := 0) (n := 0) (by decide) (by decide) (by decide)
    (by decide) (by decide) hmul (fun st hm1 hfr1 ↦ stackOk_of hn hfr1 (by decide))
    (fun st m' hm1 hfr1 hq ↦ ?_) fun st4 m4 hm4 hfr4a hq hfr4 hcs4 hb4 hc4 hkt4 ↦ ?_
  · obtain ⟨-, -, hs, hsv⟩ := hq
    exact ⟨NativeRustcVm.SameOutside.mono hs fun q hq ↦ ws_stk hn hfr1 (by decide) hq, hsv⟩
  obtain ⟨hx0, hx1, -, -⟩ := hq
  have hprod : EW.mul ⟨st4.regs.X0, st4.regs.X1⟩ ⟨st4.regs.X2, st4.regs.X3⟩ =
      multilinearEval cj.mu low * dot ws xs := by
    rw [show st4.regs.X0 = _ from (reg_of hm4 (r := .X0) (v := .reg .X19) rfl rfl).trans x19,
      show st4.regs.X1 = _ from (reg_of hm4 (r := .X1) (v := .reg .X20) rfl rfl).trans x20,
      show st4.regs.X2 = _ from (reg_of hm4 (r := .X2) (v := .reg .X0) rfl rfl).trans
        (congrArg EW.c0 hret3),
      show st4.regs.X3 = _ from (reg_of hm4 (r := .X3) (v := .reg .X1) rfl rfl).trans
        (congrArg EW.c1 hret3)]
    rfl
  rw [hprod] at hx0 hx1
  have T3 := hb4.trans hc4
  have k3 := regs_keptL f2L (by decide) (matchM hn hfr3) hm4 (by decide) hcs4
  have g : ∀ r ∈ f2L, m4.regs.getXReg r = m.regs.getXReg r := fun r hr ↦
    (k3 r hr).trans ((k2 r hr).trans (k1 r hr))
  simp only [f2L, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at g
  obtain ⟨g21, g22, g23, g24⟩ := g
  rw [show k + NativeRustcVmArm.Vm.VerifyKeccak.b63Offset + b63.length = k + NativeRustcVmArm.Vm.VerifyKeccak.b64Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyKeccak.b63_next]]
  -- `b64`, `b65`
  refine failBranchF hp hn (b64_in_code.trans hp.1 (by simp [b64])) run_b64 hfr4 rfl rfl
    (L := f3L) (by decide) (b := ((multilinearEval cj.mu low * dot ws xs).c0 == v.c0))
    (by rw [condNe, Env.ofMachine_regs, Env.ofMachine_regs, bv_beq, gx0, hx0, g22, hy.x22])
    (fun hf ↦ by rw [hy.run, afterOpen2_false hy.rs (ew_beq_c0 (by simpa using hf))])
    fun ht0 m5 hfr5 hd5 hk5 ↦ ?_
  have g5 : ∀ r ∈ f3L, m5.regs.getXReg r = m4.regs.getXReg r := hk5
  simp only [f3L, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at g5
  obtain ⟨h1, h21, h22, h23, h24⟩ := g5
  rw [show k + NativeRustcVmArm.Vm.VerifyKeccak.b64Offset + b64.length = k + NativeRustcVmArm.Vm.VerifyKeccak.b65Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyKeccak.b64_next]]
  refine failBranchF hp hn (b65_in_code.trans hp.1 (by simp [b65])) run_b65 hfr5 rfl rfl
    (L := f2L) (by decide) (b := ((multilinearEval cj.mu low * dot ws xs).c1 == v.c1))
    (by rw [condNe, Env.ofMachine_regs, Env.ofMachine_regs, bv_beq, h1, gx1, hx1, h21, g21,
      hy.x21])
    (fun hf ↦ by rw [hy.run, afterOpen2_false hy.rs (ew_beq_c1 (by simpa using hf))])
    fun ht1 m6 hfr6 hd6 hk6 ↦ ?_
  have g6 : ∀ r ∈ f2L, m6.regs.getXReg r = m5.regs.getXReg r := hk6
  simp only [f2L, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at g6
  obtain ⟨-, -, i23, i24⟩ := g6
  have T := T1.trans (T2.trans T3)
  have hd : m6.dmem = m4.dmem := hd6.trans hd5
  rw [show k + NativeRustcVmArm.Vm.VerifyKeccak.b65Offset + b65.length = k + NativeRustcVmArm.Vm.VerifyKeccak.b66Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyKeccak.b65_next]]
  refine cont m6 ⟨hfr6, by rw [i23, h23, g23]; exact hy.x23, by rw [i24, h24, g24]; exact hy.x24,
    ?_, ?_, ?_, ?_, ?_, hy.psz, hy.lowsz, ?_, hy.slsz, ?_, hy.xsz, ?_, ?_⟩
  all_goals try rw [hd]
  · exact T.word hn (by decide) (by decide) (by decide) hy.w72
  · exact T.word hn (by decide) (by decide) (by decide) hy.pk
  · exact T.ts hn (kept_tr hkt (kept_tr hkt3 hkt4)) (by decide) (by decide) (by decide) hy.ts
  · exact T.cls hn (by decide) (by decide) (by decide) hy.cls
  · exact T.claim hn (by decide) (by decide) (by decide) hy.claim
  · exact T.ews hn (by decide) (o := 3176) (k := 64) (by decide) (by decide)
      (by simp [Array.length_toList, hy.lowsz]) hy.lowv
  · exact T.ews hn (by decide) (o := 2496) (k := 96) (by decide) (by decide)
      (by simp [Array.length_toList, hy.slsz]) hy.slot
  · exact T.ewsOut hn (by decide) (by decide) (i := 3) (o := 584) (k := 1024)
      (by decide) (by decide) (by decide) (by decide) (by simp [Array.length_toList, hy.xsz])
      hy.slices
  · rw [hy.run, afterOpen2_true hy.rs (ew_beq_true (by simpa using ht0) (by simpa using ht1))]

end

end NativeRustcVmArm.KeccakGkr.VerifyKeccak
