module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.MultilinearEvalByOfMultilinearEval.Names
public import NativeRustcVmArm.Whir.FinalLevel.Keep

/-!
# `final_level`: the end check

`finish`: from `.LFinalLevel_20` (`b33`), the folded scalars' first `2 ^ μ` evaluated at the
sumcheck's tail (`multilinear_eval`), times the weight (`EW::mul`, `b34`), compared with the
sumcheck's claim at the frame's byte `24` (`b35`), to the epilogue.
-/

namespace NativeRustcVmArm.Whir.FinalLevel

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmArm.Vm.FinalLevel

public section

theorem slice_take {m : MachineData} {a : BitVec 64} {xs : Array EW} {n : UInt64}
    (h : NativeRustcVm.EWsAt m.dmem a xs.toList) (hn : n.toNat ≤ xs.size) :
    slice m (UInt64.ofBitVec a) n = xs.extract 0 n.toNat := by
  have ht := NativeRustcVm.ewsOf_of_ewsAt (NativeRustcVm.EWsAt.take h n.toNat)
  rw [List.length_take, Array.length_toList, Nat.min_eq_left hn] at ht
  unfold slice
  rw [show (UInt64.ofBitVec a).toBitVec = a from rfl, ht]
  apply Array.ext'
  simp

theorem slice_all {m : MachineData} {a : BitVec 64} {xs : Array EW} {n : UInt64}
    (h : NativeRustcVm.EWsAt m.dmem a xs.toList) (hn : n.toNat = xs.size) :
    slice m (UInt64.ofBitVec a) n = xs := by
  unfold slice
  rw [show (UInt64.ofBitVec a).toBitVec = a from rfl, hn, ← Array.length_toList,
    NativeRustcVm.ewsOf_of_ewsAt h]

theorem beq_toBitVec (x y : UInt64) : (x.toBitVec == y.toBitVec) = (x == y) := by
  by_cases h : x = y
  · subst h; simp
  · rw [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne]
    exact fun h' ↦ h (UInt64.toBitVec_inj.mp h')

variable [Host] {a : DecArea} {s0 : TState} {level : Whir.Level} {ba : BasisAddrs} {b : BasisW}
  {w : WhirStateW} {rounds : Array FoldRoundW} {m0 : MachineData} {k : Nat}

/-- **The end check.** -/
theorem finish (hp : Placed code k) (c : Ctx a s0 level ba b w rounds m0)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hmle : Spec (Labels.label NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.entryLabel) MleOfMultilinearEvalPre
      MleOfMultilinearEvalPost)
    {st : MachineState} {folded tail : Array EW} {s5 : TState} {weight claim : EW}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FinalLevel.b33Offset)) (hf : FFr m0 st.data)
    (hx19 : st.data.regs.X19.toNat = 2 ^ mu m0) (hx20 : st.data.regs.X20 = m0.regs.X3)
    (hx21 : st.data.regs.X21 = weight.c0) (hx23 : st.data.regs.X23 = weight.c1)
    (hsize : folded.size = 2 ^ mu m0 + level.fold)
    (hfold : NativeRustcVm.EWsAt st.data.dmem (loc m0 40) folded.toList)
    (htsize : tail.size = mu m0)
    (htail : NativeRustcVm.EWsAt st.data.dmem (loc m0 1096) tail.toList)
    (hclaim : NativeRustcVm.EWAt st.data.dmem (loc m0 24) claim)
    (hts : TStateAt st.data.dmem (tA m0) a s5)
    (hrun : runF s0 level b w rounds m0 =
      (require (weight * multilinearEval (folded.extract 0 (2 ^ mu m0)) tail == claim)).run s5) :
    Eventually (step1 Host.exe) (Goal a s0 level b w rounds m0) st := by
  have hfo := c.two_mu_le
  have hmu : mu m0 < 64 := c.mu64
  have hfd : 2 ^ mu m0 ≤ 64 := by omega
  have hmu6 : m0.regs.X3.toNat ≤ 6 := mu_le hfo
  -- `b33`: `multilinear_eval(folded[..2 ^ μ], tail)`.
  refine c.fblock hp b33_in_code (by simp [b33]) run_b33 rfl rfl hpc hf
    fun st1 hm1 hpc1 hf1 hd1 hk1 ↦ ?_
  have hle : 2672 + mleStack ≤ finalLevelStack := by decide
  have x0 : st1.data.regs.X0 = st.data.regs.X19 := reg_of hm1 (r := .X0) (v := .reg .X19) rfl rfl
  have x2 : st1.data.regs.X2 = st.data.regs.X19 := reg_of hm1 (r := .X2) (v := .reg .X19) rfl rfl
  have x1 : st1.data.regs.X1 = UInt64.ofBitVec (loc m0 40) :=
    reg_of hm1 (r := .X1) (v := .ptr 0 40) rfl rfl
  have x3 : st1.data.regs.X3 = UInt64.ofBitVec (loc m0 1096) :=
    reg_of hm1 (r := .X3) (v := .ptr 0 1096) rfl rfl
  have x4 : st1.data.regs.X4 = m0.regs.X3 :=
    (reg_of hm1 (r := .X4) (v := .reg .X20) rfl rfl).trans hx20
  have hq : ∀ m' : MachineData, MleOfMultilinearEvalPost st1.data m' →
      SameOutside st1.data.dmem m'.dmem fun q ↦
        InRange (stackBelow st1.data mleStack) mleStack q ∨ InRange (loc m0 0) 0 q := fun m' h ↦
    NativeRustcVm.SameOutside.mono h.2.1 fun q h ↦ by
      rcases h with h | h
      · exact absurd h (Nat.not_lt_zero _)
      · exact .inl h
  refine c.call hf1 (lo := 0) (n := 0) hle (by decide) hmle hpc1 ?_
    (fun m' h ↦ ⟨NativeRustcVm.SameOutside.mono (hq m' h) fun q h ↦ by
      rcases h with h | h
      · exact .inl h
      · exact .inr (.inl h), h.2.2⟩) fun m2 hf2 hq2 hcs2 ↦ ?_
  · refine ⟨c.stackOk' hf1 hle, x0.trans x2.symm, ?_, ?_, ?_⟩
    · rw [x4]; exact hmu
    · rw [x1, x2]; exact c.locSlice hf1 hle (by rw [hx19]; omega)
    · rw [x3, x4]; exact c.locSlice hf1 hle (by omega)
  -- `b34`: `weight * mle`.
  have hs2 := hq m2 hq2
  obtain ⟨hv, -, hsv2⟩ := hq2
  rw [x1, x2, x3, x4, slice_take (by rw [hd1]; exact hfold) (by rw [hx19, hsize]; omega), hx19,
    slice_all (by rw [hd1]; exact htail) htsize.symm] at hv
  have hstk2 := c.call_stk hf1 hle (by decide) hs2
  refine c.fblock hp b34_in_code (by simp [b34]) run_b34 rfl rfl rfl hf2
    fun st3 hm3 hpc3 hf3 hd3 hk3 ↦ ?_
  have hle' : 2672 + ewMulStack ≤ finalLevelStack := by decide
  have hpre : EWMulPre st3.data := c.stackOk' hf3 hle'
  have r0 : st3.data.regs.X0 = st.data.regs.X21 :=
    ((reg_of hm3 (r := .X0) (v := .reg .X21) rfl rfl).trans (hcs2 .X21 rfl)).trans (hk1 .X21 rfl)
  have r1 : st3.data.regs.X1 = st.data.regs.X23 :=
    ((reg_of hm3 (r := .X1) (v := .reg .X23) rfl rfl).trans (hcs2 .X23 rfl)).trans (hk1 .X23 rfl)
  have r2 : st3.data.regs.X2 = m2.regs.X0 := reg_of hm3 (r := .X2) (v := .reg .X0) rfl rfl
  have r3 : st3.data.regs.X3 = m2.regs.X1 := reg_of hm3 (r := .X3) (v := .reg .X1) rfl rfl
  have e01 : (⟨st3.data.regs.X0, st3.data.regs.X1⟩ : EW) = weight := by
    rw [r0, r1, hx21, hx23]
  have e23 : (⟨st3.data.regs.X2, st3.data.regs.X3⟩ : EW) =
      multilinearEval (folded.extract 0 (2 ^ mu m0)) tail := by
    rw [r2, r3, ← hv]
    rfl
  refine c.call hf3 (lo := 0) (n := 0) hle' (by decide) hmul hpc3 hpre
    (fun m' h ↦ ⟨NativeRustcVm.SameOutside.mono h.2.2.1 fun q h ↦ .inl h, h.2.2.2⟩)
    fun m4 hf4 hq4 hcs4 ↦ ?_
  -- `b35`: the comparison.
  obtain ⟨hy0, hy1, hs4, hsv4⟩ := hq4
  rw [e01, e23] at hy0 hy1
  have hstk4 : SameOutside st3.data.dmem m4.dmem (Ctx.Stk m0) :=
    c.call_stk hf3 hle' (lo := 0) (n := 0) (by decide)
      (NativeRustcVm.SameOutside.mono hs4 fun q h ↦ .inl h)
  -- The claim at the frame's byte `24`, kept.
  have hcl : NativeRustcVm.EWAt m4.dmem (loc m0 24) claim := by
    have h1 : NativeRustcVm.Layout.Same st.data.dmem m2.dmem (loc m0 24) 16 := by
      rw [← hd1]
      exact c.same_call hf1 hle (lo := 0) (n := 0) (NativeRustcVm.SameOutside.mono hs2
        fun q h ↦ by
          rcases h with h | h
          · exact .inl h
          · exact .inr (.inl h)) (by decide) (by omega) (by decide)
    have h2 : NativeRustcVm.Layout.Same m2.dmem m4.dmem (loc m0 24) 16 := by
      rw [← hd3]
      exact c.same_call hf3 hle' (lo := 0) (n := 0) (NativeRustcVm.SameOutside.mono hs4
        fun q h ↦ .inl h) (by decide) (by omega) (by decide)
    exact NativeRustcVm.Layout.BytesAt.of_same
      (NativeRustcVm.Layout.BytesAt.of_same hclaim h1 (by rw [NativeRustcVm.length_ewBytes])) h2
      (by rw [NativeRustcVm.length_ewBytes])
  obtain ⟨hc0, hc1⟩ := ewAt_iff.mp hcl
  rw [loc_off] at hc1
  refine exec_at (inf hp b35_in_code (by simp [b35])) run_b35 (c.fwf hf4) rfl (c.fmatch hf4)
    fun st5 hm5 hpc5 ↦ ?_
  have hf5 : FFr m0 st5.data :=
    Fr.ofBlock hf4 (c.fmatch hf4) hm5 (c.fwf hf4) rfl rfl rfl (fun _ h ↦ by cases h)
  have hd5 : st5.data.dmem = m4.dmem := hm5.dmem_eq (c.fwf hf4) rfl
  simp only [PcOk] at hpc5
  rw [hp.label (j := NativeRustcVmArm.Vm.FinalLevel.b3Offset) NativeRustcVmArm.Vm.FinalLevel.label_3_at] at hpc5
  have hts5 : TStateAt st5.data.dmem (tA m0) a s5 := by
    rw [hd5]
    refine c.ts_stk hsv4.2.2 hstk4 ?_
    rw [hd3]
    refine c.ts_stk hsv2.2.2 hstk2 ?_
    rw [hd1]
    exact hts
  rw [run_require] at hrun
  refine exit3 hp c hpc5 hf5 ?_ ?_
  · rw [hrun]
    refine UInt64.toBitVec_inj.mp ((reg_val hm5 (r := .X0) rfl).trans ?_)
    have l24 : (fenv m0 m4 []).load 0 24 8 = claim.c0.toBitVec :=
      NativeRustcVmArm.Transcript.load_ofMachine (r := 0) (o := 24) rfl hc0
    have l32 : (fenv m0 m4 []).load 0 32 8 = claim.c1.toBitVec :=
      NativeRustcVmArm.Transcript.load_ofMachine (r := 0) (o := 32) rfl hc1
    sym_simp
    simp only [show (fenv m0 m4 []).regs .X0 = m4.regs.X0.toBitVec from rfl,
      show (fenv m0 m4 []).regs .X1 = m4.regs.X1.toBitVec from rfl, l24, l32, hy0, hy1,
      beq_toBitVec, ew_beq]
    cases (EW.mul weight (multilinearEval (folded.extract 0 (2 ^ mu m0)) tail)).c0 ==
      claim.c0 <;>
    cases (EW.mul weight (multilinearEval (folded.extract 0 (2 ^ mu m0)) tail)).c1 ==
      claim.c1 <;> rfl
  · rw [hrun]
    intro x s' h
    split at h
    · cases h; exact hts5
    · cases h

end

end NativeRustcVmArm.Whir.FinalLevel
