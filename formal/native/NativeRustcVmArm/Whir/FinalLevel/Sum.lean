module

public import NativeRustcVmArm.Code.Vm.SumcheckOfSumcheckPlain.Names
public import NativeRustcVmArm.Whir.FinalLevel.Core
public import NativeRustcVm.Top.Phases

/-!
# `final_level`: the last sumcheck

`sum`: from `b14` (`μ ≤ 30`, the tail zeroed), `sumcheck_plain(claim, 3, tail)` (`b15`) into the
frame's bytes `1096` (the tail) and `2064` (its `Option<EW>`), its verdict (`b16`, `None` to
`.LFinalLevel_2`), to `b17`.
-/

namespace NativeRustcVmArm.Whir.FinalLevel

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmArm.Vm.FinalLevel
open NativeRustcVmArm.Transcript (known_ptr load_ofMachine eval_ptr wordAt_write load_of_wordAt)

public section

theorem sumcheckPlain_size {claim : EW} {count n : Nat} {s s' : TState} {xs : Array EW} {c : EW}
    (h : (sumcheckPlain claim count n).run s = some ((xs, c), s')) : xs.size = n := by
  have := (NativeRustcVm.Top.sumcheck_size claim count (Array.replicate n none)).gives s _ s' h
  simpa using this

variable [Host] {a : DecArea} {s0 : TState} {level : Whir.Level} {ba : BasisAddrs} {b : BasisW}
  {w : WhirStateW} {rounds : Array FoldRoundW} {m0 : MachineData} {k : Nat}

/-- **The last sumcheck.** -/
theorem sum (hp : Placed code k) (c : Ctx a s0 level ba b w rounds m0)
    (hsc : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.SumcheckOfSumcheckPlain.entryLabel) (SumcheckPlainPre a s)
      (SumcheckPlainPost a s))
    {st : MachineState} {folded : Array EW} {s4 : TState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FinalLevel.b14Offset)) (hl : Live level m0 st.data folded)
    (hts : TStateAt st.data.dmem (tA m0) a s4)
    (hrun : runF s0 level b w rounds m0 = (C5 (mu m0) m0.regs.X4.toNat b w folded).run s4)
    (cont : ∀ (st' : MachineState) (tail : Array EW) (claim : EW) (s5 : TState),
      st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FinalLevel.b17Offset) → Core level m0 st'.data folded → tail.size = mu m0 →
      NativeRustcVm.EWsAt st'.data.dmem (loc m0 1096) tail.toList →
      NativeRustcVm.EWAt st'.data.dmem (loc m0 2072) claim →
      TStateAt st'.data.dmem (tA m0) a s5 →
      runF s0 level b w rounds m0 = (C6 (mu m0) m0.regs.X4.toNat b w folded (tail, claim)).run s5 →
      Eventually (step1 Host.exe) (Goal a s0 level b w rounds m0) st') :
    Eventually (step1 Host.exe) (Goal a s0 level b w rounds m0) st := by
  have hfo := c.two_mu_le
  have hmu6 := mu_le hfo
  have hf := hl.fr
  -- `b14`: `μ ≤ 30`, the tail zeroed.
  have hwf := c.fwf hf
  refine exec_at (inf hp b14_in_code (by simp [b14])) run_b14 hwf hpc (c.fmatch hf)
    fun st1 hm1 hpc1 ↦ ?_
  have hS1 : ∀ w ∈ (after b14 fS).mem, w.r = 0 ∧ w.off + w.n ≤ 2576 := by
    rw [after_eq run_b14]; decide +kernel
  have hf1 : FFr m0 st1.data := c.fr_block hf (c.fmatch hf) hm1 hwf rfl
    (by rw [← after_eq run_b14]; exact hS1)
  simp only [PcOk] at hpc1
  rw [show k + NativeRustcVmArm.Vm.FinalLevel.b14Offset + b14.length = k + NativeRustcVmArm.Vm.FinalLevel.b15Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.FinalLevel.b14_next]] at hpc1
  split at hpc1
  · rename_i h
    exfalso
    revert h
    have : (st.data.regs.getXReg .X20).toNat = mu m0 := congrArg UInt64.toNat hl.base.x20
    sym_simp
    simp only [bv_ult_toNat, bv_beq_toNat, show (fenv m0 st.data []).regs .X20 =
      (st.data.regs.getXReg .X20).toBitVec from rfl, UInt64.toNat_toBitVec, this,
      BitVec.toNat_ofNat]
    simp only [Bool.not_eq_true', decide_eq_false_iff_not, Bool.and_eq_true]
    omega
  have hc1 : Core level m0 st1.data folded :=
    hl.core.saved hf1 (fun r hr ↦ reg_of hm1 (kept_of (by decide) r hr) rfl)
      (Ctx.same_block hm1 hwf (by decide +kernel) (by decide)) hfo
  have hts1 : TStateAt st1.data.dmem (tA m0) a s4 :=
    c.ts_block hm1 hwf (fun w hw ↦ by
      obtain ⟨h1, h2⟩ := hS1 w (by rw [after_eq run_b14]; exact hw); exact ⟨h1, by omega⟩) hts
  have k22 : st1.data.regs.X22 = m0.regs.X0 :=
    (reg_of hm1 (r := .X22) (v := .reg .X22) rfl rfl).trans hl.x22
  -- `b15`: `sumcheck_plain(&out, t, claim, 3, tail)`.
  have x27 : (st1.data.regs.getXReg .X27).toBitVec = pA m0 :=
    congrArg UInt64.toBitVec hc1.base.x27
  have hin : WhirIn m0 (pA m0) 16 finalLevelStack := whirIn_pre c.pIn (by decide)
  have hwf2 := c.wf1 hf1 hin
  have hm2 := c.match1 (n := 16) hf1 x27
  refine exec_at (inf hp b15_in_code (by simp [b15])) run_b15 hwf2 hpc1 hm2
    fun st2 hm2' hpc2 ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.FinalLevel.b15Offset + b15.length = k + NativeRustcVmArm.Vm.FinalLevel.b16Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.FinalLevel.b15_next]] at hpc2
  have hf2 : FFr m0 st2.data :=
    Fr.ofBlock hf1 hm2 hm2' hwf2 rfl rfl rfl (fun _ h ↦ by cases h)
  have hd2 : st2.data.dmem = st1.data.dmem := hm2'.dmem_eq hwf2 rfl
  have hc2 : Core level m0 st2.data folded :=
    hc1.saved hf2 (fun r hr ↦ by
      simp only [coreRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      all_goals first
        | exact reg_of hm2' rfl rfl
        | exact UInt64.toBitVec_inj.mp ((reg_val hm2' (r := .X27) (v := .ptr 1 0) rfl).trans
            ((eval_ptr rfl).trans x27.symm))) (fun j _ ↦ by rw [hd2]) hfo
  have hcl := (c.state_at hf1).claim
  obtain ⟨hc0, hc1'⟩ := ewAt_iff.mp hcl
  have x0 : st2.data.regs.X0.toBitVec = loc m0 2064 :=
    reg_val hm2' (r := .X0) (v := .ptr 0 2064) rfl
  have x1 : st2.data.regs.X1.toBitVec = tA m0 := by
    rw [show st2.data.regs.X1.toBitVec = _ from reg_val hm2' (r := .X1) (v := .reg .X22) rfl]
    exact congrArg UInt64.toBitVec k22
  have x23 : (⟨st2.data.regs.X2, st2.data.regs.X3⟩ : EW) = w.claim := by
    have e2 : st2.data.regs.X2 = w.claim.c0 := UInt64.toBitVec_inj.mp
      ((reg_val hm2' (r := .X2) (v := .load 1 0 8) rfl).trans
        (load_ofMachine (r := 1) (o := 0) rfl (by rw [off_zero]; exact hc0)))
    have e3 : st2.data.regs.X3 = w.claim.c1 := UInt64.toBitVec_inj.mp
      ((reg_val hm2' (r := .X3) (v := .load 1 8 8) rfl).trans
        (load_ofMachine (r := 1) (o := 8) rfl hc1'))
    rw [e2, e3]
  have x4 : st2.data.regs.X4.toNat = 3 := by
    rw [← UInt64.toNat_toBitVec]
    show (st2.data.regs.getXReg .X4).toBitVec.toNat = _
    rw [reg_val hm2' (r := .X4) (v := .lit 3) rfl]
    rfl
  have x5 : st2.data.regs.X5.toBitVec = loc m0 1096 :=
    reg_val hm2' (r := .X5) (v := .ptr 0 1096) rfl
  have x6 : st2.data.regs.X6.toNat = mu m0 := by
    rw [← UInt64.toNat_toBitVec]
    show (st2.data.regs.getXReg .X6).toBitVec.toNat = _
    rw [reg_val hm2' (r := .X6) (v := .reg .X20) rfl]
    exact congrArg UInt64.toNat hc1.base.x20
  have hle : 2672 + sumcheckPlainStack ≤ finalLevelStack := by decide
  have hso : ∀ m' : MachineData, SumcheckPlainPost a s4 st2.data m' →
      SameOutside st2.data.dmem m'.dmem fun q ↦
        InRange (stackBelow st2.data sumcheckPlainStack) sumcheckPlainStack q ∨
          InRange (loc m0 1096) 992 q ∨ InRange (tA m0) tstateBytes q := fun m' hq ↦
    NativeRustcVm.SameOutside.mono hq.2.1 fun q h ↦ by
      have := m0.regs.SP.toNat_lt
      have hlo : NoWrap (loc m0 1096) 992 := by
        unfold NoWrap; rw [c.loc_nat (by decide)]; have := c.hN'; omega
      rcases h with h | h | h | h
      · rw [x0] at h
        refine .inr (.inl ((Sym.inRange_iff hlo).mpr ?_))
        have hn : NoWrap (loc m0 2064) 24 := by
          unfold NoWrap; rw [c.loc_nat (by decide)]; have := c.hN'; omega
        rw [Sym.inRange_iff hn, c.loc_nat (by decide)] at h
        rw [c.loc_nat (by decide)]
        omega
      · rw [x5, x6] at h
        refine .inr (.inl ((Sym.inRange_iff hlo).mpr ?_))
        have hn : NoWrap (loc m0 1096) (16 * mu m0) := by
          unfold NoWrap; rw [c.loc_nat (by decide)]; have := c.hN'; omega
        rw [Sym.inRange_iff hn, c.loc_nat (by decide)] at h
        rw [c.loc_nat (by decide)]
        omega
      · rw [x1] at h; exact .inr (.inr h)
      · exact .inl h
  refine c.call hf2 (lo := 1096) (n := 992) hle (by decide) (hsc a s4) hpc2 ?_
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono (hso m' hq) fun q h ↦ by
      rcases h with h | h | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr (.inr h)), hq.2.2⟩) fun m3 hf3 hq hcs3 ↦ ?_
  · refine ⟨c.stackOk' hf2 hle, c.rcAt' hf2 hle, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show TStateAt st2.data.dmem st2.data.regs.X1.toBitVec a s4
      rw [x1, hd2]; exact hts1
    · show TStateOk st2.data st2.data.regs.X1.toBitVec a sumcheckPlainStack
      rw [x1]; exact c.tstateOk' hf2 hle
    · show 2 ≤ st2.data.regs.X4.toNat; rw [x4]; decide
    · show st2.data.regs.X4.toNat ≤ maxCount; rw [x4]; decide
    · show OutOk st2.data st2.data.regs.X1.toBitVec a st2.data.regs.X0.toBitVec 24
        sumcheckPlainStack
      rw [x0, x1]; exact c.localOk' hf2 hle (by decide)
    · show OutOk st2.data st2.data.regs.X1.toBitVec a st2.data.regs.X5.toBitVec
        (16 * st2.data.regs.X6.toNat) sumcheckPlainStack
      rw [x1, x5, x6]; exact c.localOk' hf2 hle (by omega)
    · show Apart st2.data.regs.X0.toBitVec 24 st2.data.regs.X5.toBitVec
        (16 * st2.data.regs.X6.toNat)
      rw [x0, x5, x6]
      exact NativeRustcVm.Apart.symm (c.apart_locs (by omega) (by decide))
  -- `b16`: the sumcheck's verdict.
  have hs3 := hso m3 hq
  obtain ⟨⟨hopt, hslots, hnext⟩, -, hsv⟩ := hq
  rw [x0, x1, x5, x6, x4, x23] at *
  have hc3 : Core level m0 m3 folded :=
    hc2.saved hf3 (core_cs hcs3) (c.keep_call hf2 hle (lo := 1096) (n := 992)
      (NativeRustcVm.SameOutside.mono hs3 fun q h ↦ by
        rcases h with h | h | h
        · exact .inl h
        · exact .inr (.inl h)
        · exact .inr (.inr (.inr h))) (by omega) (by decide) (by decide)) hfo
  refine c.fblock hp b16_in_code (by simp [b16]) run_b16 rfl rfl rfl hf3
    fun st4 hm4 hpc4 hf4 hd4 hk4 ↦ ?_
  simp only [PcOk] at hpc4
  cases hr : (sumcheckPlain w.claim 3 (mu m0)).run s4 with
  | none =>
    rw [hr, Option.map_none] at hopt
    have h0 : (fenv m0 m3 []).load 0 2064 8 = (0 : UInt64).toBitVec :=
      load_of_wordAt (hopt : NativeRustcVm.WordAt _ _ 0)
    rw [cbz_load h0] at hpc4
    simp only [beq_self_eq_true, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.FinalLevel.b2Offset) NativeRustcVmArm.Vm.FinalLevel.label_2_at] at hpc4
    exact exit2 hp c hpc4 hf4 (by rw [hrun, C5]; exact run_bind_none hr)
  | some p =>
    obtain ⟨⟨tail, claim⟩, s5⟩ := p
    rw [hr] at hopt
    obtain ⟨h1, hcw⟩ := hopt
    rw [cbz_load (load_of_wordAt h1)] at hpc4
    simp only [show ((1 : UInt64) == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte,
      show k + NativeRustcVmArm.Vm.FinalLevel.b16Offset + b16.length = k + NativeRustcVmArm.Vm.FinalLevel.b17Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.FinalLevel.b16_next]] at hpc4
    refine cont st4 tail claim s5 hpc4
      (hc3.saved hf4 (fun r hr ↦ hk4 r (kept_of (by decide) r hr)) (fun j _ ↦ by rw [hd4]) hfo)
      (sumcheckPlain_size hr) (by rw [hd4]; exact hslots tail claim s5 hr)
      (by have := hcw; rw [loc_off] at this; rw [hd4]; exact this) ?_ ?_
    · rw [hd4]
      exact hnext _ _ hr
    · rw [hrun, C5]; exact run_bind_some hr

end

end NativeRustcVmArm.Whir.FinalLevel
