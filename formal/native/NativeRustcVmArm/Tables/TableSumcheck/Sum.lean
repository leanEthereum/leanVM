module

public import NativeRustcVmArm.Code.Vm.SumcheckOfSumcheckPlain.Names
public import NativeRustcVmArm.Tables.TableSumcheck.Entry
public import NativeRustcVmArm.Bus.GkrModel

/-!
# `table_sumcheck`: the sumcheck

`b1` keeps the arguments in callee-saved registers and calls the plain sumcheck (`4`, `n` rounds,
the claim `target`) with its `Option<EW>` at `504` and its challenges at `24` of the frame; `b2`
leaves for the rejection on `None` (`sum`).
-/

namespace NativeRustcVmArm.Tables.TableSumcheck

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.TableSumcheck
open NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeVm.Model NativeRustcVm.Tables
open NativeRustcVmArm.Sumcheck (Ctx At)
open NativeRustcVm (ewOf)

public section

section
variable [Host] {k : Nat} {a : DecArea} {s : TState} {heights : Array Nat} {bus : BusResultW}
  {m0 : MachineData}

/-- **The sumcheck** (`b1`, `b2`): on `Some`, its challenges at `24` of the frame, its claim at
`512`, the `TState` the next state. -/
theorem sum (hp : Placed code k)
    (hsc : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.SumcheckOfSumcheckPlain.entryLabel) (SumcheckPlainPre a s)
      (SumcheckPlainPost a s))
    (hpre : TableSumcheckPre a s heights bus m0) {n : Nat} (hn : heights.foldl max 0 = n)
    (hn30 : n ≤ 30) {m : MachineData}
    (hfr : Fr m0 720 tableSumcheckStack slots keep (outs m0) m)
    (hx : ∀ r ∈ [XReg.X0, .X1, .X2, .X3, .X4, .X5, .X6, .X7],
      m.regs.getXReg r = m0.regs.getXReg r)
    (h25 : (m.regs.getXReg .X25).toNat = n) (hts : TStateAt m.dmem m0.regs.X0.toBitVec a s)
    (cont : ∀ (m3 : MachineData) (xs : Array EW) (c : EW) (s1 : TState),
      Fr m0 720 tableSumcheckStack slots keep (outs m0) m3 → Regs m0 m3 n →
      (sumcheckPlain ⟨m0.regs.X5, m0.regs.X6⟩ 4 n).run s = some ((xs, c), s1) →
      TStateAt m3.dmem m0.regs.X0.toBitVec a s1 → xs.size = n →
      (∀ i (h : i < xs.size), ewOf m3.dmem (fb m0 + BitVec.ofNat 64 (24 + 16 * i)) = xs[i]) →
      ewOf m3.dmem (fb m0 + BitVec.ofNat 64 512) = c →
      Eventually (step1 Host.exe) (Goal a s heights bus m0) ⟨m3, Host.addrOf (k + NativeRustcVmArm.Vm.TableSumcheck.b3Offset)⟩) :
    Eventually (step1 Host.exe) (Goal a s heights bus m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.TableSumcheck.b1Offset)⟩ := by
  have hpre' := hpre
  obtain ⟨hS, hrc, -, hts0, htok, heo, -, -, -, -, -⟩ := hpre'
  have hN := hS.2.1
  have cx : Ctx m0 m0.regs.X0.toBitVec a tableSumcheckStack 720 :=
    Bus.Gkr.ctx_of hS hrc hts0 htok N_ge rfl
  have hor : ∀ q, outs m0 q → ¬InRange rcAddr 192 q := fun q hq ↦
    hq.elim cx.not_rc_tstate (Bus.Gkr.out_not_rc cx heo)
  have hof : ∀ q, outs m0 q → ¬InRange (base m0 720) 720 q := fun q hq ↦
    hq.elim (Bus.Gkr.tstate_not_frame cx) (Bus.Gkr.out_not_frame cx heo)
  -- `b1`: the arguments, `sumcheck`.
  refine Bus.Gkr.Fr.runBlock hS N_ge rfl hfr (b1_in_code.trans hp.1 (by simp [b1])) run_b1 rfl rfl
    rfl rfl fun st hfr1 hd1 hm1 hpc1 ↦ ?_
  have hm1' : Match (Env.ofMachine m [(base m0 720, 720)]) (Bus.after b1 sF) st.data := by
    rw [Bus.after_eq run_b1]; exact hm1
  obtain ⟨-, -, g0, g1, g2, g3, g4, g5, g6, g19, g20, g21, g22, g23, g24, g25⟩ := ok_b1
  have e0 : st.data.regs.X0.toBitVec = fb m0 + BitVec.ofNat 64 504 := by
    show (st.data.regs.getXReg .X0).toBitVec = _
    rw [hm1'.regs .X0 _ g0, eval_ptr0]; rfl
  have e5 : st.data.regs.X5.toBitVec = fb m0 + BitVec.ofNat 64 24 := by
    show (st.data.regs.getXReg .X5).toBitVec = _
    rw [hm1'.regs .X5 _ g5, eval_ptr0]; rfl
  have e1 : st.data.regs.X1.toBitVec = m0.regs.X0.toBitVec := by
    show (st.data.regs.getXReg .X1).toBitVec = _
    rw [Bus.Gkr.reg_of hm1' g1, hx .X0 (by simp)]; rfl
  have e2 : st.data.regs.X2 = m0.regs.X5 := by
    show st.data.regs.getXReg .X2 = _
    rw [Bus.Gkr.reg_of hm1' g2, hx .X5 (by simp)]; rfl
  have e3 : st.data.regs.X3 = m0.regs.X6 := by
    show st.data.regs.getXReg .X3 = _
    rw [Bus.Gkr.reg_of hm1' g3, hx .X6 (by simp)]; rfl
  have e4 : st.data.regs.X4.toNat = 4 := by
    show (st.data.regs.getXReg .X4).toBitVec.toNat = 4
    rw [Bus.Gkr.reg_lit hm1' g4]; rfl
  have e6 : st.data.regs.X6.toNat = n := by
    show (st.data.regs.getXReg .X6).toBitVec.toNat = n
    rw [Bus.Gkr.reg_of hm1' g6]; exact h25
  have rg1 : Regs m0 st.data n :=
    ⟨by rw [Bus.Gkr.reg_of hm1' g19, hx .X2 (by simp)]; rfl,
      by rw [Bus.Gkr.reg_of hm1' g20, hx .X4 (by simp)]; rfl,
      by rw [Bus.Gkr.reg_of hm1' g21, hx .X1 (by simp)]; rfl,
      by rw [Bus.Gkr.reg_of hm1' g22, hx .X3 (by simp)]; rfl,
      by rw [Bus.Gkr.reg_of hm1' g23, hx .X0 (by simp)]; rfl,
      by rw [Bus.Gkr.reg_of hm1' g24, hx .X7 (by simp)]; rfl,
      by rw [Bus.Gkr.reg_of hm1' g25]; exact h25⟩
  have hat := Bus.Gkr.Fr.at_ cx hfr1 hor
  have hle : 720 + sumcheckPlainStack ≤ tableSumcheckStack := by
    unfold tableSumcheckStack; omega
  have hpre1 : SumcheckPlainPre a s st.data := by
    unfold SumcheckPlainPre SumcheckOk
    rw [e0, e1, e4, e5, e6]
    refine ⟨cx.stackOk hat hle, cx.rcAt hat hle, by rw [hd1]; exact hts, cx.tstateOk hat hle,
      by decide, by decide, cx.outOk hat hle (o := 504) (n := 24) (by omega),
      cx.outOk hat hle (o := 24) (n := 16 * n) (by omega), ?_⟩
    unfold Apart
    rw [fb_add hS N_ge (by omega), fb_add hS N_ge (by omega)]
    omega
  have hpc1' : st.pc = Labels.label NativeRustcVmArm.Vm.SumcheckOfSumcheckPlain.entryLabel ∧
      retOf st.data = Host.addrOf (k + NativeRustcVmArm.Vm.TableSumcheck.b2Offset) := hpc1
  refine Bus.Gkr.Fr.callLocal (o := 24) (n := 504)
    (X := fun q ↦ InRange (fb m0 + BitVec.ofNat 64 504) 24 q ∨
      InRange (fb m0 + BitVec.ofNat 64 24) (16 * n) q ∨ InRange m0.regs.X0.toBitVec tstateBytes q)
    hfr1 hN hle keep_callee (by decide) (by omega) hof (fun q hq ↦ ?_) (hsc a s) hpc1' hpre1
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun q h ↦ ?_, hq.2.2⟩)
    fun m2 hfr2 hq2 hcs2 _ ↦ ?_
  · rcases hq with h | h | h
    · exact .inr (inRange_fb hS N_ge (by omega) (by omega) (by omega) h)
    · exact .inr (inRange_fb hS N_ge (by omega) (by omega) (by omega) h)
    · exact .inl (.inl h)
  · rw [e0, e5, e6, e1] at h
    rcases h with h | h | h | h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr h))
    · exact .inl h
  -- The sumcheck's result.
  obtain ⟨⟨o1, o2, o3⟩, -, -⟩ := hq2
  rw [e2, e3, e4, e6] at o1 o2 o3
  rw [e0] at o1
  rw [e5] at o2
  rw [e1] at o3
  have hcs : ∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25],
      m2.regs.getXReg r = st.data.regs.getXReg r := fun r hr ↦ hcs2 r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
  have rg2 := rg1.of hcs
  -- `b2`: the `Option`'s tag.
  refine Bus.Gkr.Fr.runBlock hS N_ge rfl hfr2 (b2_in_code.trans hp.1 (by simp [b2])) run_b2'
    ok_b2.2.1 ok_b2.1 rfl rfl fun st3 hfr3 hd3 hm3 hpc3 ↦ ?_
  have rg3 := rg2.of fun r hr ↦ Bus.Gkr.reg_of hm3 (reg_keep ok_b2.2.2 (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp))
  have htag : ∀ w : UInt64, NativeRustcVm.WordAt m2.dmem (fb m0 + BitVec.ofNat 64 504) w →
      (Env.ofMachine m2 [(base m0 720, 720)]).load 0 504 8 = w.toBitVec := fun w h ↦
    load_word h
  simp only [PcOk, SBool.eval, Sym.eval, CmpOp.apply, low_W64] at hpc3
  cases hr : (sumcheckPlain ⟨m0.regs.X5, m0.regs.X6⟩ 4 n).run s with
  | none =>
    rw [hr] at o1
    rw [htag 0 o1] at hpc3
    simp only [show ((0 : UInt64).toBitVec == BitVec.ofNat 64 0) = true from rfl,
      ↓reduceIte] at hpc3
    have hres : res s heights bus m0 = none := by
      rw [res, tableSumcheck_run, hn, hr]; rfl
    exact Bus.Gkr.at_pc (hpc3.trans (hp.label (j := NativeRustcVmArm.Vm.TableSumcheck.b10Offset) NativeRustcVmArm.Vm.TableSumcheck.label_7_at)) (fail10 hp hS hfr3 hres)
  | some p =>
    obtain ⟨⟨xs, c⟩, s1⟩ := p
    rw [hr] at o1 o2 o3
    obtain ⟨o1a, o1b⟩ := o1
    rw [htag 1 o1a] at hpc3
    simp only [show ((1 : UInt64).toBitVec == BitVec.ofNat 64 0) = false from rfl,
      Bool.false_eq_true, ↓reduceIte] at hpc3
    rw [show k + NativeRustcVmArm.Vm.TableSumcheck.b2Offset + b2.length = k + NativeRustcVmArm.Vm.TableSumcheck.b3Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.TableSumcheck.b2_next]] at hpc3
    have hsz : xs.size = n := by
      have h' : NativeRustcVm.Sumcheck.sumcheckFn ⟨m0.regs.X5, m0.regs.X6⟩ 4 (fun _ ↦ none) n s =
          some ((xs, c), s1) := by
        rw [NativeRustcVm.Sumcheck.sumcheckFn_none]; exact hr
      exact Bus.Gkr.sumcheckFn_size _ _ _ n h'
    have hsl := o2 xs c s1 rfl
    refine Bus.Gkr.at_pc hpc3 (cont st3.data xs c s1 hfr3 rg3 hr (by rw [hd3]; exact o3 _ _ rfl)
      hsz (fun i hi ↦ ?_) ?_)
    · rw [hd3]
      have := NativeRustcVm.ewsAt_getElem hsl (i := i) (by simpa using hi)
      rw [NativeRustcVm.addr_add_add] at this
      simpa using NativeRustcVm.ewOf_of_ewAt this
    · rw [hd3]
      have := NativeRustcVm.ewOf_of_ewAt o1b
      rwa [off, NativeRustcVm.addr_add_add] at this

end

end

end NativeRustcVmArm.Tables.TableSumcheck
