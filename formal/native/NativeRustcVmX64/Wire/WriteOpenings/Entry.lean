module

public import NativeRustcVmX64.Wire.WriteOpenings.End

/-!
# `write_openings`' entry (x86-64)

The places from the precondition (`geo_of`). The prologue (`b0`): the six pushes, the phase's
head written (the query count, the height, the leaves' width), then the branch on the height:
the levels' path (`b1`, `h > 0`) or not (`b25`). Both start from `Ent`: the arguments in their
registers, the queries' end in R14, the positions' bytes `8 np` in RCX.
-/

namespace NativeRustcVmX64.Wire.WriteOpenings

open NativeRustcX64 hiding InRange SameOutside
open NativeRustcX64.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmX64.Vm.WriteOpenings
open NativeRustcVmX64.Transcript (Frame)
open NativeRustcVm (WordAt WordsAt wordOf InRange SameOutside)

@[expose] public section

variable [Host]

/-- **After the prologue**, at directive `j`: the arguments, the head written. -/
structure Ent (R : Run) (j : Nat) (st : MachineState) : Prop where
  pc : st.pc = pcOf R j
  F : Fr R 8 st.data
  head : R.Head st.data.dmem
  rdi : reg st.data .rdi = R.qa
  rbp : reg st.data .rbp = R.out
  rcx : reg st.data .rcx = BitVec.ofNat 64 (8 * R.np)
  rdx : reg st.data .rdx = R.pa
  r8 : reg st.data .r8 = R.lv
  r9 : reg st.data .r9 = BitVec.ofNat 64 R.lw
  r14 : reg st.data .r14 = R.qa + BitVec.ofNat 64 (8 * R.nq)

end

public section

/-- **The places**, from the precondition. -/
theorem geo_of {m : MachineData} {k : Nat} (h : WriteOpeningsPre m) : Geo ⟨m, k⟩ := by
  obtain ⟨hst, ⟨hamap, ha⟩, hnq, hnp, hlw, hh, hnq0, hnp0, hok, hdj⟩ := h
  have hst' : StackOk m 160 := hst
  refine ⟨hst', fun i hi ↦ ?_, hdj, hnq0, hnq, hnp0, hnp, hlw, hh⟩
  have hab : (rspOf m + BitVec.ofNat 64 8).toNat = (rspOf m).toNat + 8 :=
    NativeRustcVm.toNat_add_ofNat (by omega)
  interval_cases i
  · exact ⟨NativeRustcVmX64.mapped_stackBelow hst', NativeRustcVmX64.noWrap_stackBelow hst'⟩
  · refine ⟨hamap, ?_⟩
    show (rspOf m + BitVec.ofNat 64 8).toNat + 32 ≤ 2 ^ 64
    omega
  all_goals exact hok _ (by simp [Run.big, Run.bigs, writeOpeningsRegions])

variable {R : Run}

/-- The queries' end: `qa + 8 nq`. -/
theorem qend : R.qa + BitVec.ofNat 64 R.nq * BitVec.ofNat 64 8 =
    R.qa + BitVec.ofNat 64 (8 * R.nq) := by
  rw [ofNat_mul, Nat.mul_comm]

variable [Host]

/-- **The prologue** (`b0`): the head written, then the levels' path (`h > 0`) or not. -/
theorem entry_spec (hp : Placed code R.k) (G : Geo R) :
    Eventually (step1 Host.exe)
      (fun st ↦ (Ent R 17 st ∧ 0 < R.h) ∨ (Ent R 157 st ∧ R.h = 0)) ⟨R.m0, pcOf R 0⟩ := by
  have hin : Inside R.out 24 (R.big 7) := ⟨le_refl _, by
    show R.out.toNat + 24 ≤ R.out.toNat + phaseBytes; rw [phaseBytes_val]; omega⟩
  have hwf := G.wf1 (m := R.m0) (fun _ h ↦ h) (i := 7) (by omega) (by omega) hin (ret := 0)
  have hc0 : R.Chg R.d0 := NativeRustcVm.SameOutside.refl _ _
  have hm : Match (envOf R R.m0 [(R.out, 24)] 0) entryS R.m0 :=
    match_ofMachine ⟨rfl, rfl, rfl, trivial⟩ ⟨NativeRustcVmX64.Transcript.match_rsp, trivial⟩
      trivial trivial ⟨by
        show (envOf R R.m0 [(R.out, 24)] 0).load 1 (8 * 3) 8 = R.out + BitVec.ofInt 64 0
        rw [G.arg_load hc0 (by omega), show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero],
        argAl_ok⟩
  refine exec_at (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf nofun rfl hm
    fun st1 hm1 hpc1 ↦ ?_
  have hfr : Frame R.m0 160 slots 8 st1.data :=
    Frame.of_prologue Frame.entry hwf hm1 (by decide +kernel) slots_le (by decide +kernel)
  have hs : SameOutside R.d0 st1.data.dmem (fun q ↦ InRange R.fb 160 q ∨ InRange R.out 24 q) :=
    fun q hq ↦ hm1.get?_mem0 hwf fun hW ↦ hq (written_in hwf (by decide +kernel)
      (fun w hw ↦ by
        have : w.r = 0 ∨ (w.r = 2 ∧ w.off + w.n ≤ 24) := by revert w; decide
        refine this.imp_right fun ⟨h2, h24⟩ b sz hb jj _ hj ↦ ?_
        rw [h2] at hb
        have e := Prod.mk.inj (Option.some.inj
          ((show (envOf R R.m0 [(R.out, 24)] 0).regions[2]? = some (R.out, 24) from rfl).symm.trans
            hb))
        rw [← e.1]
        exact NativeRustcVm.inRange_add (by omega) (by omega)) hW)
  have hF : Fr R 8 st1.data := ⟨hfr, hc0.trans hs fun q h ↦ h.imp_right fun h ↦
    NativeRustcVm.InRange.mono h (hin.noWrap G.outNw) G.outNw (le_refl _)
      (by show _ ≤ _ + phaseBytes; rw [phaseBytes_val]; omega)⟩
  have hh0 : (envOf R R.m0 [(R.out, 24)] 0).load 1 0 8 = stackArg R.m0 0 :=
    G.arg_load hc0 (i := 0) (by omega)
  have hhead : R.Head st1.data.dmem := by
    refine ⟨?_, ?_, ?_⟩
    · have := stored hm1 (r := 2) (o := 0) (sz := 24) rfl (by omega) (v := .reg .rsi) (by decide +kernel)
      rw [toUInt64_toNat]
      exact this
    · have := stored hm1 (r := 2) (o := 8) (sz := 24) rfl (by omega) (v := .load 1 0 8)
        (by decide +kernel)
      simp only [Sym.eval, hh0] at this
      rw [toUInt64_toNat]
      exact this
    · have := stored hm1 (r := 2) (o := 16) (sz := 24) rfl (by omega) (v := .reg .r9)
        (by decide +kernel)
      rw [toUInt64_toNat]
      exact this
  have hnp := G.np256
  have hnq := G.nq256
  have E : ∀ j, R.h ≠ 0 ∨ R.h = 0 → st1.pc = pcOf R j → Ent R j st1 := fun j _ hpc ↦ by
    refine ⟨hpc, hF, hhead, hm1.regs .rdi _ rfl, ?_, ?_, hm1.regs .rdx _ rfl,
      hm1.regs .r8 _ rfl, ?_, ?_⟩
    · refine (hm1.regs .rbp _ rfl).trans ?_
      show (envOf R R.m0 [(R.out, 24)] 0).load 1 (8 * 3) 8 = _
      exact G.arg_load hc0 (by omega)
    · refine (hm1.regs .rcx _ rfl).trans ?_
      exact shl3 (x := reg R.m0 .rcx) (by show R.np < 2 ^ 32; omega)
    · refine (hm1.regs .r9 _ rfl).trans ?_
      exact (ofNat_toNat' _).symm
    · refine (hm1.regs .r14 _ rfl).trans ?_
      simp only [Sym.eval, add_eval, mul_eval, Env.ofMachine_regs]
      rw [← ofNat_toNat' (R.m0.regs.get64 .rsi)]
      exact qend
  simp only [PcOk, SBool.eval, Sym.eval, eq_eval, and_self_eval, hh0] at hpc1
  rw [hp.label NativeRustcVmX64.Vm.WriteOpenings.label_20_at, show R.k + NativeRustcVmX64.Vm.WriteOpenings.b0Offset + b0.length = R.k + NativeRustcVmX64.Vm.WriteOpenings.b1Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.WriteOpenings.b0_next]] at hpc1
  by_cases h0 : R.h = 0
  · have he : (stackArg R.m0 0 == BitVec.ofNat 64 0) = true := by
      rw [beq_iff_eq]; exact BitVec.eq_of_toNat_eq h0
    rw [he] at hpc1
    exact .done _ (.inr ⟨E 157 (.inr h0) hpc1, h0⟩)
  · have he : (stackArg R.m0 0 == BitVec.ofNat 64 0) = false := by
      rw [beq_eq_false_iff_ne]; intro h; exact h0 (by rw [Run.h, h]; rfl)
    rw [he] at hpc1
    exact .done _ (.inl ⟨E 17 (.inl h0) hpc1, by omega⟩)

end

end NativeRustcVmX64.Wire.WriteOpenings
