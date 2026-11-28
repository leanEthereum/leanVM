module

public import NativeRustcVmX64.Whir.NovelEval.Inv

/-!
# `novel_eval`'s doubling loops (x86-64)

`outer`: from the doubling loop's head (`OInv j`, `b4`) the basis is complete (`j` the `What`s'
count: `Mid` at `b9`) or `b5` enters the inner loop (`IInv j 0`). `inner`: a turn of the inner
loop (`b6a`, `kmul`, `b7`) stores the product of basis word `t` and value `j` after the basis;
after the last, `b8` doubles the size and goes back to the head (`OInv (j + 1)`) or, the basis
long enough, to `b9` (`Mid`). `doubling`: from `OInv 0`, `Mid` (by `Sym.loop`).
-/

namespace NativeRustcVmX64.Whir.NovelEval

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.NovelEval NativeVm.Model
open NativeRustcVm.Whir NativeRustcVmX64.Whir.Leaf
open NativeRustcVm (Region WordAt WordsAt wordOf)
open NativeRustcVmX64.Field (midS frameS frameEnv)
open NativeRustcVmX64.Arrays (load8_eq wordAt_of_write eval_reg eval_lit eval_load eval_add
  eval_cmp_eq eval_not beq_add_left)

public section

theorem mul8 (a : Nat) : BitVec.ofNat 64 a * BitVec.ofNat 64 8 = BitVec.ofNat 64 (8 * a) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
  rw [Nat.mod_mul_mod, Nat.mul_comm]

theorem ofNat_toNat {x : BitVec 64} {n : Nat} (h : x.toNat = n) : x = BitVec.ofNat 64 n := by
  rw [← h, BitVec.ofNat_toNat, BitVec.setWidth_eq]

variable [Host] {k : Nat}

theorem hb4 (hp : Placed code k) : b4.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.NovelEval.b4Offset) :=
  b4_in_code.trans hp.1 (by simp [b4])
theorem hb5 (hp : Placed code k) : b5.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.NovelEval.b5Offset) :=
  b5_in_code.trans hp.1 (by simp [b5])
theorem hb6 (hp : Placed code k) : b6a.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.NovelEval.b6Offset) ∧
    b6b.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.NovelEval.b6Offset + b6a.length) := by
  have h := b6_in_code.trans hp.1 (by simp [b6])
  rw [← List.take_append_drop 3 b6] at h
  exact h.append
theorem hb7 (hp : Placed code k) : b7.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.NovelEval.b7Offset) :=
  b7_in_code.trans hp.1 (by simp [b7])
theorem hb8 (hp : Placed code k) : b8.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.NovelEval.b8Offset) :=
  b8_in_code.trans hp.1 (by simp [b8])

/-- **The doubling loop's head**: done, or into the inner loop. -/
theorem outer (hp : Placed code k) {m0 : MachineData} (hpre : NovelEvalPre m0) {j : Nat}
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NovelEval.b4Offset)) (hI : OInv m0 j st.data) :
    Eventually (step1 Host.exe) (fun s ↦ (s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NovelEval.b9Offset) ∧ Mid m0 s.data) ∨
      (s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NovelEval.b6Offset) ∧ IInv m0 j 0 s.data)) st := by
  obtain ⟨hS, hcs, hwh, hout, _⟩ := hpre
  have hF : 1104 ≤ novelEvalStack := by decide
  have hS1 := hS.1
  obtain ⟨hfmap, hfnw, hfe⟩ := frame_ok hS hF
  have hfr := hI.fr
  have hwf := hfr.wf (vars := fun _ ↦ 0) (ret := 0) hS hF
  have hwn64 := Arrays.lt_of_offStack hwh.1.2 hwh.2
  have hwn : wn m0 = (reg m0 .r8).toNat := rfl
  have hjle := hI.hj
  refine exec_at (hb4 hp) run_b4 hwf (by intro l h; cases h) hpc hfr.mid_match
    fun st1 hm1 hpc1 ↦ ?_
  have hfr1 := hfr.of_block hfr.mid_match hm1 hwf rfl (after_eq run_b4 ▸ b4_keeps)
  have hd1 : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have e1 : ∀ r ∈ [Reg64.rbp, .r12, .r14], reg st1.data r = reg st.data r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Match.reg_eq hfr.mid_match hm1 rfl rfl
  simp only [PcOk] at hpc1
  rw [eval_cmp_eq, eval_reg, eval_load, load8_eq, Env.ofMachine_regs,
    show (frameEnv m0 st.data 1104 (fun _ ↦ 0) 0).base 0 = fbOf m0 from rfl,
    Env.ofMachine_mem0, NativeRustcVm.wordOf_of_wordAt hI.ed, UInt64.toBitVec_ofBitVec,
    show st.data.regs.get64 .r12 = reg m0 .rcx + BitVec.ofNat 64 (8 * j) from hI.r12,
    beq_add_left, ofNat_beq (by omega) (by omega)] at hpc1
  obtain ⟨hT, hF1⟩ := Arrays.pc_cond hpc1
  by_cases hjw : j = wn m0
  · subst hjw
    refine .done _ (.inl ⟨(hT (by simp)).trans (hp.label NativeRustcVmX64.Vm.NovelEval.label_7_at), hfr1, ?_, ?_, ?_, ?_⟩)
    · exact ⟨hd1 ▸ hI.sp.out, hd1 ▸ hI.sp.cs⟩
    · rw [e1 .rbp (by simp)]; exact hI.rbp
    · rw [e1 .r14 (by simp)]; exact hI.r14
    · rw [hd1]; exact hI.basis
  · have hjw' : j < wn m0 := by have := hI.hj; omega
    have hpc1' : st1.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NovelEval.b5Offset) :=
      hF1 (by simp only [decide_eq_true_eq]; omega)
    -- `b5`: the value, the inner loop's registers
    have hrd : Readable st1.data (reg m0 .rcx + BitVec.ofNat 64 (8 * j)) 8 :=
      Readable.keep (Readable.sub hwh.1 (by omega)) hfr1.kept
    have hwf2 : (Env.ofMachine st1.data [(reg m0 .rcx + BitVec.ofNat 64 (8 * j), 8)]).WF :=
      Env.wf_of ⟨⟨hrd.1, hrd.2⟩, trivial⟩ (List.pairwise_singleton _ _)
    have hm2 : Match (Env.ofMachine st1.data [(reg m0 .rcx + BitVec.ofNat 64 (8 * j), 8)]) w5S
        st1.data :=
      match_ofMachine ⟨rfl, trivial⟩
        ⟨show reg st1.data .r12 = reg m0 .rcx + BitVec.ofNat 64 (8 * j) + BitVec.ofInt 64 0 by
            rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, e1 .r12 (by simp)]
            exact hI.r12, trivial⟩
        trivial trivial trivial
    refine exec_at (hb5 hp) run_b5 hwf2 (by intro l h; cases h) hpc1' hm2 fun st2 hm3 hpc2 ↦ ?_
    have hfr2 := hfr1.of_block hm2 hm3 hwf2 rfl (after_eq run_b5 ▸ b5_keeps)
    have hd2 : st2.data.dmem = st1.data.dmem := hm3.dmem_eq hwf2 rfl
    have harg := hfr.get?_arg hS hwh fun _ hr ↦ absurd hr List.not_mem_nil
    refine .done _ (.inr ⟨hpc2, hfr2, ⟨?_, ?_⟩, ?_, hjw', hI.lt, basis_pos m0 j, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_⟩)
    · rw [hd2, hd1]; exact hI.sp.out
    · rw [hd2, hd1]; exact hI.sp.cs
    · unfold EndAt; rw [hd2, hd1]; exact hI.ed
    · exact (Match.reg_eq (r := .r12) hm2 hm3 rfl rfl).trans ((e1 .r12 (by simp)).trans hI.r12)
    · show (st2.data.regs.get64 .rbp).toNat = _
      rw [Match.reg_eq (r := .rbp) (v := .reg .rbp) hm2 hm3 rfl rfl]
      exact (congrArg BitVec.toNat (e1 .rbp (by simp))).trans hI.rbp
    · refine (hm3.regs .rbx _ rfl).trans ?_
      exact (e1 .r14 (by simp)).trans hI.r14
    · refine (hm3.regs .r13 _ rfl).trans ?_
      rw [eval_load, load8_eq, whatOf_getD m0 hjw']
      show (wordOf st1.data.dmem (reg m0 .rcx + BitVec.ofNat 64 (8 * j) + BitVec.ofNat 64 0)).toBitVec = _
      rw [NativeRustcVm.addr_add_zero, hd1]
      refine congrArg UInt64.toBitVec (NativeRustcVm.wordOf_congr fun i hi ↦ ?_)
      rw [addr_add]
      exact harg _ (by omega)
    · refine (hm3.regs .r14 _ rfl).trans ?_
      rw [eval_add, eval_reg, eval_lit, Env.ofMachine_regs]
      show rspOf st1.data + _ = _
      rw [hfr1.rsp, show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, addr_add]
      rfl
    · rw [show reg st2.data .r15 = reg st1.data .rbp from hm3.regs .r15 _ rfl, e1 .rbp (by simp),
        hI.rbp]
      rfl
    · rw [hd2, hd1]; exact hI.basis
    · exact NativeRustcVm.wordsAt_nil _ _

end

end NativeRustcVmX64.Whir.NovelEval
