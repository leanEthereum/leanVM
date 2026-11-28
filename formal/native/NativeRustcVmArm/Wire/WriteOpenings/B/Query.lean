module

public import NativeRustcVmArm.Wire.WriteOpenings.B.Chunk
public import NativeRustcVmArm.Wire.WriteOpenings.B.Scan

/-!
# `write_openings`' queries' loop (`h = 0`, a leaf)

Opening `j` done (`b36_step`, `b36`, `b37`): the next query's head (`HeadB`), or the epilogue.
Query `j` found: its leaf copied (`copyB_step`). From the head: the epilogue (`queryB_loop`).
-/

namespace NativeRustcVmArm.Wire.WriteOpenings

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt wordOf)
open NativeRustcVmArm.Vm.WriteOpenings

public section

variable {R : Run} {j i : Nat} [Host]

/-- **Opening `j` done** (`b36`, `b37`): the next query, or the epilogue. -/
theorem b36_step (hp : Placed code R.k) (G : Geo R) (hlw0 : 0 < R.lw) {st : MachineState}
    (H : AtB36 R j i st) :
    Eventually (step1 Host.exe) (fun st' ↦ Post R st' ∨ HeadB R (j + 1) st') st := by
  have C := H.c
  have hj := C.lt
  have hnq := G.nq256
  have hwf := G.wf0 C.fr.kept
  have hm := frMatch G C.fr
  refine run_block G hp b36_in_code (by simp [b36]) run_b36 C.fr H.pc hwf hm rfl
    (writesOk_frame (by decide)) fun s1 hfr1 hm1 hpc1 ↦ ?_
  have hd1 : s1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have hk1 := regs_keep hm hm1 (rs := [.X1, .X2, .X3, .X4, .X5, .X8, .X11, .X12, .X19, .X21])
    (by decide)
  have hdone : R.Done s1.data.dmem (j + 1) := by
    rw [hd1]; exact done_succ C.hz C.mem C.pos C.leaf
  have hx0 : s1.data.regs.X0 = 1 := by
    apply UInt64.toBitVec_inj.mp
    rw [show s1.data.regs.X0 = s1.data.regs.getXReg .X0 from rfl, hm1.regs .X0 _ rfl]
    rfl
  have hc : (SBool.cmp .eq .W64 (.reg .X2) (.reg .X5)).not.eval (envOf R st.data []) =
      decide (j + 1 ≠ R.nq) := by
    simp only [SBool.eval, eq_apply, Sym.eval, Env.ofMachine_regs]
    rw [C.rb.x2, C.rb.x5, qa_cmp G hj]
    simp only [ne_eq, decide_not]
  simp only [PcOk, hc] at hpc1
  have hob := ob_le (j := j) (by omega)
  have oadd : ∀ o, R.oa (ob j + o) + BitVec.ofNat 64 1544 = R.oa (ob (j + 1) + o) := fun o ↦ by
    show R.out + _ + _ = R.out + _
    rw [NativeRustcVm.addr_add_add]
    congr 2
    unfold ob; omega
  by_cases hend : j + 1 = R.nq
  · simp only [hend, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
      at hpc1
    have hwf2 := G.wf0 hfr1.kept
    have hm2 := frMatch G hfr1
    refine run_block G hp b37_in_code (by simp [b37]) run_b37 hfr1
      (hpc1.trans (congrArg Host.addrOf rfl)) hwf2 hm2 rfl (writesOk_frame (by decide))
      fun s2 hfr2 hm2' hpc2 ↦ ?_
    have hd2 : s2.data.dmem = s1.data.dmem := hm2'.dmem_eq hwf2 rfl
    have hx0' : s2.data.regs.X0 = 1 := by
      rw [show s2.data.regs.X0 = s2.data.regs.getXReg .X0 from rfl,
        Match.reg_eq hm2 hm2' (v := .reg .X0) rfl rfl]
      exact hx0
    simp only [PcOk, hp.label (j := NativeRustcVmArm.Vm.WriteOpenings.b46Offset) NativeRustcVmArm.Vm.WriteOpenings.label_39_at] at hpc2
    refine Eventually.mono (end_spec hp G ⟨hpc2, hfr2, .inl ⟨hx0', ?_⟩⟩) fun _ h ↦ .inl h
    rw [hd2, ← hend]
    exact hdone
  · simp only [ne_eq, hend, not_false_eq_true, decide_true, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.WriteOpenings.b25Offset) NativeRustcVmArm.Vm.WriteOpenings.label_22_at]
      at hpc1
    refine .done _ (.inr ⟨hpc1, hfr1, by rw [hk1 .X1 (by simp)]; exact C.rb.x1,
      by rw [hk1 .X2 (by simp)]; exact C.rb.x2, by rw [hk1 .X3 (by simp)]; exact C.rb.x3,
      by rw [hk1 .X4 (by simp)]; exact C.rb.x4, by rw [hk1 .X5 (by simp)]; exact C.rb.x5,
      by rw [hk1 .X8 (by simp)]; exact C.rb.x8, ?_, ?_,
      by rw [hk1 .X11 (by simp)]; exact C.rb.x11, by rw [hk1 .X12 (by simp)]; exact C.rb.x12,
      by rw [hk1 .X19 (by simp)]; exact C.rb.x19, by rw [hk1 .X21 (by simp)]; exact C.rb.x21,
      by omega, C.hz, hlw0, hdone⟩)
    · rw [hm1.regs .X9 _ rfl]
      simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
      rw [C.rb.x9, oadd]
    · rw [hm1.regs .X10 _ rfl]
      simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
      rw [C.rb.x10, oadd]

/-- **The leaf copied**, from the query's position. -/
theorem copyB_step (hp : Placed code R.k) (G : Geo R) {st : MachineState}
    (H : FoundB R j i st) : Eventually (step1 Host.exe) (AtB36 R j i) st := by
  have rem : ∀ {t : Nat} {s : MachineState}, AtB34 R j i t s →
      Eventually (step1 Host.exe) (AtB36 R j i) s := fun h ↦
    eventually_trans _ _ _ _ (b34_step hp G h) fun _ h3 ↦ remB_loop hp G h3
  refine eventually_trans _ _ _ _ (b29_step hp G H) fun s1 h1 ↦ ?_
  rcases h1 with h1 | h1
  · refine eventually_trans _ _ _ _ (chunkB_loop hp G h1) fun s2 h2 ↦ ?_
    rcases h2 with h2 | h2
    · exact .done _ h2
    · exact rem h2
  · exact rem h1

/-- **The queries' loop** without levels, with a leaf, from query `j`: the epilogue. -/
theorem queryB_loop (hp : Placed code R.k) (G : Geo R) {st : MachineState} (H : HeadB R j st) :
    Eventually (step1 Host.exe) (Post R) st := by
  have hlw0 := H.lw0
  refine Sym.loop (fun n st ↦ ∃ j, n = R.nq - j ∧ HeadB R j st) (fun n st ⟨j, hn, H⟩ ↦ ?_)
    ⟨j, rfl, H⟩
  have hj := H.lt
  refine eventually_trans _ _ _ _ (headB_step hp G H) fun s1 h1 ↦ ?_
  refine eventually_trans _ _ _ _ (scanB_loop hp G h1) fun s2 h2 ↦ ?_
  rcases h2 with h2 | ⟨i, h2⟩
  · exact .done _ (.inl h2)
  refine eventually_trans _ _ _ _ (copyB_step hp G h2) fun s3 h3 ↦ ?_
  refine Eventually.mono (b36_step hp G hlw0 h3) fun s4 h4 ↦ ?_
  rcases h4 with h4 | h4
  · exact .inl h4
  · exact .inr ⟨R.nq - (j + 1), by omega, j + 1, rfl, h4⟩

end

end NativeRustcVmArm.Wire.WriteOpenings
