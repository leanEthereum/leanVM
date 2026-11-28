module

public import NativeRustcVmX64.Wire.WriteOpenings.A.Defs
public import NativeRustcVmX64.Transcript.Arith

/-!
# `write_openings`' next query (`h > 0`, x86-64)

From an opening written (`NextA`, `b23`): the registers reloaded from the frame, the opening's
addresses advanced, then the next query's head (`HeadA`) or, past the last query, the epilogue
with AL `1` (`b24`, `AtEnd`). The entry's path: the prologue to the first head (`start_step`, `b1`).
-/

namespace NativeRustcVmX64.Wire.WriteOpenings

open NativeRustcX64 hiding InRange SameOutside
open NativeRustcX64.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmX64.Vm.WriteOpenings
open NativeRustcVmX64.Transcript (Frame merge_one_mod)
open NativeRustcVm (WordAt WordsAt wordOf InRange SameOutside)

public section

variable {R : Run} {j : Nat} [Host]

/-- **The next query** (`b23`, `b24`). -/
theorem next_step (hp : Placed code R.k) (G : Geo R) {st : MachineState} (H : NextA R j st) :
    Eventually (step1 Host.exe) (fun st' ↦ HeadA R (j + 1) st' ∨ AtEnd R st') st := by
  have hj := H.lt
  have hnq := G.nq256
  have hwf := G.wf0 H.F.fr.kept (ret := 0)
  refine blk hp b23_in_code (by simp [b23]) run_b23 H.F H.pc hwf (frMatch H.F.fr) nofun (o := 8)
    (by decide +kernel) (by decide +kernel) fun s1 F1 hm1 hpc1 hs1 ↦ ?_
  have hW : ∀ p, InRange R.out phaseBytes p → ¬InRange R.fb 160 p := G.frame_out
  have hdone := G.done_keepW hs1 hW (by omega) H.done
  have hfl : ∀ {o v}, (o, v) ∈ wC R j →
      (envOf R st.data [] 0).load 0 o 8 = v := fun h ↦ fw_load (H.w.get h)
  have hpc1' := pc_cond hpc1 (b := decide (j + 1 ≠ R.nq)) (by
    simp only [SBool.eval, Sym.eval, eq_eval]
    rw [hfl (o := 64) (v := R.qa + BitVec.ofNat 64 (8 * (j + 1))) (by simp),
      hfl (o := 56) (v := R.qe) (by simp), beq_add (by omega) (by omega)]
    by_cases h : j + 1 = R.nq
    · simp [h]
    · simp [h, show 8 * (j + 1) ≠ 8 * R.nq by omega])
  have hax : boolRet s1.data = 1 := by
    unfold boolRet
    rw [show reg s1.data .rax = _ from hm1.regs .rax _ rfl]
    exact merge_one_mod _
  by_cases hl : j + 1 ≠ R.nq
  · rw [decide_eq_true hl, hp.label NativeRustcVmX64.Vm.WriteOpenings.label_2_at] at hpc1'
    simp only [↓reduceIte] at hpc1'
    have hk := fwK_of hwf hm1 (o' := 8) (by decide +kernel) (os := [32, 88, 96]) (by decide +kernel) (by decide +kernel)
    refine .done _ (.inl ⟨hpc1', F1, by omega, H.h0, hdone, ?_, ?_⟩)
    · refine FWs.cons (hk 32 (by simp) _ (H.w.get (by simp)))
        (FWs.cons (hk 88 (by simp) _ (H.w.get (by simp)))
        (FWs.cons (hk 96 (by simp) _ (H.w.get (by simp))) (FWs.cons ?_ (FWs.cons ?_ (FWs.nil _)))))
      · refine fw_eq (fw_write hm1 (o := 40) (by omega) (v := .bin .add .W64 (.lit 1544)
          (.load 0 40 8)) (by decide +kernel)) ?_
        simp only [Sym.eval, add_eval]
        rw [hfl (o := 40) (v := R.oa (ob j + 8)) (by simp)]
        exact lit_add (x := ob j + 8) (z := ob (j + 1) + 8) (by simp only [ob]; omega)
      · refine fw_eq (fw_write hm1 (o := 16) (by omega) (v := .bin .add .W64 (.lit 1544)
          (.load 0 16 8)) (by decide +kernel)) ?_
        simp only [Sym.eval, add_eval]
        rw [hfl (o := 16) (v := R.oa (ob j + 544)) (by simp)]
        exact lit_add (x := ob j + 544) (z := ob (j + 1) + 544) (by simp only [ob]; omega)
    · refine Regs.cons ((hm1.regs .rdi _ rfl).trans (hfl (o := 64) (by simp)))
        (Regs.cons ((hm1.regs .rsi _ rfl).trans (hfl (o := 104) (by simp)))
        (Regs.cons ((hm1.regs .rbp _ rfl).trans (G.arg_load H.F.chg (i := 3) (by omega)))
        (Regs.cons ((hm1.regs .rcx _ rfl).trans (hfl (o := 80) (by simp)))
        (Regs.cons ((hm1.regs .rdx _ rfl).trans (hfl (o := 72) (by simp)))
        (Regs.cons ((hm1.regs .r9 _ rfl).trans (hfl (o := 96) (by simp)))
        (Regs.cons ((hm1.regs .r11 _ rfl).trans (hfl (o := 24) (by simp)))
        (Regs.cons ?_
        (Regs.cons ((hm1.regs .r13 _ rfl).trans (hfl (o := 48) (by simp)))
        (Regs.cons ((hm1.regs .rbx _ rfl).trans (G.arg_load H.F.chg (i := 1) (by omega)))
        (Regs.cons ((hm1.regs .r14 _ rfl).trans (hfl (o := 56) (by simp))) (Regs.nil _)))))))))))
      refine (hm1.regs .r12 _ rfl).trans ?_
      simp only [Sym.eval, add_eval, envRegs]
      rw [H.r12]
      exact lit_add (x := ob j + 32) (z := ob (j + 1) + 32) (by simp only [ob]; omega)
  rw [decide_eq_false hl] at hpc1'
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc1'
  have hwf2 := G.wf0 F1.fr.kept (ret := 0)
  refine blk hp b24_in_code (by simp [b24]) run_b24 F1 (hpc1'.trans (congrArg Host.addrOf rfl))
    hwf2 (frMatch F1.fr) nofun (o := 8) (by decide +kernel) (by decide +kernel) fun s2 F2 hm2 hpc2 _ ↦ ?_
  have hd2 : s2.data.dmem = s1.data.dmem := hm2.dmem_eq hwf2 rfl
  refine .done _ (.inr ⟨(pc_jump hpc2).trans (hp.label NativeRustcVmX64.Vm.WriteOpenings.label_46_at), F2, .inl ⟨?_, ?_⟩⟩)
  · unfold boolRet
    rw [kreg hm2 (r := .rax) rfl rfl]
    exact hax
  · rw [hd2, show R.nq = j + 1 by omega]
    exact hdone

/-- **The levels' path's set-up** (`b1`): the first query's head. -/
theorem start_step (hp : Placed code R.k) (G : Geo R) {st : MachineState} (H : Ent R 17 st)
    (h0 : 0 < R.h) : Eventually (step1 Host.exe) (HeadA R 0) st := by
  have hlw := G.lw64
  have hnq := G.nq256
  have hwf := G.wf0 H.F.fr.kept (ret := 0)
  refine blk hp b1_in_code (by simp [b1]) run_b1 H.F H.pc hwf (frMatch H.F.fr) nofun (o := 8)
    (by decide +kernel) (by decide +kernel) fun s1 F1 hm1 hpc1 hs1 ↦ ?_
  have hW : ∀ p, InRange R.out phaseBytes p → ¬InRange R.fb 160 p := G.frame_out
  refine .done _ ⟨(pc_fall hpc1).trans (congrArg Host.addrOf rfl), F1, G.nq0, h0,
    ⟨(G.done_keepW (j := 0) hs1 hW (by omega) ⟨H.head, fun _ h ↦ absurd h
      (Nat.not_lt_zero _)⟩).1, fun _ h ↦ absurd h (Nat.not_lt_zero _)⟩, ?_, ?_⟩
  · refine FWs.cons (fw_eq (fw_write hm1 (o := 32) (by omega) (v := .reg .r9) (by decide +kernel))
      (by rw [show (Sym.reg .r9).eval _ = reg st.data .r9 from rfl, H.r9]))
      (FWs.cons (fw_eq (fw_write hm1 (o := 88) (by omega) (v := .bin .and .W32 (.reg .r9) (.lit 124))
        (by decide +kernel)) (by simp only [Sym.eval, envRegs]; rw [H.r9, and124 (by omega)]))
      (FWs.cons (fw_eq (fw_write hm1 (o := 96) (by omega) (v := .bin .add .W64 (.reg .r8) (.lit 24))
        (by decide +kernel)) (by simp only [Sym.eval, add_eval, envRegs]; rw [H.r8]))
      (FWs.cons (fw_eq (fw_write hm1 (o := 40) (by omega) (v := .bin .add .W64 (.reg .rbp) (.lit 32))
        (by decide +kernel)) (by simp only [Sym.eval, add_eval, envRegs]; rw [H.rbp]))
      (FWs.cons (fw_eq (fw_write hm1 (o := 16) (by omega)
        (v := .bin .add .W64 (.reg .rbp) (.lit 568)) (by decide +kernel))
        (by simp only [Sym.eval, add_eval, envRegs]; rw [H.rbp]))
      (FWs.nil _)))))
  · refine Regs.cons ((kreg hm1 rfl H.rdi).trans (by rw [Nat.mul_zero, NativeRustcVm.addr_add_zero]))
      (Regs.cons (hm1.regs .rsi _ rfl)
      (Regs.cons (kreg hm1 rfl H.rbp)
      (Regs.cons (kreg hm1 rfl H.rcx)
      (Regs.cons (kreg hm1 rfl H.rdx)
      (Regs.cons ?_
      (Regs.cons ((hm1.regs .r11 _ rfl).trans H.r8)
      (Regs.cons ?_
      (Regs.cons ?_
      (Regs.cons ((hm1.regs .rbx _ rfl).trans (G.arg_load H.F.chg (i := 1) (by omega)))
      (Regs.cons (kreg hm1 rfl H.r14) (Regs.nil _)))))))))))
    · refine (hm1.regs .r9 _ rfl).trans ?_
      simp only [Sym.eval, add_eval, envRegs]
      rw [H.r8]
    · refine (hm1.regs .r12 _ rfl).trans ?_
      simp only [Sym.eval, add_eval, envRegs]
      rw [H.rbp]
    · refine (hm1.regs .r13 _ rfl).trans ?_
      simp only [Sym.eval, envRegs]
      rw [H.r9, and3 (by omega)]

end

end NativeRustcVmX64.Wire.WriteOpenings
