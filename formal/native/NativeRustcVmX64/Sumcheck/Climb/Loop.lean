module

public import NativeRustcVmX64.Sumcheck.Climb.Call
public import NativeRustcVmX64.Code.Vm.HashPair.Names

/-!
# `climb`'s loop (x86-64)

`head_spec`: from the head at level `l`, `hash_pair`'s return with the next accumulator. `b5_spec`:
`b5` copies it over the accumulator, halves the position, counts the level, and leaves for
`NativeRustcVmX64.Vm.Climb.label_9` after the last level or goes back to the head. `loop_spec`: from the head, at
`NativeRustcVmX64.Vm.Climb.label_9` with the frame holding `climb N q P`.
-/

namespace NativeRustcVmX64.Sumcheck.Climb

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.Climb NativeRustcVmX64.Transcript
open NativeVm.Model LeanVM.Protocol NativeRustcVm.Sumcheck NativeRustcVm.Transcript

public section

section
variable [Labels] (env : Env)

theorem c6_eval (h : (env.regs .r13).toNat ≤ 124) : c6.eval env = false := by
  simp only [c6, SBool.eval, Sym.eval, CmpOp.apply, low_W64]
  by_cases h' : (env.regs .r13).toNat = 124
  · have : env.regs .r13 = BitVec.ofNat 64 124 := BitVec.eq_of_toNat_eq (by simpa using h')
    simp [this]
  · have : (env.regs .r13).ult (BitVec.ofNat 64 124) = true := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
    simp [this]

theorem c7_eval : c7.eval env = decide ((env.regs .r12).toNat % 2 = 0) := by
  simp only [c7, SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, low_ext]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj]
  simp only [low, BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [show (Width.W8).bits = 8 from rfl, Nat.and_one_is_mod]
  omega

theorem c5_eval {n : Nat} (h : (env.regs .r14).toNat = n) (hn : 1 ≤ n) :
    c5.eval env = decide (n = 1) := by
  simp only [c5, SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj, BitVec.toNat_sub, h]
  simp only [BitVec.toNat_ofNat, show (2 : Nat) ^ Width.W64.bits = 2 ^ 64 from rfl]
  omega

end

variable [Host] {N : Digest} {P : Array Digest} {m0 : MachineData} {k : Nat}

/-- **A level, up to `hash_pair`'s return**: its output the next accumulator. -/
theorem head_spec (hp : Placed code k)
    (hhp : Spec (Labels.label NativeRustcVmX64.Vm.HashPair.entryLabel) HashPairPre HashPairPost)
    (hpre : ClimbPre N P m0) {l : Nat} {m : MachineData} (hinv : Inv m0 N P l m) :
    Eventually (step1 Host.exe)
      (fun st ↦ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Climb.b5Offset) ∧
        Called m0 m (climbTo N (q0 m0) P (l + 1)).1 st.data)
      ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.Climb.b6Offset)⟩ := by
  have g := Geo.of_pre hpre
  have hst := hpre.1
  have hl := hinv.lt
  have h32 : P.size ≤ 32 := by
    have h1 : P.size = (reg m0 .r8).toNat := hpre.2.2.2.1
    have h2 : (reg m0 .r8).toNat ≤ 32 := hpre.2.2.1
    omega
  obtain ⟨hsib, hsnw, hsap⟩ := sib_at hpre hl hinv.st.same
  have hfnw := frame_noWrap (F := 160) hst (by rw [climbStack_eq]; omega)
  have hap := g.apart_of_stack hsap (o := 0) (k := 168) (by omega) (by omega)
  rw [off_zero] at hap
  have hwf : (headEnv m0 m l k).WF :=
    frame_wf ⟨Mapped.keeps (frame_mapped hst (by rw [climbStack_eq]; omega)) hinv.st.frame.kept,
      hfnw⟩
      (fun x hx ↦ by
        rw [List.mem_singleton] at hx; subst hx
        exact ⟨by simpa using hsib.mapped, hsnw⟩)
      (List.pairwise_pair.mpr (Apart.symm' hap))
  have hal : sibS.eval (headEnv m0 m l k) =
      (headEnv m0 m l k).base 1 + BitVec.ofInt 64 0 := by
    rw [ofInt_zero64, BitVec.add_zero, show (headEnv m0 m l k).base 1 =
      off (reg m0 .rcx) (32 * l) from rfl]
    simp only [sibS, Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
    rw [show m.regs.get64 .r15 = reg m0 .rcx from hinv.r15, off]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_mul, show (m.regs.get64 .r13).toNat = 4 * l from hinv.r13]
    simp only [BitVec.toNat_ofNat, show (2 : Nat) ^ Width.W64.bits = 2 ^ 64 from rfl]
    omega
  have hm : Match (headEnv m0 m l k) headS m :=
    match_ofMachine ⟨rfl, rfl, trivial⟩
      ⟨hinv.st.frame.rsp_eval, hinv.rbp.trans (eval_ptr0 8).symm,
        hinv.rbx.trans (eval_ptr0 40).symm, trivial⟩ trivial trivial ⟨hal, trivial⟩
  -- `b6`: within the path's slice.
  refine exec_then (infix_of b6_in_code (by simp [b6]) hp) exit_b6 hwf nofun hm
    fun st6 hm6 hpc6 ↦ ?_
  have hc6 : c6.eval (headEnv m0 m l k) = false :=
    c6_eval _ (by show (reg m .r13).toNat ≤ 124; rw [hinv.r13]; omega)
  simp only [PcOk, hc6, Bool.false_eq_true, ite_false] at hpc6
  -- `b7`: the sibling, the position's bit.
  refine exec_at (infix_of b7_in_code (by simp [b7]) hp) exit_b7 hwf nofun
    (hpc6.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.Climb.b6_next)) hm6 fun st7 hm7 hpc7 ↦ ?_
  have hc7 : c7.eval (headEnv m0 m l k) =
      decide ((climbTo N (q0 m0) P l).2 % 2 = 0) := by
    rw [c7_eval, show (headEnv m0 m l k).regs .r12 = reg m .r12 from rfl, hinv.r12]
    simp only [decide_eq_decide, UInt64.toNat_toBitVec]
    rw [← UInt64.toNat_inj, UInt64.toNat_mod]
    simp
  have hstep : (climbTo N (q0 m0) P (l + 1)).1 =
      if (climbTo N (q0 m0) P l).2 % 2 = 0 then hashPair (climbTo N (q0 m0) P l).1 (P[l]'hl)
      else hashPair (P[l]'hl) (climbTo N (q0 m0) P l).1 := by
    rw [climbTo_succ _ _ _ hl]
    rfl
  simp only [PcOk, hc7] at hpc7
  by_cases hq : (climbTo N (q0 m0) P l).2 % 2 = 0
  · -- Even: `b3`, `b4`.
    simp only [hq, decide_true, ite_true] at hpc7
    rw [hstep]
    simp only [hq, ↓reduceIte]
    refine exec_at (infix_of b3_in_code (by simp [b3]) hp) exit_b3 hwf nofun
      (hpc7.trans (hp.label NativeRustcVmX64.Vm.Climb.label_6_at)) hm7 fun st3 hm3 hpc3 ↦ ?_
    refine exec_at (infix_of b4_in_code (by simp [b4]) hp) exit_b4l hwf (fun _ _ ↦ rfl)
      (hpc3.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.Climb.b3_next)) hm3 fun st4 hm4 hpc4 ↦ ?_
    exact call_level hhp hpre hinv ok_even.1 ok_even.2.1 ok_even.2.2
      (Or.inl ⟨rfl, rfl, rfl, rfl⟩) hwf hm4 hpc4
  · -- Odd: `b8`, `b11`, `b4`.
    simp only [hq, decide_false, Bool.false_eq_true, ite_false] at hpc7
    rw [hstep]
    simp only [hq, ↓reduceIte]
    refine exec_at (infix_of b8_in_code (by simp [b8]) hp) exit_b8 hwf nofun
      (hpc7.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.Climb.b7_next)) hm7 fun st8 hm8 hpc8 ↦ ?_
    refine exec_at (infix_of b11_in_code (by simp [b11]) hp) exit_b11 hwf nofun
      (hpc8.trans (hp.label NativeRustcVmX64.Vm.Climb.label_7_at)) hm8 fun st11 hm11 hpc11 ↦ ?_
    refine exec_at (infix_of b4_in_code (by simp [b4]) hp) exit_b4r hwf (fun _ _ ↦ rfl)
      (hpc11.trans (hp.label NativeRustcVmX64.Vm.Climb.label_8_at)) hm11 fun st4 hm4 hpc4 ↦ ?_
    exact call_level hhp hpre hinv ok_odd.1 ok_odd.2.1 ok_odd.2.2
      (Or.inr ⟨rfl, rfl, rfl, rfl⟩) hwf hm4 hpc4

/-- **After `hash_pair`**: the next level's head, or `NativeRustcVmX64.Vm.Climb.label_9` after the last. -/
theorem b5_spec (hp : Placed code k) (hpre : ClimbPre N P m0) {l : Nat} {mh m : MachineData}
    (hinv : Inv m0 N P l mh) (hc : Called m0 mh (climbTo N (q0 m0) P (l + 1)).1 m) :
    Eventually (step1 Host.exe)
      (fun st ↦ (st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Climb.b12Offset) ∧ l + 1 = P.size ∧
          Fr m0 (climbTo N (q0 m0) P (l + 1)).1 st.data) ∨
        (st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Climb.b6Offset) ∧ Inv m0 N P (l + 1) st.data))
      ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.Climb.b5Offset)⟩ := by
  have g := Geo.of_pre hpre
  have hst := hpre.1
  have hl := hinv.lt
  have hfnw := frame_noWrap (F := 160) hst (by rw [climbStack_eq]; omega)
  have hwf := frame_wf (m0 := m0) (d := m) (F := 160) (rest := []) (vars := fun _ ↦ 0) (ret := 0)
    ⟨Mapped.keeps (frame_mapped hst (by rw [climbStack_eq]; omega)) hc.frame.kept, hfnw⟩
    (by simp) (List.pairwise_singleton _ _)
  have hm : Match (frameEnv m0 m 160 [] (fun _ ↦ 0) 0) retS m :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hc.frame.rsp_eval, trivial⟩ trivial trivial trivial
  refine exec_then (infix_of b5_in_code (by simp [b5]) hp) exit_b5 hwf nofun hm
    fun st hm' hpc ↦ ?_
  obtain ⟨hmid, hW, hws, hr12, hr13, hr14, hr15, hrbp, hrbx⟩ := ok_b5
  have hf' : Frame m0 160 slots 8 st.data := Frame.of_block hc.frame hwf hm' hmid slots_le
  set D := (climbTo N (q0 m0) P (l + 1)).1 with hD
  have hacc : NativeRustcVm.WordsAt st.data.dmem (off (fa m0) 8) D.toList :=
    wordsAt_written hm' (r := 0) rfl (by omega) hW fun i hi ↦
      load_ofMachine (o := 80 + 8 * i) rfl (by
        rw [← off_off]; exact wordsAt_iff.mp hc.hashed i (by simpa using hi))
  have hout : NativeRustcVm.WordAt st.data.dmem (off (fa m0) 72) (.ofBitVec (reg m0 .rdi)) :=
    keep_frame hwf hm' (writesIn_of_mid hmid) (by simp [NativeRustcVm.length_wordBytes])
      (fun w hw _ ↦ by simp only [NativeRustcVm.length_wordBytes]; have := hws w hw; omega)
      hc.out
  have hsame : NativeRustcVm.SameOutside m0.dmem st.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 climbStack) climbStack) :=
    SameOutside.mono (hc.same.trans (sameOutside_low hwf hm' (r := 0) rfl (hi := 160)
      (by omega) fun w hw ↦ ⟨(hws w hw).1, by have := hws w hw; omega⟩))
      fun q hq ↦ by rcases hq with hq | hq; exact hq; exact g.inRange_stack hq
  have hfr : Fr m0 D st.data := ⟨hf', hacc, hout, hsame⟩
  have h14 : (reg m .r14).toNat = P.size - l := by rw [hc.regs .r14 rfl]; exact hinv.r14
  have hc5 : c5.eval (frameEnv m0 m 160 [] (fun _ ↦ 0) 0) = decide (P.size - l = 1) :=
    c5_eval _ h14 (by omega)
  simp only [PcOk, hc5] at hpc
  by_cases hend : P.size - l = 1
  · simp only [hend, decide_true, ite_true] at hpc
    exact .done _ (Or.inl ⟨hpc.trans (hp.label NativeRustcVmX64.Vm.Climb.label_9_at), by omega, hfr⟩)
  · simp only [hend, decide_false, Bool.false_eq_true, ite_false] at hpc
    refine .done _ (Or.inr ⟨hpc.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.Climb.b5_next),
      ⟨hfr, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩)
    · rw [show reg st.data .r12 = _ from hm'.regs .r12 _ hr12]
      apply BitVec.eq_of_toNat_eq
      simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
      rw [show m.regs.get64 .r12 = reg mh .r12 from hc.regs .r12 rfl, hinv.r12,
        climbTo_succ _ _ _ hl]
      simp only [climbStep, UInt64.toNat_toBitVec, UInt64.toNat_div]
      rw [show shiftCount .W64 (BitVec.ofNat 64 1) = 1 from rfl]
      simp [Nat.shiftRight_eq_div_pow]
    · rw [show reg st.data .r13 = _ from hm'.regs .r13 _ hr13]
      simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs, BitVec.toNat_add,
        BitVec.toNat_ofNat]
      have h13 : (m.regs.get64 .r13).toNat = 4 * l := by
        rw [show m.regs.get64 .r13 = reg mh .r13 from hc.regs .r13 rfl]; exact hinv.r13
      have h32 : P.size ≤ 32 := by
        have h1 : P.size = (reg m0 .r8).toNat := hpre.2.2.2.1
        have h2 : (reg m0 .r8).toNat ≤ 32 := hpre.2.2.1
        omega
      rw [h13]
      simp only [show (2 : Nat) ^ Width.W64.bits = 2 ^ 64 from rfl]
      omega
    · rw [show reg st.data .r14 = _ from hm'.regs .r14 _ hr14]
      simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
      rw [BitVec.toNat_sub, show (m.regs.get64 .r14).toNat = P.size - l from h14]
      simp only [BitVec.toNat_ofNat, show (2 : Nat) ^ Width.W64.bits = 2 ^ 64 from rfl]
      omega
    · exact (hm'.regs .r15 _ hr15).trans ((hc.regs .r15 rfl).trans hinv.r15)
    · exact (hm'.regs .rbp _ hrbp).trans ((hc.regs .rbp rfl).trans hinv.rbp)
    · exact (hm'.regs .rbx _ hrbx).trans ((hc.regs .rbx rfl).trans hinv.rbx)

/-- **The loop**: from the head, at `NativeRustcVmX64.Vm.Climb.label_9` with `climb N q P` in the frame. -/
theorem loop_spec (hp : Placed code k)
    (hhp : Spec (Labels.label NativeRustcVmX64.Vm.HashPair.entryLabel) HashPairPre HashPairPost)
    (hpre : ClimbPre N P m0) {l : Nat} {m : MachineData} (hinv : Inv m0 N P l m) :
    Eventually (step1 Host.exe)
      (fun st ↦ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Climb.b12Offset) ∧ Fr m0 (climb N (q0 m0) P) st.data)
      ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.Climb.b6Offset)⟩ := by
  refine Sym.loop (fun n st ↦ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Climb.b6Offset) ∧
      ∃ l, P.size - l = n ∧ Inv m0 N P l st.data) (fun n st ⟨hpc, l, hn, hi⟩ ↦ ?_)
    ⟨rfl, l, rfl, hinv⟩
  obtain ⟨d, pc⟩ := st
  simp only at hpc
  subst hpc hn
  have hl := hi.lt
  refine Eventually.bind (head_spec hp hhp hpre hi) fun st ⟨hpc, hc⟩ ↦ ?_
  obtain ⟨d', pc'⟩ := st
  simp only at hpc
  subst hpc
  refine Eventually.mono (b5_spec hp hpre hi hc) fun st h ↦ ?_
  rcases h with ⟨hpc, hend, hfr⟩ | ⟨hpc, hinv'⟩
  · refine Or.inl ⟨hpc, ?_⟩
    rw [← climbTo_size, ← hend]
    exact hfr
  · exact Or.inr ⟨P.size - (l + 1), by omega, hpc, l + 1, rfl, hinv'⟩

end

end NativeRustcVmX64.Sumcheck.Climb
